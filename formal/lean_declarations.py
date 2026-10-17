"""Lexical Lean theorem/lemma inventory with namespace-aware audit names.

Public API:
  strip_lean_comments(source) -> str  (positions/newlines are preserved)
  scan_declarations(source) -> list[LeanDeclaration]  (absolute Lean names)
  relative_theorem_names(source, root_namespace='MarketCrash') -> list[str]
  file_theorem_names(path, root_namespace='MarketCrash') -> list[str]

This is deliberately not a Lean elaborator. Private/protected/unsafe/partial
proof declarations and mutual blocks fail explicitly. The Lean compiler remains
the authority on syntax and name availability. Attributes, proof delimiters,
strings, characters, quoted identifiers and nested comments are lexed rather
than searched with a declaration regex. EOF implicitly closes open scopes, as
Lean does (in particular the project's anonymous noncomputable sections).
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import argparse
import bisect
import json
import unicodedata


class LeanDeclarationError(ValueError):
    """Input outside the supported, auditable Lean source subset."""


@dataclass(frozen=True)
class LeanDeclaration:
    kind: str
    full_name: str
    line: int
    column: int

    def relative_to(self, root_namespace: str = 'MarketCrash') -> str:
        prefix = root_namespace + '.'
        if not self.full_name.startswith(prefix):
            raise LeanDeclarationError(
                f'{self.line}:{self.column}: declaration {self.full_name!r} '
                f'is outside audited namespace {root_namespace!r}')
        return self.full_name[len(prefix):]


@dataclass(frozen=True)
class _Token:
    text: str
    pos: int
    line: int
    column: int
    identifier: bool = False


def _start(c: str) -> bool:
    return c == '_' or unicodedata.category(c).startswith('L')


def _continue(c: str) -> bool:
    return _start(c) or c.isdigit() or unicodedata.category(c).startswith('M') or c in "'!?"


def _literal_end(source: str, pos: int) -> int | None:
    """Return the end of a string/character literal starting here, if any."""
    n = len(source)
    if source[pos] == 'r' and (pos == 0 or not _continue(source[pos - 1])):
        j = pos + 1
        while j < n and source[j] == '#':
            j += 1
        if j < n and source[j] == '"':
            terminator = '"' + '#' * (j - pos - 1)
            end = source.find(terminator, j + 1)
            if end < 0:
                raise LeanDeclarationError(f'Unclosed raw string at offset {pos}')
            return end + len(terminator)
    if source[pos] == '"':
        j = pos + 1
        while j < n:
            if source[j] == '\\':
                j += 2
            elif source[j] == '"':
                return j + 1
            else:
                j += 1
        raise LeanDeclarationError(f'Unclosed string at offset {pos}')
    if source[pos] == "'" and (pos == 0 or not _continue(source[pos - 1])):
        # A real Lean character is one character or one escape, then a quote.
        j = pos + 1
        if j < n and source[j] == '\\':
            j += 2
            if j < n and source[j - 1] == 'u' and source[j] == '{':
                close = source.find('}', j + 1)
                if close < 0:
                    raise LeanDeclarationError(f'Unclosed character escape at offset {pos}')
                j = close + 1
        else:
            j += 1
        if j < n and source[j] == "'":
            return j + 1
    return None


def strip_lean_comments(source: str) -> str:
    chars = list(source)
    i, n = 0, len(source)
    while i < n:
        if source[i] == '«':
            end = source.find('»', i + 1)
            if end < 0:
                raise LeanDeclarationError(f'Unclosed quoted identifier at offset {i}')
            i = end + 1
            continue
        literal = _literal_end(source, i)
        if literal is not None:
            i = literal
            continue
        if source.startswith('--', i):
            j = source.find('\n', i)
            j = n if j < 0 else j
        elif source.startswith('/-', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if source.startswith('/-', j):
                    depth, j = depth + 1, j + 2
                elif source.startswith('-/', j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            if depth:
                raise LeanDeclarationError(f'Unclosed block comment at offset {i}')
        else:
            i += 1
            continue
        for k in range(i, j):
            if chars[k] not in '\r\n':
                chars[k] = ' '
        i = j
    return ''.join(chars)


def _tokens(source: str) -> list[_Token]:
    code = strip_lean_comments(source)
    starts = [0] + [i + 1 for i, c in enumerate(code) if c == '\n']
    out: list[_Token] = []
    i, n, group_depth = 0, len(code), 0
    while i < n:
        if code[i].isspace() or code[i] == '\ufeff':
            i += 1
            continue
        literal = _literal_end(code, i)
        if literal is not None:
            i = literal
            continue
        first, ident = i, False
        if code[i] == '«':
            end = code.find('»', i + 1)
            if end < 0:
                raise LeanDeclarationError(f'Unclosed quoted identifier at offset {i}')
            i, ident = end + 1, True
        elif _start(code[i]):
            i, ident = i + 1, True
            while i < n and _continue(code[i]):
                i += 1
        elif code[i].isdigit():
            i += 1
            while i < n and (code[i].isdigit() or code[i] == '_'):
                i += 1
        else:
            i += 1
        text = code[first:i]
        is_group = text in {'(', '[', '{', '⟨', '⦃', ')', ']', '}', '⟩', '⦄'}
        if is_group or group_depth == 0:
            line_index = bisect.bisect_right(starts, first) - 1
            out.append(_Token(text, first, line_index + 1,
                              first - starts[line_index] + 1, ident))
        if text in {'(', '[', '{', '⟨', '⦃'}:
            group_depth += 1
        elif text in {')', ']', '}', '⟩', '⦄'}:
            group_depth -= 1
    return out


_KEYWORDS = set("namespace section end theorem lemma def abbrev opaque instance example structure inductive class mutual where by if then else match with let in do fun forall for while return import open export variable universe set_option attribute syntax macro macro_rules notation infix infixl infixr prefix postfix deriving private protected noncomputable nonrec unsafe partial local scoped axiom constant extends at using have show from calc termination_by decreasing_by".split())


def _canonical_component(name: str) -> str:
    if name.startswith('«'):
        body = name[1:-1]
        if body and _start(body[0]) and all(_continue(c) for c in body[1:]) and body not in _KEYWORDS:
            return body
    return name


def _name(tokens: list[_Token], index: int) -> tuple[tuple[str, ...], int]:
    if index >= len(tokens) or not tokens[index].identifier:
        where = 'EOF' if index >= len(tokens) else f'{tokens[index].line}:{tokens[index].column}'
        raise LeanDeclarationError(f'{where}: expected an explicit Lean declaration/scope name')
    parts = [_canonical_component(tokens[index].text)]
    index += 1
    while index < len(tokens) and tokens[index].text == '.':
        if index + 1 >= len(tokens) or not tokens[index + 1].identifier:
            raise LeanDeclarationError(f'{tokens[index].line}:{tokens[index].column}: malformed qualified name')
        parts.append(_canonical_component(tokens[index + 1].text))
        index += 2
    return tuple(parts), index


def scan_declarations(source: str) -> list[LeanDeclaration]:
    tokens = _tokens(source)
    # frame = (kind, written name, namespace before opening)
    frames: list[tuple[str, tuple[str, ...], tuple[str, ...]]] = []
    namespace: tuple[str, ...] = ()
    delimiters: list[str] = []
    closing = {')': '(', ']': '[', '}': '{', '⟩': '⟨', '⦄': '⦃'}
    modifiers: list[str] = []
    rejected = {'private', 'protected', 'unsafe', 'partial', 'local', 'scoped'}
    declarations: list[LeanDeclaration] = []
    i = 0
    while i < len(tokens):
        token = tokens[i]
        word = token.text
        if word in {'(', '[', '{', '⟨', '⦃'}:
            delimiters.append(word)
            i += 1
            continue
        if word in closing:
            if not delimiters or delimiters.pop() != closing[word]:
                raise LeanDeclarationError(f'{token.line}:{token.column}: unbalanced delimiter {word!r}')
            i += 1
            continue
        if delimiters:
            i += 1
            continue
        if word == '`':
            # A quoted Name is data, not a command. Syntax quotations are
            # delimited by parentheses and are skipped by delimiter depth.
            if i + 1 < len(tokens) and tokens[i + 1].identifier:
                _, i = _name(tokens, i + 1)
                continue
        if word in rejected or word in {'noncomputable', 'nonrec'}:
            modifiers.append(word)
            i += 1
            continue
        if word == '@':
            i += 1
            continue
        if word == 'mutual':
            raise LeanDeclarationError(f'{token.line}:{token.column}: mutual blocks are unsupported; refusing partial audit')
        if word == 'namespace':
            parts, i = _name(tokens, i + 1)
            frames.append(('namespace', parts, namespace))
            namespace = parts[1:] if parts[0] == '_root_' else namespace + parts
            modifiers.clear()
            continue
        if word == 'section':
            parts: tuple[str, ...] = ()
            i += 1
            if i < len(tokens) and tokens[i].line == token.line and tokens[i].identifier:
                parts, i = _name(tokens, i)
            frames.append(('section', parts, namespace))
            modifiers.clear()
            continue
        if word == 'end':
            i += 1
            parts = ()
            if i < len(tokens) and tokens[i].line == token.line and tokens[i].identifier:
                parts, i = _name(tokens, i)
            if not frames:
                raise LeanDeclarationError(f'{token.line}:{token.column}: end without an open scope')
            kind, written, previous = frames.pop()
            if parts and parts not in (written, written[-1:], namespace if kind == 'namespace' else written):
                raise LeanDeclarationError(f'{token.line}:{token.column}: end {".".join(parts)} mismatches {kind} {".".join(written)}')
            namespace = previous
            modifiers.clear()
            continue
        if word in {'theorem', 'lemma'}:
            bad = set(modifiers) & rejected
            if bad:
                raise LeanDeclarationError(f'{token.line}:{token.column}: unsupported proof modifiers {sorted(bad)}')
            parts, i = _name(tokens, i + 1)
            full = parts[1:] if parts[0] == '_root_' else namespace + parts
            if not full:
                raise LeanDeclarationError(f'{token.line}:{token.column}: empty declaration name')
            declarations.append(LeanDeclaration(word, '.'.join(full), token.line, token.column))
            modifiers.clear()
            continue
        modifiers.clear()
        i += 1
    if delimiters:
        raise LeanDeclarationError('Unclosed Lean delimiter at EOF')
    return declarations


def relative_theorem_names(source: str, root_namespace: str = 'MarketCrash') -> list[str]:
    return [decl.relative_to(root_namespace) for decl in scan_declarations(source)]


def file_theorem_names(path: str | Path, root_namespace: str = 'MarketCrash') -> list[str]:
    return relative_theorem_names(Path(path).read_text(encoding='utf-8'), root_namespace)


def _self_test() -> None:
    tests = [
        ('namespace MarketCrash\ntheorem a : True := by trivial\nend MarketCrash', ['a']),
        ('namespace MarketCrash\nnamespace A.B\nlemma x : True := by trivial\nend A.B\nend MarketCrash', ['A.B.x']),
        ('namespace MarketCrash\nsection named\nnamespace A\nsection\ntheorem q : True := by trivial\nend\nend A\nend named\nlemma z : True := by trivial', ['A.q', 'z']),
        ('noncomputable section\nnamespace MarketCrash\nnoncomputable theorem x : True := by trivial\nend MarketCrash', ['x']),
        ('namespace MarketCrash\n/- theorem bad /- namespace Bad -/ lemma no -/\n-- theorem nope\ntheorem/- gap -/yes : True := by trivial', ['yes']),
        ('namespace MarketCrash\ndef s := "theorem fake /- -- namespace X"\ntheorem yes : True := by trivial', ['yes']),
        ('namespace MarketCrash\ndef s := r#"/- theorem fake -- "#\nlemma yes : True := by trivial', ['yes']),
        ('namespace MarketCrash\ndef c := \'"\'\nlemma yes : True := by trivial', ['yes']),
        ('namespace MarketCrash\nnamespace A.B\ntheorem A.B.x : True := by trivial\ntheorem _root_.MarketCrash.y : True := by trivial', ['A.B.A.B.x', 'y']),
        ('theorem MarketCrash.x : True := by trivial', ['x']),
        ('namespace MarketCrash\n@[simp]\ntheorem f\' : True := by trivial', ["f'"]),
        ('namespace MarketCrash\nnamespace «A.B»\nlemma «x.y» : True := by trivial', ['«A.B».«x.y»']),
        ('namespace MarketCrash\nlemma λ₁ : True := by trivial', ['λ₁']),
        ('namespace MarketCrash\n/- -- quote " /- nested -/ -/\nlemma x : True := by trivial', ['x']),
        ('namespace MarketCrash\nnamespace A\nend\nnamespace B\nlemma y : True := by trivial', ['B.y']),
        ('namespace MarketCrash\nset_option maxHeartbeats 1000 in\nlemma y : True := by trivial', ['y']),
        ('namespace «MarketCrash»\nlemma «a/-not-comment-/b» : True := by trivial', ['«a/-not-comment-/b»']),
        ('namespace MarketCrash\nlemma «theorem» : True := by trivial', ['«theorem»']),
    ]
    for source, expected in tests:
        got = relative_theorem_names(source)
        assert got == expected, (source, got, expected)
        cleaned = strip_lean_comments(source)
        assert len(cleaned) == len(source)
        assert [i for i, c in enumerate(cleaned) if c == '\n'] == [i for i, c in enumerate(source) if c == '\n']
    bad = [
        'namespace MarketCrash\nprivate theorem x : True := by trivial',
        'namespace MarketCrash\nprotected lemma x : True := by trivial',
        'namespace MarketCrash\nprivate\nnoncomputable\ntheorem x : True := by trivial',
        'namespace MarketCrash\nunsafe theorem x : True := by trivial',
        'namespace MarketCrash\n/- unfinished',
        'namespace MarketCrash\nend Wrong',
        'end MarketCrash',
        'namespace MarketCrash\ntheorem : True := by trivial',
        'namespace Other\nlemma x : True := by trivial',
        'namespace MarketCrash\nmutual\ndef x := 1\nend',
        'namespace MarketCrash\nlemma x : (True := by trivial',
    ]
    for source in bad:
        try:
            relative_theorem_names(source)
        except LeanDeclarationError:
            pass
        else:
            raise AssertionError(f'Expected explicit rejection: {source}')
    print(f'PASS: {len(tests)} supported fixtures, {len(bad)} explicit rejection fixtures')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paths', nargs='*', type=Path)
    parser.add_argument('--root-namespace', default='MarketCrash')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        _self_test()
    for path in args.paths:
        print(json.dumps({'path': str(path), 'declarations': file_theorem_names(path, args.root_namespace)}, ensure_ascii=False))
