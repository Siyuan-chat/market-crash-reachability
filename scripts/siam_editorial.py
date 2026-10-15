"""Explicit, reversible, nonmathematical edits for the SIFIN derivative only."""
import re

BASELINE_COMMIT = 'ea831c44f5b77b7039dd6644f6f0a791bb74d176'
JOURNALS = {
    'SIAM Journal on Financial Mathematics': 'SIAM J. Financial Math.',
    'Mathematics of Operations Research': 'Math. Oper. Res.',
    'Mathematical Finance': 'Math. Finance',
    'The Review of Financial Studies': 'Rev. Financ. Stud.',
    'Journal of Econometrics': 'J. Econometrics',
    'Annals of Operations Research': 'Ann. Oper. Res.',
    'Quantitative Finance': 'Quant. Finance',
    'American Economic Review': 'Amer. Econ. Rev.',
    'Econometrica': 'Econometrica',
    'The Journal of Finance': 'J. Finance',
    'Review of Finance': 'Rev. Finance',
    'Journal of Financial Markets': 'J. Financial Markets',
    'Stochastic Models': 'Stoch. Models',
}

CALLOUTS = {
    'main': {
        'fig:abcnum': 'The common trading experiment across the three response regimes is illustrated in Figure~\\ref{fig:abcnum}.',
        'fig:localrate': 'Figure~\\ref{fig:localrate} compares the numerical small-rate loss with the quadratic coefficient.',
        'fig:multiday-crisis-trigger': 'Figure~\\ref{fig:multiday-crisis-trigger} illustrates the distinction between repeated closing-limit losses and the systemic crisis criterion.',
        'fig:v7path': 'Figure~\\ref{fig:v7path} displays the price paths of the certified construction.',
        'fig:v7rates': 'Figure~\\ref{fig:v7rates} displays the corresponding gross execution rates.',
    },
    'supplementary': {
        'fig:streak-witness': 'Figure~\\ref{fig:streak-witness} displays the earlier exploratory two-session price paths.',
        'fig:streak-ledger': 'Figure~\\ref{fig:streak-ledger} displays the ledgers and rates of that exploratory witness.',
        'fig:market': 'Figures~\\ref{fig:market} and~\\ref{fig:elasticity} present the market primitives and local elasticity examples, respectively.',
        'fig:sharp': 'Figures~\\ref{fig:sharp} and~\\ref{fig:heatmap} illustrate the model-specific full-coverage boundary. Figures~\\ref{fig:resource} and~\\ref{fig:nscale} illustrate the necessary resource bounds and their asset-count dependence.',
        'fig:continuous': 'Figure~\\ref{fig:continuous} displays the bounded-rate continuous example and its closed dollar ledgers. Figure~\\ref{fig:regulation} compares the rate and price-limit exclusion bounds. Figures~\\ref{fig:streak-rate} and~\\ref{fig:streak-full-obstruction} show the scalar necessary-rate floor and the region covered by the all-asset obstruction.',
        'fig:v7bracket': 'Figure~\\ref{fig:v7bracket} distinguishes the necessary rate floor from the certified feasible rate; Figure~\\ref{fig:v7cutN} displays the funding-capacity constraint as the falling majority grows.',
        'fig:paths': 'Figure~\\ref{fig:paths} displays terminally dollar-closed price paths, while Figure~\\ref{fig:closure} distinguishes dollar closure from net share positions. Figure~\\ref{fig:finite} illustrates the construction families with bounded feasible resources. Figure~\\ref{fig:oldrejected} shows why the earlier pulse example does not satisfy the newer execution restrictions.',
    },
}

AVAILABILITY_OLD = 'The accompanying reproducibility package includes \\path{verification/certify_streak_interval.py} (exact rational root isolation and outward-rounded fixed-point enclosures), \\path{verification/verify_consistency.py}, numerical sensitivity scripts, figure-generating code, machine-readable outputs, the LaTeX source, and a file-hash manifest. Reproduction commands and software requirements are in \\path{REPRODUCE.md}. The certificate was rerun from source, with independent floating-point ODE and exact-rational consistency checks. A versioned, checksum-indexed reproducibility archive accompanies this manuscript; the computations are tied to the supplied source and certificate versions.'
AVAILABILITY_NEW = r'''The research code, numerical data, certificates, and reproduction instructions are publicly available at \url{https://github.com/Siyuan-chat/market-crash-reachability}. The computational baseline for this SIFIN edition is identified by \href{https://github.com/Siyuan-chat/market-crash-reachability/tree/ea831c44f5b77b7039dd6644f6f0a791bb74d176}{commit \texttt{ea831c4}}. The repository includes \path{verification/certify_streak_interval.py} (exact rational root isolation and outward-rounded fixed-point enclosures), \path{verification/verify_consistency.py}, numerical sensitivity scripts, figure-generating code, and machine-readable outputs. Reproduction commands and software requirements are in \path{REPRODUCE.md}; the checksum manifest is \path{release/SHA256SUMS}. The certificate was rerun from source, with independent floating-point ODE and exact-rational consistency checks. The SIFIN build instructions describe the separate, nonmathematical bibliography and figure-style transformations used for this edition.'''


def editorial_changes(text, kind, *, reverse=False):
    """Only named figure callouts and the exact availability paragraph may change."""
    for label, sentence in CALLOUTS[kind].items():
        assert not re.search(r'\$|\\(?:begin|end)\{|\\[()[\]]', sentence), 'No mathematical additions'
        addition = sentence + '\n\n'
        if reverse:
            assert text.count(addition) == 1, 'Missing/changed editorial callout: '+label
            text = text.replace(addition, '', 1)
        else:
            blocks = list(re.finditer(r'\\begin\{figure\}.*?\\end\{figure\}', text, re.S))
            matches = [m for m in blocks if r'\label{'+label+'}' in m[0]]
            assert len(matches) == 1, 'Missing/ambiguous figure: '+label
            position = matches[0].start()
            text = text[:position] + addition + text[position:]
    if kind == 'main':
        assert not re.search(r'\$|\\(?:begin|end)\{|\\[()[\]]', AVAILABILITY_NEW), 'Availability edit must contain no mathematics'
        before, after = (AVAILABILITY_NEW, AVAILABILITY_OLD) if reverse else (AVAILABILITY_OLD, AVAILABILITY_NEW)
        assert text.count(before) == 1, 'Availability baseline changed'
        text = text.replace(before, after, 1)
    return text


def bibliography(text):
    pattern = r'(journal\s*=\s*\{)([^}]+)(\})'
    fields = re.findall(pattern, text)
    assert {x[1] for x in fields} == set(JOURNALS), 'Review journal mapping for changed bibliography'
    result = re.sub(pattern, lambda m: m[1]+JOURNALS[m[2]]+m[3], text)
    assert re.sub(pattern, r'\1JOURNAL\3', text) == re.sub(pattern, r'\1JOURNAL\3', result), 'Non-journal metadata changed'
    return result
