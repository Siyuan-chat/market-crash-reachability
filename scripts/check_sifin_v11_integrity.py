"""Exact historical-result audit for the SIFIN V1.1 editorial restructuring.

This verifies source preservation, not theorem truth. The fixed source
commit predates all V1.1 edits and is intentionally never updated.
CI must check out full git history before running this script.
"""
from __future__ import annotations

from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCE = "submission/v14-turnover-dissipation/main.tex"
BASELINE = "bebc17df99174ad7dabe2bd2cc41a9216b04c230"
current = (ROOT / SOURCE).read_text(encoding="utf-8")
try:
    original = subprocess.check_output(
        ["git", "show", f"{BASELINE}:{SOURCE}"],
        cwd=ROOT, text=True, encoding="utf-8", stderr=subprocess.PIPE
    )
except subprocess.CalledProcessError as exc:
    raise RuntimeError(
        "Historical SIFIN source commit unavailable; CI checkout needs fetch-depth: 0"
    ) from exc


def result_environments(s: str) -> list[str]:
    out = []
    for name in ("assumption", "definition", "theorem", "proposition", "lemma"):
        out.extend(re.findall(
            rf"\\begin\{{{name}\}}(?:\[[^\]]*\])?[\s\S]*?\\end\{{{name}\}}", s
        ))
    return sorted(out)


def proof_environments(s: str) -> list[str]:
    return sorted(re.findall(
        r"\\begin\{proof\}(?:\[[^\]]*\])?[\s\S]*?\\end\{proof\}", s
    ))


def numbered_equations(s: str) -> list[str]:
    return sorted(re.findall(
        r"\\begin\{equation\}[\s\S]*?\\end\{equation\}", s
    ))


for name, selector, expected in (
    ("formal result and model statements", result_environments, 24),
    ("proof environments", proof_environments, 21),
    ("numbered equation blocks", numbered_equations, 86),
):
    old, new = selector(original), selector(current)
    assert len(old) == len(new) == expected, (name, len(old), len(new))
    assert old == new, (name, "historical mathematical contents changed")
    print(f"PASS exact preservation of {expected} {name}")

old_labels = set(re.findall(r"\\label\{([^}]+)\}", original))
new_labels = re.findall(r"\\label\{([^}]+)\}", current)
assert len(new_labels) == len(set(new_labels)), "Duplicate LaTeX labels"
assert old_labels <= set(new_labels), ("Removed labels", old_labels - set(new_labels))
assert set(new_labels) - old_labels == {"app:rolling-support"}

abstract = current.split(r"\begin{abstract}", 1)[1].split(
    r"\end{abstract}", 1
)[0]
assert "$" not in abstract and r"\(" not in abstract and r"\[" not in abstract
assert r"\begin{equation}" not in abstract and r"\cite" not in abstract

order = [
    r"\section{Introduction}",
    r"\section{The market: assumptions, execution, and price dynamics}",
    r"\section{Structural Barriers and Robustness}",
    r"\section{Reachability Regimes under Power-Law Impact}",
    r"\section{Execution Resources and Turnover Bounds}",
    r"\section{Reachability under Bounded Execution Rates}",
    r"\section{Rolling Price Limits: Constrained Realizations}",
    r"\section{Discussion}",
    r"\section{Conclusion}",
]
positions = [current.index(heading) for heading in order]
assert positions == sorted(positions), "Section hierarchy regressed"

start3 = current.index(r"\section{Structural Barriers and Robustness}")
end3 = current.index(r"\section{Reachability Regimes under Power-Law Impact}")
barriers = current[start3:end3]
assert r"\label{prop:unbalanced-stability}" in barriers
assert r"\label{prop:heterogeneous-quadratic}" in barriers

start4 = end3
end4 = current.index(r"\section{Execution Resources and Turnover Bounds}")
reach = current[start4:end4]
assert r"\label{thm:sublinear-severe}" in reach
assert r"\label{thm:critical}" in reach
assert r"\paragraph{Construction in four steps}" in reach

start7 = current.index(r"\section{Rolling Price Limits: Constrained Realizations}")
end7 = current.index(r"\section{Discussion}")
rolling = current[start7:end7]
for label in ("thm:no-second-global", "prop:streak-precondition",
              "prop:market-cut", "prop:certified-v7", "prop:loss-breadth-eight"):
    assert rf"\label{{{label}}}" in rolling
assert r"\label{tab:loss-breadth}" not in rolling
assert r"\label{tab:loss-breadth}" in current.split(
    r"\section{Reproducing the uniform-band loss--breadth witnesses}", 1
)[1]
assert r"\label{tab:sensitivity}" in current.split(
    r"\section{Supplementary Rolling-Band Diagnostics}", 1
)[1]

discussion = current[end7:current.index(r"\section{Conclusion}", end7)]
assert r"\begin{theorem}" not in discussion
assert r"\begin{proposition}" not in discussion

assert current.count(r"\label{fig:v7path}") == 1
assert current.count(r"\label{fig:v7rates}") == 1
assert current.count(r"\label{tab:loss-breadth-additional}") == 1
print("PASS SIFIN V1.1 abstract, result hierarchy, appendix placement and labels")
