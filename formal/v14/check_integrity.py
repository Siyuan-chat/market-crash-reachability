"""Independent V14 formal check without modifying the frozen V12 Lean library.

Source checks do not count as Lean proof acceptance. Unless --static is set,
each new Lean file is elaborated using the repository's pinned Mathlib and
its own explicitly audited theorem declarations.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "formal"))
from lean_declarations import relative_theorem_names, strip_lean_comments

PROOFS = {
    "OneSidedBV.lean": ["one_sided_BV_original_trace", "one_sided_BV_original_path"],
    "SublinearSevere.lean": [
        "sublinear_radial_exponent_gt_one",
        "normalized_radial_flow_pairing",
    ],
    "Robustness.lean": [
        "weighted_flow_decomposition",
        "paired_flow_can_have_positive_weighted_imbalance",
    ],
}
MANUSCRIPT_LABELS = {
    "lem:one-sided-BV",
    "thm:sublinear-severe",
    "prop:unbalanced-stability",
    "prop:heterogeneous-quadratic",
    "prop:turnover-dissipation",
    "prop:loss-breadth-eight",
}
FOUNDATIONAL_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def static_check() -> None:
    manuscript = (
        ROOT / "submission/v14-turnover-dissipation/main.tex"
    ).read_text(encoding="utf-8")
    for label in sorted(MANUSCRIPT_LABELS):
        if not re.search(r"\\label\{" + re.escape(label) + r"\}", manuscript):
            raise AssertionError(f"V14-R1 manuscript label absent: {label}")

    for filename, expected in PROOFS.items():
        path = ROOT / "formal/v14" / filename
        source = path.read_text(encoding="utf-8")
        code = strip_lean_comments(source)
        if re.search(r"\b(sorry|admit|axiom)\b", code):
            raise AssertionError(f"Unfinished proof/custom axiom in {filename}")
        actual = relative_theorem_names(source, root_namespace="MarketCrashV14")
        if actual != expected:
            raise AssertionError(f"Theorem declaration mismatch in {filename}: {actual} != {expected}")
        for name in expected:
            marker = f"#print axioms MarketCrashV14.{name}"
            if source.count(marker) != 1:
                raise AssertionError(f"Missing/duplicated per-theorem axiom audit: {marker}")

    source_index = ROOT / "formal/ORIGINAL_RESULT_MANIFEST.md"
    if len(re.findall(r"^\| (?:Theorem|Proposition) \d", source_index.read_text(), re.M)) != 16:
        raise AssertionError("Original 16-result manifest unexpectedly changed")
    print("PASS: V14 labels, declaration roster, axiom markers and original-result count")


def prove_and_audit() -> None:
    for filename, names in PROOFS.items():
        completed = subprocess.run(
            ["lake", "env", "lean", f"../v14/{filename}"],
            cwd=ROOT / "formal/lean", capture_output=True, text=True, check=False,
        )
        if completed.returncode:
            raise AssertionError(
                f"{filename}: Lean kernel/elaboration failed (exit {completed.returncode}):\\n"
                f"{completed.stdout}\\n{completed.stderr}"
            )
        out = completed.stdout
        printed = {}
        for full_name, dependencies, no_axioms in re.findall(
            r"^'MarketCrashV14\.([^']+)' (?:depends on axioms: \[([^]]*)\]|(does not depend on any axioms))$",
            out, re.M,
        ):
            if full_name in printed:
                raise AssertionError(f"Duplicate Lean axiom output: {full_name}")
            found = set(x.strip() for x in dependencies.split(",") if x.strip())
            if not no_axioms and not dependencies:
                raise AssertionError(f"Unexpected empty axiom report for {full_name}")
            unexpected = found - FOUNDATIONAL_AXIOMS
            if unexpected:
                raise AssertionError(f"{filename}/{full_name}: unexpected axioms {unexpected}")
            printed[full_name] = found
        if set(printed) != set(names):
            raise AssertionError(
                f"{filename}: incomplete axiom output, expected {names}, got {printed}; "
                f"stdout={out[:4000]!r}"
            )
        print(f"PASS: kernel elaboration and axiom audit, {filename}: {len(names)} theorem(s)")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--static", action="store_true", help="only inspect source; do not claim Lean verification")
    args = parser.parse_args()
    static_check()
    if not args.static:
        prove_and_audit()


if __name__ == "__main__":
    main()
