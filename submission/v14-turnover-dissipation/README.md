# V14 public research manuscript

**[Open the compiled V14 manuscript PDF](manuscript.pdf)** · [Build provenance](manuscript-build.json).

The PDF is built by GitHub Actions and committed to this directory after a successful source/build check. V14 is the latest publicly available GitHub research manuscript. V14 was deposited on [Zenodo, DOI 10.5281/zenodo.23478787](https://doi.org/10.5281/zenodo.23478787), on 20 October 2026; its displayed checksum matches this PDF. V13 remains a preserved archival edition. No journal acceptance is asserted. See [versions](../../docs/VERSIONS.md).


This **complete English manuscript source** extends the published V13 preprint.
Section 4 now includes a [continuous power-law exponent analysis](../../docs/V14_CONTINUOUS_EXPONENT_SPECTRUM.md)
covering the two thresholds at p=1 and p=2, with explicit inventory-growth
comparisons. A new **uniform-resource severe-loss theorem** extends the
partial-coverage global construction from p=0 to every fixed 0<=p<1,
with a complete generalized-radius appendix proof. No bounds uniform
as p approaches 1 or finite gross-rate feasibility are claimed.
See [new theorem proof audit](../../docs/V14_SUBLINEAR_SEVERE_PROOF_AUDIT.md).

The new **Proposition 5.2 (Turnover--dissipation bound under constant impact)**
and its analytical proof appear in Section 5 of [main.tex](main.tex), with
a time-kernel interpretation and three distinct sharpening directions in
the Discussion. [Detailed proof audit](../../docs/V14_TURNOVER_DISSIPATION_AUDIT.md).

The sublinear uniform-resource theorem now follows the continuous-spectrum discussion and precedes the sharp all-asset horizon subsection. Its mathematical statement is unchanged; the printed theorem numbering updates automatically. The polynomial-root bracket in Section 7 is already correct and independently checked.

Section 7 now includes an independently rerunnable **80% coverage / over 10.8% target-price decline** interval witness under uniform +/-25% rolling bands, a comparison table of six new internally certified paths, and a reproduction appendix. See [loss-breadth certificate methodology](../../docs/LOSS_BREADTH_CERTIFICATES.md), [rational verifier](../../verification/loss_breadth_certified.py), [per-case summary](../../verification/loss_breadth_witness_summary.csv), and [independent SciPy ODE audit](../../verification/loss_breadth_ode_crosscheck.py). The relaxed M<5 row is visibly distinguished from the original M<3 budget. This **new proposition** is not covered by the original Lean formalization.

Section 8 now also derives **two purely theoretical robustness bounds**:
an exponentially recovery-weighted bound on the mean systemic loss when
dollar flows in the modeled basket are not perfectly matched, and a
weighted-flow bound for asset-specific quadratic impact strengths.
An explicit two-asset, **terminally dollar-closed** matched-pulse
counterexample shows that heterogeneous impact can invalidate the
homogeneous elasticity barrier even when both per-asset exponents equal 2.
These calculations leave the original barrier theorems, existing nine
appendices, and all interval-witness inputs unchanged. They use no market
observations or empirical calibration and are not included in the
historical Lean formalization.

The published V13 manuscript, PDF, Lean proofs, and archived numeric certificates
are unchanged. This GitHub research manuscript now includes new internally verified numerical witnesses, but does not claim optimal controls or impossibility results. The fixed [V14 Zenodo deposit](https://doi.org/10.5281/zenodo.23478787) is verified; see [versions](../../docs/VERSIONS.md) for the newer live SSRN revision and unresolved PDF/source identity. The additional V14 propositions and sublinear-impact severe-loss theorem,
including the two Section 8 robustness propositions, have not been
Lean-formalized and are not counted in the original 16/16 Lean acceptance report.

For constant per-share impact and absolutely continuous paired-dollar controls,
if prices are bounded below by a>0 and |S_i-F|<=b, writing
V_2(T)=sum_i(S_i(T)^2-F^2)/2 gives

    0 <= -V_2(T) <= [eta*b/(a*exp(1))] * M(T).

Under two hypothetical 25% rolling bands a=b=9F/16, so with eta=1,
-V_2(T) <= M(T)/exp(1). In the full-coverage N=10, F=eta=1,
2% ordinary-loss example, M>=0.5382, **not** an exclusion at M<=3.

The gross-versus-net trade relation is a <= bound; see the proof audit.
In the paper, executed-dollar flow rates are written as dot X_i; q_i remains
reserved for log prices in Section 2.

Rebuild with:
    python scripts/check_v14_resource_bound.py
    python scripts/build_v14_resource_bound.py

The build takes unchanged figure PDFs from the earlier English source directory and
writes its new output to build/v14-turnover-dissipation.

Independent dollar-ledger reconstruction tests (not a mathematical proof):

    python scripts/check_sublinear_severe_extension.py


## Additional certified loss--breadth comparisons

Appendix I now displays six further prescribed controls beyond the six main
Table 3 interval witnesses, covering k=7, 9, and 10, with M<3 and separately
relaxed M<4/M<7 turnover cases. All twelve exact rational schedules, their
SHA-256 input/program manifest, and the 24-cell research matrix are retained
in [`verification/loss_breadth/`](../../verification/loss_breadth/).

Reproduce with `python verification/loss_breadth/verify_all.py` from the
repository root. The runner refuses optimized Python because the underlying
proof-critical modules use enabled assertions. New numerical comparisons
remain internally certified existence statements, not optimum-frontier
or negative reachability results. The original main theorem statements,
the original comparison table (now in Appendix I), and the published V13 snapshots are preserved.


## SIFIN V1.1 editorial organization

The SIFIN V1.1 revision groups the manuscript around structural barriers,
reachability regimes, and execution resources. Its Introduction is rewritten,
the Abstract contains no mathematical notation, robustness propositions move
to Section 3, and the sharp all-asset theorem remains in Section 4.
Section 7 retains the principal constrained existence results, with extra
numerical figures and comparison tables now in Appendices G and I.
See [the editorial migration and result-location map](../../docs/V14_SIFIN_V11_MIGRATION.md).
Formal statements, existing numbered equations, bibliography, and exact
certificate inputs are unchanged. The independent proof audit is a
separate future step; this editorial release does not claim it is complete.
