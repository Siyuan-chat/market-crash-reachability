# V14 turnover--dissipation research draft

**[Open the compiled V14 manuscript PDF](manuscript.pdf)** · [Build provenance](manuscript-build.json).

The PDF is built by GitHub Actions and committed to this directory after a successful source/build check. V14 is still an unpublished research draft; the public citable preprint remains V13.


This **complete English manuscript source** extends the published V13 preprint.
Section 4 now includes a [continuous power-law exponent analysis](../../docs/V14_CONTINUOUS_EXPONENT_SPECTRUM.md)
covering the two thresholds at p=1 and p=2, with explicit inventory-growth
comparisons and careful separation of local reachability from the p=0
global severe-loss construction.

The new **Proposition 5.2 (Turnover--dissipation bound under constant impact)**
and its formal proof appear in Section 5 of [main.tex](main.tex), with
a time-kernel interpretation and three distinct sharpening directions in
the Discussion. [Detailed proof audit](../../docs/V14_TURNOVER_DISSIPATION_AUDIT.md).

The published V13 manuscript, PDF, Lean proofs, and archived numeric certificates
are unchanged. This draft does not claim any new numerical witness, optimal control,
or impossibility result, and is not deposited on Zenodo/SSRN. The new
Proposition 5.2 has not been Lean-formalized and is not counted in the
original 16/16 Lean acceptance report.

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
