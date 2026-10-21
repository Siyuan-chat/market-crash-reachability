# Versions, source identities and citations

**Current GitHub working manuscript: V14-R1** · [PDF](../submission/v14-turnover-dissipation/manuscript.pdf) · [LaTeX](../submission/v14-turnover-dissipation/main.tex) · [machine-readable PDF provenance](../submission/v14-turnover-dissipation/manuscript-build.json)

The PDF in the GitHub repository is updated by the manuscript workflow. To identify the **exact paper edition**, use the `source_commit` and `pdf_sha256` in `manuscript-build.json`; the tip of `main` may instead be a subsequent PDF-only or documentation commit. At the 22 October 2026 audit, the tracked PDF was built from source commit `970bf26193dfa988f041a905e3ba8dd16d1e197f` by [this successful build](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39691071017). The build record, not this dated statement, is authoritative as the working file evolves.

## Edition index

| Edition | Source and PDF | Scope | Publication identity |
|---|---|---|---|
| **GitHub V14-R1 · current working edition** | [Source](../submission/v14-turnover-dissipation/main.tex) · [PDF](../submission/v14-turnover-dissipation/manuscript.pdf) · [build metadata](../submission/v14-turnover-dissipation/manuscript-build.json) | The V14 results plus conservation/ten-asset A1/A2 narrative and reconstructions, B1/B2 comparison, subsequent analytical BV lemma and proof-completeness/editorial revisions | **No new fixed archival DOI** assigned to V14-R1. Cite an exact Git commit |
| **Frozen V14 · 20 Oct 2026** | [Zenodo V14 PDF and record](https://doi.org/10.5281/zenodo.23478787) | Five V14 result additions and loss–breadth comparisons **before** the later V14-R1 figure, numerical reconstructions and BV supplement | **10.5281/zenodo.23478787**, deposited snapshot; 46 pages |
| **V13 · 18 Oct 2026** | [Source](../submission/v13-review-response/main.tex) · [GitHub PDF](../submission/v13-review-response/manuscript.pdf) · [Zenodo record](https://doi.org/10.5281/zenodo.23444647) | Preserved pre-V14 mathematical paper and appendix | **10.5281/zenodo.23444647** |
| **Earlier English SIAM-language edition** | [Source](../submission/siam-language-revision/main.tex) · [PDF](../submission/siam-language-revision/manuscript.pdf) | Historical 33-page English edition | [Zenodo 23438609](https://doi.org/10.5281/zenodo.23438609) |
| **Original V12 computational baseline** | [Source](../paper/main.tex) · [PDF](../paper/manuscript.pdf) · [supplement](../supplementary/supplementary.pdf) | Historical analytic, numerical and formalization baseline | Original research assets remain at fixed repository paths |

The older [`submission/siam/`](../submission/siam/main.tex) edition and baseline [Japanese/Chinese translations](../translations/README.md) remain available separately. The translations do **not** purport to include every revision in the current English V14-R1 source.

## Distinct evidence generations

The original **16 substantive result families** have recorded partial Lean 4 acceptance, subject to the exact hypotheses and the documented boundary amendment in [formal/README.md](../formal/README.md). The **five later V14 additions** are not Lean-formalized. V14-R1 subsequently adds an analytical **one-sided finite-variation (BV) lemma** and proof exposition. This new lemma is also **not Lean-formalized** merely because historical Lean workflows pass.

The working A1/A2 examples combine analytical paths with **double-precision numerical regression**. The constrained B1/B2 cases reuse **internally checked outward-rounded interval certificates** for particular rational schedules; their execution budgets differ. The earlier original 80,000-step certificate has its own archived identity. See [result/evidence boundaries](RESULTS_AND_EVIDENCE.md), [twin-benchmark note](TWIN_TEN_ASSET_REVISION_V1.md), and [reproduction](../REPRODUCE.md).

## Fixed archive and citation records

- **Frozen manuscript V14:** [10.5281/zenodo.23478787](https://doi.org/10.5281/zenodo.23478787). The 20 October record identified GitHub PDF commit `d548d287e221097b82b46cb7affbfd366a96875b`, source commit `3b6dc06bcdba4ec18764ace6adf1c0211be14006` and displayed MD5 `1a0e333e8f528c7b2f47e359e85dddc1`. Those checks refer to the frozen source/PDF only.
- **V13:** [10.5281/zenodo.23444647](https://doi.org/10.5281/zenodo.23444647). The manuscript concept DOI [10.5281/zenodo.23427879](https://doi.org/10.5281/zenodo.23427879) and earlier record [23427880](https://doi.org/10.5281/zenodo.23427880) retain their archival meanings.
- **Immutable research software:** [10.5281/zenodo.23428183](https://doi.org/10.5281/zenodo.23428183), `1.0.0rc1+git.d6e2606` at commit `d6e2606590f955a6287c6945488a080e5acab004`. The software-specific [CITATION.cff](../CITATION.cff) intentionally retains this fixed version, DOI, and its earlier V13 preferred paper citation. That metadata is **not** a claim that current V14-R1 code or PDF is included in the old software archive.
- **SSRN:** [abstract ID 7622079](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7622079) (DOI `10.2139/ssrn.7622079`) is a **mutable preprint record**. Its page report was 46 pages and 19 October revision when checked on 20 October 2026. Its PDF has not been checked against the current V14-R1 GitHub hash.

A GitHub revision, a Zenodo record, an SSRN entry and journal acceptance are different states. **No journal acceptance or V14-R1 Zenodo DOI is asserted.**

## How to cite or reproduce the current working edition

For the evolving manuscript, specify the paper title, Siyuan Ye, **V14-R1**, the [GitHub repository](https://github.com/Siyuan-chat/market-crash-reachability), the `source_commit` from the [PDF metadata](../submission/v14-turnover-dissipation/manuscript-build.json), and the access date. Cite the **frozen V14 DOI** only for results actually contained in that archived V14 snapshot. For the pinned original software cite its separate DOI and version.

The original [`release/SHA256SUMS`](../release/SHA256SUMS) is unchanged. The explicitly permitted working-file edits use the separate [`release/SHA256SUMS_V14_R1`](../release/SHA256SUMS_V14_R1) and [two-layer checker](../scripts/check_revision_hashes.py). See the [directory map](REPOSITORY_STRUCTURE.md).

