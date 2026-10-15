# SIFIN derivative: editorial and figure changes

The canonical V12 Final manuscript, bibliography, supplement, original figures,
data, verification algorithms and model parameters remain unchanged. The
SIFIN edition is generated with `scripts/build_siam_submission.py`.

## Explicit changes and checks

- `scripts/siam_editorial.py` maps journal names, adds 5 main and 18 supplement
  figure callouts, and replaces the exact code/data availability paragraph with
  the public repository and computational baseline commit `ea831c4` (full SHA
  in the link). It does not claim a Release or DOI exists.
- `check_siam_submission.py` reverses only these named prose edits and the
  existing layout changes, then compares the entire original body. Equations,
  theorem statements, proofs, captions and all remaining prose must match.
  All figures require a body callout. Main printed label numbers must match
  the canonical compiled edition; supplement SM mapping is reported.
- The derived BibTeX changes only `journal` fields (15 entries); all other
  bibliographic fields remain byte-identical. BibTeX regenerates `main.bbl`.
- `prepare_siam_figures.py` creates 24 derivative PDFs in `figures/`. Only PDF
  `w` (stroke-width) operands may differ: paths, coordinates, text, images,
  colors and all other content instructions are compared. Original figure
  PDFs remain untouched. Thin strokes are clamped to achieve at least 1.02pt
  at the specified final embedding width; already thick strokes are retained.
  Source/derived hashes, scale and measured minimums are in
  `figures/figure-metrics.json` and the CI figure evidence.
  The compiled check independently extracts the actual embedded PDF Forms,
  measures their strokes and applies the real placement transforms. A negative
  control requires the original thin-line manuscript PDFs to be rejected,
  even though they use the same figure names.

## Journal abbreviation evidence

[SIFIN instructions](https://epubs.siam.org/journal/sifin/instructions-for-authors)
ask for Mathematical Reviews abbreviations. The following direct MR entries
were checked in the [official serials list](https://mathscinet.ams.org/msnhtml/serials.pdf),
updated October 15, 2026:

| Journal | Display form | PDF page |
|---|---|---|
| SIAM Journal on Financial Mathematics | SIAM J. Financial Math. | 24 |
| Mathematics of Operations Research | Math. Oper. Res. | 18 |
| Mathematical Finance | Math. Finance | 17 |
| Journal of Econometrics | J. Econometrics | 14 |
| Annals of Operations Research | Ann. Oper. Res. | 3 |
| Quantitative Finance | Quant. Finance | 22 |
| Econometrica | Econometrica | 8 |
| Stochastic Models | Stoch. Models | 25 |

`Rev. Financ. Stud.` and `J. Finance` have supporting evidence from the
[historical MR journal index](https://mathscinet.ams.org/mathscinet/help/msnlinking_by_journal.html)
in search cache; that endpoint returned HTTP 403 on direct retrieval. The
former is preferred to the variant `Rev. Financial Stud.` found in some
published SIAM bibliographies.

For the following three journals, the selected forms have publisher usage
evidence; direct MR entries were not obtained. These are documented choices,
not a claim of complete direct MR verification:

- `Amer. Econ. Rev.`: [SIAM bibliography, entries 10/63](https://epubs.siam.org/doi/10.1137/1016005).
- `Rev. Finance`: [Springer bibliography, Deng et al.](https://link.springer.com/article/10.1007/s11156-018-0771-0)
  uses `Rev Finance`; abbreviation periods follow the edition's typography.
- `J. Financial Markets`: [SIFIN bibliography, entry 23](https://epubs.siam.org/doi/pdf/10.1137/20M135409X).

## Remaining author decisions

See [AUTHOR_TODO.md](AUTHOR_TODO.md). Missing author information or declarations
have not been filled with guesses. This edition does not represent journal
submission, full-paper machine formalization, acceptance or a new certificate.
