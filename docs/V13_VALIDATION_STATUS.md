# V13 validation and claim ledger

**Current public English preprint: V13, 37 pages.** Published on Zenodo on
18 October 2026: [10.5281/zenodo.23444647](https://doi.org/10.5281/zenodo.23444647).
SSRN synchronization currently requires author reauthentication; the public
SSRN record still contains the earlier 33-page edition.

[Page-by-page review and corrections](V13_PDF_REVIEW.md). V13 exposition was prepared against the already
published 18 October English edition. Statements and numeric results retain
their earlier meaning; no independent new certificate or Lean proof is claimed.

## Automated gates

- `scripts/check_v13_revision.py`: PASS locally after editorial corrections.
  Compares original numbered theorem/assumption/proposition/definition bodies
  with the frozen English source, verifies old numbered equations unchanged,
  and checks that cited bibliography keys exist.
- Four pdfLaTeX passes and BibTeX: PASS in an isolated fixed review directory.
  The default builder encountered a Windows temporary-directory permission
  error; no successful local run of that wrapper is claimed. Its log checker
  now also rejects natbib undefined-author warnings.
  Outputs PDF and logs, checks TeX/BibTeX convergence, undefined citations,
  missing glyphs and overfull boxes.
- Standard repository Reproducibility, SIAM, translation and Lean CI are
  independent gates; their checks do not by themselves validate V13's new prose.

## Evidence boundaries

- Direct algebraic consequences (normalized resources, p=1 conservation)
  need no additional numerical certificate but remain subject to author review.
- The cost inequality `K > 0.0976` follows from the original certified
  terminal lower price of the compensator and the unchanged terminal potential;
  the full recovery-dissipation integral is **not** independently recomputed.
- The alternate recovery formula is a model comparison, **not** an extension
  of the elasticity theorems.
- The certified upper witness and strict coarse lower gross-rate bound remain
  distinct; no claim of a numerically optimized critical rate.
- The immutable software DOI 10.5281/zenodo.23428183 identifies the earlier
  d6e2606 software snapshot. The new manuscript DOI identifies V13, not new code
  or newly executed certificate verification.

## Acceptance and publication history

The author explicitly authorized page-by-page writing review followed by SSRN,
Zenodo and GitHub synchronization if satisfactory. Review and the listed
editorial fixes are complete; no blocking writing issue remained. Zenodo V13
is public. Earlier English PDFs and the code archive remain unchanged.

Historical: the initial PR #11 draft required compilation and author acceptance;
those pending-draft instructions are superseded by this review and authorization.
