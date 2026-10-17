# V13 validation and claim ledger

**Working draft only.** V13 exposition was prepared against the already
published 18 October English edition. Statements and numeric results retain
their earlier meaning; no independent new certificate or Lean proof is claimed.

## Automated gates

- `scripts/check_v13_revision.py`: to be run and reported by the PR CI.
  Compares original numbered theorem/assumption/proposition/definition bodies
  with the frozen English source, verifies old numbered equations unchanged,
  and checks that cited bibliography keys exist.
- `scripts/build_v13_revision.py`: to be run by PR CI in an isolated workspace.
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
- The existing V12 research software record and public manuscript DOIs
  identify earlier published artifacts, not this unmerged V13 draft.

## Required human acceptance before a new public preprint

Review the final PDF page by page; confirm bibliography metadata, full
equation labels, the small illustrative calculations, and author wording.
Then publish and update public metadata only through separate author-approved
steps. Do not overwrite the historical English PDF or archive.
