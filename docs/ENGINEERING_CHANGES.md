# Changes from the supplied V12 Final package

The original ZIP and full extracted history are retained outside the publication
repository in the local private backup. SOURCE_INVENTORY.json records each
whitelisted source file and its original hash. No manuscript mathematical
definitions, statements, proofs, model parameters or algorithms were edited.

- Main and supplementary LaTeX, final PDFs, bibliography and cited figures are
  copied byte-for-byte. The separate SIAM template duplicates the manuscript
  and remains in the backup; journal formatting can be prepared after approval.
- `verify_consistency.py` reads the final certificate and fixture in their new
  locations. `audit_manuscript_certificate_v11.py` is renamed without a version
  suffix and reads `paper/main.tex` and the same final certificate.
- The certifier's single output-write call now fixes LF line endings. The
  initial Windows rerun differed only by CRLF; parsed fields were identical.
  With LF the entire regenerated certificate is byte-identical to the original.
- The sensitivity audit is renamed, defaults to the final certificate, and
  imports its relocated helper from `scripts/`. Its calculations are unchanged.
- Dependency pins include NumPy 2.1.3 because original scripts call
  `numpy.trapezoid`; NumPy 1.26 does not provide this API. `mpmath` is explicit:
  the certifier uses it for auxiliary high-precision logarithm display/checks,
  while its decisive crisis comparisons also use exact rational bounds.
- New runner, figure checker, figure orchestration, TeX build, hash checker,
  documentation, metadata and CI configuration provide the engineering layer.
  The figure orchestrator writes a scratch collection and preserves the
  distributed V12 figure bytes. Old version names within original scripts are
  retained as provenance, not alternative formal baselines.
- Follow-up pdfLaTeX acceptance: the build helper accepts a portable engine,
  uses fresh scratch workspaces and repeats passes until references stabilize.
  The optional PDF comparison tool and its dependency extra record per-page
  raster/text differences. The original 34/10-page final PDFs remain unchanged;
  the earlier Tectonic overflow is not an original-manuscript defect.
- Public Git preparation standardizes engineering reports, lockfiles and
  relocated checker files to LF before generating SHA256SUMS. This avoids
  Git's text normalization changing bytes after checksum creation. Formal
  manuscript/supplement artifacts and the final certificate are preserved.

Excluded: history and reviewer responses, patching/packaging scripts, obsolete
certificates, duplicate manuscript trees, diagnostic contact sheets and unused
figures. The old-path comparison figure is retained because the final supplement
explicitly includes it; it illustrates infeasibility rather than certifying a path.
