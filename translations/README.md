# Complete research-edition drafts

[简体中文](zh-CN/README.md) · [日本語](ja/README.md) · [Trilingual glossary](GLOSSARY.md)

Both editions include the complete manuscript, proofs, appendices and supplement.
Canonical mathematics is English V12 Final. Engineering provenance is recorded
separately in `docs/PHASE2_BASELINE.json`. Edition date: 2026-10-15. The author
has authorized public distribution; further language corrections may follow. English is the authoritative
mathematical source and the reference to cite; see the root CITATION.cff.
The software MIT grant does not extend to translated manuscript text or figures.

## Build and check

Use Python 3.11, pdfLaTeX for the English comparison and LuaLaTeX for the
translations. TeX Live dependencies include `texlive-luatex`,
`texlive-latex-extra`, `texlive-fonts-recommended`, `texlive-lang-chinese` and
`texlive-lang-japanese` (Debian/Ubuntu package names). TinyTeX users need the
standard manuscript packages plus `luatexja`, `fandol`, `haranoaji` and `regexpatch`.
Free Fandol and HaranoAji fonts are used through TeX; font files are not distributed.

From the repository root:

```bash
python scripts/check_translation_consistency.py
python scripts/build_translations.py
python scripts/check_translation_consistency.py --aux-root build/translations --out build/translations/compiled_consistency.json
```

For a portable installation, pass `--lualatex /path/to/lualatex` and
`--pdflatex /path/to/pdflatex` to the build script. Each build uses a fresh
source directory, canonical bibliography and original figures, and repeats TeX
until references stabilize. PDFs and logs are written to
`build/translations/{en,zh-CN,ja}/`; `main.pdf` is the manuscript and
`supplementary.pdf` the supplement. The canonical committed English PDFs are
never overwritten. Generated PDFs are intended as review or CI artifacts and
subsequent approved Release assets.

The checker compares normalized mathematical content and order, theorem
environments, labels and references, explicit numerical sequences, figure/table
structure, and compiled label numbers. It cannot establish semantic equivalence
of prose. The language-specific REVIEW files record manual review and exceptions.
Original embedded English figure labels, bibliography titles and six English
phrases inside protected mathematical units are retained and disclosed there.
LuaTeX-ja editions omit microtype because of its local font-patch incompatibility.

The workflow `.github/workflows/translations.yml` builds and uploads PDFs and
evidence in a clean runner. The initial 2026-10-15 local review recorded remote
CI as pending; that is a historical checkpoint, not the present branch status.
The translations were subsequently merged into public main. See the
[workflow runs](https://github.com/Siyuan-chat/market-crash-reachability/actions/workflows/translations.yml)
for commit-specific remote results and [project status](../docs/STATUS.md) for
current publication and archival links. No whole-paper formal-proof claim follows
from translation or consistency checks.
