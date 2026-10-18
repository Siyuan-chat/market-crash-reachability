# Historical edition — revised English preprint, 18 October 2026

Superseded by the [reviewed V13 preprint](../v13-review-response/README.md);
this 33-page PDF and its source are preserved unchanged as Zenodo v2.

[Manuscript (33 pages)](manuscript.pdf) · [LaTeX](main.tex) · [Bibliography](references.bib)

This is the revised English manuscript approved for public synchronization on
18 October 2026. The original title is retained, without a subtitle. It incorporates
the editorial review and the explicitly requested statement and proof-parameter
clarifications. The numerical certificates and algorithms are unchanged.

The separate [supplementary material](../siam/supplementary.pdf) is unchanged.
The earlier [SIAM edition](../siam/manuscript.pdf), original research edition,
translations and software archive remain available as historical editions.

## Rebuild

Use pdfLaTeX and BibTeX with the dependencies listed in the
[SIAM build instructions](../siam/README.md). Obtain the official SIAM
`siamonline250211.cls` and `siamplain.bst` from the complete official template
distribution described there; these third-party files are not redistributed
individually in this directory. From this directory, run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The published `manuscript.pdf` is the final checked build of `main.tex`.
See [validation summary](VALIDATION.md) and [file hashes](SHA256SUMS).
Copyright and license scope remain as specified in the repository NOTICE.
