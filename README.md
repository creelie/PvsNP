# Superlinear Wire Lower Bounds toward P versus NP

Deep Bhattacharjee. Source, figures and verification programs of the paper.

The paper surveys the P versus NP problem and proves four results:

- **Theorem A (counting).** The satisfying inputs of a circuit in K(s^{4/5}, s^{2/3}), whose gates are arbitrary functions of at most s^{4/5} inputs or threshold, exact, modular and symmetric gates of any fan-in with weights of at most s^{2/3} bits, are counted in time 2^{O(s/sqrt(log s))}, where s is the number of inputs plus wires.
- **Theorem B (lower bound).** A language in E^NP needs more than cN sqrt(log N) wires in K(N^{3/4}, N^{1/2}) for infinitely many N.
- **Theorem C (zero-one programs).** Counting and exact optimisation over {0,1}^n subject to Ax <= b in time 2^{O(sigma/sqrt(log sigma))}, sigma = n + nnz(A).
- **Theorem D (transfer).** A 2^{O(s/(log s)^gamma)} satisfiability algorithm for these circuits gives a cN(log N)^gamma wire lower bound.

Theorem A rests on the tensor network contraction theorem of OpenAI (preprint, October 2026, Theorem D.1), whose proof is reproduced in Appendix A of the paper. P versus NP itself remains open; nothing here separates P from NP.

## Layout

- `mdpi-preprints/PvsNP_MDPI.pdf`: the paper (30 pages).
- `mdpi-preprints/TexmdpiPvsNP.zip`: flat LaTeX source (`main.tex`) with its seven PNG figures; it compiles with `pdflatex main.tex` (run twice).
- `paper/`: the source in parts (`part0_preamble.tex` to `part7_bib.tex`); `build.sh` assembles `main.tex`, `tools/make_bib.py` writes the bibliography, `figures/make_figures.py` draws the figures (200 dpi).
- `code/check_encoding.py`: exact checks of the finite statements (network contraction against exhaustive counting, the size lemma, the zero-one program reduction, the valuation identity, integrality of the Cauchy deformation, the Hermite formula, the packing lemma); `code/check_output.txt` is its output, `27 checks passed, 0 failed`.
- `literature/`: the arXiv catalogue of 6,480 records (`arxiv_catalogue.csv`, `fetch_arxiv.py`), the Crossref records of the bibliography DOIs (`crossref_records.json`, `check_dois.py`, `doi_check.txt`), and the tally of Woeginger's list of announced solutions (`woeginger_claims.csv`).

## Running

```
cd code && python3 check_encoding.py        # Python 3 with numpy; about 20 seconds
cd paper && bash build.sh && latexmk -pdf main.tex
```

## Archive

| Release | DOI |
|---|---|
| v1.0.0 | [10.5281/zenodo.23934035](https://doi.org/10.5281/zenodo.23934035) |
| all versions (concept) | [10.5281/zenodo.23934034](https://doi.org/10.5281/zenodo.23934034) |

GitHub-related contact: egspl@proton.me.
