<p align="center"><img src="assets/banner.svg" alt="Superlinear Wire Lower Bounds for Gates of Fan-In N^(1-δ)" width="100%"></p>

<p align="center">
  <a href="https://doi.org/10.5281/zenodo.24163297"><img src="https://img.shields.io/badge/DOI-10.5281%2Fzenodo.24163297-22d3ee?style=for-the-badge" alt="DOI"></a>
  <a href="papers/PvsNPPaper.pdf"><img src="https://img.shields.io/badge/paper-PDF-f472b6?style=for-the-badge" alt="paper"></a>
  <img src="https://img.shields.io/badge/Lean_4-46_theorems-7c5cff?style=for-the-badge" alt="Lean 4">
  <img src="https://img.shields.io/badge/Julia-44_checks-34d399?style=for-the-badge" alt="Julia">
  <img src="https://img.shields.io/badge/license-MIT-f59e0b?style=for-the-badge" alt="MIT">
</p>

**Deep Bhattacharjee**

| Proved | Open |
| :--- | :--- |
| For every δ > 0, a language in E<sup>NP</sup> needs more than c(δ) N √log N wires in circuits of any depth whose gates are arbitrary functions of N<sup>1−δ</sup> inputs, or threshold, exact, modular and symmetric gates with weights of N<sup>1−δ</sup> bits | Superpolynomial lower bounds for E<sup>NP</sup> |
| Tensor-network contraction at degree s<sup>1−δ</sup>, and counting for these circuits in time 2<sup>O(s/√log s)</sup> | Bounds beyond N √log N by this method |
| Tree encodings of weighted gates need degree close to the weight length (unconditional) | P versus NP |

| Folder | Contents | Run |
| :--- | :--- | :--- |
| [`papers/`](papers) | the paper | |
| [`lean/`](lean) | Lean 4 project over Mathlib, axiom audit | `cd lean && lake exe cache get && lake build && lake env lean audit.lean` |
| [`julia/`](julia) | finite statements and constants | `julia julia/run_all.jl` |

| Release | DOI |
| :--- | :--- |
| v2.0.0 | [10.5281/zenodo.24163297](https://doi.org/10.5281/zenodo.24163297) |
| v1.0.0 | [10.5281/zenodo.23934035](https://doi.org/10.5281/zenodo.23934035) |
| all versions | [10.5281/zenodo.23934034](https://doi.org/10.5281/zenodo.23934034) |

 Contact: egspl@proton.me.
