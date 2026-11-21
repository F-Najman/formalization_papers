# Formalizations of papers

Lean 4 / Mathlib formalizations of results from papers by Filip Najman. Each directory is a self-contained Lean
project, with its own toolchain, a [Comparator](https://github.com/leanprover/comparator) challenge stating the
formalized results over Mathlib alone, and a README.

| directory | paper | results |
|---|---|---|
| [`gaussian-quartics`](gaussian-quartics) | F. Najman, *The Diophantine equation x⁴ ± y⁴ = iz² in Gaussian integers*, Amer. Math. Monthly 117 (2010), 637–641, [arXiv:1005.1528](https://arxiv.org/abs/1005.1528) | Theorems 1 and 2, the closing remark over ℚ(i), and the ℚ(i)-points of y² = x³ ± x: 9 theorems and 2 definitions, no `sorry` |

The formalization of the paper on normalizers and modular automorphisms is in a repository of its own,
[F-Najman/normalizer-lean](https://github.com/F-Najman/normalizer-lean).

## License

Apache-2.0, see [`LICENSE`](LICENSE).
