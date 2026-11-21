# Gaussian-integer quartic equations in Lean

This Lean 4 project formalizes the main results of Filip Najman's *The Diophantine equation
\(x^4 \pm y^4 = iz^2\) in Gaussian integers*, the extension to \(\mathbb Q(i)\) in the final remark,
and the two elliptic-curve point groups in the proof. [Paper](https://arxiv.org/abs/1005.1528)

## Results

| Lean declaration | Statement |
| --- | --- |
| `GaussianQuartics.theorem1i` | Every solution of \(x^4-y^4=iz^2\) over \(\mathbb Z[i]\) has \(xyz=0\). |
| `GaussianQuartics.theorem1ii` | The nontrivial primitive solutions of \(x^4+y^4=iz^2\) are exactly those with \(x,y\in\{1,-1,i,-i\}\) and \(z=\pm i(1+i)\). |
| `GaussianQuartics.theorem2_plus`, `theorem2_minus` | Every solution of \(x^4\pm y^4=z^2\) over \(\mathbb Z[i]\) has \(xyz=0\). |
| `GaussianQuartics.rat_minus_i_trivial`, `rat_plus_i_iff`, `rat_hilbert_plus`, `rat_hilbert_minus` | The corresponding results over \(\mathbb Q(i)\). The plus equation with imaginary coefficient is an equivalence describing all nontrivial solutions, including scaling. |
| `GaussianQuartics.plusPointGroup`, `minusPointGroup` | The full point groups of \(Y^2=X^3+X\) and \(Y^2=X^3-X\) over \(\mathbb Q(i)\) are additively isomorphic to \(\mathbb Z/2\times\mathbb Z/2\) and \(\mathbb Z/2\times\mathbb Z/4\), respectively. |

`Primitive` means that every common divisor of the three coordinates is a unit.
`GaussianRat` is mathlib's quadratic algebra over \(\mathbb Q\) with generator squaring to \(-1\).

## Proof

The proof follows the paper's substitutions into the two elliptic curves. For the twisted
equations, it uses \(b=ir\) so that the displayed Weierstrass equations hold with \(a=st\).
The rational-point arguments use Fermat's exponent-four obstruction and the square-area
theorem. Over \(\mathbb Q(i)\), the lines through a point and its conjugate, applied to both
\((X,Y)\) and \((-X,iY)\), determine the possible coordinates. The additive equivalences
check the group laws on the resulting lists of points.

`GaussianQuartics/FermatTriangle.lean` comes from yachi's *lean-playground*.
Its Apache 2.0 license is included. [Pinned source](https://github.com/yachi/lean-playground/blob/fa9f1abf44db835b54667120a3c545a7eb2c30e7/LeanPlayground/PerfectCuboid/FermatTriangle.lean)

## Build and audit

Run these commands from the project directory with Elan installed. The toolchain and
dependencies are pinned to Lean and mathlib v4.35.0.

```sh
lake exe cache get Mathlib/NumberTheory/FLT/Four.lean \
  Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean \
  Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean \
  Mathlib/Algebra/QuadraticAlgebra/Basic.lean Mathlib/Tactic.lean
lake build
lake env lean CheckAxioms.lean
```
