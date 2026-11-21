# The Diophantine equation x⁴ ± y⁴ = iz² in Gaussian integers, in Lean 4

A Lean 4 / Mathlib formalization of the results of

> F. Najman, *The Diophantine equation x⁴ ± y⁴ = iz² in Gaussian integers*, Amer. Math. Monthly **117** (2010),
> no. 7, 637–641, [doi:10.4169/000298910X496769](https://doi.org/10.4169/000298910X496769),
> [arXiv:1005.1528](https://arxiv.org/abs/1005.1528).

* Theorems 1 and 2 of the paper over ℤ[i], the closing remark (the same results over ℚ(i)), and the groups of
  ℚ(i)-points of the two elliptic curves y² = x³ ± x used in the proofs.
* **9 theorems and 2 definitions, all proved.** No `sorry`. Every result depends only on the standard axioms
  `propext`, `Classical.choice` and `Quot.sound`.
* [`Challenge.lean`](Challenge.lean) states all of them, with `sorry` as proofs, together with every definition
  they use, over Mathlib alone (174 lines). [Comparator](https://github.com/leanprover/comparator) checks that the
  library proves exactly these statements about exactly these definitions.
* About 1,100 lines of Lean, on Lean v4.35.0 and Mathlib v4.35.0, using Lean's module system.

The Lean code was written by Codex (an AI coding agent) at the author's request; the Comparator challenge, the
checks and the Palomar metadata were added afterwards. See [`formalization.yaml`](formalization.yaml) for the
details and for the reviews of the statements.

## Results

The statements are in [`Challenge.lean`](Challenge.lean); the proofs are in the library
[`GaussianQuartics`](GaussianQuartics.lean).

| paper | statement | proof | in words |
|---|---|---|---|
| Theorem 1(i) | [`theorem1i`](Challenge.lean#L114) | [GaussianQuartics.lean](GaussianQuartics.lean#L105) | every solution of x⁴ − y⁴ = iz² in ℤ[i] is trivial (xyz = 0) |
| Theorem 1(ii) | [`theorem1ii`](Challenge.lean#L118) | [GaussianQuartics.lean](GaussianQuartics.lean#L124) | the nontrivial primitive solutions of x⁴ + y⁴ = iz² in ℤ[i] are exactly x, y ∈ {±1, ±i}, z = ±i(1 + i) |
| | [`gaussian_int_plus_i_iff`](Challenge.lean#L131) | [GaussianQuartics.lean](GaussianQuartics.lean#L112) | all nontrivial solutions of x⁴ + y⁴ = iz² in ℤ[i], primitive or not: x ∈ {±y, ±iy}, z = ±i(1 + i)y² |
| Theorem 2 | [`theorem2_plus`](Challenge.lean#L123) | [GaussianQuartics.lean](GaussianQuartics.lean#L173) | every solution of x⁴ + y⁴ = z² in ℤ[i] is trivial (Hilbert) |
| | [`theorem2_minus`](Challenge.lean#L127) | [GaussianQuartics.lean](GaussianQuartics.lean#L180) | every solution of x⁴ − y⁴ = z² in ℤ[i] is trivial (Hilbert) |
| Remark | [`rat_minus_i_trivial`](Challenge.lean#L143) | [FieldClassification.lean](GaussianQuartics/FieldClassification.lean#L102) | every solution of x⁴ − y⁴ = iz² in ℚ(i) is trivial |
| | [`rat_plus_i_iff`](Challenge.lean#L147) | [FieldClassification.lean](GaussianQuartics/FieldClassification.lean#L112) | the nontrivial solutions of x⁴ + y⁴ = iz² in ℚ(i) are x ∈ {±y, ±iy}, z = ±i(1 + i)y² |
| | [`rat_hilbert_plus`](Challenge.lean#L151) | [FieldClassification.lean](GaussianQuartics/FieldClassification.lean#L158) | every solution of x⁴ + y⁴ = z² in ℚ(i) is trivial |
| | [`rat_hilbert_minus`](Challenge.lean#L155) | [FieldClassification.lean](GaussianQuartics/FieldClassification.lean#L173) | every solution of x⁴ − y⁴ = z² in ℚ(i) is trivial |
| proof of Theorem 1(i) | [`plusPointGroup`](Challenge.lean#L167) | [PointGroups.lean](GaussianQuartics/PointGroups.lean#L106) | E(ℚ(i)) ≅ ℤ/2 × ℤ/2 for E : y² = x³ + x, the point at infinity included |
| proof of Theorem 1(ii) | [`minusPointGroup`](Challenge.lean#L170) | [PointGroups.lean](GaussianQuartics/PointGroups.lean#L116) | E(ℚ(i)) ≅ ℤ/2 × ℤ/4 for E : y² = x³ − x, the point at infinity included |

The last two are definitions: an additive isomorphism `ZMod 2 × ZMod 2 ≃+ plusCurve.toAffine.Point` (and
`ZMod 2 × ZMod 4 ≃+ …`). The Challenge leaves their values to the library, so their types are the statements: the
group of ℚ(i)-points is isomorphic to ℤ/2 × ℤ/2 (resp. ℤ/2 × ℤ/4). The paper states only the torsion subgroups and
computes the ranks with Simon's program; the Lean proof determines the whole group.

Definitions used by the statements (all in [`Challenge.lean`](Challenge.lean)):

* `GaussianInt` is Mathlib's ℤ[i]; `intI` is i ∈ ℤ[i].
* `GaussianRat` is ℚ(i), as Mathlib's `QuadraticAlgebra ℚ (-1) 0` (generator ω with ω² = −1); `I` is ω.
* `Trivial x y z` means xyz = 0, the paper's Definition 1.
* `Primitive x y z` means that every common divisor of x, y, z is a unit, i.e. gcd(x, y, z) = 1.
* `UnitChoice x` means x ∈ {1, −1, i, −i}, the units of ℤ[i].
* `ScaledPlusSolution i x y z` means x ∈ {y, −y, iy, −iy} and z = ±i(1 + i)y².
* `plusCurve` and `minusCurve` are the Weierstrass curves y² = x³ + x and y² = x³ − x over ℚ(i).

## Proof

The proof follows the paper. Dividing by y⁴, a nontrivial solution gives a point on y² = x³ + x or y² = x³ − x
over ℚ(i), and the points of these curves are determined. For the equations with coefficient i, the substitution is
a = st, b = ir. (The paper writes b = −ir, which gives a² = −(b³ ± b); these curves are isomorphic to a² = b³ ± b by
b ↦ −b, so the argument is unaffected.) Instead of computing ranks, the Lean proof finds the ℚ(i)-points directly:

* the line through a ℚ(i)-point and its complex conjugate has rational slope; applied to (X, Y) and to (−X, iY),
  this reduces a ℚ(i)-point to rational points on y² = x³ ± x ([`GaussianCurves.lean`](GaussianQuartics/GaussianCurves.lean));
* the rational points of y² = x³ + x and y² = x³ − x have y = 0, by Fermat's descent (Mathlib's `not_fermat_42`)
  and Fermat's right triangle theorem ([`RationalCurves.lean`](GaussianQuartics/RationalCurves.lean));
* the group laws on the resulting lists of points are checked by `decide`
  ([`PointGroups.lean`](GaussianQuartics/PointGroups.lean)).

[`GaussianQuartics/FermatTriangle.lean`](GaussianQuartics/FermatTriangle.lean) (Fermat's right triangle theorem)
is taken without proof changes from yachi's
[lean-playground](https://github.com/yachi/lean-playground/blob/fa9f1abf44db835b54667120a3c545a7eb2c30e7/LeanPlayground/PerfectCuboid/FermatTriangle.lean)
(Apache-2.0); only a header naming its source was added.

## Building and checking

With [elan](https://github.com/leanprover/elan) installed, from this directory:

```sh
lake exe cache get                 # Mathlib's compiled files
lake build                         # the library
lake env lean CheckAxioms.lean     # prints the axioms of the 11 results
```

**Comparator.** [`comparator.json`](comparator.json) names the 9 theorems and the 2 definitions. Comparator builds
[`Challenge.lean`](Challenge.lean) and [`Solution.lean`](Solution.lean) (which imports the library), checks that
each compared declaration has the same type in both, about the same definitions, uses no axioms other than
`propext`, `Classical.choice` and `Quot.sound`, and is accepted by the Lean kernel (and, with `--paranoid`, by
lean4lean, nanoda, con-leche and con-ron). In the pinned Lean version Comparator is part of Lake; it runs inside a
[bubblewrap](https://github.com/containers/bubblewrap) sandbox, so `bwrap` must be installed:

```sh
lake comparator --config comparator.json --paranoid
```

**Scripts** (Python 3, from this directory):

* `python3 scripts/make_challenge.py [--check]` writes `Challenge.lean` from the library sources (or checks that it is
  up to date). It copies the definitions verbatim and replaces each proof by `sorry`.
* `python3 scripts/check_statements.py` checks that the 23 declarations of the Challenge are, in the library, exactly
  as Codex wrote them (in this repository's first commit, 3c51761). Since then only two things changed in the
  library, both so that the Challenge and the library elaborate to the same constants: three anonymous instances
  were given names, and `PointGroups.lean` imports `Mathlib.Algebra.Field.ZMod`.

## Layout

```
Challenge.lean            the statements, with the definitions they use (generated)
Solution.lean             imports the library
comparator.json           the compared declarations
formalization.yaml        Palomar metadata
CheckAxioms.lean          #print axioms for the 11 results
GaussianQuartics.lean     Theorems 1 and 2 over ℤ[i]
GaussianQuartics/
  FieldClassification.lean  the equations over ℚ(i) (the closing remark)
  GaussianCurves.lean       ℚ(i), and the ℚ(i)-points of y² = x³ ± x
  PointGroups.lean          the two groups of ℚ(i)-points
  RationalCurves.lean       the rational points of y² = x³ ± x
  FermatTriangle.lean       Fermat's right triangle theorem (from lean-playground)
scripts/                  make_challenge.py, check_statements.py
```

## License

Apache-2.0 (see [`LICENSE`](../LICENSE) at the root of this repository).
