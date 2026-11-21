module

public import GaussianQuartics.GaussianCurves
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.ZMod.Basic
-- The field structure of `ZMod p`, which the Gaussian integers bring into `GaussianQuartics.lean` and the Challenge:
-- with it `ZMod 2 × ZMod 2` gets the same instances here as in the Challenge.
public import Mathlib.Algebra.Field.ZMod

import Mathlib.Tactic

/-! The two point groups computed in the paper, including the points at infinity. -/

public section

namespace GaussianQuartics

open WeierstrassCurve.Affine

/-- The curve `Y² = X³ + X` over the Gaussian rationals. -/
@[expose] def plusCurve : WeierstrassCurve GaussianRat := ⟨0, 0, 0, 1, 0⟩

/-- The curve `Y² = X³ - X` over the Gaussian rationals. -/
@[expose] def minusCurve : WeierstrassCurve GaussianRat := ⟨0, 0, 0, -1, 0⟩

instance instIsEllipticPlusCurve : plusCurve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

instance instIsEllipticMinusCurve : minusCurve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

private theorem plus_equation {x y : GaussianRat} :
    plusCurve.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + x := by
  simp [equation_iff, plusCurve, WeierstrassCurve.toAffine]

private theorem minus_equation {x y : GaussianRat} :
    minusCurve.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - x := by
  simp [equation_iff, minusCurve, WeierstrassCurve.toAffine, sub_eq_add_neg]

private def plusPoint (x y : GaussianRat) (h : y ^ 2 = x ^ 3 + x) :
    plusCurve.toAffine.Point :=
  Point.mk (plus_equation.mpr h)

private def minusPoint (x y : GaussianRat) (h : y ^ 2 = x ^ 3 - x) :
    minusCurve.toAffine.Point :=
  Point.mk (minus_equation.mpr h)

-- The coordinates of aP + bQ, with P = (0, 0) and Q = (i, 0).
private def plusTable (indices : ZMod 2 × ZMod 2) : plusCurve.toAffine.Point :=
  ![![0, plusPoint I 0 (by decide +kernel)],
    ![plusPoint 0 0 (by decide +kernel), plusPoint (-I) 0 (by decide +kernel)]]
    indices.1 indices.2

-- The coordinates of aP + bQ, with P = (1, 0) and Q = (i, 1-i).
private def minusTable (indices : ZMod 2 × ZMod 4) : minusCurve.toAffine.Point :=
  ![![0, minusPoint I (1 - I) (by decide +kernel),
      minusPoint 0 0 (by decide +kernel), minusPoint I (-(1 - I)) (by decide +kernel)],
    ![minusPoint 1 0 (by decide +kernel), minusPoint (-I) (-(1 + I)) (by decide +kernel),
      minusPoint (-1) 0 (by decide +kernel), minusPoint (-I) (1 + I) (by decide +kernel)]]
    indices.1 indices.2

private theorem plusTable_surjective : Function.Surjective plusTable := by
  intro point
  cases point with
  | zero => exact ⟨(0, 0), rfl⟩
  | some x y h =>
    have he := plus_equation.mp h.1
    obtain rfl : y = 0 := gaussian_plus_y_eq_zero he
    have hx : x * (x ^ 2 + 1) = 0 := by linear_combination -he
    rcases mul_eq_zero.mp hx with rfl | hsq
    · exact ⟨(1, 0), rfl⟩
    have hxI : x ^ 2 = I ^ 2 := by
      rw [I_sq]
      linear_combination hsq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxI with rfl | rfl
    · exact ⟨(0, 1), rfl⟩
    · exact ⟨(1, 1), rfl⟩

private theorem minusTable_surjective : Function.Surjective minusTable := by
  intro point
  cases point with
  | zero => exact ⟨(0, 0), rfl⟩
  | some x y h =>
    have he := minus_equation.mp h.1
    rcases gaussian_minus_y_eq_zero_or_x he with rfl | rfl | rfl
    · have hx : x * (x ^ 2 - 1) = 0 := by linear_combination -he
      rcases mul_eq_zero.mp hx with rfl | hsq
      · exact ⟨(0, 2), rfl⟩
      have hx1 : x ^ 2 = (1 : GaussianRat) ^ 2 := by
        linear_combination hsq
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx1 with rfl | rfl
      · exact ⟨(1, 0), rfl⟩
      · exact ⟨(1, 2), rfl⟩
    · have hsq : y ^ 2 = (1 - I) ^ 2 := by
        linear_combination he + (I - 1) * I_sq
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with rfl | rfl
      · exact ⟨(0, 1), rfl⟩
      · exact ⟨(0, 3), rfl⟩
    · have hsq : y ^ 2 = (1 + I) ^ 2 := by
        linear_combination he - (I + 1) * I_sq
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with rfl | rfl
      · exact ⟨(1, 3), rfl⟩
      · exact ⟨(1, 1), rfl⟩

/-- `E(ℚ(i)) ≃ ℤ/2 × ℤ/2` for `Y² = X³ + X`. -/
noncomputable def plusPointGroup : ZMod 2 × ZMod 2 ≃+ plusCurve.toAffine.Point := by
  let hom : ZMod 2 × ZMod 2 →+ plusCurve.toAffine.Point :=
    { toFun := plusTable
      map_zero' := rfl
      map_add' := by decide +kernel }
  refine AddEquiv.ofBijective hom ⟨?_, plusTable_surjective⟩
  change ∀ a b, plusTable a = plusTable b → a = b
  decide +kernel

/-- `E(ℚ(i)) ≃ ℤ/2 × ℤ/4` for `Y² = X³ - X`. -/
noncomputable def minusPointGroup : ZMod 2 × ZMod 4 ≃+ minusCurve.toAffine.Point := by
  let hom : ZMod 2 × ZMod 4 →+ minusCurve.toAffine.Point :=
    { toFun := minusTable
      map_zero' := rfl
      map_add' := by decide +kernel }
  refine AddEquiv.ofBijective hom ⟨?_, minusTable_surjective⟩
  change ∀ a b, minusTable a = minusTable b → a = b
  decide +kernel

end GaussianQuartics
