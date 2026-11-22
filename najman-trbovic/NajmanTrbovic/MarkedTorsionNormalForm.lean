module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

import Mathlib.Tactic

/-! The Weierstrass normalizations at a two-torsion point and a second marked point. -/

@[expose] public section

namespace NajmanTrbovic.Cubic

open WeierstrassCurve

/-- Taking a nonzero two-torsion point as `(0,0)` and completing the square gives
an equation of the form `y² = x³ + A*x² + B*x`. -/
theorem short_equation_of_two_torsion {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (E : WeierstrassCurve F) (P : E.toAffine.Point) (hP : P ≠ 0) (h₂ : 2 • P = 0) :
    ∃ (C : VariableChange F) (A B : F), C • E = ⟨0,A,0,B,0⟩ := by
  classical
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h =>
    have hneg : y = E.toAffine.negY x y := by
      by_contra hn
      rw [two_nsmul, Affine.Point.add_self_of_Y_ne hn] at h₂
      exact Affine.Point.some_ne_zero _ h₂
    change y = -y-E.a₁*x-E.a₃ at hneg
    have heq := (Affine.equation_iff x y).mp h.1
    change y ^ 2 + E.a₁*x*y + E.a₃*y = x^3 + E.a₂*x^2 + E.a₄*x + E.a₆ at heq
    let C : VariableChange F := ⟨1,x,-E.a₁/2,y⟩
    refine ⟨C, (C • E).a₂, (C • E).a₄, ?_⟩
    ext
    · simp only [variableChange_def, C, Units.val_one, inv_one, one_mul]
      ring
    · rfl
    · simp only [variableChange_def, C, Units.val_one, inv_one, one_pow, one_mul]
      linear_combination hneg
    · rfl
    · simp only [variableChange_def, C, Units.val_one, inv_one, one_pow, one_mul]
      linear_combination -heq

/-- On the indicated open chart, rescaling a short equation with a marked origin
puts a second point and the coefficients in the Derickx–Sutherland form. -/
theorem normalize_second_point {F : Type*} [Field F] [CharZero F] (A B x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) (hplus : x^2+B ≠ 0) (hminus : x^2-B ≠ 0)
    (he : y^2 = x^3+A*x^2+B*x) :
    ∃ (s : Fˣ) (q t : F),
      VariableChange.mk s 0 0 0 • (⟨0,A,0,B,0⟩ : WeierstrassCurve F) =
        ⟨0,t^2-2*q*t-2,0,-(t^2-1)*(q*t+1)^2,0⟩ ∧
      x / (s : F)^2 = (t+1)*(q*t+1) ∧ y / (s : F)^3 = t*((t+1)*(q*t+1)) := by
  let t := (x^2-B)/(x^2+B)
  have ht : t ≠ 0 := div_ne_zero hminus hplus
  have hT : t+1 ≠ 0 := by
    have hT : t+1 = 2*x^2/(x^2+B) := by dsimp [t]; field_simp; ring
    rw [hT]
    exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hx)) hplus
  let a := y/(x*t)
  have ha : a ≠ 0 := div_ne_zero hy (mul_ne_zero hx ht)
  let s := Units.mk0 a ha
  let X := x/a^2
  let Y := y/a^3
  let q := (X/(t+1)-1)/t
  have hX : X ≠ 0 := div_ne_zero hx (pow_ne_zero _ ha)
  have hq : q*t+1 = X/(t+1) := by dsimp [q]; rw [div_mul_cancel₀ _ ht, sub_add_cancel]
  have hXform : X = (t+1)*(q*t+1) := by rw [hq, ← mul_div_assoc, mul_div_cancel_left₀ _ hT]
  have hYform : Y = t*X := by
    have hax : a * (x*t) = y := by dsimp [a]; rw [div_mul_cancel₀ _ (mul_ne_zero hx ht)]
    dsimp [X,Y]
    rw [← hax]
    field_simp
  have hBt : B*(t+1) = x^2*(1-t) := by dsimp [t]; field_simp; ring
  have hB : B/a^4 = -(t^2-1)*(q*t+1)^2 := by
    rw [hq]
    dsimp [X]
    field_simp
    linear_combination (t+1)*hBt
  have hNorm : Y^2 = X^3+(A/a^2)*X^2+(B/a^4)*X := by
    dsimp [X,Y]
    field_simp
    linear_combination he
  have hA : A/a^2 = t^2-2*q*t-2 := by
    rw [hYform, hB, hXform] at hNorm
    have hnot : (t+1)*(q*t+1) ≠ 0 := hXform ▸ hX
    apply mul_right_cancel₀ (pow_ne_zero 2 hnot)
    linear_combination -hNorm
  refine ⟨s,q,t,?_,hXform, hYform.trans (congrArg (t*·) hXform)⟩
  ext <;> simp only [variableChange_def, zero_mul, mul_zero, add_zero,
    zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), sub_zero] <;>
    change _⁻¹ ^ _ * _ = _
  · rw [inv_pow, inv_mul_eq_div]
    exact hA
  · rw [inv_pow, inv_mul_eq_div]
    exact hB

end NajmanTrbovic.Cubic
