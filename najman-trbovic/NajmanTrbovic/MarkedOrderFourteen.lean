module

public import NajmanTrbovic.CubicMarkedParameters
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

import Mathlib.Tactic

/-! Recovering the parameter equation from the order-fourteen condition in the
normalized marked equation. -/

@[expose] public section

namespace NajmanTrbovic.Cubic

open WeierstrassCurve

def normalizedMarkedCurve {F : Type*} [Field F] (q t : F) : WeierstrassCurve F :=
  ⟨0,t^2-2*q*t-2,0,-(t^2-1)*(q*t+1)^2,0⟩

section

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

private def shortCurve (A B : F) : WeierstrassCurve F := ⟨0,A,0,B,0⟩

private theorem double_on_short (A B x y : F) (h : (shortCurve A B).toAffine.Nonsingular x y)
    (hy : y ≠ 0) :
    let s := (3*x^2+2*A*x+B)/(2*y)
    let X := s^2-A-2*x
    let Y := s*(x-X)-y
    ∃ h' : (shortCurve A B).toAffine.Nonsingular X Y,
      Affine.Point.some x y h + Affine.Point.some x y h = Affine.Point.some X Y h' := by
  have hn : y ≠ (shortCurve A B).toAffine.negY x y := by
    change y ≠ -y-0*x-0
    intro he
    apply hy
    linear_combination (1/2 : F)*he
  let W := (shortCurve A B).toAffine
  let L := W.slope x x y y
  have hL : L = (3*x^2+2*A*x+B)/(2*y) := by
    dsimp [L,W]
    rw [Affine.slope_of_Y_ne rfl hn]
    simp only [Affine.negY, shortCurve, toAffine, zero_mul, sub_zero]
    congr 1
    ring
  have hX : W.addX x x L = L^2-A-2*x := by dsimp [W, Affine.addX, shortCurve, toAffine]; ring
  have hY : W.addY x x y L = L*(x-(L^2-A-2*x))-y := by
    rw [Affine.addY, Affine.negY, Affine.negAddY, hX]
    dsimp [W, shortCurve, toAffine]
    ring
  dsimp only
  rw [← hL, ← hY, ← hX]
  exact ⟨_, Affine.Point.add_self_of_Y_ne hn⟩

private theorem double_x_on_short (A B x y : F) (h : (shortCurve A B).toAffine.Nonsingular x y)
    (hy : y ≠ 0) :
    ((Affine.Point.some x y h + Affine.Point.some x y h).xRep 0) = (x^2-B)^2/(4*y^2) := by
  have hn : y ≠ (shortCurve A B).toAffine.negY x y := by
    change y ≠ -y-0*x-0
    intro he
    apply hy
    linear_combination (1/2 : F)*he
  rw [Affine.Point.xRep_add_self_of_Y_ne h hn]
  have he := (Affine.equation_iff x y).mp h.1
  change y^2+0*x*y+0*y = x^3+A*x^2+B*x+0 at he
  simp only [zero_mul, add_zero] at he
  simp only [Matrix.cons_val_zero, shortCurve, toAffine, b₂, b₄, b₆, b₈, mul_zero, zero_mul,
    zero_add, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0)]
  congr 1
  · ring
  · linear_combination -4*he

omit [CharZero F] in
private theorem x_translate_marked_origin (A B x y : F)
    (h : (shortCurve A B).toAffine.Nonsingular x y)
    (h₀ : (shortCurve A B).toAffine.Nonsingular 0 0) (hx : x ≠ 0) :
    ((Affine.Point.some x y h + Affine.Point.some 0 0 h₀).xRep 0) = B/x := by
  rw [Affine.Point.xRep_add_of_X_ne h h₀ hx]
  have he := (Affine.equation_iff x y).mp h.1
  change y^2 + 0*x*y + 0*y = x^3 + A*x^2 + B*x + 0 at he
  simp only [zero_mul, add_zero] at he
  simp only [Matrix.cons_val_zero, shortCurve, toAffine, sub_zero, zero_mul, add_zero]
  field_simp
  linear_combination he


private def c (q t : F) := q*t+1
private def markedA (q t : F) := t^2-2*q*t-2
private def markedB (q t : F) := -(t^2-1)*c q t^2
private def x1 (q t : F) := (t+1)*c q t
private def y1 (q t : F) := t*x1 q t
private def x2 (q t : F) := c q t^2
private def y2 (q t : F) := -q*t*x2 q t
private def J (q t : F) := q^4*t - 4*q^2*t - 4*q - t
private def x4 (q t : F) := parameterDenominator q t^2/(4*q^2)
private def y4 (q t : F) := -t*parameterDenominator q t*J q t/(8*q^3)
private def d6 (q t : F) := (q^2-1)^2 * parameterNumerator q t^2
private def d8 (q t : F) := 16*q^2 * parameterDenominator q t^2 * J q t^2
private def z6 (q t : F) := q^4*t + 4*q^3 + 6*q^2*t + 4*q + t
private def z8 (q t : F) :=
  q^8*t^3+8*q^7*t^2+20*q^6*t^3+8*q^6*t+56*q^5*t^2+6*q^4*t^3+64*q^4*t+
    24*q^3*t^2+32*q^3+4*q^2*t^3+24*q^2*t+8*q*t^2+t^3

omit [DecidableEq F] in
private theorem first_double_formula (q t : F) (hy : y1 q t ≠ 0) :
    let s := (3*x1 q t^2+2*markedA q t*x1 q t+markedB q t)/(2*y1 q t)
    let X := s^2-markedA q t-2*x1 q t
    X = x2 q t ∧ s*(x1 q t-X)-y1 q t = y2 q t := by
  dsimp only
  have hs : (3*x1 q t^2 + 2*markedA q t*x1 q t + markedB q t)/(2*y1 q t) =
      q*t+t+1 := by
    field_simp
    simp only [y1, x1, markedA, markedB, c]
    ring
  rw [hs]
  constructor <;> simp only [x1, y1, x2, y2, markedA, c] <;> ring

omit [DecidableEq F] in
private theorem second_double_formula (q t : F) (hq : q ≠ 0) (hy : y2 q t ≠ 0) :
    let s := (3*x2 q t^2+2*markedA q t*x2 q t+markedB q t)/(2*y2 q t)
    let X := s^2-markedA q t-2*x2 q t
    X = x4 q t ∧ s*(x2 q t-X)-y2 q t = y4 q t := by
  dsimp only
  have hs : (3*x2 q t^2+2*markedA q t*x2 q t+markedB q t)/(2*y2 q t) =
      -(3*q^2*t+2*q+t)/(2*q) := by
    field_simp
    simp only [y2, x2, markedA, markedB, c]
    ring
  rw [hs]
  constructor <;>
    simp only [x2, y2, x4, y4, markedA, c, parameterDenominator, J] <;> field_simp <;> ring

omit [DecidableEq F] in
private theorem fourth_minus_second (q t : F) (hq : q ≠ 0) :
    x4 q t-x2 q t = -t*(q^2-1)*parameterNumerator q t/(4*q^2) := by
  unfold x4 x2 c parameterDenominator parameterNumerator
  field_simp
  ring

omit [DecidableEq F] in
private theorem sixth_x_formula (q t : F) (hq : q ≠ 0) (ht : t ≠ 0)
    (hp : q^2-1 ≠ 0) (hn : parameterNumerator q t ≠ 0) :
    ((y4 q t-y2 q t)/(x4 q t-x2 q t))^2-markedA q t-x4 q t-x2 q t =
      c q t^2*z6 q t^2/d6 q t := by
  have hm : (y4 q t-y2 q t)/(x4 q t-x2 q t) =
      -(7*q^6*t^2+14*q^5*t+3*q^4*t^2+8*q^4+12*q^3*t+5*q^2*t^2+8*q^2+6*q*t+t^2)/
      (2*q*(q^2-1)*parameterNumerator q t) := by
    rw [fourth_minus_second _ _ hq]
    unfold y4 y2 x2 c parameterDenominator J
    field_simp
    ring
  rw [hm]
  unfold markedA x4 x2 c z6 d6 parameterDenominator
  field_simp
  unfold parameterNumerator
  ring

omit [DecidableEq F] in
private theorem eighth_x_formula (q t : F) (hq : q ≠ 0) (ht : t ≠ 0)
    (hH : parameterDenominator q t ≠ 0) (hJ : J q t ≠ 0) :
    (x4 q t^2-markedB q t)^2/(4*y4 q t^2) = z8 q t^2/d8 q t := by
  have hnum : x4 q t^2-markedB q t = t*z8 q t/(16*q^4) := by
    unfold x4 markedB c z8 parameterDenominator
    field_simp
    ring
  rw [hnum]
  unfold d8 y4
  field_simp
  ring

private def factorMinus (q t : F) :=
  q^6*t^2 - 6*q^5*t^2 - 5*q^4*t^2 - 20*q^4*t - 8*q^3*t^2 - 4*q^3*t -
    16*q^3 + 3*q^2*t^2 - 12*q^2*t - 2*q*t^2 + 4*q*t + t^2

private def factorPlus (q t : F) :=
  q^6*t^2 + 6*q^5*t^2 - 5*q^4*t^2 + 20*q^4*t + 8*q^3*t^2 - 4*q^3*t +
    16*q^3 + 3*q^2*t^2 + 12*q^2*t + 2*q*t^2 + 4*q*t + t^2

omit [CharZero F] [DecidableEq F] in
private theorem sixth_x_sub_first (q t : F) :
    c q t^2*z6 q t^2 - x1 q t*d6 q t =
      c q t*(q^3*t-3*q^2*t-q*t-4*q-t)*factorMinus q t := by
  simp only [x1, c, z6, d6, parameterNumerator, factorMinus]
  ring

omit [CharZero F] [DecidableEq F] in
private theorem sixth_x_sub_translated (q t : F) :
    c q t^2*z6 q t^2 - ((1-t)*c q t)*d6 q t =
      c q t*(q^3*t+3*q^2*t-q*t+4*q+t)*factorPlus q t := by
  unfold c z6 d6 parameterNumerator factorPlus
  ring

set_option maxHeartbeats 0 in
omit [CharZero F] [DecidableEq F] in
private theorem eighth_x_sub_sixth (q t : F) :
    z8 q t^2*d6 q t - c q t^2*z6 q t^2*d8 q t =
      -(factorMinus q t*factorPlus q t*markedParameterPolynomial q t) := by
  unfold z8 d6 c z6 d8 factorMinus factorPlus markedParameterPolynomial
  unfold parameterDenominator parameterNumerator J
  ring


omit [CharZero F] [DecidableEq F] in
private theorem affine_point_with_coordinates {W : WeierstrassCurve.Affine F}
    {P : W.Point} {x y X Y : F} {h : W.Nonsingular x y}
    (hP : P = Affine.Point.some x y h) (hx : x = X) (hy : y = Y) :
    ∃ h' : W.Nonsingular X Y, P = Affine.Point.some X Y h' := by
  subst X
  subst Y
  exact ⟨h,hP⟩

omit [CharZero F] [DecidableEq F] in
private theorem eq_or_neg_of_x_coordinate {W : WeierstrassCurve.Affine F} {P Q : W.Point}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (h : P.xRep 0 = Q.xRep 0) : P = Q ∨ P = -Q := by
  apply Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep
  funext i
  fin_cases i
  · exact h
  · cases P with
    | zero => exact (hP rfl).elim
    | some x y hp =>
      cases Q with
      | zero => exact (hQ rfl).elim
      | some x' y' hq => rfl

omit [CharZero F] in
private theorem y_ne_zero_of_double_ne_zero {A B x y : F}
    {h : (shortCurve A B).toAffine.Nonsingular x y}
    (hh : Affine.Point.some x y h + Affine.Point.some x y h ≠ 0) : y ≠ 0 := by
  rintro rfl
  apply hh
  apply Affine.Point.add_self_of_Y_eq
  change (0 : F) = -0-0*x-0
  simp

set_option maxHeartbeats 0 in
/-- The polynomial in the explicit (q,t) chart follows from a point of exact
order fourteen whose seventh multiple differs from the marked point (0,0). -/
theorem marked_parameters_of_order_fourteen (q t : F)
    (h : (normalizedMarkedCurve q t).toAffine.Nonsingular ((t+1)*(q*t+1)) (t*((t+1)*(q*t+1))))
    (h₀ : (normalizedMarkedCurve q t).toAffine.Nonsingular 0 0)
    (ho : addOrderOf (Affine.Point.some _ _ h) = 14)
    (hindep : 7 • (Affine.Point.some _ _ h) ≠ Affine.Point.some 0 0 h₀) :
    q ≠ 0 ∧ parameterDenominator q t ≠ 0 ∧ q^2-1 ≠ 0 ∧ parameterNumerator q t ≠ 0 ∧
      markedParameterPolynomial q t = 0 := by
  change (shortCurve (markedA q t) (markedB q t)).toAffine.Nonsingular (x1 q t) (y1 q t) at h
  change (shortCurve (markedA q t) (markedB q t)).toAffine.Nonsingular 0 0 at h₀
  let Q := Affine.Point.some (x1 q t) (y1 q t) h
  let T := Affine.Point.some 0 0 h₀
  change addOrderOf Q = 14 at ho
  change 7 • Q ≠ T at hindep
  have hzero (n : ℕ) : n • Q = 0 ↔ 14 ∣ n := by
    rw [← ho, addOrderOf_dvd_iff_nsmul_eq_zero]
  have hnz {n : ℕ} (hn : ¬14 ∣ n) : n • Q ≠ 0 := fun h => hn ((hzero n).mp h)
  have hT : T+T = 0 := by
    apply Affine.Point.add_self_of_Y_eq
    change (0 : F) = -0-0*0-0
    simp
  have hnegT : -T = T := (eq_neg_of_add_eq_zero_left hT).symm
  have hy : y1 q t ≠ 0 := y_ne_zero_of_double_ne_zero (by rw [← two_nsmul]; exact hnz (by decide))
  have hX : x1 q t ≠ 0 := by
    intro he
    apply hy
    rw [y1, he, mul_zero]
  have ht : t ≠ 0 := by
    intro he
    apply hy
    rw [y1, he, zero_mul]
  obtain ⟨hP2, eP2⟩ := double_on_short (markedA q t) (markedB q t) (x1 q t) (y1 q t) h hy
  obtain ⟨h2x, h2y⟩ := first_double_formula q t hy
  obtain ⟨h2, e2⟩ := affine_point_with_coordinates eP2 h2x h2y
  change Q+Q = _ at e2
  rw [← two_nsmul] at e2
  have hy2 : y2 q t ≠ 0 := by
    apply y_ne_zero_of_double_ne_zero
    rw [← e2, ← add_nsmul]
    exact hnz (by decide : ¬14 ∣ 4)
  have hq : q ≠ 0 := by
    intro he
    apply hy2
    rw [y2, he, neg_zero, zero_mul, zero_mul]
  obtain ⟨hP4, eP4⟩ := double_on_short (markedA q t) (markedB q t) (x2 q t) (y2 q t) h2 hy2
  obtain ⟨h4x, h4y⟩ := second_double_formula q t hq hy2
  obtain ⟨h4, e4⟩ := affine_point_with_coordinates eP4 h4x h4y
  rw [← e2, ← add_nsmul] at e4
  change 4 • Q = _ at e4
  have hy4 : y4 q t ≠ 0 := by
    apply y_ne_zero_of_double_ne_zero
    rw [← e4, ← add_nsmul]
    exact hnz (by decide : ¬14 ∣ 8)
  have hH : parameterDenominator q t ≠ 0 := by
    intro he
    apply hy4
    rw [y4,he,mul_zero,zero_mul,zero_div]
  have hJ : J q t ≠ 0 := by
    intro he
    apply hy4
    rw [y4,he,mul_zero,zero_div]
  have hX42 : x4 q t ≠ x2 q t := by
    intro he
    have hx : (4 • Q).xRep 0 = (2 • Q).xRep 0 := by
      rw [e4,e2]
      simpa only [Affine.Point.xRep_some, Matrix.cons_val_zero] using he
    rcases eq_or_neg_of_x_coordinate (hnz (n := 4) (by decide)) (hnz (n := 2) (by decide)) hx with hq | hq
    · apply hnz (by decide : ¬14 ∣ 2)
      calc
        2 • Q = 4 • Q - 2 • Q := by abel
        _ = 0 := by rw [hq,sub_self]
    · apply hnz (by decide : ¬14 ∣ 6)
      calc
        6 • Q = 4 • Q + 2 • Q := by abel
        _ = 0 := by rw [hq,neg_add_cancel]
  have hD : q^2-1 ≠ 0 := by
    intro hD
    apply hX42
    apply sub_eq_zero.mp
    rw [fourth_minus_second _ _ hq,hD,mul_zero,zero_mul,zero_div]
  have hN : parameterNumerator q t ≠ 0 := by
    intro hN
    apply hX42
    apply sub_eq_zero.mp
    rw [fourth_minus_second _ _ hq,hN,mul_zero,zero_div]
  have hd6 : d6 q t ≠ 0 := mul_ne_zero (pow_ne_zero _ hD) (pow_ne_zero _ hN)
  have hd8 : d8 q t ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hq))
    (pow_ne_zero _ hH)) (pow_ne_zero _ hJ)
  have e6 : (6 • Q).xRep 0 = c q t^2*z6 q t^2/d6 q t := by
    rw [show 6 • Q = 4 • Q+2 • Q by abel, e4, e2, Affine.Point.xRep_add_of_X_ne h4 h2 hX42]
    simp only [Matrix.cons_val_zero, shortCurve, toAffine, zero_mul]
    rw [← sixth_x_formula q t hq ht hD hN]
    have hn : x4 q t-x2 q t ≠ 0 := sub_ne_zero.mpr hX42
    field_simp
    ring
  have e8 : (8 • Q).xRep 0 = z8 q t^2/d8 q t := by
    rw [show 8 • Q = 4 • Q+4 • Q by abel, e4]
    rw [double_x_on_short _ _ _ _ h4 hy4, eighth_x_formula q t hq ht hH hJ]
  have h18 : (8 : ℕ) • Q = -((6 : ℕ) • Q) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← add_nsmul]
    exact (hzero 14).mpr (dvd_refl _)
  have hex : (8 • Q).xRep 0 = (6 • Q).xRep 0 := by rw [h18, Affine.Point.xRep_neg]
  rw [e8,e6] at hex
  have hmul := (div_eq_div_iff hd8 hd6).mp hex
  have hp := eighth_x_sub_sixth q t
  rw [hmul,sub_self,zero_eq_neg] at hp
  have hminus : factorMinus q t ≠ 0 := by
    intro hz
    have hmul := sixth_x_sub_first q t
    rw [hz,mul_zero] at hmul
    have he : (6 • Q).xRep 0 = Q.xRep 0 := by
      rw [e6, show Q.xRep 0 = x1 q t from rfl]
      exact (div_eq_iff hd6).mpr (sub_eq_zero.mp hmul)
    have hQ : Q ≠ 0 := by simpa only [one_nsmul] using hnz (n := 1) (by decide)
    rcases eq_or_neg_of_x_coordinate (hnz (n := 6) (by decide)) hQ he with hq | hq
    · apply hnz (by decide : ¬14 ∣ 5)
      calc
        5 • Q = 6 • Q-Q := by abel
        _ = 0 := by rw [hq,sub_self]
    · apply hnz (by decide : ¬14 ∣ 7)
      calc
        7 • Q = 6 • Q+Q := by abel
        _ = 0 := by rw [hq,neg_add_cancel]
  have hplus : factorPlus q t ≠ 0 := by
    intro hz
    have hmul := sixth_x_sub_translated q t
    rw [hz,mul_zero] at hmul
    have hxT : (Q+T).xRep 0 = (1-t)*c q t := by
      rw [x_translate_marked_origin _ _ _ _ h h₀ hX]
      apply (div_eq_iff hX).mpr
      unfold markedB x1
      ring
    have hne : Q+T ≠ 0 := by
      intro hQT
      apply hnz (by decide : ¬14 ∣ 2)
      have e : Q = -T := eq_neg_of_add_eq_zero_left hQT
      rw [two_nsmul,e,hnegT,hT]
    have he : (6 • Q).xRep 0 = (Q+T).xRep 0 := by
      rw [e6,hxT]
      exact (div_eq_iff hd6).mpr (sub_eq_zero.mp hmul)
    rcases eq_or_neg_of_x_coordinate (hnz (n := 6) (by decide)) hne he with hq | hq
    · have e : 5 • Q = T := by
        calc
          5 • Q = 6 • Q-Q := by abel
          _ = T := by rw [hq]; abel
      apply hnz (by decide : ¬14 ∣ 10)
      rw [show 10 • Q = 5 • Q+5 • Q by abel, e,hT]
    · apply hindep
      calc
        7 • Q = 6 • Q+Q := by abel
        _ = -T := by rw [hq]; abel
        _ = T := hnegT
  exact ⟨hq,hH,hD,hN,(mul_eq_zero.mp hp).resolve_left (mul_ne_zero hminus hplus)⟩

/-- Independent marked torsion in this normal form gives an affine point on the
symmetric model and recovers the marked Weierstrass equation at that point. -/
theorem normalized_torsion_has_affine_model (q t : F)
    (h : (normalizedMarkedCurve q t).toAffine.Nonsingular ((t+1)*(q*t+1)) (t*((t+1)*(q*t+1))))
    (h₀ : (normalizedMarkedCurve q t).toAffine.Nonsingular 0 0)
    (ho : addOrderOf (Affine.Point.some _ _ h) = 14)
    (hindep : 7 • (Affine.Point.some _ _ h) ≠ Affine.Point.some 0 0 h₀) :
    ∃ u v : F, fibre u 1 v 1 = 0 ∧ markedCurve u v = normalizedMarkedCurve q t := by
  obtain ⟨hq,hd,hD,hn,hP⟩ := marked_parameters_of_order_fourteen q t h h₀ ho hindep
  exact ⟨(affineCoordinates q t).1, (affineCoordinates q t).2,
    affine_equation_of_marked_parameters q t hq hd hP,
    (affine_coordinates_recover_marked_equation q t hq hd hD hn).2⟩

theorem order_fourteen_short_nonvanishing (A B x y : F)
    (h : (⟨0,A,0,B,0⟩ : WeierstrassCurve F).toAffine.Nonsingular x y)
    (h₀ : (⟨0,A,0,B,0⟩ : WeierstrassCurve F).toAffine.Nonsingular 0 0)
    (ho : addOrderOf (Affine.Point.some _ _ h) = 14) :
    x ≠ 0 ∧ y ≠ 0 ∧ x^2-B ≠ 0 := by
  change (shortCurve A B).toAffine.Nonsingular x y at h
  change (shortCurve A B).toAffine.Nonsingular 0 0 at h₀
  let Q := Affine.Point.some x y h
  let T := Affine.Point.some 0 0 h₀
  have hne (n : ℕ) (hn : ¬14 ∣ n) : n • Q ≠ 0 := by
    intro he
    apply hn
    rw [← ho, addOrderOf_dvd_iff_nsmul_eq_zero]
    exact he
  have hy : y ≠ 0 := y_ne_zero_of_double_ne_zero (by rw [← two_nsmul]; exact hne 2 (by decide))
  have hEq := (Affine.equation_iff x y).mp h.1
  have hx : x ≠ 0 := by
    intro he
    change y^2+0*x*y+0*y = x^3+A*x^2+B*x+0 at hEq
    rw [he] at hEq
    simp [hy] at hEq
  refine ⟨hx,hy,?_⟩
  intro he
  have hT : T+T = 0 := Affine.Point.add_self_of_Y_eq (by change (0 : F) = -0-0*0-0; simp)
  have hNeg : -T = T := (eq_neg_of_add_eq_zero_left hT).symm
  have hc : (2 • Q).xRep 0 = T.xRep 0 := by
    rw [two_nsmul]
    change (Affine.Point.some x y h + Affine.Point.some x y h).xRep 0 = 0
    rw [double_x_on_short A B x y h hy, he]
    simp
  have h2 : 2 • Q = T := (eq_or_neg_of_x_coordinate (hne 2 (by decide))
    (Affine.Point.some_ne_zero h₀) hc).elim id (fun h => h.trans hNeg)
  apply hne 4 (by decide)
  calc
    4 • Q = 2 • Q + 2 • Q := by abel
    _ = 0 := by rw [h2, hT]

end

end NajmanTrbovic.Cubic
