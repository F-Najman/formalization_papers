module

public import NajmanTrbovic.CubicFieldModel

import Mathlib.Tactic

/-! Rational parameters of the two affine projections of the symmetric cubic model. -/

@[expose] public section

namespace NajmanTrbovic.Cubic

theorem fibre_swap {R : Type*} [CommRing R] (u w v z : R) :
    fibre u w v z = fibre v z u w := by simp only [fibre, add_comm]

theorem descended_map {F L : Type*} [Field F] [Field L] (f : F →+* L) (x : F) :
    (descended x).map f = descended (f x) := by
  ext <;> simp [descended, a2Numerator, a4Numerator, a6Numerator, denominator, g2, g6, map_ofNat]

private theorem r_of_primitive_at_two {a b : ZMod 2} (h : a ≠ 0 ∨ b ≠ 0) : r a b = 1 :=
  (by decide +kernel : ∀ a b : ZMod 2, a ≠ 0 ∨ b ≠ 0 → r a b = 1) a b h

theorem r_ne_zero_on_rationals (x : ℚ) : r x 1 ≠ 0 := by
  intro hx
  let u := x.num
  let w : ℤ := x.den
  have hg : u.gcd w = 1 := by simpa [u, w, Int.gcd_def] using x.reduced
  have hw : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hux : (x.den : ℚ)*x = (u : ℚ) := by
    rw [mul_comm]
    exact ((div_eq_iff hw).mp x.num_div_den).symm
  have hcast : (w : ℚ) = (x.den : ℚ) := by simp [w]
  have hr : r (u : ℚ) (w : ℚ) = 0 := by
    rw [hcast, ← hux, show r ((x.den : ℚ)*x) x.den = (x.den : ℚ)^3*r x 1 by unfold r; ring,
      hx, mul_zero]
  have hr' : r u w = 0 := by
    have hc : ((r u w : ℤ) : ℚ) = r (u : ℚ) (w : ℚ) := by simp [r]
    exact Int.cast_injective (by rw [hc, hr, Int.cast_zero])
  have hprim : (u : ZMod 2) ≠ 0 ∨ (w : ZMod 2) ≠ 0 := by
    by_contra! h
    exact not_both_dvd Nat.prime_two hg ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp h.1,
      (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp h.2⟩
  have he := congrArg (Int.castRingHom (ZMod 2)) hr'
  have he' : r (u : ZMod 2) (w : ZMod 2) = 0 := by simpa [r] using he
  rw [r_of_primitive_at_two hprim] at he'
  exact (by decide +kernel : (1 : ZMod 2) ≠ 0) he'

private theorem g2_pos {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] (x : F) :
    0 < g2 x := by
  unfold g2
  nlinarith [sq_nonneg (2*x+1)]

private theorem nonzero_r_at_rational_pole {F : Type*} [Field F] (x : F) (h : x*(x+1) = 0) :
    r x 1 ≠ 0 := by
  rcases mul_eq_zero.mp h with rfl | h
  · simp [r]
  · have hx : x = -1 := eq_neg_of_add_eq_zero_left h
    rw [hx, show r (-1 : F) 1 = 1 by unfold r; ring]
    exact one_ne_zero

private theorem g6_pos {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] (x : F) :
    0 < g6 x := by
  have hid : 4*g6 x = (2*r x 1-x*(x+1))^2 + 27*(x*(x+1))^2 := by
    unfold g6 r
    ring
  by_cases h : x*(x+1) = 0
  · simp only [h, sub_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hid
    have hr : 2*r x 1 ≠ 0 := mul_ne_zero (by norm_num) (nonzero_r_at_rational_pole x h)
    have hp := sq_pos_of_ne_zero hr
    linarith
  · have hp := sq_pos_of_ne_zero h
    nlinarith [sq_nonneg (2*r x 1-x*(x+1))]

theorem denominator_ne_zero_of_ordered {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (x : F) : denominator x ≠ 0 :=
  (mul_pos (pow_pos (g2_pos x) _) (g6_pos x)).ne'

theorem g12_ne_zero_of_ordered {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (x : F) : g12 x ≠ 0 := by
  let T := x*(x+1)
  have hid : g12 x = r x 1^4 + 5*(r x 1)^2*T^2 + T^4 := by unfold g12 r; dsimp [T]; ring
  apply ne_of_gt
  rw [hid]
  by_cases h : T = 0
  · have he : r x 1 ≠ 0 := nonzero_r_at_rational_pole x h
    have hr := pow_pos (sq_pos_of_ne_zero he) 2
    simp only [h, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0), mul_zero, add_zero]
    simpa only [← pow_mul] using hr
  · have h4 : 0 < T^4 := by simpa only [← pow_mul] using pow_pos (sq_pos_of_ne_zero h) 2
    have hg : 0 ≤ r x 1^4 + 5*(r x 1)^2*T^2 := by positivity
    exact add_pos_of_nonneg_of_pos hg h4

theorem denominator_ne_zero_on_rationals (x : ℚ) : denominator x ≠ 0 :=
  denominator_ne_zero_of_ordered x

theorem jDenominator_ne_zero_on_rationals (x : ℚ) (hx : x*(x+1) ≠ 0) : jDenominator x ≠ 0 := by
  unfold jDenominator
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (fun h => hx (by simp [h])))
    (pow_ne_zero _ (fun h => hx (by simp [h])))) (pow_ne_zero _ (r_ne_zero_on_rationals x))

theorem descended_isElliptic_of_rational (x : ℚ) (hx : x*(x+1) ≠ 0) : (descended x).IsElliptic := by
  have hd := denominator_ne_zero_on_rationals x
  rw [WeierstrassCurve.isElliptic_iff, (descended_invariants x hd).2]
  exact (div_ne_zero (jDenominator_ne_zero_on_rationals x hx) (pow_ne_zero _ hd)).isUnit

theorem rational_coordinate_ne_pole {K : Type*} [Field K] [Algebra ℚ K] (x : ℚ) (v : K)
    (hv : v ∉ Set.range (algebraMap ℚ K)) (h : fibre (algebraMap ℚ K x) 1 v 1 = 0) :
    x*(x+1) ≠ 0 := by
  intro hx
  have hv' : v*(v+1) ≠ 0 := by
    intro he
    rcases mul_eq_zero.mp he with he | he
    · exact hv ⟨0, (map_zero _).trans he.symm⟩
    · exact hv ⟨-1, by simpa using (eq_neg_of_add_eq_zero_left he).symm⟩
  rcases mul_eq_zero.mp hx with rfl | hx
  · rw [map_zero, fibre_at_zero, mul_one, neg_eq_zero] at h
    exact hv' h
  · have hx' : x = -1 := eq_neg_of_add_eq_zero_left hx
    rw [hx', map_neg, map_one, fibre_at_neg_one, mul_one] at h
    exact hv' h

/-- The three conjugates on a cubic projection are related by the fractional-linear
transformation `v ↦ -1/(v+1)`. This identity is independent of the arithmetic
classification of rational or cubic points on the curve. -/
theorem finiteChart_factors_from_root {F : Type*} [Field F] (u v : F)
    (hv : v*(v+1) ≠ 0) (hf : fibre u 1 v 1 = 0) :
    finiteChart u 1 = Polynomial.C (u*(u+1)) *
      (Polynomial.X - Polynomial.C v) * (Polynomial.X - Polynomial.C (-1/(v+1))) *
      (Polynomial.X - Polynomial.C (-(v+1)/v)) := by
  let b := -1/(v+1)
  let c := -(v+1)/v
  let k := r v 1/(v*(v+1))
  have hv₀ : v ≠ 0 := fun h => hv (by rw [h, zero_mul])
  have hv₁ : v+1 ≠ 0 := fun h => hv (by rw [h, mul_zero])
  have hr : r u 1 = -(u*(u+1))*k := by
    change r u 1 = -(u*(u+1))*(r v 1/(v*(v+1)))
    rw [← mul_div_assoc, eq_div_iff hv]
    have he : r u 1 * (v*(v+1)) + r v 1 * (u*(u+1)) = 0 := by simpa [fibre] using hf
    linear_combination he
  have h₁ : v+b+c = k-1 := by dsimp [b,c,k]; unfold r; field_simp; ring
  have h₂ : v*b+v*c+b*c = -2-k := by dsimp [b,c,k]; unfold r; field_simp; ring
  have h₃ : v*b*c = 1 := by dsimp [b,c]; field_simp
  open Polynomial in
  have hsplit : (X-C v)*(X-C b)*(X-C c) = X^3 - C (k-1)*X^2 + C (-2-k)*X - 1 := by
    have he : (C (v*b*c) : F[X]) = 1 := by rw [h₃, C_1]
    rw [← h₁, ← h₂, ← he]
    simp only [map_add, map_mul]
    ring
  change finiteChart u 1 = Polynomial.C (u*(u+1)) * _ * (Polynomial.X - Polynomial.C b) *
    (Polynomial.X - Polynomial.C c)
  rw [mul_assoc, mul_assoc, ← mul_assoc (Polynomial.X-Polynomial.C v), hsplit]
  rw [finiteChart, hr]
  simp only [r, one_pow, mul_one, map_mul, map_add, map_sub, map_neg, map_ofNat,
    Polynomial.C_1]
  ring

end NajmanTrbovic.Cubic
