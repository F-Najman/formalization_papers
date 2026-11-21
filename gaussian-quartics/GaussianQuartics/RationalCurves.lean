module

public import GaussianQuartics.FermatTriangle
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-! The rational points of the two curves used in the quartic equations. -/

public section

namespace GaussianQuartics

/-- The affine rational points of `Y² = X³ + X` all have `Y = 0`. -/
theorem rational_plus_y_eq_zero {x y : ℚ} (h : y ^ 2 = x ^ 3 + x) : y = 0 := by
  by_contra hy
  have hx : 0 < x := by
    have hprod : 0 < x * (x ^ 2 + 1) := by nlinarith [sq_pos_of_ne_zero hy]
    exact pos_of_mul_pos_left hprod (by positivity)
  let a : ℤ := x.num
  let b : ℤ := x.den
  have ha : 0 < a := by
    have ha' : 0 < (a : ℚ) := by
      change 0 < (x.num : ℚ)
      rw [← Rat.mul_den_eq_num]
      positivity
    exact_mod_cast ha'
  have hb : 0 < b := by dsimp [b]; exact_mod_cast x.den_pos
  have hcop : IsCoprime a b := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa [a, b] using x.reduced
  have hab : x * (b : ℚ) = a := by simp [a, b]
  have hs : IsSquare (a * b * (a ^ 2 + b ^ 2)) := by
    apply Rat.isSquare_intCast_iff.mp
    push_cast
    refine ⟨y * b ^ 2, ?_⟩
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hx' : x = (a : ℚ) / b := (eq_div_iff hbq).2 hab
    rw [hx'] at h
    field_simp at h
    linear_combination -(b : ℚ) * h
  have haCop : IsCoprime a (a ^ 2 + b ^ 2) := by
    simpa [pow_two, add_comm] using (hcop.pow_right (n := 2)).add_mul_left_right a
  have hbCop : IsCoprime b (a ^ 2 + b ^ 2) := by
    simpa [pow_two] using (hcop.symm.pow_right (n := 2)).add_mul_left_right b
  obtain ⟨c, hc⟩ := hs
  rw [← pow_two] at hc
  obtain ⟨d, e, _, _, hd, he⟩ :=
    FermatTriangle.exists_sq_sq_eq_of_isCoprime
      (haCop.mul_left hbCop) hc (mul_pos ha hb) (by positivity)
  obtain ⟨p, q, hp, hq, hpa, hqb⟩ :=
    FermatTriangle.exists_sq_sq_eq_of_isCoprime hcop hd ha hb
  apply not_fermat_42 hp.ne' hq.ne' (c := e)
  rw [hpa, hqb] at he
  linear_combination he

/-- The affine rational points of `Y² = X³ - X` all have `Y = 0`. -/
theorem rational_minus_y_eq_zero {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) : y = 0 := by
  by_contra hy
  let a := (x ^ 2 - 1) / y
  let b := 2 * x / y
  let c := (x ^ 2 + 1) / y
  have hp : a ^ 2 + b ^ 2 = c ^ 2 := by
    dsimp [a, b, c]
    field_simp
    ring
  have hab : a * b = 2 := by
    dsimp [a, b]
    field_simp
    linear_combination -h
  have ha : a ≠ 0 := by
    intro ha
    simp [ha] at hab
  have hb : b ≠ 0 := by
    intro hb
    simp [hb] at hab
  apply FermatTriangle.not_congruent_one
  exact ⟨|a|, |b|, c, abs_pos.mpr ha, abs_pos.mpr hb, by simpa [sq_abs] using hp, by
    rw [← abs_mul, hab]
    norm_num⟩

end GaussianQuartics
