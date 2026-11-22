module

public import ThreeFactorials.PadeJets
public import ThreeFactorials.PellPruning26

import Mathlib.Tactic

/-! The unconditional classification at 26 in Theorem 1.1. -/

@[expose] public section

namespace ThreeFactorials

open Finset

theorem pade_approximations {m : ℕ} (hm : m = 323 ∨ m = 2737) : PadeApproximations m := by
  intro k hk
  have hm₀ : 320 ≤ m := by omega
  have hmR : (320 : ℝ) ≤ m := by exact_mod_cast hm₀
  have hmod : m % 2 = 1 := by rcases hm with rfl | rfl <;> decide
  have hratio : 8 * (1 / (2 * ((m : ℝ) - 2) ^ 2)) ≤ 1 / (errorBase m : ℝ) := by
    rcases hm with rfl | rfl <;> norm_num [errorBase]
  choose A hA using pade_entry_integral m k hk
  have hAR (i j : Fin 3) : (A i j : ℝ) = 8 ^ k * (padeCoefficient m k i j : ℝ) := by
    exact_mod_cast hA i j
  have hind : ∀ (v : Fin 3 → ℤ), v ≠ 0 → ∃ i : Fin 3, ∑ j, A i j * v j ≠ 0 := by
    intro v hv
    by_contra! hn
    let B : Matrix (Fin 3) (Fin 3) ℚ := padeCoefficient m k
    let w (j : Fin 3) : ℚ := v j
    have hBw : B.mulVec w = 0 := by
      funext i
      change (∑ j, padeCoefficient m k i j * (v j : ℚ)) = 0
      have hrow : (∑ j, (A i j : ℚ) * (v j : ℚ)) = 0 := by exact_mod_cast hn i
      simp only [hA, mul_assoc, ← Finset.mul_sum] at hrow
      exact (mul_eq_zero.mp hrow).resolve_left (by positivity)
    have hw := Matrix.eq_zero_of_mulVec_eq_zero (pade_matrix_det_ne_zero hmod hk) hBw
    apply hv
    funext j
    have he : (v j : ℚ) = 0 := congrFun hw j
    exact_mod_cast he
  refine ⟨A, hind, ?_, ?_⟩
  · intro i j
    have hθ := half_le_target (by omega : 2 ≤ m) j
    have hθ₀ : 0 ≤ approximationTarget m j := by linarith
    have he := inner_pade_estimate hmR k i j
    rw [pade_inner_eq hm₀ hk, ← Complex.ofReal_ratCast, ← Complex.ofReal_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hθ₀] at he
    have hcoeff : |(padeCoefficient m k i j : ℝ)| ≤ 4 * (8 * ((m : ℝ) + 2)) ^ k := by
      have hhalf := (mul_le_mul_of_nonneg_left hθ (abs_nonneg (padeCoefficient m k i j : ℝ))).trans he
      linarith
    rw [hAR, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 ^ k)]
    calc
      _ ≤ 8 ^ k * (4 * (8 * ((m : ℝ) + 2)) ^ k) := mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ = _ := by
        push_cast [approximationBase]
        rw [mul_left_comm, ← mul_pow, ← mul_assoc]
        norm_num
  · intro i
    have he := outer_pade_estimate hmR k i
    -- The centre and radius have the real cast used in the contour bound.
    rw [show ((m : ℝ) : ℂ) = (m : ℂ) by norm_cast, pade_outer_eq hm₀ hk] at he
    have hcast : (∑ j : Fin 3, (padeCoefficient m k i j : ℂ) * (approximationTarget m j : ℂ)) =
        (↑(∑ j : Fin 3, (padeCoefficient m k i j : ℝ) * approximationTarget m j) : ℂ) := by
      push_cast
      rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs] at he
    simp only [hAR, mul_assoc, ← Finset.mul_sum]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 ^ k)]
    calc
      _ ≤ 8 ^ k * (12 * (1 / (2 * ((m : ℝ) - 2) ^ 2)) ^ k) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = 12 * (8 * (1 / (2 * ((m : ℝ) - 2) ^ 2))) ^ k := by rw [mul_pow]; ring
      _ ≤ 12 * (1 / (errorBase m : ℝ)) ^ k := by gcongr
      _ = _ := by rw [div_pow, one_pow, mul_one_div]

/-- The first squarefree system has exactly one positive solution. -/
theorem unique_first_system {x y z : ℕ} (hy : 0 < y)
    (hx : x ^ 2 = 323 * y ^ 2 + 1) (hz : 322 * z ^ 2 + 1 = 323 * y ^ 2) :
    x = 18 ∧ y = 1 ∧ z = 1 := by
  have hb := middle_bound_of_pade (x₀ := 18) (z₀ := 1) (Or.inl rfl) hy
    (by decide : 1 * 18 ^ 2 = 323 + 1) (by decide : 322 * 1 ^ 2 + 1 = 323)
    (by simpa using hx) hz (pade_approximations (Or.inl rfl))
  have he := first_system_of_bound hy hx hz hb
  subst x
  have hys : y ^ 2 = 1 ^ 2 := by omega
  have hye := Nat.pow_left_injective (by decide : 2 ≠ 0) hys
  subst y
  have hzs : z ^ 2 = 1 ^ 2 := by omega
  exact ⟨rfl, rfl, Nat.pow_left_injective (by decide : 2 ≠ 0) hzs⟩

/-- The second squarefree system has exactly one positive solution. -/
theorem unique_second_system {x y z : ℕ} (hy : 0 < y)
    (hx : 2 * x ^ 2 = 2737 * y ^ 2 + 1) (hz : 19 * z ^ 2 + 1 = 2737 * y ^ 2) :
    x = 37 ∧ y = 1 ∧ z = 12 := by
  have hb := middle_bound_of_pade (x₀ := 37) (z₀ := 12) (Or.inr rfl) hy
    (by decide : 2 * 37 ^ 2 = 2737 + 1) (by decide : 19 * 12 ^ 2 + 1 = 2737)
    hx hz (pade_approximations (Or.inr rfl))
  have he := second_system_of_bound hy hx hz hb
  subst x
  have hys : y ^ 2 = 1 ^ 2 := by omega
  have hye := Nat.pow_left_injective (by decide : 2 ≠ 0) hys
  subst y
  have hzs : z ^ 2 = 12 ^ 2 := by omega
  exact ⟨rfl, rfl, Nat.pow_left_injective (by decide : 2 ≠ 0) hzs⟩

/-- The classification for (a_3=26) in Theorem 1.1, with no size restriction. -/
theorem case26_iff (a : ℕ) : Solution a 26 ↔ a = 324 ∨ a = 2738 :=
  case26_iff_of_pade (pade_approximations (Or.inl rfl)) (pade_approximations (Or.inr rfl)) a

end ThreeFactorials
