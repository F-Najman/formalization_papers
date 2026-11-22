module

public import ThreeFactorials.Pell26
public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic

/-! The simultaneous approximation criterion for the two remaining systems. -/

@[expose] public section

namespace ThreeFactorials

open Finset

def approximationBase (m : ℕ) : ℕ := 64 * (m + 2)

def errorBase (m : ℕ) : ℕ := (m - 2) ^ 2 / 4

def approximationCutoff (m : ℕ) : ℕ := if m = 323 then 128 else 16

noncomputable def approximationTarget (m : ℕ) (i : Fin 3) : ℝ :=
  √((m : ℝ) + ((i.val : ℝ) - 1)) / √(m : ℝ)

/-- The integer linear forms and the uniform estimates needed from Padé approximation. -/
def PadeApproximations (m : ℕ) : Prop :=
  ∀ k : ℕ, 0 < k →
    ∃ A : Fin 3 → Fin 3 → ℤ,
      (∀ v : Fin 3 → ℤ, v ≠ 0 → ∃ i : Fin 3, ∑ j, A i j * v j ≠ 0) ∧
      (∀ i j, |(A i j : ℝ)| ≤ 4 * (approximationBase m : ℝ) ^ k) ∧
      (∀ i, |∑ j, (A i j : ℝ) * approximationTarget m j| ≤ 12 / (errorBase m : ℝ) ^ k)

private theorem denominator_bound_of_approximants {m q : ℕ} (hm : m = 323 ∨ m = 2737)
    (hq : 0 < q) (p : Fin 3 → ℤ) (hp₀ : p 1 = (q : ℤ))
    (hp : ∀ j, |(q : ℝ) * approximationTarget m j - (p j : ℝ)| ≤ 4 * (m : ℝ) / q)
    (approximants : PadeApproximations m) :
    q ≤ errorBase m ^ approximationCutoff m := by
  let L : ℝ := errorBase m
  let P : ℝ := approximationBase m
  have hL : 1 < L := by rcases hm with rfl | rfl <;> norm_num [L, errorBase]
  have hP : 0 < P := by dsimp [P, approximationBase]; positivity
  have hPL : P / L < 1 := by rcases hm with rfl | rfl <;> norm_num [P, L, approximationBase, errorBase]
  have hnum : (2304 * (m : ℝ) * L) * (P / L) ^ approximationCutoff m ≤ 1 / 4 := by
    rcases hm with rfl | rfl <;> norm_num [L, P, errorBase, approximationBase, approximationCutoff]
  have hc : 0 < approximationCutoff m := by
    rcases hm with rfl | rfl <;> decide
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hExists : ∃ k : ℕ, 48 * (q : ℝ) ≤ L ^ k := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (48 * (q : ℝ)) hL
    exact ⟨k, hk.le⟩
  let k := Nat.find hExists
  have hk : 48 * (q : ℝ) ≤ L ^ k := Nat.find_spec hExists
  have hklt : k < approximationCutoff m := by
    by_contra! hkl
    have hkpos : 0 < k := by omega
    have hpmin := Nat.find_min hExists (show k - 1 < k by omega)
    have hprev : L ^ (k - 1) < 48 * (q : ℝ) := lt_of_not_ge hpmin
    have hkpow : L ^ k = L ^ (k - 1) * L := by
      rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ k by omega)]
    have hLpow : 0 < L ^ k := pow_pos (by linarith) _
    obtain ⟨A, hind, hA, herr⟩ := approximants k hkpos
    have hpne : p ≠ 0 := by
      intro he
      have h := congrFun he 1
      rw [hp₀, Pi.zero_apply] at h
      exact hq.ne' (by exact_mod_cast h)
    obtain ⟨i, hi⟩ := hind p hpne
    have hi' : (1 : ℝ) ≤ |((∑ j, A i j * p j : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs hi
    have hdecomp : (∑ j, ((A i j * p j : ℤ) : ℝ)) =
        (q : ℝ) * (∑ j, (A i j : ℝ) * approximationTarget m j) +
        ∑ j, (A i j : ℝ) * ((p j : ℝ) - (q : ℝ) * approximationTarget m j) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    have h₁ : (q : ℝ) * (12 / L ^ k) ≤ 1 / 4 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hLpow).mpr
      linarith
    have h₂ : 48 * (m : ℝ) * P ^ k / (q : ℝ) ≤ 1 / 4 := by
      have hp' : L ^ k ≤ (48 * (q : ℝ)) * L := by
        rw [hkpow]
        gcongr
      have hmon : (P / L) ^ k ≤ (P / L) ^ approximationCutoff m :=
        (pow_le_pow_iff_right_of_lt_one₀ (by positivity) hPL).mpr hkl
      have haux : 48 * (m : ℝ) * P ^ k / (q : ℝ) ≤
          (2304 * (m : ℝ) * L) * (P / L) ^ k := by
        rw [div_pow, ← mul_div_assoc]
        have hcleared : 48 * (m : ℝ) * P ^ k * L ^ k ≤
            2304 * (m : ℝ) * L * P ^ k * (q : ℝ) := by
          calc
            _ ≤ (48 * (m : ℝ) * P ^ k) * ((48 * (q : ℝ)) * L) :=
              mul_le_mul_of_nonneg_left hp' (by positivity)
            _ = _ := by ring
        exact (div_le_div_iff₀ hqR hLpow).mpr hcleared
      exact haux.trans ((mul_le_mul_of_nonneg_left hmon (by positivity)).trans hnum)
    have hrest :
        |∑ j, (A i j : ℝ) * ((p j : ℝ) - (q : ℝ) * approximationTarget m j)| ≤
          48 * (m : ℝ) * P ^ k / (q : ℝ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc
        _ ≤ ∑ _j : Fin 3, (4 * P ^ k) * (4 * (m : ℝ) / q) := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul, abs_sub_comm]
          exact mul_le_mul (hA i j) (hp j) (abs_nonneg _) (by positivity)
        _ = _ := by simp; ring
    have hf :
        |((∑ j, A i j * p j : ℤ) : ℝ)| ≤ (1 / 2 : ℝ) := by
      rw [Int.cast_sum, hdecomp]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hqR, show (1 / 2 : ℝ) = 1 / 4 + 1 / 4 by norm_num]
      exact add_le_add ((mul_le_mul_of_nonneg_left (herr i) hqR.le).trans h₁) (hrest.trans h₂)
    linarith
  have : (q : ℝ) ≤ (errorBase m : ℝ) ^ approximationCutoff m := by
    have hqL := hk.trans (pow_le_pow_right₀ hL.le hklt.le)
    linarith
  exact_mod_cast this

theorem half_le_target {m : ℕ} (hm : 2 ≤ m) (j : Fin 3) :
    (1 / 2 : ℝ) ≤ approximationTarget m j := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hv : (0 : ℝ) ≤ j.val := by positivity
  have hs := Real.sq_sqrt (by linarith : 0 ≤ (m : ℝ) + ((j.val : ℝ) - 1))
  have hr := Real.sq_sqrt (by linarith : 0 ≤ (m : ℝ))
  unfold approximationTarget
  have hsR : 0 < √(m : ℝ) := Real.sqrt_pos.2 (by linarith)
  refine (le_div_iff₀ hsR).2 ?_
  refine (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp ?_
  rw [mul_pow, hs, hr]
  linarith

private theorem close_to_target {m q : ℕ} (hm : 2 ≤ m) (hq : 0 < q)
    {j : Fin 3} {p : ℤ} (hp : 0 ≤ p)
    (he : |((q : ℝ) * approximationTarget m j) ^ 2 - (p : ℝ) ^ 2| ≤ (m : ℝ) + 1) :
    |(q : ℝ) * approximationTarget m j - (p : ℝ)| ≤ 4 * (m : ℝ) / q := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpR : (0 : ℝ) ≤ p := by exact_mod_cast hp
  have hθ := half_le_target hm j
  let a : ℝ := q * approximationTarget m j
  have ha : (q : ℝ) / 2 ≤ a := by dsimp [a]; nlinarith only [mul_le_mul_of_nonneg_left hθ hqR.le]
  have ha' : 0 ≤ a + (p : ℝ) := by linarith
  have hprod : |a - (p : ℝ)| * (a + (p : ℝ)) ≤ (m : ℝ) + 1 := by
    rw [← abs_of_nonneg ha', ← abs_mul]
    calc
      _ = |a ^ 2 - (p : ℝ) ^ 2| := by ring_nf
      _ ≤ _ := he
  have hle : |a - (p : ℝ)| * ((q : ℝ) / 2) ≤ (m : ℝ) + 1 :=
    (mul_le_mul_of_nonneg_left (by linarith : (q : ℝ) / 2 ≤ a + (p : ℝ)) (abs_nonneg _)).trans hprod
  apply (le_div_iff₀ hqR).mpr
  linarith

private theorem target_sq {m : ℕ} (hm : 2 ≤ m) (j : Fin 3) :
    (approximationTarget m j) ^ 2 = ((m : ℝ) + ((j.val : ℝ) - 1)) / (m : ℝ) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hj : (0 : ℝ) ≤ j.val := by positivity
  rw [approximationTarget, div_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]

/-- The common denominator of the two rational approximations is (m y).
The hypothesis concerns only the integer linear forms, independently of the system. -/
theorem middle_bound_of_pade {a m c x y z x₀ z₀ : ℕ}
    (hm : m = 323 ∨ m = 2737) (hy : 0 < y)
    (hx₀ : a * x₀ ^ 2 = m + 1) (hz₀ : c * z₀ ^ 2 + 1 = m)
    (hx : a * x ^ 2 = m * y ^ 2 + 1) (hz : c * z ^ 2 + 1 = m * y ^ 2)
    (approximants : PadeApproximations m) : m * y ≤ errorBase m ^ approximationCutoff m := by
  have hm₂ : 2 ≤ m := by omega
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm₂
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  let q := m * y
  let p : Fin 3 → ℤ := ![c * z₀ * z, q, a * x₀ * x]
  have hq : 0 < q := Nat.mul_pos (by omega) hy
  have hqR : (q : ℝ) = (m : ℝ) * (y : ℝ) := by simp [q]
  apply denominator_bound_of_approximants hm hq p (by simp [p]) ?_ approximants
  intro j
  have hp : 0 ≤ p j := by fin_cases j <;> simp [p] <;> positivity
  apply close_to_target hm₂ hq hp
  have hx₀' : (a : ℝ) * (x₀ : ℝ) ^ 2 = (m : ℝ) + 1 := by exact_mod_cast hx₀
  have hz₀' : (c : ℝ) * (z₀ : ℝ) ^ 2 + 1 = (m : ℝ) := by exact_mod_cast hz₀
  have hx' : (a : ℝ) * (x : ℝ) ^ 2 = (m : ℝ) * (y : ℝ) ^ 2 + 1 := by exact_mod_cast hx
  have hz' : (c : ℝ) * (z : ℝ) ^ 2 + 1 = (m : ℝ) * (y : ℝ) ^ 2 := by exact_mod_cast hz
  rw [mul_pow, target_sq hm₂, hqR]
  fin_cases j
  · simp [p]
    rw [← sub_eq_add_neg (m : ℝ) 1]
    have hprod : ((c : ℝ) * (z₀ : ℝ) * (z : ℝ)) ^ 2 =
        ((m : ℝ) - 1) * ((m : ℝ) * (y : ℝ) ^ 2 - 1) := by
      calc
        _ = ((c : ℝ) * (z₀ : ℝ) ^ 2) * ((c : ℝ) * (z : ℝ) ^ 2) := by ring
        _ = _ := by rw [show (c : ℝ) * (z₀ : ℝ) ^ 2 = (m : ℝ) - 1 by linarith,
          show (c : ℝ) * (z : ℝ) ^ 2 = (m : ℝ) * (y : ℝ) ^ 2 - 1 by linarith]
    rw [show ((m : ℝ) * (y : ℝ)) ^ 2 * (((m : ℝ) - 1) / (m : ℝ)) -
        ((c : ℝ) * (z₀ : ℝ) * (z : ℝ)) ^ 2 = (m : ℝ) - 1 by rw [hprod]; field_simp; ring]
    rw [abs_of_nonneg (by linarith : 0 ≤ (m : ℝ) - 1)]
    linarith
  · simp [p, div_self hm0, hqR]
    linarith
  · simp [p]
    norm_num
    have hprod : ((a : ℝ) * (x₀ : ℝ) * (x : ℝ)) ^ 2 =
        ((m : ℝ) + 1) * ((m : ℝ) * (y : ℝ) ^ 2 + 1) := by
      calc
        _ = ((a : ℝ) * (x₀ : ℝ) ^ 2) * ((a : ℝ) * (x : ℝ) ^ 2) := by ring
        _ = _ := by rw [hx₀', hx']
    rw [show ((m : ℝ) * (y : ℝ)) ^ 2 * (((m : ℝ) + 1) / (m : ℝ)) -
        ((a : ℝ) * (x₀ : ℝ) * (x : ℝ)) ^ 2 = -((m : ℝ) + 1) by rw [hprod]; field_simp; ring]
    rw [abs_neg, abs_of_nonneg (by linarith : 0 ≤ (m : ℝ) + 1)]

end ThreeFactorials
