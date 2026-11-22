module

public import ThreeFactorials.Approximation26
public import ThreeFactorials.PadeContour
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic

/-! Uniform norms for the simultaneous Padé contour integrals. -/

@[expose] public section

noncomputable section

namespace ThreeFactorials

open Complex Metric Finset

def padeNode (j : Fin 3) : ℂ := (j.val : ℂ) - 1

def padeNumerator (m : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  (↑(√m) : ℂ)⁻¹ * (z + (m : ℂ)) ^ (((k : ℝ) + 1 / 2 : ℝ) : ℂ)

def padeKernel (m : ℝ) (k : ℕ) (i : Fin 3) (z : ℂ) : ℂ :=
  padeNumerator m k z / ((z - padeNode i) * ∏ j : Fin 3, (z - padeNode j) ^ k)

/-- The integral normalized by (2πi). -/
def padeIntegral (m : ℝ) (k : ℕ) (i : Fin 3) (c : ℂ) (R : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ • ∮ z in C(c, R), padeKernel m k i z

private theorem norm_cast_nonneg {m : ℝ} (hm : 0 ≤ m) : ‖(m : ℂ)‖ = m := by
  rw [norm_real, Real.norm_of_nonneg hm]

theorem norm_node (j : Fin 3) : ‖padeNode j‖ ≤ 1 := by
  fin_cases j <;> norm_num [padeNode]

theorem node_dist {v j : Fin 3} (h : v ≠ j) : 1 ≤ ‖padeNode v - padeNode j‖ := by
  fin_cases v <;> fin_cases j <;> first | exact (h rfl).elim | norm_num [padeNode]

private theorem kernel_bound {m ρ T : ℝ} (hρ : 0 < ρ)
    (z : ℂ) (k : ℕ) (i : Fin 3) (hmin : ∀ j, ρ ≤ ‖z - padeNode j‖)
    (ht : √(‖z + (m : ℂ)‖ / m) ≤ T) :
    ‖padeKernel m k i z‖ ≤ (T / ρ) * (‖z + (m : ℂ)‖ / ρ ^ 3) ^ k := by
  have hp :
      (ρ ^ 3) ^ k ≤ ∏ j : Fin 3, ‖z - padeNode j‖ ^ k := by
    calc
      _ = ∏ _ : Fin 3, ρ ^ k := by simp [← pow_mul, mul_comm]
      _ ≤ _ := by
        simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
        gcongr <;> exact hmin _
  have hd := mul_le_mul (hmin i) hp (by positivity) (norm_nonneg _)
  have hn : 0 ≤ ‖z + (m : ℂ)‖ ^ k * √(‖z + (m : ℂ)‖ / m) := by positivity
  have hnum : ‖padeNumerator m k z‖ = ‖z + (m : ℂ)‖ ^ k * √(‖z + (m : ℂ)‖ / m) := by
    rw [padeNumerator, norm_mul, norm_inv, norm_cast_nonneg (Real.sqrt_nonneg _),
      Complex.norm_cpow_real, Real.rpow_add_of_nonneg (norm_nonneg _) (by positivity) (by norm_num),
      Real.rpow_natCast, ← Real.sqrt_eq_rpow, Real.sqrt_div (norm_nonneg _)]
    ring
  rw [padeKernel, norm_div, hnum, norm_mul, norm_prod]
  simp only [norm_pow]
  calc
    _ ≤ (‖z + (m : ℂ)‖ ^ k * √(‖z + (m : ℂ)‖ / m)) /
        (ρ * (ρ ^ 3) ^ k) := div_le_div_of_nonneg_left hn (by positivity) hd
    _ ≤ (‖z + (m : ℂ)‖ ^ k * T) / (ρ * (ρ ^ 3) ^ k) := by gcongr
    _ = _ := by rw [div_pow]; field_simp

/-- The large contour yields the exponentially small linear forms. -/
theorem outer_pade_estimate {m : ℝ} (hm : 320 ≤ m) (k : ℕ) (i : Fin 3) :
    ‖padeIntegral m k i (2 * (m : ℂ)) (3 * m - 1)‖ ≤
      12 * (1 / (2 * (m - 2) ^ 2)) ^ k := by
  have hm0 : 0 < m := by linarith
  have hr : 0 ≤ 3 * m - 1 := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have hp : ∀ z ∈ sphere (2 * (m : ℂ)) (3 * m - 1),
      ‖padeKernel m k i z‖ ≤ (3 / (m - 2)) * (1 / (2 * (m - 2) ^ 2)) ^ k := by
    intro z hz
    have hnorm : ‖z - 2 * (m : ℂ)‖ = 3 * m - 1 := by
      simpa [dist_eq_norm] using mem_sphere.mp hz
    have hnorm₂ : ‖(2 * (m : ℂ))‖ = 2 * m := by
      rw [norm_mul, norm_ofNat, norm_cast_nonneg hm0.le]
    have hzl : m - 1 ≤ ‖z‖ := by linarith [norm_sub_le z (2 * (m : ℂ))]
    let ρ := ‖z‖ - 1
    have hρ : m - 2 ≤ ρ := by dsimp [ρ]; linarith
    have hρpos := hm2.trans_le hρ
    have hf : ‖z + (m : ℂ)‖ ≤ 6 * m := calc
      _ = ‖(z - 2 * (m : ℂ)) + 3 * (m : ℂ)‖ := by congr 1; ring
      _ ≤ ‖z - 2 * (m : ℂ)‖ + ‖(3 * (m : ℂ))‖ := norm_add_le _ _
      _ ≤ _ := by rw [hnorm, norm_mul, norm_ofNat, norm_cast_nonneg hm0.le]; linarith
    have hT : √(‖z + (m : ℂ)‖ / m) ≤ 3 := by
      refine Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
      apply (div_le_iff₀ hm0).mpr
      linarith
    have hmin (j : Fin 3) : ρ ≤ ‖z - padeNode j‖ := by
      dsimp [ρ]
      linarith [norm_sub_norm_le z (padeNode j), norm_node j]
    have hh := kernel_bound hρpos z k i hmin hT
    have hx : ‖z + (m : ℂ)‖ / ρ ^ 3 ≤ 1 / (2 * (m - 2) ^ 2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      simpa [ρ, mul_comm] using outside_contour_bound hm hz
    exact hh.trans (mul_le_mul
      (div_le_div_of_nonneg_left (by norm_num) hm2 hρ)
      (pow_le_pow_left₀ (by positivity) hx _) (by positivity) (by positivity))
  unfold padeIntegral
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr hp).trans ?_
  have hR : 3 * m - 1 ≤ 4 * (m - 2) := by linarith
  calc
    _ ≤ (4 * (m - 2)) * ((3 / (m - 2)) * (1 / (2 * (m - 2) ^ 2)) ^ k) :=
      mul_le_mul_of_nonneg_right hR (by positivity)
    _ = _ := by field_simp; ring

/-- Each small contour yields an exponential bound for its individual form coefficient. -/
theorem inner_pade_estimate {m : ℝ} (hm : 320 ≤ m) (k : ℕ) (i j : Fin 3) :
    ‖padeIntegral m k i (padeNode j) (1 / 2)‖ ≤ 2 * (8 * (m + 2)) ^ k := by
  have hm0 : 0 < m := by linarith
  unfold padeIntegral
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (by norm_num) (C := 4 * (8 * (m + 2)) ^ k) ?_).trans_eq (by ring)
  intro z hz
  have hnorm : ‖z - padeNode j‖ = 1 / 2 := by
    simpa [dist_eq_norm] using mem_sphere.mp hz
  have hmin (v : Fin 3) : (1 / 2 : ℝ) ≤ ‖z - padeNode v‖ := by
    by_cases h : v = j
    · simpa [h] using hnorm.ge
    · have hh := norm_add_le (padeNode v - z) (z - padeNode j)
      rw [show padeNode v - z + (z - padeNode j) = padeNode v - padeNode j by ring,
        norm_sub_rev (padeNode v) z, hnorm] at hh
      linarith [node_dist h]
  have hV : ‖z + (m : ℂ)‖ ≤ m + 2 := calc
    _ = ‖(z - padeNode j) + (padeNode j + (m : ℂ))‖ := by congr 1; ring
    _ ≤ ‖z - padeNode j‖ + ‖padeNode j + (m : ℂ)‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [hnorm]
      have hn := norm_add_le (padeNode j) (m : ℂ)
      rw [norm_cast_nonneg hm0.le] at hn
      linarith [norm_node j]
  have hT : √(‖z + (m : ℂ)‖ / m) ≤ 2 := by
    refine Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ hm0).mpr
    linarith
  refine (kernel_bound (by norm_num) z k i hmin hT).trans ?_
  calc
    _ = 4 * (8 * ‖z + (m : ℂ)‖) ^ k := by norm_num [div_eq_mul_inv, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) k) (by norm_num)

end ThreeFactorials
