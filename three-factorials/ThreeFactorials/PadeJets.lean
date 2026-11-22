module

public import ThreeFactorials.PadeEstimates
public import ThreeFactorials.PadeCoefficients

import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-! Local coefficients and their contour representation. -/

@[expose] public section

noncomputable section

namespace ThreeFactorials

open Complex Metric Set Filter Finset
open scoped Topology

private def jet (n : ℕ) (f : ℂ → ℂ) (a : ℂ) : ℂ :=
  iteratedDeriv n f a / n.factorial

private theorem binomial_product (α : ℂ) (n : ℕ) :
    Ring.choose α n = (∏ j ∈ range n, (α - j)) / n.factorial := by
  rw [Ring.choose_eq_smul, descPochhammer_smeval_prod, smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem iterated_cpow (α : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t : ℂ => t ^ α) z = (∏ j ∈ range n, (α - j)) * z ^ (α - n) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    have he : iteratedDeriv n (fun t : ℂ => t ^ α) =ᶠ[𝓝 z]
        (fun t => (∏ j ∈ range n, (α - j)) * t ^ (α - n)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with t ht
      exact ih ht
    rw [iteratedDeriv_succ, he.deriv_eq]
    have hh : deriv (fun t : ℂ => (∏ j ∈ range n, (α - j)) * t ^ (α - n)) z =
        (∏ j ∈ range n, (α - j)) * ((α - n) * z ^ (α - n - 1)) := by
      simpa using (((hasDerivAt_id z).cpow_const (c := α - n) hz).const_mul
        (∏ j ∈ range n, (α - j))).deriv
    rw [hh, Finset.prod_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show α - (n : ℂ) - 1 = α - ((n : ℂ) + 1) by ring]
    ring

private theorem jet_mul {n : ℕ} {f g : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) :
    jet n (fun t => f t * g t) a =
      ∑ p ∈ antidiagonal n, jet p.1 f a * jet p.2 g a := by
  unfold jet
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, Finset.sum_div]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (f := fun i j => iteratedDeriv i f a / ↑i.factorial * (iteratedDeriv j g a / ↑j.factorial))]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := by simpa using hj
  have he : (n.choose j : ℂ) * (j.factorial : ℂ) * ((n - j).factorial : ℂ) =
      (n.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj'
  have hfac (t : ℕ) : (t.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
  field_simp [hfac]
  linear_combination iteratedDeriv j f a * iteratedDeriv (n - j) g a * he

private theorem padeNode_eq (j : Fin 3) : padeNode j = (nodeOffset j : ℂ) := by
  simp [padeNode, nodeOffset]

private theorem jet_numerator {m k h : ℕ} (hm : 320 ≤ m) (hk : h ≤ k) (j : Fin 3) :
    jet h (padeNumerator (m : ℝ) k) (padeNode j) =
      ((Ring.choose ((k : ℚ) + 1 / 2) h : ℚ) : ℂ) *
        ((m : ℂ) + (nodeOffset j : ℂ)) ^ (k - h) * (approximationTarget m j : ℂ) := by
  have hm' : (320 : ℝ) ≤ m := by exact_mod_cast hm
  have hj : (0 : ℝ) ≤ j.val := by positivity
  have ha : 0 < (m : ℝ) + ((j.val : ℝ) - 1) := by linarith
  have hp : padeNode j + (m : ℂ) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    left
    simpa [padeNode, add_comm] using ha
  have hp0 := (mem_slitPlane_iff_arg.mp hp).2
  unfold jet padeNumerator
  change iteratedDeriv h (fun z => (↑(√(m : ℝ)) : ℂ)⁻¹ •
    (fun t : ℂ => t ^ (↑((k : ℝ) + 1 / 2) : ℂ)) (z + (m : ℂ))) (padeNode j) / _ = _
  rw [iteratedDeriv_fun_const_smul_field,
    iteratedDeriv_comp_add_const (f := fun t : ℂ => t ^ (↑((k : ℝ) + 1 / 2) : ℂ))]
  dsimp only
  rw [iterated_cpow _ _ hp]
  simp only [smul_eq_mul]
  have hchoice :
      ((Ring.choose ((k : ℚ) + 1 / 2) h : ℚ) : ℂ) =
        (∏ a ∈ range h, ((((k : ℝ) + 1 / 2 : ℝ) : ℂ) - (a : ℂ))) / h.factorial := by
    rw [← binomial_product (↑((k : ℝ) + 1 / 2) : ℂ) h]
    have he := Ring.map_choose (Rat.castHom ℂ) ((k : ℚ) + 1 / 2) h
    change ((Ring.choose ((k : ℚ) + 1 / 2) h : ℚ) : ℂ) =
      Ring.choose (↑((k : ℚ) + 1 / 2) : ℂ) h at he
    push_cast at he ⊢
    exact he
  rw [hchoice]
  have ha0 : (padeNode j + (m : ℂ)) ≠ 0 := hp0
  have hexp : (↑((k : ℝ) + 1 / 2) : ℂ) - h = ((k - h : ℕ) : ℂ) + ((1 / 2 : ℝ) : ℂ) := by
    push_cast [Nat.cast_sub hk]
    ring
  rw [hexp, cpow_add _ _ ha0, cpow_natCast]
  have hs : (padeNode j + (m : ℂ)) ^ ((1 / 2 : ℝ) : ℂ) =
      (↑(√((m : ℝ) + ((j.val : ℝ) - 1))) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]
    congr 1
    push_cast
    simp [padeNode, add_comm]
  rw [hs, padeNode_eq, approximationTarget]
  push_cast
  ring

private theorem jet_reciprocal (j l : Fin 3) (hl : j ≠ l) (p n : ℕ) :
    jet n (fun z => (z - padeNode l) ^ (-(p : ℤ))) (padeNode j) =
      (Ring.choose (-(p : ℤ)) n * gapSign j l (p + n) : ℤ) /
        (2 : ℂ) ^ gapExponent j l (p + n) := by
  have hEq := iteratedDerivWithin_zpow (𝕜 := ℂ) (s := univ) (-(p : ℤ)) n isOpen_univ
    (Set.mem_univ (padeNode j - padeNode l))
  rw [iteratedDerivWithin_univ] at hEq
  unfold jet
  rw [iteratedDeriv_comp_sub_const (f := fun t : ℂ => t ^ (-(p : ℤ)))]
  dsimp only
  rw [hEq]
  dsimp only
  have hnum : (∏ j' ∈ range n, (-(p : ℂ) - (j' : ℂ))) / n.factorial =
      (Ring.choose (-(p : ℤ)) n : ℤ) := by
    rw [← binomial_product]
    simpa using (Ring.map_choose (Int.castRingHom ℂ) (-(p : ℤ)) n).symm
  push_cast at hnum ⊢
  rw [← div_mul_eq_mul_div, hnum, mul_div_assoc]
  congr 1
  rw [show -(p : ℤ) - n = -((p + n : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  have hs : (((-1 : ℂ) ^ (p + n))⁻¹) = (-1) ^ (p + n) := by
    rw [← inv_pow]
    simp
  have ht : (((-2 : ℂ) ^ (p + n))⁻¹) = (-1) ^ (p + n) / 2 ^ (p + n) := by
    rw [show (-2 : ℂ) = (-1) * 2 by ring, mul_pow, mul_inv_rev, hs, div_eq_mul_inv, mul_comm]
  fin_cases j <;> fin_cases l <;>
    (first | exact (hl rfl).elim | norm_num [padeNode, nodeOffset, gapExponent, gapSign]) <;>
    first | exact hs | exact ht

private theorem padeNumerator_diff {m : ℝ} {s : Set ℂ} (k : ℕ)
    (hs : ∀ z ∈ s, 0 < (z + (m : ℂ)).re) : DifferentiableOn ℂ (padeNumerator m k) s := by
  have h : Differentiable ℂ (fun z : ℂ => z + (m : ℂ)) := by fun_prop
  exact (h.differentiableOn.cpow_const (fun z hz => mem_slitPlane_iff.mpr (Or.inl (hs z hz)))).const_mul _

private theorem small_avoids {j l : Fin 3} (h : l ≠ j) :
    padeNode l ∉ closedBall (padeNode j) (1 / 2) := by
  intro hj
  have hd : ‖padeNode l - padeNode j‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hj
  linarith [node_dist h]

private theorem small_diff {m : ℝ} (hm : 320 ≤ m) (k : ℕ) (j : Fin 3) :
    DifferentiableOn ℂ (padeNumerator m k) (closedBall (padeNode j) (1 / 2)) := by
  apply padeNumerator_diff
  intro z hz
  have hd : ‖z - padeNode j‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hz
  have hn := norm_node j
  have hh := abs_re_le_norm (z - padeNode j)
  have hj := abs_re_le_norm (padeNode j)
  simp only [sub_re, add_re, ofReal_re] at hh ⊢
  linarith [neg_abs_le (z.re - (padeNode j).re), neg_abs_le (padeNode j).re]

private theorem poleOrder_pos {k : ℕ} (hk : 0 < k) (i j : Fin 3) :
    0 < poleOrder k i j := by unfold poleOrder; omega

private theorem padeKernel_eq (m : ℝ) (k : ℕ) (i : Fin 3) (z : ℂ) :
    padeKernel m k i z = padeNumerator m k z / ∏ j : Fin 3, (z - padeNode j) ^ poleOrder k i j := by
  unfold padeKernel
  congr 1
  fin_cases i <;> simp [Fin.prod_univ_succ, poleOrder, pow_succ] <;> ring

private theorem rotated_prod (f : Fin 3 → ℂ) (j : Fin 3) :
    (∏ l, f l) = f j * (f (j + 1) * f (j + 2)) := by
  fin_cases j <;> simp [Fin.prod_univ_succ, Fin.add_def] <;> ring

/-- The residue at a node is the corresponding matrix coefficient times its square root. -/
theorem pade_inner_eq {m k : ℕ} (hm : 320 ≤ m) (hk : 0 < k) (i j : Fin 3) :
    padeIntegral (m : ℝ) k i (padeNode j) (1 / 2) =
      (padeCoefficient m k i j : ℂ) * (approximationTarget m j : ℂ) := by
  let e : Fin 3 → ℕ := poleOrder k i
  let n := e j - 1
  let F := padeNumerator (m : ℝ) k
  let G (l : Fin 3) (z : ℂ) := (z - padeNode l) ^ (-(e l : ℤ))
  let H (z : ℂ) := F z * (G (j + 1) z * G (j + 2) z)
  have hj₁ : j + 1 ≠ j := by fin_cases j <;> decide
  have hj₂ : j + 2 ≠ j := by fin_cases j <;> decide
  have hR : (0 : ℝ) < 1 / 2 := by norm_num
  have hj : padeNode j ∈ ball (padeNode j) (1 / 2) := mem_ball_self hR
  have hdF := small_diff (show (320 : ℝ) ≤ m by exact_mod_cast hm) k j
  have hdG {l : Fin 3} (hl : l ≠ j) :
      DifferentiableOn ℂ (G l) (closedBall (padeNode j) (1 / 2)) := by
    have hd : Differentiable ℂ (fun z : ℂ => z - padeNode l) := by fun_prop
    exact hd.differentiableOn.zpow (Or.inl fun z hz h => small_avoids hl ((sub_eq_zero.mp h) ▸ hz))
  have hdH : DifferentiableOn ℂ H (closedBall (padeNode j) (1 / 2)) :=
    hdF.mul ((hdG hj₁).mul (hdG hj₂))
  have haF : AnalyticAt ℂ F (padeNode j) :=
    ((hdF.mono ball_subset_closedBall).analyticOnNhd isOpen_ball) _ hj
  have haG {l : Fin 3} (hl : l ≠ j) : AnalyticAt ℂ (G l) (padeNode j) :=
    (((hdG hl).mono ball_subset_closedBall).analyticOnNhd isOpen_ball) _ hj
  have hmoment : padeIntegral (m : ℝ) k i (padeNode j) (1 / 2) = jet n H (padeNode j) := by
    have he : -(n : ℤ) - 1 = -(e j : ℤ) := by
      have hp := poleOrder_pos hk i j
      change 0 < e j at hp
      dsimp [n]
      omega
    unfold padeIntegral
    have hI : (∮ z in C(padeNode j, 1 / 2), padeKernel (m : ℝ) k i z) =
        cauchyMoment H (padeNode j) (1 / 2) n (padeNode j) := by
      unfold cauchyMoment
      apply circleIntegral.integral_congr hR.le
      intro z _
      rw [padeKernel_eq, rotated_prod _ j, he]
      simp only [smul_eq_mul, H, G, zpow_neg, zpow_natCast, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hI, cauchyMoment_eq hR ((hdH.mono closure_ball_subset_closedBall).diffContOnCl) hj]
    unfold jet
    simp only [smul_eq_mul]
    field_simp [Complex.two_pi_I_ne_zero]
  rw [hmoment]
  change jet n (fun z => F z * (G (j + 1) z * G (j + 2) z)) (padeNode j) = _
  have haPair : AnalyticAt ℂ (fun z => G (j + 1) z * G (j + 2) z) (padeNode j) :=
    (haG hj₁).mul (haG hj₂)
  rw [jet_mul haF haPair]
  simp_rw [jet_mul (haG hj₁) (haG hj₂), Finset.mul_sum]
  unfold padeCoefficient
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hu' := Finset.mem_antidiagonal.mp hu
  have hu₁ : u.1 ≤ k := by
    change u.1 + u.2 = poleOrder k i j - 1 at hu'
    unfold poleOrder at hu'
    split at hu' <;> omega
  change jet u.1 (padeNumerator (m : ℝ) k) (padeNode j) *
    (jet v.1 (G (j + 1)) (padeNode j) * jet v.2 (G (j + 2)) (padeNode j)) = _
  rw [jet_numerator hm hu₁, jet_reciprocal j _ (Ne.symm hj₁), jet_reciprocal j _ (Ne.symm hj₂)]
  simp only [padeTerm, polePairNumerator, polePairDenom, e, pow_add]
  push_cast
  ring

/-- Splitting the large circle reads off the complete linear form. -/
theorem pade_outer_eq {m k : ℕ} (hm : 320 ≤ m) (hk : 0 < k) (i : Fin 3) :
    padeIntegral (m : ℝ) k i (2 * (m : ℂ)) (3 * (m : ℝ) - 1) =
      ∑ j : Fin 3, (padeCoefficient m k i j : ℂ) * (approximationTarget m j : ℂ) := by
  have hm' : (320 : ℝ) ≤ m := by exact_mod_cast hm
  have hR : (0 : ℝ) < 3 * (m : ℝ) - 1 := by linarith
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have hinj : Function.Injective padeNode := by
    intro j l h
    by_contra hn
    have hd := node_dist hn
    rw [h, sub_self, norm_zero] at hd
    norm_num at hd
  have hout : DifferentiableOn ℂ (padeNumerator (m : ℝ) k)
      (closedBall (2 * (m : ℂ)) (3 * (m : ℝ) - 1)) := by
    apply padeNumerator_diff
    intro z hz
    have hd : ‖z - 2 * (m : ℂ)‖ ≤ 3 * (m : ℝ) - 1 := by simpa [dist_eq_norm] using hz
    have hh := abs_re_le_norm (z - 2 * (m : ℂ))
    have he : ((2 : ℂ) * (m : ℂ)).re = 2 * (m : ℝ) := by simp [mul_re]
    simp only [sub_re, add_re, ofReal_re, he] at hh ⊢
    linarith [neg_abs_le (z.re - 2 * (m : ℝ))]
  have hin (j : Fin 3) : padeNode j ∈ ball (2 * (m : ℂ)) (3 * (m : ℝ) - 1) := by
    have he : ‖2 * (m : ℂ)‖ = 2 * (m : ℝ) := by rw [norm_mul, norm_ofNat, Complex.norm_natCast]
    rw [mem_ball, dist_eq_norm]
    linarith [norm_sub_le (padeNode j) (2 * (m : ℂ)), norm_node j]
  have he := split_circle_quotient padeNode hinj (poleOrder k i) (padeNumerator (m : ℝ) k)
    hR hr hout hin (small_diff hm' k) (fun _ _ => small_avoids)
  simp_rw [← pade_inner_eq hm hk i, padeIntegral, padeKernel_eq]
  rw [he, Finset.smul_sum]

end ThreeFactorials
