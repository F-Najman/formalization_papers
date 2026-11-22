module

public import Mathlib.Analysis.Complex.CauchyIntegral

import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-! Circle integrals used to estimate the Padé forms. -/

@[expose] public section

noncomputable section

namespace ThreeFactorials

open Complex Metric Set Filter Finset
open scoped Topology

section Cauchy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def cauchyMoment (f : ℂ → E) (c : ℂ) (R : ℝ) (k : ℕ) (w : ℂ) : E :=
  ∮ z in C(c, R), (z - w) ^ (-(k : ℤ) - 1) • f z

/-- The Cauchy coefficient formula at an arbitrary point of the disc. -/
theorem cauchyMoment_eq {f : ℂ → E} {c w : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) (k : ℕ) :
    cauchyMoment f c R k w = (2 * (Real.pi : ℂ) * I / k.factorial) • iteratedDeriv k f w := by
  have hInt : CircleIntegrable f c R :=
    (hf.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable hR.le
  induction k generalizing w with
  | zero =>
    simpa [cauchyMoment, zpow_neg_one] using hf.circleIntegral_sub_inv_smul hw
  | succ k ih =>
    have hw' : w ∉ sphere c |R| := by
      rw [abs_of_pos hR]
      intro ha
      exact (mem_ball.mp hw).ne (mem_sphere.mp ha)
    have hd : HasDerivAt (cauchyMoment f c R k)
        (((k : ℂ) + 1) • cauchyMoment f c R (k + 1) w) w := by
      have h := hasDerivAt_circleIntegral_sub_zpow_smul (n := -(k : ℤ) - 1) hInt hw'
      have hexp : -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
      have hcoeff : -(↑(-(k : ℤ) - 1) : ℂ) = (k : ℂ) + 1 := by push_cast; ring
      change HasDerivAt (fun t => ∮ z in C(c, R), (z - t) ^ (-(k : ℤ) - 1) • f z)
        (((k : ℂ) + 1) • ∮ z in C(c, R), (z - w) ^ (-((k + 1 : ℕ) : ℤ) - 1) • f z) w
      simpa only [cauchyMoment, hexp, hcoeff] using h
    have he : cauchyMoment f c R k =ᶠ[𝓝 w]
        (fun t => (2 * (Real.pi : ℂ) * I / k.factorial) • iteratedDeriv k f t) := by
      filter_upwards [isOpen_ball.mem_nhds hw] with _ ht
      exact ih ht
    have hderiv : ((k : ℂ) + 1) • cauchyMoment f c R (k + 1) w =
        (2 * (Real.pi : ℂ) * I / k.factorial) • iteratedDeriv (k + 1) f w := by
      rw [← hd.deriv, he.deriv_eq]
      simpa only [iteratedDeriv_succ] using
        (deriv_fun_const_smul_field (x := w) (2 * (Real.pi : ℂ) * I / k.factorial) (iteratedDeriv k f))
    have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    apply smul_right_injective (M := E) hk
    dsimp only
    rw [hderiv, smul_smul]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp

omit [CompleteSpace E] in
theorem node_quotient_integral {f : ℂ → E} {c a : ℂ} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (closedBall c R)) (ha : a ∉ closedBall c R) :
    cauchyMoment f c R n a = 0 := by
  apply DiffContOnCl.circleIntegral_eq_zero hR.le
  apply DifferentiableOn.diffContOnCl
  apply DifferentiableOn.mono _ closure_ball_subset_closedBall
  have hh : ∀ z ∈ closedBall c R, z - a ≠ 0 :=
    fun z hz h => ha ((sub_eq_zero.mp h) ▸ hz)
  have hd : Differentiable ℂ (fun z : ℂ => z - a) := by fun_prop
  exact ((hd.differentiableOn.zpow (Or.inl hh)).smul hf)

end Cauchy

/-- Repeated poles can be separated into small circles using partial fractions. -/
theorem split_circle_quotient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (ha : Function.Injective a) (n : ι → ℕ) (f : ℂ → ℂ)
    {c : ℂ} {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hout : DifferentiableOn ℂ f (closedBall c R))
    (hin : ∀ i, a i ∈ ball c R)
    (hsmall : ∀ i, DifferentiableOn ℂ f (closedBall (a i) r))
    (hdisj : ∀ i j, i ≠ j → a i ∉ closedBall (a j) r) :
    (∮ z in C(c, R), f z / ∏ i, (z - a i) ^ n i) =
      ∑ i, ∮ z in C(a i, r), f z / ∏ j, (z - a j) ^ n j := by
  let g (i : ι) : Polynomial ℂ := Polynomial.X - Polynomial.C (a i)
  have hg (i : ι) : (g i).Monic := Polynomial.monic_X_sub_C _
  have hcop : Set.Pairwise (↑(univ : Finset ι)) (fun i j => IsCoprime (g i) (g j)) := by
    intro i _ j _ hij
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (ha.ne hij)))
  obtain ⟨q, b, hdegree, hp⟩ :=
    Polynomial.eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow (s := univ) (1 : Polynomial ℂ)
      (fun i _ => hg i) hcop n
  have hb (i : ι) (j : Fin (n i)) : b i j = Polynomial.C ((b i j).coeff 0) := by
    by_cases hzero : b i j = 0
    · simp [hzero]
    apply Polynomial.eq_C_of_natDegree_le_zero
    have hlt := hdegree i (mem_univ i) j
    rw [show (g i).degree = 1 from Polynomial.degree_X_sub_C _,
      Polynomial.degree_eq_natDegree hzero] at hlt
    exact Nat.lt_succ_iff.mp (by exact_mod_cast hlt)
  let H (i : ι) (j : Fin (n i)) (z : ℂ) :=
    (b i j).coeff 0 * (z - a i) ^ (-(↑(n i - (j : ℕ) - 1) : ℤ) - 1) * f z
  have hpoint (z : ℂ) (hz : ∀ i, z ≠ a i) :
      f z / ∏ i, (z - a i) ^ n i = q.eval z * f z + ∑ i, ∑ j, H i j z := by
    have hP : (∏ i, (z - a i) ^ n i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (sub_ne_zero.mpr (hz i))
    have he := congrArg (Polynomial.evalRingHom z) hp
    simp only [map_one, map_add, map_mul, map_pow, map_sum, map_prod, Polynomial.coe_evalRingHom,
      g, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at he
    have hscalar (i : ι) (j : Fin (n i)) : (b i j).eval z = (b i j).coeff 0 := by
      nth_rw 1 [hb i j]
      rw [Polynomial.eval_C]
    simp only [hscalar] at he
    have hterm (i : ι) (j : Fin (n i)) :
        (b i j).coeff 0 * (z - a i) ^ (j : ℕ) * (∏ l ∈ univ.erase i, (z - a l) ^ n l) * f z =
        H i j z * ∏ l, (z - a l) ^ n l := by
      have hj : (-(↑(n i - (j : ℕ) - 1) : ℤ)) - 1 = -((n i - j : ℕ) : ℤ) := by omega
      have hn : n i = n i - (j : ℕ) + j := (Nat.sub_add_cancel j.is_lt.le).symm
      dsimp only [H]
      rw [hj, zpow_neg, zpow_natCast,
        ← Finset.mul_prod_erase univ (fun i => (z - a i) ^ n i) (mem_univ i),
        show (z - a i) ^ n i = (z - a i) ^ (n i - j) * (z - a i) ^ (j : ℕ) by rw [← pow_add, ← hn]]
      have hNE : (z - a i) ^ (n i - (j : ℕ)) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (hz i))
      field_simp
    apply (div_eq_iff hP).2
    calc
      f z = 1 * f z := (one_mul _).symm
      _ = _ := by
        rw [he, add_mul, add_mul]
        simp only [Finset.sum_mul, hterm]
        congr 1
        ring
  have integrals {c' : ℂ} {r' : ℝ} (hr' : 0 < r')
      (hf : DifferentiableOn ℂ f (closedBall c' r')) (havoid : ∀ i, a i ∉ sphere c' r') :
      (∮ z in C(c', r'), f z / ∏ i, (z - a i) ^ n i) =
        ∑ i, ∑ j : Fin (n i), (b i j).coeff 0 * cauchyMoment f c' r' (n i - j - 1) (a i) := by
    have hqc : DifferentiableOn ℂ (fun z => q.eval z * f z) (closedBall c' r') :=
      q.differentiableOn.mul hf
    have hh (i : ι) (j : Fin (n i)) : CircleIntegrable (H i j) c' r' := by
      have hv : ∀ z ∈ sphere c' r', z - a i ≠ 0 := by
        intro z hz h
        exact havoid i ((sub_eq_zero.mp h) ▸ hz)
      have hz : Differentiable ℂ (fun z : ℂ => z - a i) := by fun_prop
      have hd := hz.differentiableOn.zpow (m := -(↑(n i - (j : ℕ) - 1) : ℤ) - 1) (Or.inl hv)
      have hb' : DifferentiableOn ℂ (fun _ : ℂ => (b i j).coeff 0) (sphere c' r') := by fun_prop
      unfold H
      exact ((hb'.mul hd).mul
        (hf.mono sphere_subset_closedBall)).continuousOn.circleIntegrable hr'.le
    calc
      _ = ∮ z in C(c', r'), q.eval z * f z + ∑ i, ∑ j, H i j z := by
        apply circleIntegral.integral_congr hr'.le
        intro z hz
        exact hpoint z (fun i hi => havoid i (hi ▸ hz))
      _ = _ := by
        rw [circleIntegral.integral_add
          ((hqc.continuousOn.mono sphere_subset_closedBall).circleIntegrable hr'.le)
          (CircleIntegrable.fun_sum _ (fun i _ => CircleIntegrable.fun_sum _ (fun j _ => hh i j)))]
        rw [(hqc.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hr'.le, zero_add]
        rw [circleIntegral.integral_fun_sum
          (fun i _ => CircleIntegrable.fun_sum _ (fun j _ => hh i j))]
        simp only [circleIntegral.integral_fun_sum (fun j _ => hh _ j)]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp [H, cauchyMoment, smul_eq_mul, mul_assoc]
  have hRavoid (i : ι) : a i ∉ sphere c R := by
    intro hi
    exact (mem_ball.mp (hin i)).ne (mem_sphere.mp hi)
  have hravoid (i j : ι) : a j ∉ sphere (a i) r := by
    by_cases hj : j = i
    · subst j
      simp [Ne.symm hr.ne']
    · exact fun h => hdisj j i hj (sphere_subset_closedBall h)
  rw [integrals hR hout hRavoid]
  simp_rw [integrals hr (hsmall _) (hravoid _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [cauchyMoment_eq hR (hout.mono closure_ball_subset_closedBall).diffContOnCl (hin i),
      cauchyMoment_eq hr ((hsmall i).mono closure_ball_subset_closedBall).diffContOnCl
        (mem_ball_self hr)]
  · intro i' _ hne
    rw [node_quotient_integral hr (hsmall i') (hdisj i i' hne.symm), mul_zero]
  · exact fun h => (h (mem_univ _)).elim

theorem outside_contour_bound {m : ℝ} (hm : 320 ≤ m) {z : ℂ}
    (hz : z ∈ sphere (2 * (m : ℂ)) (3 * m - 1)) :
    2 * (m - 2) ^ 2 * ‖z + (m : ℂ)‖ ≤ (‖z‖ - 1) ^ 3 := by
  have hnorm : ‖z - 2 * (m : ℂ)‖ = 3 * m - 1 := by
    simpa [dist_eq_norm] using (mem_sphere.mp hz)
  have habs : ‖(2 * (m : ℂ))‖ = 2 * m := by
    rw [norm_mul, norm_ofNat, norm_real, Real.norm_of_nonneg (by linarith)]
  have hzlow : m - 1 ≤ ‖z‖ := by
    linarith [norm_sub_le z (2 * (m : ℂ))]
  have hsq : ‖z + (m : ℂ)‖ ^ 2 = (3 / 2 : ℝ) * ‖z‖ ^ 2 + 3 * m ^ 2 - (3 * m - 1) ^ 2 / 2 := by
    have he := congrArg (fun t : ℝ => t ^ 2) hnorm
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, show (2 : ℂ).re = 2 by norm_num,
      show (2 : ℂ).im = 0 by norm_num] at he ⊢
    nlinarith only [he]
  let t := ‖z‖ ^ 2
  let s := (m - 2) ^ 2
  have ht : 0 ≤ t := sq_nonneg _
  have hs : 0 ≤ s := sq_nonneg _
  have h₁ : ‖z + (m : ℂ)‖ ^ 2 ≤ (3 / 2 : ℝ) * (t - s) := by
    dsimp [t, s]
    linarith only [hsq, hm]
  have h₂ : (3 / 2 : ℝ) * (t - s) * s ^ 2 ≤ (2 / 9 : ℝ) * t ^ 3 := by
    have hh := mul_nonneg (sq_nonneg (2 * t - 3 * s)) (by positivity : 0 ≤ t + 3 * s)
    linarith only [show (2 * t - 3 * s) ^ 2 * (t + 3 * s) =
      4 * t ^ 3 - 27 * t * s ^ 2 + 27 * s ^ 3 by ring, hh]
  have h₃ : (99 / 100 : ℝ) * ‖z‖ ≤ ‖z‖ - 1 := by linarith
  have h₄ : ((99 / 100 : ℝ) * ‖z‖) ^ 6 ≤ (‖z‖ - 1) ^ 6 :=
    pow_le_pow_left₀ (by positivity) h₃ 6
  have h₅ : (8 / 9 : ℝ) * t ^ 3 ≤ ((99 / 100 : ℝ) * ‖z‖) ^ 6 := by
    dsimp [t]
    rw [mul_pow, show ‖z‖ ^ 6 = (‖z‖ ^ 2) ^ 3 by ring]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  apply (sq_le_sq₀ (by positivity) (pow_nonneg (by linarith : 0 ≤ ‖z‖ - 1) _)).mp
  calc
    _ = 4 * (‖z + (m : ℂ)‖ ^ 2 * s ^ 2) := by dsimp [s]; ring
    _ ≤ 4 * ((3 / 2 : ℝ) * (t - s) * s ^ 2) := by gcongr
    _ ≤ (8 / 9 : ℝ) * t ^ 3 := by linarith only [h₂]
    _ ≤ ((99 / 100 : ℝ) * ‖z‖) ^ 6 := h₅
    _ ≤ (‖z‖ - 1) ^ 6 := h₄
    _ = _ := by ring

end ThreeFactorials
