module

public import NajmanTrbovic.CubicInvariantSplitting
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

import Mathlib.Tactic

/-! The multiplicative-reduction hypothesis in Proposition 3.1. -/

@[expose] public section

noncomputable section

namespace NajmanTrbovic.Cubic

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
open scoped TensorProduct

private theorem integral_norm_lt_one_iff {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) :
    ‖(a : ℚ_[p])‖ < 1 ↔ valuation ℚ_[p] (maximalIdeal ℤ_[p]) (algebraMap ℤ_[p] ℚ_[p] a) < 1 := by
  rw [PadicInt.norm_coe, PadicInt.norm_lt_one_iff_dvd, valuation_lt_one_iff_mem]
  change _ ↔ a ∈ IsLocalRing.maximalIdeal ℤ_[p]
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]

/-- The j-invariant of a p-adic elliptic curve with multiplicative reduction has norm greater
than one. The hypothesis is stated on the minimal equation supplied by mathlib. -/
theorem norm_j_gt_one_of_multiplicative_reduction {p : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve ℚ_[p]) [E.IsElliptic]
    (h : (E.minimal ℤ_[p]).HasMultiplicativeReduction ℤ_[p]) : 1 < ‖E.j‖ := by
  let W := E.minimal ℤ_[p]
  have : W.IsElliptic := by dsimp [W, WeierstrassCurve.minimal]; infer_instance
  let T := W.integralModel ℤ_[p]
  have hc : (T.c₄ : ℚ_[p]) = W.c₄ := W.integralModel_c₄_eq ℤ_[p]
  have hΔ : (T.Δ : ℚ_[p]) = W.Δ := W.integralModel_Δ_eq ℤ_[p]
  have hc₁ : ‖W.c₄‖ = 1 := by
    rw [← hc]
    refine le_antisymm (PadicInt.norm_le_one _) (le_of_not_gt fun he => ?_)
    have hv := (integral_norm_lt_one_iff T.c₄).mp he
    rw [show algebraMap ℤ_[p] ℚ_[p] T.c₄ = (T.c₄ : ℚ_[p]) from rfl, hc,
      h.multiplicativeReduction] at hv
    exact lt_irrefl _ hv
  have hd₁ : ‖W.Δ‖ < 1 := by
    rw [← hΔ, integral_norm_lt_one_iff]
    change valuation ℚ_[p] (maximalIdeal ℤ_[p]) (T.Δ : ℚ_[p]) < 1
    rw [hΔ]
    exact h.badReduction
  have hj : W.j = E.j := WeierstrassCurve.variableChange_j E _
  rw [← hj, WeierstrassCurve.j_eq, norm_mul, norm_inv, norm_pow, hc₁, one_pow, mul_one]
  exact (one_lt_inv₀ (norm_pos_iff.mpr W.isUnit_Δ.ne_zero)).mpr hd₁

/-- Proposition 3.1 with the explicit cubic-fiber parametrization supplied as a hypothesis. -/
theorem cubic_tensor_splits_of_multiplicative_reduction {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] (hK : Module.finrank ℚ K = 3)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (x : ℚ) [(descended x).IsElliptic]
    (hd : denominator x ≠ 0) (hE : E.j = (descended x).j) (α : K)
    (hα : α ∉ Set.range (algebraMap ℚ K))
    (hF : (finiteChart x 1).aeval α = 0) (hp : p = 2 ∨ p % 7 = 1 ∨ p % 7 = 6)
    (h : ((E.map (algebraMap ℚ ℚ_[p])).minimal ℤ_[p]).HasMultiplicativeReduction ℤ_[p]) :
    Nonempty ((ℚ_[p] ⊗[ℚ] K) ≃ₐ[ℚ_[p]] (Fin 3 → ℚ_[p])) := by
  apply cubic_tensor_splits_of_nonintegral_j hK x hd α hα hF hp
  have hj := norm_j_gt_one_of_multiplicative_reduction (E.map (algebraMap ℚ ℚ_[p])) h
  rw [WeierstrassCurve.map_j, hE] at hj
  exact hj

end NajmanTrbovic.Cubic
