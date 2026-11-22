module

public import NajmanTrbovic.CubicIntegralSplitting
public import NajmanTrbovic.CubicMarkedCertificate
public import NajmanTrbovic.CubicProjection
public import NajmanTrbovic.TorsionToMarked

import Mathlib.Tactic
import Mathlib.Algebra.Order.Ring.InjSurj

/-! The equality of j-invariants identifies the marked model used in Section 3
with the descended j-map. This applies to either projection from the affine equation. -/

@[expose] public section

noncomputable section

namespace NajmanTrbovic.Cubic

open scoped NumberField BigOperators

theorem marked_j_eq_descended {F : Type*} [Field F] [CharZero F] (u v : F)
    [(markedCurve u v).IsElliptic] [(descended u).IsElliptic]
    (hf : fibre u 1 v 1 = 0) (hd : denominator u ≠ 0) (hj : jDenominator u ≠ 0) :
    (markedCurve u v).j = (descended u).j := by
  obtain ⟨hm, hdisc⟩ := marked_j u v
  rw [hm, descended_j u hd hj]
  exact (div_eq_div_iff hdisc hj).mpr (marked_j_cross_multiplication u v hf)

theorem marked_j_eq_descended_of_ordered {F : Type*} [Field F] [CharZero F]
    [LinearOrder F] [IsStrictOrderedRing F] (u v : F) [(markedCurve u v).IsElliptic]
    (hf : fibre u 1 v 1 = 0) :
    ∃ _h : (descended u).IsElliptic, (markedCurve u v).j = (descended u).j := by
  have hd := denominator_ne_zero_of_ordered u
  have hj : jDenominator u ≠ 0 := by
    intro hz
    have he := marked_j_cross_multiplication u v hf
    rw [hz, mul_zero] at he
    exact (mul_ne_zero (mul_ne_zero hd (pow_ne_zero _ (g12_ne_zero_of_ordered u)))
      (marked_j u v).2) he.symm
  have hE : (descended u).IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff, (descended_invariants u hd).2]
    exact (div_ne_zero hj (pow_ne_zero _ hd)).isUnit
  exact ⟨hE, marked_j_eq_descended u v hf hd hj⟩

private theorem j_congr {F : Type*} [Field F] {A B : WeierstrassCurve F}
    [A.IsElliptic] [B.IsElliptic] (h : A = B) : A.j = B.j := by
  subst B
  rfl

theorem marked_fiber_j {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (x : ℚ) (v : K)
    (hv : v ∉ Set.range (algebraMap ℚ K)) (hf : fibre (algebraMap ℚ K x) 1 v 1 = 0)
    (C : WeierstrassCurve.VariableChange K)
    (hC : C • E.map (algebraMap ℚ K) = markedCurve (algebraMap ℚ K x) v) :
    ∃ _hE : (descended x).IsElliptic, E.j = (descended x).j := by
  let f : ℚ →+* K := algebraMap ℚ K
  have hpx : x*(x+1) ≠ 0 := rational_coordinate_ne_pole x v hv hf
  let hEll := descended_isElliptic_of_rational x hpx
  refine ⟨hEll, ?_⟩
  have hmark : (markedCurve (f x) v).IsElliptic := by rw [← hC]; infer_instance
  have hdesc : (descended (f x)).IsElliptic := by rw [← descended_map f]; infer_instance
  have hden : denominator (f x) ≠ 0 := by
    have hd : f (denominator x) ≠ 0 := (_root_.map_ne_zero f).mpr (denominator_ne_zero_on_rationals x)
    simpa only [denominator, g2, g6, map_mul, map_pow, map_add, map_one, map_ofNat] using hd
  have hjden : jDenominator (f x) ≠ 0 := by
    have hd : f (jDenominator x) ≠ 0 := (_root_.map_ne_zero f).mpr (jDenominator_ne_zero_on_rationals x hpx)
    simpa only [jDenominator, r, map_mul, map_pow, map_add, map_sub, map_one, map_ofNat] using hd
  apply f.injective
  calc
    f E.j = (E.map f).j := (E.map_j f).symm
    _ = (C • E.map f).j := (WeierstrassCurve.variableChange_j (E.map f) C).symm
    _ = (markedCurve (f x) v).j := j_congr hC
    _ = (descended (f x)).j := marked_j_eq_descended (f x) v hf hden hjden
    _ = ((descended x).map f).j := j_congr (descended_map f x).symm
    _ = f (descended x).j := (descended x).map_j f

/-- The explicit point of the marked model supplies the hypotheses of the splitting proof.
The displayed Weierstrass change relates the input elliptic curve to the marked model. -/
theorem cubic_prime_splits_of_marked_fiber {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 3) {p : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (x : ℚ) (v : K)
    (hv : v ∉ Set.range (algebraMap ℚ K)) (hf : fibre (algebraMap ℚ K x) 1 v 1 = 0)
    (C : WeierstrassCurve.VariableChange K)
    (hC : C • E.map (algebraMap ℚ K) = markedCurve (algebraMap ℚ K x) v)
    (hp : p = 2 ∨ p % 7 = 1 ∨ p % 7 = 6)
    (h : ((E.map (algebraMap ℚ ℚ_[p])).minimal ℤ_[p]).HasMultiplicativeReduction ℤ_[p]) :
    ∃ P : Fin 3 → Ideal (𝓞 K), Function.Injective P ∧ (∏ i, P i) = Ideal.span {(p : 𝓞 K)} ∧
      ∀ i, (P i).IsPrime ∧ Nonempty (((𝓞 K) ⧸ P i) ≃+* ZMod p) := by
  obtain ⟨hEll, he⟩ := marked_fiber_j E x v hv hf C hC
  have hF : (finiteChart x 1).aeval v = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, map_finite, map_one, finite_eval]
    exact hf
  exact cubic_prime_splits_of_multiplicative_reduction hK E x
    (denominator_ne_zero_on_rationals x) he v hv hF hp h

/-- The actual torsion hypothesis supplies the explicit affine model and equality
of the descended j-invariants over the cubic field, for both coordinates. -/
theorem cubic_torsion_group_has_descended_j {K : Type*} [Field K] [NumberField K] [DecidableEq K]
    (hK : Module.finrank ℚ K = 3) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hT : Nonempty ((AddCommGroup.torsion (E.map (algebraMap ℚ K)).toAffine.Point) ≃+
      (ZMod 2 × ZMod 14))) :
    ∃ (u v : K) (C : WeierstrassCurve.VariableChange K)
        (_hu : (descended u).IsElliptic) (_hv : (descended v).IsElliptic),
      fibre u 1 v 1 = 0 ∧ C • E.map (algebraMap ℚ K) = markedCurve u v ∧
      algebraMap ℚ K E.j = (descended u).j ∧ algebraMap ℚ K E.j = (descended v).j := by
  obtain ⟨u,v,C,hf,hC⟩ := cubic_torsion_group_has_marked_model hK E hT
  obtain ⟨f⟩ := cubic_has_real_embedding hK
  let : LinearOrder K := LinearOrder.lift' f f.injective
  let : IsStrictOrderedRing K := Function.Injective.isStrictOrderedRing f (map_zero f) (map_one f)
    (map_add f) (map_mul f) (by intros; rfl) (by intros; rfl)
  let Eₖ := E.map (algebraMap ℚ K)
  have hmark : (markedCurve u v).IsElliptic := by rw [← hC]; infer_instance
  have hmark' : (markedCurve v u).IsElliptic := by rw [← markedCurve_swap u v]; exact hmark
  obtain ⟨hu,hju⟩ := marked_j_eq_descended_of_ordered u v hf
  obtain ⟨hv,hjv⟩ := marked_j_eq_descended_of_ordered v u ((fibre_swap u 1 v 1).symm ▸ hf)
  have hJ : algebraMap ℚ K E.j = (markedCurve u v).j := by
    calc
      _ = Eₖ.j := (E.map_j _).symm
      _ = (C • Eₖ).j := (WeierstrassCurve.variableChange_j Eₖ C).symm
      _ = _ := j_congr hC
  exact ⟨u,v,C,hu,hv,hf,hC,hJ.trans hju,(hJ.trans (j_congr (markedCurve_swap u v))).trans hjv⟩

/-- Proposition 3.1 reduces to the arithmetic assertion that the marked affine
point has one rational and one nonrational coordinate. -/
theorem cubic_prime_splits_of_torsion_and_rational_projection
    {K : Type*} [Field K] [NumberField K] [DecidableEq K]
    (hK : Module.finrank ℚ K = 3) {p : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hT : Nonempty ((AddCommGroup.torsion (E.map (algebraMap ℚ K)).toAffine.Point) ≃+
      (ZMod 2 × ZMod 14)))
    (hprojection : ∀ (u v : K) (C : WeierstrassCurve.VariableChange K), fibre u 1 v 1 = 0 →
      C • E.map (algebraMap ℚ K) = markedCurve u v →
      (∃ x : ℚ, u = algebraMap ℚ K x ∧ v ∉ Set.range (algebraMap ℚ K)) ∨
      (∃ x : ℚ, v = algebraMap ℚ K x ∧ u ∉ Set.range (algebraMap ℚ K)))
    (hp : p = 2 ∨ p % 7 = 1 ∨ p % 7 = 6)
    (h : ((E.map (algebraMap ℚ ℚ_[p])).minimal ℤ_[p]).HasMultiplicativeReduction ℤ_[p]) :
    ∃ P : Fin 3 → Ideal (𝓞 K), Function.Injective P ∧ (∏ i, P i) = Ideal.span {(p : 𝓞 K)} ∧
      ∀ i, (P i).IsPrime ∧ Nonempty (((𝓞 K) ⧸ P i) ≃+* ZMod p) := by
  obtain ⟨u,v,C,hf,hC⟩ := cubic_torsion_group_has_marked_model hK E hT
  rcases hprojection u v C hf hC with ⟨x,hu,hv⟩ | ⟨x,hv,hu⟩
  · rw [hu] at hf hC
    exact cubic_prime_splits_of_marked_fiber hK E x v hv hf C hC hp h
  · rw [fibre_swap u 1 v 1, hv] at hf
    rw [markedCurve_swap u v, hv] at hC
    exact cubic_prime_splits_of_marked_fiber hK E x u hu hf C hC hp h

end NajmanTrbovic.Cubic
