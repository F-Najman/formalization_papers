module

public import NajmanTrbovic.MultiplicativeReduction
public import Mathlib.NumberTheory.NumberField.Basic

import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Tactic

/-! A split p-adic algebra gives a split residue algebra in the ring of integers. -/

@[expose] public section

noncomputable section

namespace NajmanTrbovic.Cubic

open Polynomial NumberField
open scoped TensorProduct BigOperators NumberField

variable {K : Type*} [Field K] [NumberField K] {p n : ℕ} [Fact p.Prime]

private abbrev SplitEquiv (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ K] (n : ℕ) :=
  (ℚ_[p] ⊗[ℚ] K) ≃ₐ[ℚ_[p]] (Fin n → ℚ_[p])

private def splitEmbedding (e : SplitEquiv p K n) : K →ₐ[ℚ] (Fin n → ℚ_[p]) :=
  (e.toAlgHom.restrictScalars ℚ).comp Algebra.TensorProduct.includeRight

private theorem charpoly_split (e : SplitEquiv p K n) (x : K) :
    (Algebra.lmul ℚ K x).charpoly.map (algebraMap ℚ ℚ_[p]) =
      ∏ i, (X - C (splitEmbedding e x i)) := by
  rw [← LinearMap.charpoly_baseChange, Algebra.baseChange_lmul]
  have hconj : e.toLinearEquiv.conj (Algebra.lmul ℚ_[p] (ℚ_[p] ⊗[ℚ] K) (1 ⊗ₜ[ℚ] x)) =
      Algebra.lmul ℚ_[p] (Fin n → ℚ_[p]) (splitEmbedding e x) := by
    apply LinearMap.ext
    intro v
    funext i
    change e ((1 ⊗ₜ[ℚ] x) * e.symm v) i = e (1 ⊗ₜ[ℚ] x) i * v i
    rw [map_mul, Pi.mul_apply, e.apply_symm_apply]
  rw [← e.toLinearEquiv.charpoly_conj, hconj,
    ← (Algebra.lmul ℚ_[p] (Fin n → ℚ_[p]) (splitEmbedding e x)).charpoly_toMatrix
      (Pi.basisFun ℚ_[p] (Fin n))]
  have hdiagonal : (Algebra.lmul ℚ_[p] (Fin n → ℚ_[p]) (splitEmbedding e x)).toMatrix
      (Pi.basisFun ℚ_[p] (Fin n)) (Pi.basisFun ℚ_[p] (Fin n)) =
      Matrix.diagonal (splitEmbedding e x) := by
    ext i j
    simp [Matrix.diagonal_apply, Pi.single_apply]
  rw [hdiagonal, Matrix.charpoly_diagonal]

private theorem charpoly_integral (y : 𝓞 K) :
    (Algebra.lmul ℚ K (y : K)).charpoly =
      (Algebra.lmul ℤ (𝓞 K) y).charpoly.map (algebraMap ℤ ℚ) := by
  classical
  rw [← (Algebra.lmul ℚ K (y : K)).charpoly_toMatrix (integralBasis K),
    ← (Algebra.lmul ℤ (𝓞 K) y).charpoly_toMatrix (RingOfIntegers.basis K), ← Matrix.charpoly_map]
  congr 1
  ext i j
  simp only [LinearMap.toMatrix_apply, integralBasis_apply, Matrix.map_apply]
  change (integralBasis K).repr
    ((algebraMap (𝓞 K) K y) * algebraMap (𝓞 K) K (RingOfIntegers.basis K j)) i = _
  rw [← map_mul, integralBasis_repr_apply]
  rfl

private theorem charpoly_natCast_mul (e : SplitEquiv p K n) (x : K) :
    ((Algebra.lmul ℚ K x).charpoly.scaleRoots (p : ℚ)) =
      (Algebra.lmul ℚ K ((p : K)*x)).charpoly := by
  apply Polynomial.map_injective (algebraMap ℚ ℚ_[p]) (algebraMap ℚ ℚ_[p]).injective
  rw [map_scaleRoots _ _ _ (by rw [(Algebra.lmul ℚ K x).charpoly_monic.leadingCoeff, map_one]; exact one_ne_zero),
    charpoly_split e x, charpoly_split e ((p : K)*x), map_natCast]
  have hprod (s : Finset (Fin n)) :
      (∏ i ∈ s, (X - C (splitEmbedding e x i))).scaleRoots (p : ℚ_[p]) =
        ∏ i ∈ s, (X - C (splitEmbedding e ((p : K)*x) i)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      simp only [Finset.prod_insert hi, mul_scaleRoots_of_noZeroDivisors, ih]
      congr 1
      rw [sub_eq_add_neg, ← C_neg, X_add_C_scaleRoots, neg_mul, C_neg, ← sub_eq_add_neg]
      simp [mul_comm]
  exact hprod Finset.univ

private theorem charpoly_of_integral_coordinates (e : SplitEquiv p K n) (x : K)
    (a : Fin n → ℤ_[p]) (ha : ∀ i, (a i : ℚ_[p]) = splitEmbedding e x i) :
    ∃ Q : ℤ_[p][X], Q.map PadicInt.Coe.ringHom =
      (Algebra.lmul ℚ K x).charpoly.map (algebraMap ℚ ℚ_[p]) := by
  refine ⟨∏ i, (X - C (a i)), ?_⟩
  rw [charpoly_split e]
  simp [Polynomial.map_prod, PadicInt.Coe.ringHom_apply, ha]

private theorem isIntegral_of_integral_coordinates (e : SplitEquiv p K n) (x : K) (y : 𝓞 K)
    (hy : (p : K)*x = (y : K)) (a : Fin n → ℤ_[p])
    (ha : ∀ i, (a i : ℚ_[p]) = splitEmbedding e x i) : IsIntegral ℤ x := by
  let P := (Algebra.lmul ℚ K x).charpoly
  let R := (Algebra.lmul ℤ (𝓞 K) y).charpoly
  obtain ⟨Q, hQ⟩ := charpoly_of_integral_coordinates e x a ha
  have hy' : P.scaleRoots (p : ℚ) = R.map (algebraMap ℤ ℚ) := by
    rw [charpoly_natCast_mul e, hy, charpoly_integral]
  have hc (i : ℕ) : P.coeff i ∈ Set.range (algebraMap ℤ ℚ) := by
    let k := P.natDegree - i
    have hq : (Q.coeff i : ℚ_[p]) = algebraMap ℚ ℚ_[p] (P.coeff i) := by
      simpa only [Polynomial.coeff_map, PadicInt.Coe.ringHom_apply] using
        congrArg (fun f : ℚ_[p][X] => f.coeff i) hQ
    have hr : P.coeff i * (p : ℚ)^k = algebraMap ℤ ℚ (R.coeff i) := by
      simpa only [coeff_scaleRoots, coeff_map] using congrArg (fun f : ℚ[X] => f.coeff i) hy'
    have hr' : (Q.coeff i : ℚ_[p]) * (p : ℚ_[p])^k = (R.coeff i : ℚ_[p]) := by
      have he := congrArg (algebraMap ℚ ℚ_[p]) hr
      change _ = (algebraMap ℚ ℚ_[p]) ((R.coeff i : ℤ) : ℚ) at he
      simpa only [map_mul, map_pow, map_natCast, map_intCast, ← hq] using he
    have hbound : ‖(R.coeff i : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
      rw [← hr', norm_mul, PadicInt.norm_coe, norm_pow, Padic.norm_p, zpow_neg, zpow_natCast, inv_pow]
      exact mul_le_of_le_one_left (by positivity) (PadicInt.norm_le_one _)
    obtain ⟨c, hc⟩ := (Padic.norm_int_le_pow_iff_dvd (p := p) (R.coeff i) k).mp hbound
    refine ⟨c, ?_⟩
    rw [hc] at hr
    simp only [map_mul, map_pow, map_natCast] at hr
    apply mul_right_cancel₀ (pow_ne_zero k (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
    simpa [mul_comm] using hr.symm
  obtain ⟨B, hB⟩ := (lifts_iff_set_range P).mp ((lifts_iff_coeff_lifts P).mpr hc)
  refine ⟨B, ?_, ?_⟩
  · apply (FaithfulSMul.algebraMap_injective ℤ ℚ).monic_map_iff.mpr
    rw [hB]
    exact (Algebra.lmul ℚ K x).charpoly_monic
  · change aeval x B = 0
    rw [← aeval_map_algebraMap ℚ, hB]
    exact Algebra.aeval_self_charpoly_lmul x

private def integralCoordinate (e : SplitEquiv p K n) (i : Fin n) : 𝓞 K →+* ℤ_[p] := by
  let f : K →ₐ[ℚ] ℚ_[p] := (Pi.evalAlgHom ℚ (fun _ : Fin n => ℚ_[p]) i).comp (splitEmbedding e)
  apply (f.toRingHom.comp (algebraMap (𝓞 K) K)).codRestrict (PadicInt.subring p)
  intro y
  have hi : IsIntegral ℤ (f (y : K)) := IsIntegral.map f y.2
  have hi' : IsIntegral ℤ_[p] (f (y : K)) := IsIntegral.tower_top hi
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi'
  change f (y : K) ∈ PadicInt.subring p
  exact ha ▸ a.2

/-- The reduction of the ring of integers modulo p is a product of prime fields if the
p-adic tensor algebra is a product of copies of the base field. -/
theorem residue_algebra_of_split_tensor (hn : Module.finrank ℚ K = n)
    (e : (ℚ_[p] ⊗[ℚ] K) ≃ₐ[ℚ_[p]] (Fin n → ℚ_[p])) :
    Nonempty (((𝓞 K) ⧸ Ideal.span {(p : 𝓞 K)}) ≃+* (Fin n → ZMod p)) := by
  classical
  let I : Ideal (𝓞 K) := Ideal.span {(p : 𝓞 K)}
  let f : 𝓞 K →+* (Fin n → ZMod p) := RingHom.pi fun i => PadicInt.toZMod.comp (integralCoordinate e i)
  have hker : RingHom.ker f = I := by
    ext y
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    constructor
    · intro hy
      let x : K := (y : K)/(p : K)
      have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
      have hx : (p : K)*x = (y : K) := by rw [mul_comm]; exact div_mul_cancel₀ _ hp
      have hred (i : Fin n) : PadicInt.toZMod (integralCoordinate e i y) = 0 := congrFun hy i
      have hdvd (i : Fin n) : (p : ℤ_[p]) ∣ integralCoordinate e i y := by
        have h := hred i
        rwa [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
          Ideal.mem_span_singleton] at h
      choose a ha using hdvd
      have hcoords (i : Fin n) : (a i : ℚ_[p]) = splitEmbedding e x i := by
        have hh := congrArg (fun t : K => splitEmbedding e t i) hx
        simp only [map_mul, map_natCast, Pi.mul_apply, Pi.natCast_apply] at hh
        apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : ℚ_[p]) ≠ 0)
        rw [hh]
        exact (congrArg (fun b : ℤ_[p] => (b : ℚ_[p])) (ha i)).symm
      refine ⟨⟨x, isIntegral_of_integral_coordinates e x y hx a hcoords⟩, ?_⟩
      apply Subtype.ext
      change (y : K) = algebraMap (𝓞 K) K (p : 𝓞 K) * x
      rw [map_natCast]
      exact hx.symm
    · rintro ⟨z, rfl⟩
      rw [map_mul, map_natCast]
      have hz : (p : Fin n → ZMod p) = 0 := funext fun i => ZMod.natCast_self p
      rw [hz, zero_mul]
  let g : (𝓞 K ⧸ I) →+* (Fin n → ZMod p) := Ideal.Quotient.lift I f fun y hy =>
    RingHom.mem_ker.mp (hker ▸ hy)
  have hi : Function.Injective g := by
    apply (injective_iff_map_eq_zero g).mpr
    intro z hz
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← hker]
    exact hz
  have hc : Nat.card (𝓞 K ⧸ I) = Nat.card (Fin n → ZMod p) := by
    have : Infinite (𝓞 K) := Module.Free.infinite ℤ _
    unfold I
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast,
      RingOfIntegers.rank, hn, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  exact ⟨RingEquiv.ofBijective g (hi.bijective_of_nat_card_le hc.ge)⟩

/-- A residue ring isomorphic to a product of fields gives the corresponding prime ideal
factorization, with each prime occurring once. -/
theorem distinct_prime_factors_of_residue_product {R F : Type*} [CommRing R] [Field F]
    (I : Ideal R) (e : (R ⧸ I) ≃+* (Fin n → F)) :
    ∃ P : Fin n → Ideal R, Function.Injective P ∧ (∏ i, P i) = I ∧
      ∀ i, (P i).IsPrime ∧ Nonempty ((R ⧸ P i) ≃+* F) := by
  classical
  let f := e.toRingHom.comp (Ideal.Quotient.mk I)
  have hf : Function.Surjective f := e.surjective.comp Ideal.Quotient.mk_surjective
  let g (i : Fin n) := (Pi.evalRingHom (fun _ : Fin n => F) i).comp f
  let P (i : Fin n) := RingHom.ker (g i)
  have hs (i : Fin n) : Function.Surjective (g i) := (Function.surjective_eval _).comp hf
  have hP : Function.Injective P := by
    intro i j he
    by_contra hij
    obtain ⟨x, hx⟩ := hf (fun k => if k = j then 1 else 0)
    have hi : x ∈ P i := RingHom.mem_ker.mpr (by change f x i = 0; simp [hx, hij])
    have hj := RingHom.mem_ker.mp (he ▸ hi)
    change f x j = 0 at hj
    simp [hx] at hj
  have hmax (i : Fin n) : (P i).IsMaximal := RingHom.ker_isMaximal_of_surjective _ (hs i)
  refine ⟨P, hP, ?_, fun i => ⟨RingHom.ker_isPrime (g i), ⟨(g i).quotientKerEquivOfSurjective (hs i)⟩⟩⟩
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime (fun i _ j _ hij => by
    have := hmax i
    have := hmax j
    exact Ideal.isCoprime_of_isMaximal (fun h => hij (hP h)))]
  simp only [Finset.mem_univ, iInf_pos]
  ext x
  rw [Ideal.mem_iInf, ← Ideal.Quotient.eq_zero_iff_mem]
  change (∀ i, f x i = 0) ↔ Ideal.Quotient.mk I x = 0
  rw [← funext_iff]
  exact ⟨fun h => e.injective (h.trans e.map_zero.symm), fun h => by
    change e (Ideal.Quotient.mk I x) = 0
    rw [h, map_zero]⟩

/-- Complete splitting in the cubic field of an explicit fiber under the hypotheses
on the prime and elliptic reduction in Proposition 3.1. -/
theorem cubic_residue_splits_of_multiplicative_reduction (hK : Module.finrank ℚ K = 3)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (x : ℚ) [(descended x).IsElliptic]
    (hd : denominator x ≠ 0) (hE : E.j = (descended x).j) (α : K)
    (hα : α ∉ Set.range (algebraMap ℚ K))
    (hF : (finiteChart x 1).aeval α = 0) (hp : p = 2 ∨ p % 7 = 1 ∨ p % 7 = 6)
    (h : ((E.map (algebraMap ℚ ℚ_[p])).minimal ℤ_[p]).HasMultiplicativeReduction ℤ_[p]) :
    Nonempty (((𝓞 K) ⧸ Ideal.span {(p : 𝓞 K)}) ≃+* (Fin 3 → ZMod p)) := by
  obtain ⟨e⟩ := cubic_tensor_splits_of_multiplicative_reduction hK E x hd hE α hα hF hp h
  exact residue_algebra_of_split_tensor hK e

/-- The explicit parametrization implies that the prime ideal `(p)` factors as three
distinct primes, each with residue field `ZMod p`. -/
theorem cubic_prime_splits_of_multiplicative_reduction (hK : Module.finrank ℚ K = 3)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (x : ℚ) [(descended x).IsElliptic]
    (hd : denominator x ≠ 0) (hE : E.j = (descended x).j) (α : K)
    (hα : α ∉ Set.range (algebraMap ℚ K))
    (hF : (finiteChart x 1).aeval α = 0) (hp : p = 2 ∨ p % 7 = 1 ∨ p % 7 = 6)
    (h : ((E.map (algebraMap ℚ ℚ_[p])).minimal ℤ_[p]).HasMultiplicativeReduction ℤ_[p]) :
    ∃ P : Fin 3 → Ideal (𝓞 K), Function.Injective P ∧ (∏ i, P i) = Ideal.span {(p : 𝓞 K)} ∧
      ∀ i, (P i).IsPrime ∧ Nonempty (((𝓞 K) ⧸ P i) ≃+* ZMod p) := by
  obtain ⟨e⟩ := cubic_residue_splits_of_multiplicative_reduction hK E x hd hE α hα hF hp h
  exact distinct_prime_factors_of_residue_product _ e

/-- For the cubic field of an explicit fiber, complete splitting at 2 holds for every
primitive rational base point away from the rational poles. -/
theorem cubic_residue_splits_at_two (hK : Module.finrank ℚ K = 3) (u w : ℤ) (hg : u.gcd w = 1)
    (hc : u*w*(u+w) ≠ 0) (α : K) (hα : α ∉ Set.range (algebraMap ℚ K))
    (hF : (finiteChart (u : ℚ) (w : ℚ)).aeval α = 0) :
    Nonempty (((𝓞 K) ⧸ Ideal.span {(2 : 𝓞 K)}) ≃+* (Fin 3 → ZMod 2)) := by
  obtain ⟨e⟩ := cubic_tensor_splits_at_two hK u w hg hc α hα hF
  exact residue_algebra_of_split_tensor hK e

end NajmanTrbovic.Cubic
