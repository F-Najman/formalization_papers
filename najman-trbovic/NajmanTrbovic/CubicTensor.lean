module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! Splitting of a number field after base change, proved by interpolation. -/

@[expose] public section

noncomputable section

namespace NajmanTrbovic.Cubic

open scoped TensorProduct BigOperators
open Finset Polynomial

/-- Evaluation at a set of distinct conjugates gives a product algebra after base change. -/
theorem tensor_split_of_embeddings {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [FiniteDimensional F K] {n : ℕ}
    (hn : Module.finrank F K = n) (α : K) (emb : Fin n → K →ₐ[F] L)
    (h : Function.Injective fun i => emb i α) :
    Nonempty ((L ⊗[F] K) ≃ₐ[L] (Fin n → L)) := by
  classical
  let g (i : Fin n) : L ⊗[F] K →ₐ[L] L := (emb i).liftEquiv F L K L
  let G := AlgHom.pi g
  let z : L ⊗[F] K := 1 ⊗ₜ[F] α
  let value (i : Fin n) := emb i α
  have hZ (i : Fin n) : g i z = value i := by simp [g, z, value]
  let project (i : Fin n) : L ⊗[F] K :=
    ∏ j ∈ univ.erase i,
      (z - algebraMap L (L ⊗[F] K) (value j)) * algebraMap L (L ⊗[F] K) ((value i - value j)⁻¹)
  have hP (i k : Fin n) : g k (project i) = if k=i then 1 else 0 := by
    dsimp only [project]
    simp only [map_prod, map_mul, map_sub, AlgHom.commutes, hZ]
    by_cases he : k=i
    · subst k
      rw [ite_eq_left rfl]
      apply Finset.prod_eq_one
      intro j hj
      exact mul_inv_cancel₀ (sub_ne_zero.mpr (fun hh => (mem_erase.mp hj).1 (h hh).symm))
    · rw [ite_eq_right he]
      apply Finset.prod_eq_zero (mem_erase.mpr ⟨he, mem_univ k⟩)
      simp
  have hsurj : Function.Surjective G := by
    intro v
    refine ⟨∑ i, algebraMap L (L ⊗[F] K) (v i) * project i, ?_⟩
    funext k
    change g k (∑ i, algebraMap L (L ⊗[F] K) (v i) * project i) = v k
    simp only [map_sum, map_mul, AlgHom.commutes, hP, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact Algebra.algebraMap_self_apply _
  have hdim : Module.finrank L (L ⊗[F] K) = Module.finrank L (Fin n → L) := by
    rw [Module.finrank_baseChange, hn]
    simp
  have hinj : Function.Injective G :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := G.toLinearMap) hdim).mpr hsurj
  exact ⟨AlgEquiv.ofBijective G ⟨hinj, hsurj⟩⟩

theorem tensor_split_of_minpoly_roots {F K L : Type*} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [FiniteDimensional F K] {n : ℕ}
    (hn : Module.finrank F K = n) (α : K) (hα : IntermediateField.adjoin F {α} = ⊤)
    (ρ : Fin n → L) (hρ : Function.Injective ρ)
    (hroot : ∀ i, (minpoly F α).eval₂ (algebraMap F L) (ρ i) = 0) :
    Nonempty ((L ⊗[F] K) ≃ₐ[L] (Fin n → L)) := by
  have hi : IsIntegral F α := IsIntegral.of_finite F α
  let e : AdjoinRoot (minpoly F α) ≃ₐ[F] K := (IntermediateField.adjoinRootEquivAdjoin F hi).trans
    ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)
  have he : e (AdjoinRoot.root (minpoly F α)) = α := by
    change (↑(IntermediateField.adjoinRootEquivAdjoin F hi (AdjoinRoot.root (minpoly F α))) : K) = α
    rw [IntermediateField.adjoinRootEquivAdjoin_apply_root]
    rfl
  have hroot' (i : Fin n) : (minpoly F α).eval₂ (Algebra.ofId F L) (ρ i) = 0 := hroot i
  let emb (i : Fin n) : K →ₐ[F] L :=
    (AdjoinRoot.liftAlgHom (minpoly F α) (Algebra.ofId F L) (ρ i) (hroot' i)).comp e.symm.toAlgHom
  have hm (i : Fin n) : emb i α = ρ i := by
    have he' : e.symm α = AdjoinRoot.root (minpoly F α) := by
      apply e.injective
      rw [AlgEquiv.apply_symm_apply, he]
    dsimp [emb]
    rw [he', AdjoinRoot.liftAlgHom_root]
  exact tensor_split_of_embeddings hn α emb (fun i j hh => hρ (by simpa only [hm] using hh))

end NajmanTrbovic.Cubic
