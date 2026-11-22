module

public import NajmanTrbovic.QuadraticFields

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-! Quotient-ring criteria for the decomposition of primes in the quadratic fields. -/

@[expose] public section

noncomputable section

namespace NajmanTrbovic

open QuadraticAlgebra

abbrev ReducedOrder (D : ℤ) (p : ℕ) :=
  QuadraticAlgebra (ZMod p) (orderA D : ZMod p) (orderB D : ZMod p)

def orderReduction (D : ℤ) (p : ℕ) : QuadraticOrder D →+* ReducedOrder D p :=
  QuadraticAlgebra.mapRingHom (Int.castRingHom (ZMod p)) (orderA D) (orderB D)

theorem reduction_kernel (D : ℤ) (p : ℕ) :
    RingHom.ker (orderReduction D p) = Ideal.span ({(p : QuadraticOrder D)} : Set _) := by
  ext z
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hz
    have hz₁ : (z.re : ZMod p) = 0 := congrArg QuadraticAlgebra.re hz
    have hz₂ : (z.im : ZMod p) = 0 := congrArg QuadraticAlgebra.im hz
    obtain ⟨v, hv⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz₁
    obtain ⟨w, hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz₂
    use (⟨v,w⟩ : QuadraticOrder D)
    ext
    · simpa using hv
    · simpa using hw
  · rintro ⟨v, rfl⟩
    rw [map_mul, map_natCast]
    have hz : (p : ReducedOrder D p) = 0 := by
      ext <;> simp
    rw [hz, zero_mul]

theorem reduction_surjective (D : ℤ) (p : ℕ) : Function.Surjective (orderReduction D p) :=
  QuadraticAlgebra.mapRingHom_surjective _ _ _ ZMod.intCast_surjective

def ResidueRing (D : ℤ) [Fact (Squarefree D)] [Fact (D ≠ 1)] (p : ℕ) :=
  NumberField.RingOfIntegers (QuadraticField D) ⧸ Ideal.span
    ({(p : NumberField.RingOfIntegers (QuadraticField D))} : Set _)

instance (D : ℤ) [Fact (Squarefree D)] [Fact (D ≠ 1)] (p : ℕ) : CommRing (ResidueRing D p) := by
  unfold ResidueRing
  infer_instance

/-- Splitting in the quadratic extension, expressed by the product residue ring. -/
def SplitsAt (D : ℤ) [Fact (Squarefree D)] [Fact (D ≠ 1)] (p : ℕ) : Prop :=
  Nonempty (ResidueRing D p ≃+* (ZMod p × ZMod p))

/-- Inertia in the quadratic extension, expressed by primality of the extended ideal. -/
def InertAt (D : ℤ) [Fact (Squarefree D)] [Fact (D ≠ 1)] (p : ℕ) : Prop :=
  IsDomain (ResidueRing D p)

def residueRingEquiv (D : ℤ) [Fact (Squarefree D)] [Fact (D ≠ 1)] (p : ℕ) :
    ResidueRing D p ≃+* ReducedOrder D p := by
  let : IsIntegralClosure (QuadraticOrder D) ℤ (QuadraticField D) :=
    quadraticOrder_isIntegralClosure D Fact.out
  let f := (IsIntegralClosure.equiv ℤ (QuadraticOrder D) (QuadraticField D)
    (NumberField.RingOfIntegers (QuadraticField D))).symm.toRingEquiv
  let I := (Ideal.span ({(p : QuadraticOrder D)} : Set _))
  let J := (Ideal.span ({(p : NumberField.RingOfIntegers (QuadraticField D))} : Set _))
  have hI : I = J.map f.toRingHom := by simp [I, J, Ideal.map_span]
  refine (Ideal.quotientEquiv J I f hI).trans ?_
  exact (show RingHom.ker (orderReduction D p) = I from reduction_kernel D p) ▸
    (orderReduction D p).quotientKerEquivOfSurjective (reduction_surjective D p)

private def pairEval {F : Type*} [Field F] {a b x y : F}
    (hx : x*x = a+b*x) (hy : y*y = a+b*y) :
    QuadraticAlgebra F a b →ₐ[F] F × F :=
  QuadraticAlgebra.lift ⟨(x,y), Prod.ext (by simpa [smul_eq_mul] using hx)
    (by simpa [smul_eq_mul] using hy)⟩

private theorem pairEval_apply {F : Type*} [Field F] {a b x y : F}
    (hx : x*x = a+b*x) (hy : y*y = a+b*y) (z : QuadraticAlgebra F a b) :
    pairEval hx hy z = (z.re+z.im*x,z.re+z.im*y) := by
  ext <;> simp [pairEval, QuadraticAlgebra.lift, smul_eq_mul]

private def splitQuadraticAlgebra {F : Type*} [Field F] {a b x y : F}
    (hx : x*x = a+b*x) (hy : y*y = a+b*y) (hxy : x ≠ y) :
    QuadraticAlgebra F a b ≃+* (F × F) := by
  apply RingEquiv.ofBijective (pairEval hx hy).toRingHom
  constructor
  · intro z w h
    change pairEval hx hy z = pairEval hx hy w at h
    rw [pairEval_apply, pairEval_apply] at h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    dsimp only at h₁ h₂
    have h₃ : (z.im-w.im)*(x-y)=0 := by linear_combination h₁-h₂
    have him := sub_eq_zero.mp ((mul_eq_zero.mp h₃).resolve_right (sub_ne_zero.mpr hxy))
    rw [him, add_left_inj] at h₁
    exact QuadraticAlgebra.ext h₁ him
  · rintro ⟨v,w⟩
    let s := (v-w)/(x-y)
    refine ⟨⟨v-s*x,s⟩, ?_⟩
    change pairEval hx hy ⟨v-s*x,s⟩ = (v,w)
    rw [pairEval_apply]
    apply Prod.ext
    · simp
    · dsimp [s]
      field_simp [sub_ne_zero.mpr hxy]
      ring

private theorem quad_roots_of_discr {F : Type*} [Field F] {a b t : F} (h₂ : (2 : F) ≠ 0)
    (ht : t^2 = QuadraticAlgebra.discr a b) :
    ((b+t)/2)*((b+t)/2) = a + b*((b+t)/2) ∧
    ((b-t)/2)*((b-t)/2) = a + b*((b-t)/2) := by
  rw [QuadraticAlgebra.discr_def] at ht
  constructor <;> field_simp <;> linear_combination ht

private theorem cast_disc (D : ℤ) (p : ℕ) :
    QuadraticAlgebra.discr (orderA D : ZMod p) (orderB D : ZMod p) =
      (quadraticDiscriminant D : ZMod p) := by
  rw [QuadraticAlgebra.discr_intCast, order_discriminant]

private theorem two_ne_zero {p : ℕ} (hp : p.Prime) (h₂ : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  change ((2 : ℕ) : ZMod p) ≠ 0
  intro hz
  exact h₂ ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp hz))

theorem splits_odd_of_residue {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)] {p : ℕ}
    (hp : p.Prime) (h₂ : p ≠ 2) (h₀ : (D : ZMod p) ≠ 0) (hs : IsSquare (D : ZMod p)) :
    SplitsAt D p := by
  let : Fact p.Prime := ⟨hp⟩
  have h2 := two_ne_zero hp h₂
  let b := (orderB D : ZMod p)
  obtain ⟨y, hy⟩ := hs
  have hy₀ : y ≠ 0 := by rintro rfl; simp at hy; exact h₀ hy
  have ht : ∃ t : ZMod p, t ≠ 0 ∧ t^2 = QuadraticAlgebra.discr (orderA D : ZMod p) b := by
    change ∃ t : ZMod p, t ≠ 0 ∧ t^2 = QuadraticAlgebra.discr (orderA D : ZMod p) (orderB D : ZMod p)
    rw [cast_disc, quadraticDiscriminant]
    split
    · exact ⟨y, hy₀, by rw [pow_two, hy]⟩
    · refine ⟨2*y, mul_ne_zero h2 hy₀, ?_⟩
      push_cast
      linear_combination -4*hy
  obtain ⟨t, ht₀, ht⟩ := ht
  obtain ⟨hR, hS⟩ := quad_roots_of_discr h2 ht
  have hRS : (b+t)/2 ≠ (b-t)/2 := by
    intro h
    field_simp at h
    exact ht₀ ((mul_eq_zero.mp (show (2 : ZMod p)*t=0 by linear_combination h)).resolve_left h2)
  exact ⟨(residueRingEquiv D p).trans (splitQuadraticAlgebra hR hS hRS)⟩

theorem splits_two_of_residue {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)] (h : D%8=1) :
    SplitsAt D 2 := by
  have h4 : D%4=1 := by omega
  have ha : (orderA D : ZMod 2) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr
    rw [orderA, ite_eq_left h4]
    omega
  have hb : (orderB D : ZMod 2) = 1 := by simp [orderB, h4]
  refine ⟨(residueRingEquiv D 2).trans (splitQuadraticAlgebra (x := 0) (y := 1) ?_ ?_ zero_ne_one)⟩
  · simp [ha, hb]
  · simp [ha, hb]

theorem not_inert_of_split {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)] {p : ℕ}
    (hp : p.Prime) (h : SplitsAt D p) : ¬ InertAt D p := by
  obtain ⟨e⟩ := h
  let : Fact p.Prime := ⟨hp⟩
  intro hi
  have hDom : IsDomain (ZMod p × ZMod p) := e.toMulEquiv.isDomain_iff.mp hi
  let : IsDomain (ZMod p × ZMod p) := hDom
  have h₁ : ((1,0) : ZMod p × ZMod p) ≠ 0 := by simp
  have h₂ : ((0,1) : ZMod p × ZMod p) ≠ 0 := by simp
  exact (mul_ne_zero h₁ h₂) (by simp [Prod.mul_def])

private theorem not_inert_of_repeated_root {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    {p : ℕ} [Fact p.Prime] (x : ZMod p) (hA : (orderA D : ZMod p) = -(x*x))
    (hB : (orderB D : ZMod p) = 2*x) : ¬ InertAt D p := by
  intro hi
  let : IsDomain (ReducedOrder D p) := (residueRingEquiv D p).toMulEquiv.isDomain_iff.mp hi
  let z : ReducedOrder D p := ⟨-x,1⟩
  have hz₀ : z ≠ 0 := by
    intro he
    exact one_ne_zero (congrArg QuadraticAlgebra.im he)
  have hz : z*z=0 := by
    ext
    · simp [z, hA]
    · simp [z, hB]
      ring
  exact (mul_ne_zero hz₀ hz₀) hz

theorem not_inert_odd_of_residue {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)] {p : ℕ}
    (hp : p.Prime) (h₂ : p ≠ 2) (hs : IsSquare (D : ZMod p)) : ¬ InertAt D p := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hz : (D : ZMod p) = 0
  · let x := (orderB D : ZMod p)/2
    have hdisc : QuadraticAlgebra.discr (orderA D : ZMod p) (orderB D : ZMod p) = 0 := by
      rw [cast_disc, quadraticDiscriminant]
      split <;> simp [hz]
    rw [QuadraticAlgebra.discr_def] at hdisc
    have h2 := two_ne_zero hp h₂
    apply not_inert_of_repeated_root x
    · dsimp [x]
      field_simp
      linear_combination hdisc
    · dsimp [x]
      field_simp
  · exact not_inert_of_split hp (splits_odd_of_residue hp h₂ hz hs)

theorem not_inert_two_of_residue {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)]
    (h : D%8=1 ∨ D%8=2 ∨ D%8=6) : ¬InertAt D 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with h | h | h
  · exact not_inert_of_split Nat.prime_two (splits_two_of_residue h)
  all_goals
    have h4 : D%4 ≠ 1 := by omega
    apply not_inert_of_repeated_root 0
    · simp only [orderA, ite_eq_right h4, mul_zero, neg_zero]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (by omega)
    · simp [orderB, h4]

end NajmanTrbovic
