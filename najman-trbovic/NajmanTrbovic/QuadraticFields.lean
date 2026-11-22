module

public import NajmanTrbovic.AffinePoints
public import Mathlib.Algebra.QuadraticAlgebra.Int
public import Mathlib.NumberTheory.NumberField.Discriminant.Different

import Mathlib.Tactic

/-! The discriminant test as ramification in an actual quadratic number field. -/

@[expose] public section

noncomputable section

namespace NajmanTrbovic

open QuadraticAlgebra

def orderA (D : ℤ) : ℤ := if D % 4 = 1 then (D - 1) / 4 else D
def orderB (D : ℤ) : ℤ := if D % 4 = 1 then 1 else 0

abbrev QuadraticOrder (D : ℤ) := QuadraticAlgebra ℤ (orderA D) (orderB D)
abbrev QuadraticField (D : ℤ) := QuadraticAlgebra ℚ (orderA D : ℚ) (orderB D : ℚ)

theorem order_discriminant (D : ℤ) : QuadraticAlgebra.discr (orderA D) (orderB D) =
    quadraticDiscriminant D := by
  unfold orderA orderB quadraticDiscriminant
  split <;> rename_i h
  · simp [QuadraticAlgebra.discr_def]
    omega
  · simp [QuadraticAlgebra.discr_def]

theorem radicand_not_square (D : ℤ) (hd : Squarefree D) (hD : D ≠ 1) :
    ¬ IsSquare (D : ℚ) := by
  rintro ⟨q, hq⟩
  obtain ⟨e, he⟩ := exists_int_of_mul_square_eq (show Squarefree (1 : ℤ) from squarefree_one)
    (q := q) (by simpa [pow_two] using hq.symm)
  have h : D = e * e := by rw [← he] at hq; exact_mod_cast hq
  have hu : IsUnit e := hd e (h ▸ dvd_rfl)
  rcases Int.isUnit_iff.mp hu with rfl | rfl <;> exact hD (by simpa using h)

instance quadraticField (D : ℤ) [Fact (Squarefree D)] [Fact (D ≠ 1)] :
    Field (QuadraticField D) := by
  have hf : ¬IsSquare ((quadraticDiscriminant D : ℤ) : ℚ) := by
    have hn := radicand_not_square D (Fact.out : Squarefree D) (Fact.out : D ≠ 1)
    unfold quadraticDiscriminant
    split
    · exact hn
    · rintro ⟨q, hq⟩
      apply hn
      refine ⟨q / 2, ?_⟩
      push_cast at hq
      linear_combination hq / 4
  have : Fact (¬IsSquare (QuadraticAlgebra.discr (orderA D : ℚ) (orderB D : ℚ))) :=
    ⟨by rwa [QuadraticAlgebra.discr_intCast, order_discriminant]⟩
  infer_instance

instance quadraticNumberField (D : ℤ) [Fact (Squarefree D)] [Fact (D ≠ 1)] :
    NumberField (QuadraticField D) := ⟨⟩

private theorem coord_parity {D T Y : ℤ} (hd : Squarefree D) (h : (4 : ℤ) ∣ T ^ 2 - D * Y ^ 2) :
    (D % 4 = 1 → (2 : ℤ) ∣ T - Y) ∧
    (D % 4 ≠ 1 → (2 : ℤ) ∣ T ∧ (2 : ℤ) ∣ Y) := by
  let f := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)
  have htest : ∀ d t y : ZMod 4, d ≠ 0 → t ^ 2 = d * y ^ 2 →
      (d = 1 → f t = f y) ∧ (d ≠ 1 → f t = 0 ∧ f y = 0) := by decide +kernel
  have hD : (D : ZMod 4) ≠ 0 := by
    intro hz
    exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
      ((ZMod.intCast_zmod_eq_zero_iff_dvd D 4).mp hz)
  have he : (T : ZMod 4) ^ 2 = (D : ZMod 4) * (Y : ZMod 4) ^ 2 := by
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    push_cast at hz
    exact sub_eq_zero.mp hz
  have h₄ := htest D T Y hD he
  have h1 : ((D : ZMod 4) = 1) ↔ D % 4 = 1 := by
    rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff']
    rfl
  constructor
  · intro h0
    have ht := h₄.1 (h1.mpr h0)
    rw [map_intCast, map_intCast] at ht
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [Int.cast_sub, ht, sub_self]
  · intro h0
    obtain ⟨ht, hy⟩ := h₄.2 (h1.not.mpr h0)
    rw [map_intCast] at ht hy
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ht,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hy⟩

private theorem trace_norm_integer {D : ℤ} {z : QuadraticField D} (hz : IsIntegral ℤ z) :
    ∃ T U : ℤ, (T : ℚ) = z.trace ∧ (U : ℚ) = z.norm := by
  let f : QuadraticField D →ₐ[ℤ] QuadraticField D :=
    { starRingEnd _ with commutes' := by intro r; simp }
  have hz' : IsIntegral ℤ (star z) := hz.map f
  have ht : IsIntegral ℤ (QuadraticAlgebra.trace z) := by
    apply (isIntegral_algebraMap_iff (B := QuadraticField D)).mp
    rw [QuadraticAlgebra.algebraMap_trace_eq_add_star]
    exact hz.add hz'
  have hu : IsIntegral ℤ z.norm := by
    apply (isIntegral_algebraMap_iff (B := QuadraticField D)).mp
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    exact hz.mul hz'
  obtain ⟨T, hT⟩ := IsIntegrallyClosed.isIntegral_iff.mp ht
  obtain ⟨U, hU⟩ := IsIntegrallyClosed.isIntegral_iff.mp hu
  exact ⟨T, U, hT, hU⟩

theorem quadraticOrder_isIntegralClosure (D : ℤ) (hd : Squarefree D) :
    IsIntegralClosure (QuadraticOrder D) ℤ (QuadraticField D) := by
  constructor
  · intro a b hab
    ext
    · have he := congrArg QuadraticAlgebra.re hab
      change (a.re : ℚ) = (b.re : ℚ) at he
      exact_mod_cast he
    · have he := congrArg QuadraticAlgebra.im hab
      change (a.im : ℚ) = (b.im : ℚ) at he
      exact_mod_cast he
  · intro z
    constructor
    · intro hz
      obtain ⟨T, U, hT, hU⟩ := trace_norm_integer hz
      have he : (T : ℚ)^2 - 4 * (U : ℚ) = (quadraticDiscriminant D : ℚ) * z.im^2 := by
        rw [← order_discriminant, ← QuadraticAlgebra.discr_intCast, hT, hU,
          QuadraticAlgebra.trace_def, QuadraticAlgebra.norm_def, QuadraticAlgebra.discr_def]
        ring
      by_cases h4 : D % 4 = 1
      · simp [quadraticDiscriminant, h4] at he
        obtain ⟨Y, hY⟩ := exists_int_of_mul_square_eq hd (q := z.im)
          (A := T ^ 2 - 4 * U) (by push_cast; exact he.symm)
        rw [← hY] at he
        have hh : T ^ 2 - 4 * U = D * Y ^ 2 := by exact_mod_cast he
        have hc : (4 : ℤ) ∣ T ^ 2 - D * Y ^ 2 := ⟨U, by linarith only [hh]⟩
        obtain ⟨X, hx⟩ := (coord_parity hd hc).1 h4
        refine ⟨⟨X, Y⟩, ?_⟩
        ext
        · rw [QuadraticAlgebra.Int.re_algebraMap]
          have hTx : (T : ℚ) = 2 * z.re + (Y : ℚ) := by
            change (T : ℚ) = 2 * z.re + (orderB D : ℚ) * z.im at hT
            simpa [orderB, h4, hY] using hT
          have hx' : (T : ℚ) - (Y : ℚ) = 2 * (X : ℚ) := by exact_mod_cast hx
          linarith
        · simpa using hY
      · simp [quadraticDiscriminant, h4] at he
        obtain ⟨Y, hY⟩ := exists_int_of_mul_square_eq hd (q := 2 * z.im)
          (A := T ^ 2 - 4 * U) (by push_cast; linear_combination -he)
        have hY' : z.im = (Y : ℚ) / 2 := by linarith
        have he' : (T : ℚ)^2 - 4 * (U : ℚ) = (D : ℚ) * (Y : ℚ)^2 := by
          rw [hY'] at he
          linear_combination he
        have hh : T ^ 2 - 4 * U = D * Y ^ 2 := by exact_mod_cast he'
        have hc : (4 : ℤ) ∣ T ^ 2 - D * Y ^ 2 := ⟨U, by linarith only [hh]⟩
        obtain ⟨⟨X, hx⟩, ⟨W, hw⟩⟩ := (coord_parity hd hc).2 h4
        refine ⟨⟨X, W⟩, ?_⟩
        ext
        · rw [QuadraticAlgebra.Int.re_algebraMap]
          have hTx : (T : ℚ) = 2 * z.re := by
            change (T : ℚ) = 2 * z.re + (orderB D : ℚ) * z.im at hT
            simpa [orderB, h4] using hT
          have hx' : (T : ℚ) = 2 * (X : ℚ) := by exact_mod_cast hx
          linarith
        · rw [QuadraticAlgebra.Int.im_algebraMap]
          have hw' : (Y : ℚ) = 2 * (W : ℚ) := by exact_mod_cast hw
          linarith
    · rintro ⟨x, rfl⟩
      exact (IsIntegral.of_finite (R := ℤ) x).algebraMap

private theorem algebra_trace_eq {R : Type*} [CommRing R] {a b : R}
    (z : QuadraticAlgebra R a b) : Algebra.trace R _ z = z.trace := by
  rw [Algebra.trace_apply, LinearMap.trace_eq_matrix_trace R (QuadraticAlgebra.basis a b)]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, LinearMap.toMatrix_apply,
    QuadraticAlgebra.trace_def, QuadraticAlgebra.basis]
  ring

private theorem order_basis_discriminant (D : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis (orderA D) (orderB D)) = quadraticDiscriminant D := by
  rw [← order_discriminant]
  unfold Algebra.discr
  rw [Matrix.det_fin_two]
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, algebra_trace_eq,
    QuadraticAlgebra.basis, QuadraticAlgebra.trace_def, QuadraticAlgebra.discr_def]
  ring

theorem numberField_discriminant (D : ℤ) [Fact (Squarefree D)] [Fact (D ≠ 1)] :
    NumberField.discr (QuadraticField D) = quadraticDiscriminant D := by
  let : IsIntegralClosure (QuadraticOrder D) ℤ (QuadraticField D) :=
    quadraticOrder_isIntegralClosure D Fact.out
  let f := IsIntegralClosure.equiv ℤ (QuadraticOrder D) (QuadraticField D)
    (NumberField.RingOfIntegers (QuadraticField D))
  let b := QuadraticAlgebra.basis (orderA D) (orderB D)
  rw [← order_basis_discriminant D, Algebra.discr_eq_discr_of_algEquiv (f := f)]
  exact (NumberField.discr_eq_discr _ (b.map f.toLinearEquiv)).symm

theorem unramified_iff_order {D : ℤ} [Fact (Squarefree D)] [Fact (D ≠ 1)] {p : ℕ}
    (hp : p.Prime) : Unramified D p ↔
      Algebra.IsUnramifiedIn (NumberField.RingOfIntegers (QuadraticField D))
        (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
  unfold Unramified
  rw [← numberField_discriminant]
  exact NumberField.not_dvd_discr_iff_isUnramifiedIn _ _
    (Int.prime_iff_natAbs_prime.mpr (by simpa using hp))

end NajmanTrbovic
