module

public import NajmanTrbovic.FieldSpecialization
public import NajmanTrbovic.InfinitudeData
public import NajmanTrbovic.PrimeLifting

import Mathlib.Tactic

/-! The infinitude argument for the four rows of Theorem 2.12. -/

@[expose] public section

noncomputable section

namespace NajmanTrbovic

open Polynomial

def Level.poly (N : Level) : ℤ[X] := N.form (X : ℤ[X]) 1

theorem Level.eval_poly (N : Level) (x : ℤ) : N.poly.eval x = N.form x 1 := by
  simpa [Level.poly] using map_form (evalRingHom x) N X 1

private def coefficientPoly (c : List ℤ) : ℤ[X] := affine c (X : ℤ[X])

set_option maxHeartbeats 0 in
private theorem bezout_certificate (N : InfinitudeCase) :
    coefficientPoly N.certificate.left * N.normCase.level.poly +
      coefficientPoly N.certificate.right * N.normCase.level.poly.derivative =
      Polynomial.C N.certificate.constant := by
  cases N <;> simp [InfinitudeCase.certificate, InfinitudeCase.normCase, NormCase.level,
    Level.poly, Level.form, Level.coefficients, coefficientPoly, affine, homogeneous,
    derivative_add, derivative_mul, derivative_neg] <;> ring

private theorem nonconstant (N : InfinitudeCase) : N.normCase.level.poly.natDegree ≠ 0 := by
  intro h
  have he := eq_C_of_natDegree_le_zero (p := N.normCase.level.poly) h.le
  have hv : N.normCase.level.form (0 : ℤ) 1 ≠ N.normCase.level.form 2 1 := by
    cases N <;> decide +kernel
  apply hv
  rw [← Level.eval_poly, ← Level.eval_poly, he, eval_C, eval_C]

private def badFactors : ℕ := 2^10 * 3^6 * 5^3 * 7^2 * 11^3

private theorem certificate_not_dvd (N : InfinitudeCase) {p : ℕ} (hp : p.Prime) (hl : 100 < p) :
    ¬ (p : ℤ) ∣ N.certificate.constant := by
  have hd : N.certificate.constant.natAbs ∣ badFactors := by cases N <;> decide +kernel
  intro h
  have h1 : p ∣ N.certificate.constant.natAbs := by simpa [← Int.natAbs_dvd_natAbs] using h
  have h2 := dvd_trans h1 hd
  simp only [badFactors, hp.dvd_mul] at h2
  rcases h2 with ((((h2 | h3) | h5) | h7) | h11)
  · have hh := Nat.le_of_dvd (by decide : 0 < 2) (hp.dvd_of_dvd_pow h2)
    omega
  · have hh := Nat.le_of_dvd (by decide : 0 < 3) (hp.dvd_of_dvd_pow h3)
    omega
  · have hh := Nat.le_of_dvd (by decide : 0 < 5) (hp.dvd_of_dvd_pow h5)
    omega
  · have hh := Nat.le_of_dvd (by decide : 0 < 7) (hp.dvd_of_dvd_pow h7)
    omega
  · have hh := Nat.le_of_dvd (by decide : 0 < 11) (hp.dvd_of_dvd_pow h11)
    omega

private def linearRoot {K : Type*} [Field K] (N : InfinitudeCase) (s : K) : K :=
  match N with
  | .n28 | .n33 => (s + 1) / 2
  | .n30 => s - 3
  | .n35 => (s - 1) / 2

private theorem root_of_square {K : Type*} [Field K] (N : InfinitudeCase) (h2 : (2 : K) ≠ 0)
    (s : K) (hs : s^2 = (N.normCase.radicand : K)) :
    N.normCase.level.form (linearRoot N s) 1 = 0 := by
  have he := factored N.normCase (linearRoot N s)
  have hm : (N.normCase.multiplier : K) ≠ 0 := by
    cases N
    · simp only [InfinitudeCase.normCase, NormCase.multiplier, Int.cast_ofNat]
      rw [show (256 : K) = 2^8 by ring]
      exact pow_ne_zero _ h2
    all_goals
      simp only [InfinitudeCase.normCase, NormCase.multiplier, Int.cast_ofNat]
      rw [show (16 : K) = 2^4 by ring]
      exact pow_ne_zero _ h2
  have hz (t : K) : 2 * (t / 2) = t := by field_simp
  apply (mul_eq_zero.mp _).resolve_left hm
  rw [he]
  cases N <;> simp [InfinitudeCase.normCase, NormCase.factors, NormCase.radicand,
    List.map_cons, List.prod_cons, NormFactor.norm, affine, homogeneous, linearRoot] at hs ⊢
  all_goals apply Or.inl
  all_goals
    first
    | exact sub_eq_zero.mpr hs
    | have h : (-(1 : K) + (s + 1) / 2 * 2) = s := by rw [mul_comm, hz]; ring
      rw [h]
      linear_combination hs
    | have h : (1 : K) + (s - 1) / 2 * 2 = s := by rw [mul_comm, hz]; ring
      rw [h]
      linear_combination hs

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
private theorem small_witness_valid (N : InfinitudeCase) : ∀ p : Fin 101, p.val.Prime →
    p.val ≠ 2 → FiniteSquare p.val N.normCase.radicand →
    ExactOne p.val (N.normCase.level.form (N.smallWitness p.val : ℤ) 1) := by
  cases N <;> decide +kernel

theorem exists_valuation_one (N : InfinitudeCase) {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2)
    (hs : IsSquare (N.normCase.radicand : ZMod p)) :
    ∃ a : ℤ, ExactOne p (N.normCase.level.form a 1) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, he⟩ := hs
  by_cases h100 : p ≤ 100
  · obtain ⟨x, hx⟩ := residue_cases s
    refine ⟨N.smallWitness p, small_witness_valid N ⟨p, by omega⟩ hp h2 ⟨x, ?_⟩⟩
    rw [hx, he, pow_two]
  · have h₂ : (2 : ZMod p) ≠ 0 := by
      change ((2 : ℕ) : ZMod p) ≠ 0
      intro h
      have hh := Nat.le_of_dvd (by decide : 0 < 2) ((ZMod.natCast_eq_zero_iff 2 p).mp h)
      omega
    let x := linearRoot N s
    have hx : N.normCase.level.form x 1 = 0 := root_of_square N h₂ s (by rw [he, pow_two])
    let a : ℤ := x.val
    have hxa : (a : ZMod p) = x := by simp [a]
    have hpa : (p : ℤ) ∣ N.normCase.level.poly.eval a := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      rw [Level.eval_poly, form_mod, hxa, Int.cast_one, hx]
    have hpd : ¬ (p : ℤ) ∣ N.normCase.level.poly.derivative.eval a := by
      intro hd
      apply certificate_not_dvd N hp (by omega)
      have hc := congrArg (Polynomial.eval a) (bezout_certificate N)
      simp only [eval_add, eval_mul, eval_C] at hc
      rw [← hc]
      exact dvd_add (dvd_mul_of_dvd_right hpa _) (dvd_mul_of_dvd_right hd _)
    rcases simple_root_lift N.normCase.level.poly hp a 1 (by exact_mod_cast hp.not_dvd_one) hpa hpd with h | h
    · exact ⟨a, by rwa [Level.eval_poly] at h⟩
    · exact ⟨a + (p : ℤ) * 1, by rwa [Level.eval_poly] at h⟩

/-- The four families of Theorem 2.12 yield infinitely many ramified quadratic squareclasses. -/
theorem infinite_ramified_squareclasses (N : InfinitudeCase) {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2)
    (hs : IsSquare (N.normCase.radicand : ZMod p)) :
    Set.Infinite {D : ℤ | Represents N.normCase.level D ∧ ¬ Unramified D p} := by
  obtain ⟨a, ha⟩ := exists_valuation_one N hp h2 hs
  have hc : N.certificate.constant ≠ 0 := by cases N <;> decide
  have hi := infinite_squareclasses N.normCase.level.poly (nonconstant N) hp a
    (by rwa [Level.eval_poly]) (coefficientPoly N.certificate.left)
    (coefficientPoly N.certificate.right) N.certificate.constant hc (bezout_certificate N)
  apply hi.mono
  rintro D ⟨hd, hpD, x, s, hs, he⟩
  rw [Level.eval_poly] at he
  have hD : D ≠ 1 := by
    rintro rfl
    exact hp.not_dvd_one (by exact_mod_cast hpD)
  exact ⟨⟨hd, hD, x, 1, s, by simp, one_ne_zero, hs, he⟩,
    fun h => (unramified_odd hp h2).mp h hpD⟩

/-- Infinitely many nonisomorphic quadratic fields generated by the affine models ramify at
the given prime. Nonisomorphism for distinct parameters is `radicand_eq_of_isomorphic`. -/
theorem infinite_ramified_field_parameters (N : InfinitudeCase) {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2)
    (hs : IsSquare (N.normCase.radicand : ZMod p)) :
    Set.Infinite {D : ℤ | Squarefree D ∧ D ≠ 1 ∧ FieldSpecialization N.normCase.level D ∧
      ∀ [Fact (Squarefree D)] [Fact (D ≠ 1)],
        ¬ Algebra.IsUnramifiedIn (NumberField.RingOfIntegers (QuadraticField D))
          (Ideal.span ({(p : ℤ)} : Set ℤ))} := by
  apply (infinite_ramified_squareclasses N hp h2 hs).mono
  rintro D ⟨hD, hr⟩
  obtain ⟨hd, hne, hx⟩ := represents_iff_rational_twist.mp hD
  exact ⟨hd, hne, fieldSpecialization_iff_twist.mpr hx,
    fun {_ _} h => hr ((unramified_iff_order hp).mpr h)⟩

end NajmanTrbovic
