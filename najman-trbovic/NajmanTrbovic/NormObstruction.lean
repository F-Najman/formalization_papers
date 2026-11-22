module

public import NajmanTrbovic.NormData
public import NajmanTrbovic.Table7

import Mathlib.Tactic

/-! The norm obstruction for the odd primes in Theorem 2.8. -/

@[expose] public section

namespace NajmanTrbovic

def affine {R : Type*} [Ring R] (c : List ℤ) (x : R) : R :=
  homogeneous x 1 (c.map fun a : ℤ => (a : R))

def NormFactor.norm {R : Type*} [Ring R] (f : NormFactor) (d : ℤ) (x : R) : R :=
  affine f.realPart x ^ 2 - (d : R) * affine f.radicalPart x ^ 2

theorem factored {R : Type*} [CommRing R] (C : NormCase) (x : R) :
    (C.multiplier : R) * C.level.form x 1 =
      (C.factors.map fun f => f.norm C.radicand x).prod := by
  cases C <;> simp [NormCase.level, NormCase.radicand, NormCase.multiplier, NormCase.factors,
    Level.form, Level.coefficients, NormFactor.norm, affine, homogeneous] <;> ring

private theorem bezout {R : Type*} [CommRing R] (C : NormCase) (x : R) :
    ∀ f ∈ C.factors, affine f.bezoutReal x * affine f.realPart x +
      affine f.bezoutRadical x * affine f.radicalPart x = (f.constant : R) := by
  cases C <;> simp [NormCase.factors, affine, homogeneous] <;>
    repeat' first | apply And.intro | ring

private def badPrimeProduct : ℤ := 2 ^ 4 * 5 * 11 * 29 * 41

private theorem constant_dvd (C : NormCase) : ∀ f ∈ C.factors, f.constant ∣ badPrimeProduct := by
  cases C <;> simp only [NormCase.factors, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] <;> decide +kernel

private theorem cast_badPrimeProduct_ne_zero {p : ℕ} (hp : p.Prime) (hl : 100 < p) :
    (badPrimeProduct : ZMod p) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have h (r : ℕ) (h₀ : 0 < r) (hr : r ≤ 41) : (r : ZMod p) ≠ 0 := by
    intro hz
    exact (Nat.le_of_dvd h₀ ((ZMod.natCast_eq_zero_iff r p).mp hz)).not_gt (by omega)
  simp only [badPrimeProduct, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  simpa only [Nat.cast_ofNat] using mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (pow_ne_zero 4 (h 2 (by decide) (by decide)))
    (h 5 (by decide) (by decide))) (h 11 (by decide) (by decide)))
    (h 29 (by decide) (by decide))) (h 41 (by decide) (by decide))

private theorem norm_ne_zero {p : ℕ} (hp : p.Prime) (hl : 100 < p) {C : NormCase}
    (hns : ¬ IsSquare (C.radicand : ZMod p)) (f : NormFactor) (hf : f ∈ C.factors)
    (x : ZMod p) : f.norm C.radicand x ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let A := affine f.realPart x
  let B := affine f.radicalPart x
  intro he
  have hn : A ^ 2 = (C.radicand : ZMod p) * B ^ 2 := sub_eq_zero.mp he
  by_cases hB : B = 0
  · have hA : A = 0 := by
      rw [hB, zero_pow (by decide), mul_zero] at hn
      by_contra hA
      exact (pow_ne_zero 2 hA) hn
    have hc := bezout C x f hf
    change affine f.bezoutReal x * A + affine f.bezoutRadical x * B = _ at hc
    rw [hA, hB, mul_zero, mul_zero, add_zero] at hc
    obtain ⟨k, hk⟩ := constant_dvd C f hf
    have hz : (badPrimeProduct : ZMod p) = 0 := by rw [hk, Int.cast_mul, ← hc, zero_mul]
    exact cast_badPrimeProduct_ne_zero hp hl hz
  · apply hns
    refine ⟨A / B, ?_⟩
    rw [← pow_two, div_pow, eq_div_iff (pow_ne_zero _ hB)]
    exact hn.symm

private theorem product_ne_zero {R : Type*} [MonoidWithZero R] [NoZeroDivisors R] [Nontrivial R]
    (l : List R) (h : ∀ a ∈ l, a ≠ 0) : l.prod ≠ 0 := by
  induction l with
  | nil => exact one_ne_zero
  | cons a l ih =>
    have ha := (List.forall_mem_cons.mp h).1
    have hl := ih (List.forall_mem_cons.mp h).2
    exact mul_ne_zero ha hl

private theorem no_root_large_prime {p : ℕ} (hp : p.Prime) (hl : 100 < p) (C : NormCase)
    (hns : ¬ IsSquare (C.radicand : ZMod p)) : RootFree C.level p := by
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨?_, fun x h => ?_⟩
  · have h : (4 : ZMod p) ≠ 0 := by
      change ((4 : ℕ) : ZMod p) ≠ 0
      intro h0
      exact (Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff 4 p).mp h0)).not_gt (by omega)
    cases C <;> simp [NormCase.level, Level.form, Level.coefficients, homogeneous, h]
  · have hf := factored C (x.val : ZMod p)
    rw [h, mul_zero] at hf
    apply product_ne_zero _ _ hf.symm
    intro a ha
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
    exact norm_ne_zero hp hl hns f hf x.val

def FiniteSquare (p : ℕ) (a : ℤ) : Prop :=
  ∃ x : Fin p, (a : ZMod p) = (x.val : ZMod p) ^ 2

instance (p : ℕ) (a : ℤ) : Decidable (FiniteSquare p a) := by
  unfold FiniteSquare
  infer_instance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem small_prime_condition (C : NormCase) : ∀ p : Fin 101, p.val.Prime →
    p.val ≠ 2 → ¬ FiniteSquare p.val C.radicand → p.val ∈ C.level.table7 := by
  cases C <;> decide +kernel

theorem norm_root_free (C : NormCase) {p : ℕ} (hp : p.Prime) (h₂ : p ≠ 2)
    (hns : ¬IsSquare (C.radicand : ZMod p)) : RootFree C.level p := by
  by_cases h100 : p ≤ 100
  · have hn : ¬FiniteSquare p C.radicand := by
      rintro ⟨x, hx⟩
      exact hns ⟨x.val, by simpa [pow_two] using hx⟩
    exact table7_root_free C.level ⟨p, by omega⟩ hp h₂
      (small_prime_condition C ⟨p, by omega⟩ hp h₂ hn)
  · exact no_root_large_prime hp (by omega) C hns

/-- The odd-prime assertion of Theorem 2.8 at the level of the squareclasses of the models. -/
theorem odd_ramified_imp_square (C : NormCase) {p : ℕ} (hp : p.Prime) (h₂ : p ≠ 2)
    {D : ℤ} (hD : Represents C.level D) (hr : ¬ Unramified D p) :
    IsSquare (C.radicand : ZMod p) := by
  by_contra hns
  obtain ⟨_, _, m, n, s, hg, _, _, he⟩ := hD
  have hF := form_nonzero_at_prime hp (norm_root_free C hp h₂ hns) hg
  apply hr
  rw [unramified_odd hp h₂]
  intro hpD
  rw [he, Int.cast_mul, Int.cast_pow, (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr hpD,
    zero_mul] at hF
  exact hF rfl

end NajmanTrbovic
