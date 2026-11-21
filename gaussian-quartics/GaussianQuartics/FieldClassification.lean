module

public import GaussianQuartics.GaussianCurves

import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-! The quartic equations over the Gaussian rationals, including the paper's final remark. -/

@[expose] public section

namespace GaussianQuartics

/-- A solution is trivial when one of its coordinates is zero. -/
def Trivial {R : Type*} [Mul R] [Zero R] (x y z : R) : Prop :=
  x * y * z = 0

theorem trivial_iff {R : Type*} [MulZeroClass R] [NoZeroDivisors R] (x y z : R) :
    Trivial x y z ↔ x = 0 ∨ y = 0 ∨ z = 0 := by
  simp [Trivial, mul_eq_zero, or_assoc]

/-- The nontrivial solutions of the plus equation with imaginary coefficient,
written in terms of the freely chosen coordinate `y`. -/
def ScaledPlusSolution {R : Type*} [Ring R] (i x y z : R) : Prop :=
  (x = y ∨ x = -y ∨ x = i * y ∨ x = -(i * y)) ∧
    (z = i * (1 + i) * y ^ 2 ∨ z = -(i * (1 + i) * y ^ 2))

private theorem normalized {x y z A k : GaussianRat} (hy : y ≠ 0)
    (h : x ^ 4 + A * y ^ 4 = k * z ^ 2) :
    (x / y) ^ 4 + A = k * (z / y ^ 2) ^ 2 := by
  field_simp
  linear_combination h

private theorem twisted_curve {s t A : GaussianRat} (h : s ^ 4 + A = I * t ^ 2) :
    (s * t) ^ 2 = (I * s ^ 2) ^ 3 - A * (I * s ^ 2) := by
  calc
    (s * t) ^ 2 = -I * s ^ 2 * (I * t ^ 2) := by
      linear_combination (s ^ 2 * t ^ 2) * I_sq
    _ = -I * s ^ 2 * (s ^ 4 + A) := by rw [h]
    _ = (I * s ^ 2) ^ 3 - A * (I * s ^ 2) := by
      linear_combination -(I * s ^ 6) * I_sq

private theorem sq_ne_I (s : GaussianRat) : s ^ 2 ≠ I := by
  intro h
  have hr := congrArg QuadraticAlgebra.re h
  have hi := congrArg QuadraticAlgebra.im h
  simp only [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, I,
    QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, zero_mul, add_zero] at hr hi
  have heq : s.re ^ 2 = s.im ^ 2 := by linear_combination hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with he | he
  · have ht : IsSquare (2 : ℚ) := ⟨2 * s.im, by
      rw [he] at hi
      linear_combination -2 * hi⟩
    obtain ⟨n, hn⟩ := Rat.isSquare_natCast_iff.mp ht
    change (2 : ℕ) = n * n at hn
    by_cases hn' : n ≤ 1
    · interval_cases n <;> norm_num at hn
    · have hle : 2 ≤ n := by omega
      have hmul := Nat.mul_le_mul hle hle
      rw [← hn] at hmul
      norm_num at hmul
  · rw [he] at hi
    nlinarith [sq_nonneg s.im]

private theorem sq_ne_neg_I (s : GaussianRat) : s ^ 2 ≠ -I := by
  intro h
  apply sq_ne_I (I * s)
  rw [mul_pow, I_sq, h]
  ring

private theorem fourth_of_imaginary_unit {R : Type*} [CommRing R] {i : R}
    (hi : i ^ 2 = -1) : i ^ 4 = 1 := by
  rw [show i ^ 4 = (i ^ 2) ^ 2 by ring, hi]
  ring

theorem imaginary_factor {R : Type*} [CommRing R] {i : R} (hi : i ^ 2 = -1) :
    i * (i * (1 + i)) ^ 2 = 2 := by
  have h : (i * (1 + i)) ^ 2 = -2 * i := by
    rw [mul_pow, hi]
    linear_combination -hi
  rw [h]
  linear_combination -2 * hi

theorem eq_of_scaled_plus_solution {R : Type*} [CommRing R] {i x y z : R}
    (hi : i ^ 2 = -1) (h : ScaledPlusSolution i x y z) :
    x ^ 4 + y ^ 4 = i * z ^ 2 := by
  obtain ⟨hx, hz⟩ := h
  have hx4 : x ^ 4 = y ^ 4 := by
    rcases hx with hx | hx | hx | hx
    · rw [hx]
    · rw [hx]
      ring
    · rw [hx, mul_pow, fourth_of_imaginary_unit hi, one_mul]
    · rw [hx, show (-(i * y)) ^ 4 = (i * y) ^ 4 by ring, mul_pow,
        fourth_of_imaginary_unit hi, one_mul]
  have hz2 : z ^ 2 = (i * (1 + i) * y ^ 2) ^ 2 := by
    rcases hz with rfl | rfl <;> simp
  rw [hx4, hz2, mul_pow, ← mul_assoc, imaginary_factor hi]
  ring

/-- Theorem 1(i) over the Gaussian rationals. -/
theorem rat_minus_i_trivial {x y z : GaussianRat} (h : x ^ 4 - y ^ 4 = I * z ^ 2) :
    Trivial x y z := by
  by_contra ht
  rw [trivial_iff, not_or, not_or] at ht
  obtain ⟨hx, hy, hz⟩ := ht
  have hn := normalized (A := -1) hy (by simpa [sub_eq_add_neg] using h)
  have hc := gaussian_plus_y_eq_zero (by simpa using twisted_curve hn)
  exact mul_ne_zero (div_ne_zero hx hy) (div_ne_zero hz (pow_ne_zero 2 hy)) hc

/-- Theorem 1(ii) over the Gaussian rationals. -/
theorem rat_plus_i_iff {x y z : GaussianRat} (ht : ¬ Trivial x y z) :
    x ^ 4 + y ^ 4 = I * z ^ 2 ↔ ScaledPlusSolution I x y z := by
  refine ⟨?_, eq_of_scaled_plus_solution I_sq⟩
  intro h
  rw [trivial_iff, not_or, not_or] at ht
  obtain ⟨hx, hy, hz⟩ := ht
  let s := x / y
  let t := z / y ^ 2
  have hn : s ^ 4 + 1 = I * t ^ 2 :=
    normalized (A := 1) hy (by simpa using h)
  have hp : s * t ≠ 0 :=
    mul_ne_zero (div_ne_zero hx hy) (div_ne_zero hz (pow_ne_zero 2 hy))
  have hb := (gaussian_minus_y_eq_zero_or_x (by simpa using twisted_curve hn)).resolve_left hp
  have hsq : s ^ 2 = (1 : GaussianRat) ∨ s ^ 2 = -1 := by
    rcases hb with hpos | hneg
    · exact Or.inl (mul_left_cancel₀ I_ne_zero (by simpa using hpos))
    · exact Or.inr (mul_left_cancel₀ I_ne_zero (by simpa using hneg))
  have hroots : s = 1 ∨ s = -1 ∨ s = I ∨ s = -I := by
    rcases hsq with hpos | hneg
    · have hpos' : s ^ 2 = (1 : GaussianRat) ^ 2 := by rw [one_pow]; exact hpos
      exact (sq_eq_sq_iff_eq_or_eq_neg.mp hpos').imp_right Or.inl
    · exact Or.inr (Or.inr (sq_eq_sq_iff_eq_or_eq_neg.mp (hneg.trans I_sq.symm)))
  have hxy : x = s * y := (div_mul_cancel₀ x hy).symm
  have hx4 : x ^ 4 = y ^ 4 := by
    have hs4 : s ^ 4 = 1 := by
      rw [show s ^ 4 = (s ^ 2) ^ 2 by ring]
      rcases hsq with hpos | hneg
      · rw [hpos, one_pow]
      · rw [hneg]
        ring
    rw [hxy, mul_pow, hs4, one_mul]
  refine ⟨?_, ?_⟩
  · rcases hroots with hs | hs | hs | hs
    · exact Or.inl (by simpa [hs] using hxy)
    · exact Or.inr (Or.inl (by simpa [hs] using hxy))
    · exact Or.inr (Or.inr (Or.inl (by simpa [hs] using hxy)))
    · exact Or.inr (Or.inr (Or.inr (by simpa [hs] using hxy)))
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  apply mul_left_cancel₀ I_ne_zero
  calc
    I * z ^ 2 = 2 * y ^ 4 := by rw [← h, hx4]; ring
    _ = I * (I * (1 + I) * y ^ 2) ^ 2 := by
      rw [mul_pow, ← mul_assoc, imaginary_factor I_sq]
      ring

/-- Theorem 2, plus sign, over the Gaussian rationals. -/
theorem rat_hilbert_plus {x y z : GaussianRat} (h : x ^ 4 + y ^ 4 = z ^ 2) :
    Trivial x y z := by
  by_contra ht
  rw [trivial_iff, not_or, not_or] at ht
  obtain ⟨hx, hy, hz⟩ := ht
  let s := x / y
  let t := z / y ^ 2
  have hn : s ^ 4 + 1 = t ^ 2 := by
    simpa using normalized (A := 1) (k := 1) hy (by simpa using h)
  have hc : (s * t) ^ 2 = (s ^ 2) ^ 3 + s ^ 2 := by
    linear_combination -(s ^ 2) * hn
  exact mul_ne_zero (div_ne_zero hx hy) (div_ne_zero hz (pow_ne_zero 2 hy))
    (gaussian_plus_y_eq_zero hc)

/-- Theorem 2, minus sign, over the Gaussian rationals. -/
theorem rat_hilbert_minus {x y z : GaussianRat} (h : x ^ 4 - y ^ 4 = z ^ 2) :
    Trivial x y z := by
  by_contra ht
  rw [trivial_iff, not_or, not_or] at ht
  obtain ⟨hx, hy, hz⟩ := ht
  let s := x / y
  let t := z / y ^ 2
  have hn : s ^ 4 - 1 = t ^ 2 := by
    simpa [sub_eq_add_neg] using
      normalized (A := -1) (k := 1) hy (by simpa [sub_eq_add_neg] using h)
  have hc : (s * t) ^ 2 = (s ^ 2) ^ 3 - s ^ 2 := by
    linear_combination -(s ^ 2) * hn
  have hp : s * t ≠ 0 :=
    mul_ne_zero (div_ne_zero hx hy) (div_ne_zero hz (pow_ne_zero 2 hy))
  rcases (gaussian_minus_y_eq_zero_or_x hc).resolve_left hp with hb | hb
  · exact sq_ne_I s hb
  · exact sq_ne_neg_I s hb

end GaussianQuartics
