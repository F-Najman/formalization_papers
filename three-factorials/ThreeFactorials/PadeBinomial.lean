module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Catalan

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

/-! Denominators of the half-integer binomial coefficients in the Padé forms. -/

@[expose] public section

noncomputable section

namespace ThreeFactorials

open Finset PowerSeries

/-- An integral square root of `1 + 4X` in the power series ring. -/
def integralSqrtSeries : PowerSeries ℤ :=
  1 + C 2 * X * rescale (-1) (PowerSeries.map (Nat.castRingHom ℤ) catalanSeries)

theorem integralSqrtSeries_sq : integralSqrtSeries ^ 2 = 1 + C 4 * X := by
  let C₀ := rescale (-1 : ℤ) (PowerSeries.map (Nat.castRingHom ℤ) catalanSeries)
  have hc := congrArg
    (fun p => rescale (-1 : ℤ) (PowerSeries.map (Nat.castRingHom ℤ) p)) catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_pow, map_mul, map_X, map_one, rescale_X] at hc
  change C₀ ^ 2 * (C (-1) * X) + 1 = C₀ at hc
  change (1 + C 2 * X * C₀) ^ 2 = 1 + C 4 * X
  simp only [map_neg, map_one, map_ofNat] at hc ⊢
  linear_combination -4 * X * hc

private theorem rationalSqrtSeries_eq :
    rescale (4 : ℚ) (binomialSeries ℚ (1 / 2 : ℚ)) =
      map (Int.castRingHom ℚ) integralSqrtSeries := by
  let P := rescale (4 : ℚ) (binomialSeries ℚ (1 / 2 : ℚ))
  let Q := map (Int.castRingHom ℚ) integralSqrtSeries
  have hp : P ^ 2 = 1 + C 4 * X := by
    dsimp [P]
    rw [← map_pow, pow_two, ← binomialSeries_add, show (1 / 2 + 1 / 2 : ℚ) = (1 : ℕ) by norm_num,
      binomialSeries_nat, pow_one, map_add, map_one, rescale_X]
  have hq : Q ^ 2 = 1 + C 4 * X := by
    dsimp [Q]
    rw [← map_pow, integralSqrtSeries_sq, map_add, map_mul, map_one, map_X, map_C]
    norm_num
  have h0p : constantCoeff P = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [P, coeff_rescale]
  have h0q : constantCoeff Q = 1 := by simp [Q, integralSqrtSeries]
  have hprod : (P - Q) * (P + Q) = 0 := by rw [mul_comm, ← sq_sub_sq, hp, hq, sub_self]
  have hu : IsUnit (P + Q) := by
    apply isUnit_iff_constantCoeff.mpr
    simp [h0p, h0q]
  obtain ⟨u, hU⟩ := hu
  have hh := congrArg (fun s : PowerSeries ℚ => s * ↑u⁻¹) hprod
  rw [← hU] at hh
  change P = Q
  exact sub_eq_zero.mp (by simpa [mul_assoc] using hh)

/-- Multiplication by `4^h` clears the denominator of `choose (k + 1/2) h`. -/
theorem half_choose_integral (k h : ℕ) :
    ∃ t : ℤ, (t : ℚ) = 4 ^ h * Ring.choose ((k : ℚ) + 1 / 2) h := by
  let S : PowerSeries ℤ := (1 + C 4 * X) ^ k * integralSqrtSeries
  have hc : map (Int.castRingHom ℚ) S =
      rescale (4 : ℚ) (binomialSeries ℚ ((k : ℚ) + 1 / 2)) := by
    rw [binomialSeries_add, binomialSeries_nat, map_mul, map_mul, rationalSqrtSeries_eq]
    simp only [map_pow, map_add, map_one, map_mul, map_C, map_X, rescale_X]
    norm_num
  refine ⟨coeff h S, ?_⟩
  have hh := congrArg (coeff (R := ℚ) h) hc
  rw [coeff_map, coeff_rescale, binomialSeries_coeff, smul_eq_mul, mul_one] at hh
  exact hh

end ThreeFactorials
