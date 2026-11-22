module

public import NajmanTrbovic.CubicMarkedEquation

import NajmanTrbovic.CubicMarkedData
import Mathlib.Tactic

/-! Transfer the checked integer polynomial identity to the marked Weierstrass model. -/

@[expose] public section

namespace NajmanTrbovic.Cubic

open PolynomialCertificate MarkedCertificate

theorem marked_j_cross_multiplication {R : Type*} [CommRing R] (u v : R)
    (h : fibre u 1 v 1 = 0) :
    256*(markedA2Numerator u v ^ 2 - 3*markedA4Numerator u v)^3*jDenominator u =
      denominator u*g12 u^3*(markedA4Numerator u v ^ 2*
        (markedA2Numerator u v ^ 2 - 4*markedA4Numerator u v)) := by
  have he := congrArg (Coefficients.value u v) checked_cofactor
  simp only [Coefficients.value_normal, lhs, rhs, F, A, B, D, N,
    Coefficients.value_add, Coefficients.value_sub, Coefficients.value_neg, Coefficients.value_mul,
    Coefficients.value_pow, Coefficients.value_one, Coefficients.value_ofNat,
    Coefficients.value_u, Coefficients.value_v] at he
  simp only [fibre, r, one_pow, mul_one] at h
  rw [h, mul_zero, add_zero] at he
  simpa only [markedA2Numerator, markedA4Numerator, markedTNumerator, markedSumTerm,
    markedDenominator, denominator, jDenominator, g2, g6, g12, r, one_pow, mul_one] using he

end NajmanTrbovic.Cubic
