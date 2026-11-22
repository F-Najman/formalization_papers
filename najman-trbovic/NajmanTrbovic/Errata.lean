module

public import NajmanTrbovic.FieldSpecialization

import Mathlib.Tactic

/-! Explicit counterexamples to the uncorrected statements. -/

@[expose] public section

namespace NajmanTrbovic

/-- The (N=26) point from the review, written in the integral-generator basis of
`QuadraticField (-11)`. Its first coordinate generates the field. -/
theorem exceptional26 :
    ∃ x y : QuadraticField (-11), x.im ≠ 0 ∧ y ^ 2 = Level.n26.form x 1 := by
  exact ⟨⟨-1, 1⟩, ⟨8, 2⟩, by decide +kernel⟩

theorem eleven_ramifies_exceptional26 : ¬ Unramified (-11) 11 := by
  unfold Unramified quadraticDiscriminant
  decide +kernel

/-- The modulus claimed in Lemma 2.6(b) cannot be used without the residual square factor. -/
theorem lemma26b_counterexample :
    Squarefree (2 : ℤ) ∧ ¬ (2 : ℤ) ∣ 9 ∧
      (2 * 3^2 : ℤ) ≡ (2^1 * 9 : ℤ) [ZMOD 2^6] := by
  exact ⟨Int.squarefree_natAbs.mp (by decide +kernel), by decide +kernel⟩

theorem lemma26b_conclusion_fails : ¬ ((2 : ℤ) ≡ 2 * 9 [ZMOD 2^6]) := by
  decide +kernel

/-- At level 22 a root modulo 7 coexists with nonsquare discriminants of both cubic factors. -/
theorem lemma29_counterexample :
    Level.n22.form (1 : ℤ) 1 = -7 ∧
      ¬ FiniteSquare 7 (-176) ∧ ¬ FiniteSquare 7 (-2816) := by
  decide +kernel

end NajmanTrbovic
