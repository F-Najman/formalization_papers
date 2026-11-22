module

public import NajmanTrbovic.Table2Congruences
public import NajmanTrbovic.RealFields

import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-! The three entries of Table 2 whose proof uses quadratic reciprocity. -/

@[expose] public section

namespace NajmanTrbovic

theorem square_of_prime_divisors {p : ℕ} {D : ℤ} (hd : D ≠ 0)
    (hneg : D < 0 → IsSquare (-1 : ZMod p))
    (hP : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ D → IsSquare (q : ZMod p)) : IsSquare (D : ZMod p) := by
  have aux (l : List ℕ) (h : ∀ q ∈ l, IsSquare (q : ZMod p)) : IsSquare (l.prod : ZMod p) := by
    induction l with
    | nil => exact ⟨1, by simp⟩
    | cons a l ih =>
      rw [List.prod_cons, Nat.cast_mul]
      exact (List.forall_mem_cons.mp h).1.mul (ih (List.forall_mem_cons.mp h).2)
  have habs : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd
  have habs' : IsSquare (D.natAbs : ZMod p) := by
    rw [← Nat.prod_primeFactorsList habs]
    apply aux
    intro q hq
    have ⟨hqp, hqd⟩ := (Nat.mem_primeFactorsList habs).mp hq
    exact hP q hqp (by simpa [← Int.natAbs_dvd_natAbs] using hqd)
  rcases Int.natAbs_eq D with he | he
  · rw [he, Int.cast_natCast]
    exact habs'
  · have hneg' : D < 0 := by omega
    rw [he, Int.cast_neg, Int.cast_natCast, ← neg_one_mul]
    exact (hneg hneg').mul habs'

private theorem neg11_reciprocity {q : ℕ} [Fact q.Prime] [Fact (Nat.Prime 11)] (hq2 : q ≠ 2) :
    legendreSym q (-11) = legendreSym 11 q := by
  have hqo := (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : q.Prime)).mpr hq2
  have hh : (-1 : ℤ)^(q/2) * (-1 : ℤ)^(11/2*(q/2)) = 1 := by
    rw [← pow_add, show q/2 + 11/2*(q/2) = 6*(q/2) by omega, pow_mul]
    norm_num
  have hr := legendreSym.quadratic_reciprocity' (p := 11) (q := q) (by decide) hq2
  change legendreSym q (11 : ℤ) = _ at hr
  rw [legendreSym.at_neg hq2, ZMod.χ₄_eq_neg_one_pow hqo, hr, ← mul_assoc, hh, one_mul]

inductive ReciprocityCase where
  | n29 | n33 | n41
  deriving DecidableEq

def ReciprocityCase.normCase : ReciprocityCase → NormCase
  | .n29 => .n29_29
  | .n33 => .n33_neg11
  | .n41 => .n41_41

def ReciprocityCase.prime : ReciprocityCase → ℕ
  | .n29 => 29
  | .n33 => 11
  | .n41 => 41

private theorem inverse_residue (C : ReciprocityCase) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h : IsSquare (C.normCase.radicand : ZMod q)) : IsSquare (q : ZMod C.prime) := by
  let : Fact q.Prime := ⟨hq⟩
  cases C
  · let : Fact (Nat.Prime 29) := ⟨by decide⟩
    exact (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 29) (q := q) (by decide) hq2).mpr
      (by simpa [ReciprocityCase.normCase, NormCase.radicand] using h)
  · let : Fact (Nat.Prime 11) := ⟨by decide⟩
    change IsSquare (q : ZMod 11)
    by_cases hq11 : q = 11
    · subst q
      rw [ZMod.natCast_self]
      exact IsSquare.zero
    · have hqn : (q : ZMod 11) ≠ 0 := ZMod.prime_ne_zero _ _ (Ne.symm hq11)
      have ht : (-11 : ZMod q) ≠ 0 := by
        rw [show (-11 : ZMod q) = -(11 : ℕ) by norm_cast]
        exact neg_ne_zero.mpr (ZMod.prime_ne_zero _ _ hq11)
      have he := (legendreSym.eq_one_iff q (a := -11) (by exact_mod_cast ht)).mpr h
      rw [neg11_reciprocity hq2] at he
      exact (legendreSym.eq_one_iff' 11 hqn).mp he
  · let : Fact (Nat.Prime 41) := ⟨by decide⟩
    exact (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 41) (q := q) (by decide) hq2).mpr
      (by simpa [ReciprocityCase.normCase, NormCase.radicand] using h)

theorem table2_reciprocity_not_inert (C : ReciprocityCase) {D : ℤ}
    (hD : Represents C.normCase.level D) : IsSquare (D : ZMod C.prime) := by
  apply square_of_prime_divisors hD.1.ne_zero
  · intro hn
    cases C
    · exact ⟨12, by decide +kernel⟩
    · have hp := real_radicand_of_specialization (N := .n33) (by simp) hD.1
        (fieldSpecialization_iff_twist.mpr (represents_iff_rational_twist.mp hD).2.2)
      omega
    · exact ⟨9, by decide +kernel⟩
  · intro q hq hd
    by_cases hq₂ : q = 2
    · subst q
      change (2 : ℤ) ∣ D at hd
      cases C
      · have hh := table2_two .n29 hD
        change D%2 = 1 at hh
        omega
      · have hh := table2_two .n33 hD
        change D%8 = 1 at hh
        omega
      · exact ⟨17, by decide +kernel⟩
    · have hr : ¬Unramified D q := fun h => (unramified_odd hq hq₂).mp h hd
      exact inverse_residue C hq hq₂ (odd_ramified_imp_square C.normCase hq hq₂ hD hr)

end NajmanTrbovic
