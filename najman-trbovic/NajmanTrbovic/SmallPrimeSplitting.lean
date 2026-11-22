module

public import NajmanTrbovic.FieldSpecialization

import Mathlib.Tactic

/-! The odd-prime split entries of Table 2, expressed as nonzero square residues. -/

@[expose] public section

namespace NajmanTrbovic

inductive OddSplitCase where
  | n28p3 | n30p3 | n35p7 | n39p13 | n40p3 | n40p5 | n48p3 | n48p5
  deriving DecidableEq

def OddSplitCase.level : OddSplitCase → Level
  | .n28p3 => .n28
  | .n30p3 => .n30
  | .n35p7 => .n35
  | .n39p13 => .n39
  | .n40p3 | .n40p5 => .n40
  | .n48p3 | .n48p5 => .n48

def OddSplitCase.prime : OddSplitCase → ℕ
  | .n28p3 | .n30p3 | .n40p3 | .n48p3 => 3
  | .n40p5 | .n48p5 => 5
  | .n35p7 => 7
  | .n39p13 => 13

private def NonzeroSquare (p : ℕ) (v : ZMod p) : Prop :=
  v ≠ 0 ∧ ∃ t : Fin p, v = (t.val : ZMod p)^2

private instance (p : ℕ) (v : ZMod p) : Decidable (NonzeroSquare p v) := by
  unfold NonzeroSquare
  infer_instance

private theorem checked_charts (C : OddSplitCase) :
    NonzeroSquare C.prime (C.level.form 1 0) ∧
      ∀ t : Fin C.prime, NonzeroSquare C.prime (C.level.form t.val 1) := by
  cases C <;> decide +kernel

/-- Every radicand in the eight odd-prime split cases of Table 2 is a nonzero square
modulo the indicated prime. -/
theorem table2_odd_split_residue (C : OddSplitCase) {D : ℤ}
    (hD : FieldSpecialization C.level D) (hd : Squarefree D) (hne : D ≠ 1) :
    (D : ZMod C.prime) ≠ 0 ∧ IsSquare (D : ZMod C.prime) := by
  have hp : C.prime.Prime := by cases C <;> decide
  let : Fact C.prime.Prime := ⟨hp⟩
  let : NeZero C.prime := ⟨hp.ne_zero⟩
  obtain ⟨_, _, m, n, s, hg, _, _, h⟩ := represents_iff_rational_twist.mpr
    ⟨hd, hne, fieldSpecialization_iff_twist.mp hD⟩
  let p := C.prime
  have hsquare (v w : ZMod p) (hv : NonzeroSquare p v) (he : v = (D : ZMod p) * w^2) :
      (D : ZMod p) ≠ 0 ∧ IsSquare (D : ZMod p) := by
    have hd₀ : (D : ZMod p) ≠ 0 := by
      intro hh
      exact hv.1 (by simp [he, hh])
    have hw : w ≠ 0 := by
      intro hh
      exact hv.1 (by simp [he, hh])
    obtain ⟨t, ht⟩ := hv.2
    refine ⟨hd₀, (t.val : ZMod p)/w, ?_⟩
    rw [← pow_two, div_pow, eq_div_iff (pow_ne_zero _ hw), ← he, ht]
  have hF : C.level.form (m : ZMod p) (n : ZMod p) = (D : ZMod p) * (s : ZMod p)^2 := by
    rw [← form_mod, h, Int.cast_mul, Int.cast_pow]
  have hscale (c : ZMod p) : C.level.form (c * (m : ZMod p)) (c * (n : ZMod p)) =
      (D : ZMod p) * (c ^ ((C.level.coefficients.length - 1) / 2) * (s : ZMod p)) ^ 2 := by
    rw [form_scale, hF]
    ring
  by_cases hn : (n : ZMod p) = 0
  · have hm : (m : ZMod p) ≠ 0 := by
      intro he
      exact not_both_dvd hp hg ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp he,
        (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp hn⟩
    have he := hscale (m : ZMod p)⁻¹
    rw [inv_mul_cancel₀ hm, hn, mul_zero] at he
    exact hsquare _ _ (checked_charts C).1 he
  · let c := (n : ZMod p)⁻¹
    obtain ⟨t, ht⟩ := residue_cases (c * (m : ZMod p))
    have he := hscale c
    have hc : c * (n : ZMod p) = 1 := inv_mul_cancel₀ hn
    rw [← ht, hc] at he
    exact hsquare _ _ ((checked_charts C).2 t) he

end NajmanTrbovic
