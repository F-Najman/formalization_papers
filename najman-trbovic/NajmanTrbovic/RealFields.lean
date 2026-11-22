module

public import NajmanTrbovic.FieldSpecialization

import Mathlib.Tactic

/-! The four real-field assertions in Theorem 2.2. -/

@[expose] public section

namespace NajmanTrbovic

private theorem nonneg_prod (xs : List ℚ) (h : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ xs.prod := by
  induction xs with
  | nil => exact zero_le_one
  | cons x xs ih =>
    have hx := (List.forall_mem_cons.mp h).1
    exact mul_nonneg hx (ih (List.forall_mem_cons.mp h).2)

private theorem nonneg_of_negative_norms (C : NormCase) (hC : C.radicand ≤ 0)
    (hm : 0 < C.multiplier) (x : ℚ) : 0 ≤ C.level.form x 1 := by
  have h := factored C x
  have hp : 0 ≤ (C.factors.map fun f => f.norm C.radicand x).prod := by
    apply nonneg_prod
    intro y hy
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hy
    exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hC)
      (sq_nonneg (affine f.radicalPart x))).trans (sq_nonneg (affine f.realPart x)))
  rw [← h] at hp
  have hm' : (0 : ℚ) < (C.multiplier : ℚ) := by exact_mod_cast hm
  exact nonneg_of_mul_nonneg_right hp hm'

private theorem nonneg_form {N : Level} (hn : N = .n28 ∨ N = .n33 ∨ N = .n40 ∨ N = .n48)
    (x : ℚ) : 0 ≤ N.form x 1 := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact nonneg_of_negative_norms .n28_neg7 (by decide) (by decide) x
  · exact nonneg_of_negative_norms .n33_neg11 (by decide) (by decide) x
  · exact nonneg_of_negative_norms .n40_neg1 (by decide) (by decide) x
  · exact nonneg_of_negative_norms .n48_neg1 (by decide) (by decide) x

theorem real_radicand_of_specialization {N : Level}
    (hn : N = .n28 ∨ N = .n33 ∨ N = .n40 ∨ N = .n48)
    {D : ℤ} (hD : Squarefree D) (h : FieldSpecialization N D) : 0 < D := by
  obtain ⟨x, y, hy, he⟩ := fieldSpecialization_iff_twist.mp h
  have hh := nonneg_form hn x
  rw [he] at hh
  have hd : (0 : ℚ) ≤ (D : ℚ) := nonneg_of_mul_nonneg_left hh (sq_pos_of_ne_zero hy)
  exact lt_of_le_of_ne (by exact_mod_cast hd) hD.ne_zero.symm

end NajmanTrbovic
