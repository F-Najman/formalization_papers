module

public import ThreeFactorials.Case26

/-! The witnessed direction of Theorem 1.1. -/

@[expose] public section

namespace ThreeFactorials

def solutionsUpTo100 : List (ℕ × ℕ) :=
  [(10, 6), (50, 3), (50, 4), (324, 26), (352, 13), (442, 18), (2738, 26)]

theorem solutionsUpTo100_sound {a n : ℕ} (h : (a, n) ∈ solutionsUpTo100) :
    n ≤ 100 ∧ Solution a n := by
  simp only [solutionsUpTo100, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h <;> cases h
  · exact ⟨by decide, solution_iff.mpr ⟨by decide, by decide, 720, by decide +kernel⟩⟩
  · exact ⟨by decide, solution_iff.mpr ⟨by decide, by decide, 840, by decide +kernel⟩⟩
  · exact ⟨by decide, solution_iff.mpr ⟨by decide, by decide, 1680, by decide +kernel⟩⟩
  · exact ⟨by decide, solution324_26⟩
  · exact ⟨by decide, solution_iff.mpr ⟨by decide, by decide, 518918400, by decide +kernel⟩⟩
  · exact ⟨by decide, solution_iff.mpr ⟨by decide, by decide, 741015475200, by decide +kernel⟩⟩
  · exact ⟨by decide, solution2738_26⟩

/-- The finite list gives Theorem 1.1 when its completeness has been established. -/
theorem theorem11_iff_of_completeness
    (complete : ∀ a n : ℕ, n ≤ 100 → Solution a n → (a, n) ∈ solutionsUpTo100)
    (a n : ℕ) : (n ≤ 100 ∧ Solution a n) ↔ (a, n) ∈ solutionsUpTo100 :=
  ⟨fun h => complete a n h.1 h.2, solutionsUpTo100_sound⟩

/-- The published proof's prime-support assertion fails at a genuine solution. -/
theorem prime_support_counterexample :
    Solution 2738 26 ∧ Nat.Prime 37 ∧ 26 < 37 ∧ 2738 = 2 * 37 ^ 2 :=
  ⟨solution2738_26, by decide, by decide, by decide⟩

/-- The auxiliary quartic has a positive solution at n = 6. -/
theorem auxiliary_quartic_six :
    (6 : ℕ).factorial = 5 * 12 ^ 2 ∧ Squarefree (5 : ℕ) ∧ (3 : ℕ) ^ 4 = 5 * 4 ^ 2 + 1 :=
  ⟨by decide, (by decide : Nat.Prime 5).squarefree, by decide⟩

end ThreeFactorials
