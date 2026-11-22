module

public import ThreeFactorials.Basic

import Mathlib.Tactic

/-! The `a₃ = 26` case. The final exclusion is isolated as integral-point completeness. -/

@[expose] public section

namespace ThreeFactorials

theorem factorial26 : Nat.factorial 26 = 104006 * 62270208000 ^ 2 := by decide +kernel

theorem squarefree104006 : Squarefree (104006 : ℕ) := by
  have h₂ : Nat.Prime 2 := by decide
  have h₇ : Nat.Prime 7 := by decide
  have h₁₇ : Nat.Prime 17 := by decide
  have h₁₉ : Nat.Prime 19 := by decide
  have h₂₃ : Nat.Prime 23 := by decide
  have h := Nat.squarefree_mul (m := 4522) (n := 23) (by decide)
  apply h.mpr
  refine ⟨(Nat.squarefree_mul (m := 238) (n := 19) (by decide)).mpr ?_, h₂₃.squarefree⟩
  refine ⟨(Nat.squarefree_mul (m := 14) (n := 17) (by decide)).mpr ?_, h₁₉.squarefree⟩
  exact ⟨(Nat.squarefree_mul (m := 2) (n := 7) (by decide)).mpr
    ⟨h₂.squarefree, h₇.squarefree⟩, h₁₇.squarefree⟩

theorem solution26_iff_block {a : ℕ} :
    Solution a 26 ↔ 29 < a ∧ ∃ t : ℕ, block a = 104006 * t ^ 2 := by
  simpa using solution_iff_squarefree (a := a) factorial26 squarefree104006 (by decide)

theorem solution324_26 : Solution 324 26 :=
  solution26_iff_block.mpr ⟨by decide, 18, by decide +kernel⟩

theorem solution2738_26 : Solution 2738 26 :=
  solution26_iff_block.mpr ⟨by decide, 444, by decide +kernel⟩

/-- The review's integral-point table for `Y² = X³ − 104006² X`, with nonnegative ordinates. -/
def integralPoints26 : List (ℤ × ℕ) :=
  [(-104006, 0), (-102850, 4959240), (-51842, 20529432), (-49419, 20344155),
    (-322, 1866312), (-38, 641136), (0, 0), (104006, 0), (104652, 3755844),
    (208658, 82628568), (18610956, 80287186980), (33593938, 194710464648),
    (284664422, 4802858127984)]

/-- Lean checks the curve equation at every entry in the reviewed table. -/
theorem integralPoints26_sound :
    ∀ p ∈ integralPoints26, CongruentPoint 104006 p.1 p.2 := by
  change ∀ p ∈ integralPoints26, (p.2 : ℤ) ^ 2 = p.1 ^ 3 - (104006 : ℤ) ^ 2 * p.1
  decide +kernel

/-- The unbounded assertion needed about the integral-point table. -/
def IntegralPoints26Complete : Prop :=
  ∀ x y : ℤ, CongruentPoint 104006 x y → (x, y.natAbs) ∈ integralPoints26

private theorem integralPoints26_filter :
    ∀ p ∈ integralPoints26, 104006 * 28 < p.1 → (104006 : ℤ) ∣ p.1 →
      p.1 = 33593938 ∨ p.1 = 284664422 := by decide +kernel

/-- The reviewed integral-point completeness assertion implies precisely the desired two cases. -/
theorem case26_iff_of_integral_points (complete : IntegralPoints26Complete) (a : ℕ) :
    Solution a 26 ↔ a = 324 ∨ a = 2738 := by
  constructor
  · intro h
    obtain ⟨ha, t, ht⟩ := solution26_iff_block.mp h
    let x : ℤ := 104006 * ((a : ℤ) - 1)
    let y : ℤ := 104006 ^ 2 * (t : ℤ)
    have hp : CongruentPoint 104006 x y := congruent_point_of_block (by omega) ht
    have hsize : 104006 * 28 < x := by dsimp [x]; omega
    have hdiv : (104006 : ℤ) ∣ x := ⟨(a : ℤ) - 1, rfl⟩
    rcases integralPoints26_filter (x, y.natAbs) (complete x y hp) hsize hdiv with h | h
    · left
      change 104006 * ((a : ℤ) - 1) = 33593938 at h
      omega
    · right
      change 104006 * ((a : ℤ) - 1) = 284664422 at h
      omega
  · rintro (rfl | rfl)
    · exact solution324_26
    · exact solution2738_26

end ThreeFactorials
