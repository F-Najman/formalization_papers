module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Factorial.Basic

import Mathlib.Tactic

/-! The factorial equation and its squarefree reduction. -/

@[expose] public section

namespace ThreeFactorials

/-- The three factors left after removing the square of `(a-3)!`. -/
def block (a : ℕ) : ℕ := a * (a - 1) * (a - 2)

/-- The equation with strictly decreasing indices `a > a-3 > n > 1`. -/
def Solution (a n : ℕ) : Prop :=
  1 < n ∧ n + 3 < a ∧ IsSquare (a.factorial * (a - 3).factorial * n.factorial)

theorem block_pos {a : ℕ} (ha : 2 < a) : 0 < block a := by
  unfold block
  exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)

theorem square_mul_iff {k m : ℕ} (hk : 0 < k) :
    IsSquare (k ^ 2 * m) ↔ IsSquare m := by
  constructor
  · rintro ⟨t, ht⟩
    have hd : k ^ 2 ∣ t ^ 2 := ⟨m, by simpa only [pow_two] using ht.symm⟩
    obtain ⟨u, rfl⟩ := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp hd
    refine ⟨u, Nat.mul_left_cancel (pow_pos hk 2) ?_⟩
    calc
      k ^ 2 * m = (k * u) * (k * u) := ht
      _ = k ^ 2 * (u * u) := by ring
  · rintro ⟨u, rfl⟩
    exact ⟨k * u, by ring⟩

theorem solution_iff {a n : ℕ} :
    Solution a n ↔ 1 < n ∧ n + 3 < a ∧ IsSquare (block a * n.factorial) := by
  unfold Solution
  refine and_congr_right fun _ => and_congr_right fun ha => ?_
  have hf : a.factorial = (a - 3).factorial * block a := by
    rw [← Nat.factorial_mul_descFactorial (show 3 ≤ a by omega)]
    simp [Nat.descFactorial, block, mul_assoc, mul_comm]
  rw [hf, show (a - 3).factorial * block a * (a - 3).factorial * n.factorial =
      (a - 3).factorial ^ 2 * (block a * n.factorial) by ring]
  exact square_mul_iff (Nat.factorial_pos _)

/-- Remove a squarefree factor from a square product. -/
theorem isSquare_mul_squarefree_iff {d m : ℕ} (hd : Squarefree d) :
    IsSquare (m * d) ↔ ∃ t : ℕ, m = d * t ^ 2 := by
  constructor
  · rintro ⟨t, ht⟩
    have hdvd : d ∣ t ^ 2 := ⟨m, by simpa [pow_two, mul_comm] using ht.symm⟩
    obtain ⟨u, rfl⟩ := (hd.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hdvd
    refine ⟨u, Nat.mul_right_cancel (Nat.pos_of_ne_zero hd.ne_zero) ?_⟩
    calc
      m * d = (d * u) * (d * u) := ht
      _ = (d * u ^ 2) * d := by ring
  · rintro ⟨t, rfl⟩
    exact ⟨d * t, by ring⟩

theorem solution_iff_squarefree {a n d k : ℕ}
    (hn : n.factorial = d * k ^ 2) (hd : Squarefree d) (hk : 0 < k) :
    Solution a n ↔ 1 < n ∧ n + 3 < a ∧ ∃ t : ℕ, block a = d * t ^ 2 := by
  rw [solution_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [hn, show block a * (d * k ^ 2) = k ^ 2 * (block a * d) by ring]
  exact (square_mul_iff hk).trans (isSquare_mul_squarefree_iff hd)

/-- The integral-point equation for the congruent-number curve of parameter `d`. -/
def CongruentPoint (d : ℕ) (x y : ℤ) : Prop :=
  y ^ 2 = x ^ 3 - (d : ℤ) ^ 2 * x

/-- Equation (6) of the paper, with the divisibility needed to recover `a`. -/
theorem congruent_point_of_block {a d t : ℕ} (ha : 2 < a)
    (he : block a = d * t ^ 2) :
    CongruentPoint d ((d : ℤ) * (a - 1 : ℤ)) ((d : ℤ) ^ 2 * t) := by
  have he' : (a : ℤ) * (a - 1 : ℤ) * (a - 2 : ℤ) = (d : ℤ) * (t : ℤ) ^ 2 := by
    unfold block at he
    have hc := congrArg (fun n : ℕ => (n : ℤ)) he
    push_cast [Nat.cast_sub (show 1 ≤ a by omega), Nat.cast_sub (show 2 ≤ a by omega)] at hc
    exact hc
  unfold CongruentPoint
  linear_combination -(d : ℤ) ^ 3 * he'

end ThreeFactorials
