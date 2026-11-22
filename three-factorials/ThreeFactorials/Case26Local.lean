module

public import ThreeFactorials.Case26
public import ThreeFactorials.SquarefreeSplit

import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-! A certified local sieve for the canonical squarefree triples at n = 26. -/

@[expose] public section

namespace ThreeFactorials

/-- The canonical coefficient triples surviving the congruence checks. -/
def coefficients26 : List (ℕ × ℕ × ℕ) :=
  [(1, 323, 322), (1, 3059, 34), (2, 1, 52003), (2, 2737, 19),
    (161, 19, 34), (322, 17, 19)]

private def allocations : List ℕ → List (ℕ × ℕ × ℕ)
  | [] => [(1, 1, 1)]
  | p :: ps => (allocations ps).flatMap fun (a, b, c) =>
      [(p * a, b, c), (a, p * b, c), (a, b, p * c)]

private theorem mem_allocations {ps : List ℕ} (hp : ∀ p ∈ ps, Nat.Prime p)
    {A B C : ℕ} (h : A * B * C = ps.prod) : (A, B, C) ∈ allocations ps := by
  induction ps generalizing A B C with
  | nil =>
    obtain ⟨rfl, rfl, rfl⟩ : A = 1 ∧ B = 1 ∧ C = 1 := by
      simpa [and_assoc] using h
    simp [allocations]
  | cons p ps ih =>
    have hprime := hp p (by simp)
    have htail : ∀ p ∈ ps, Nat.Prime p := fun q hq => hp q (List.mem_cons_of_mem _ hq)
    have hpdiv : p ∣ A * B * C := ⟨ps.prod, by simpa using h⟩
    rw [hprime.dvd_mul, hprime.dvd_mul] at hpdiv
    simp only [allocations, List.mem_flatMap]
    rcases hpdiv with (⟨A', hA⟩ | ⟨B', hB⟩) | ⟨C', hC⟩
    · have hh : A' * B * C = ps.prod :=
        Nat.mul_left_cancel hprime.pos (by simpa [hA, mul_assoc, mul_left_comm, mul_comm] using h)
      exact ⟨(A', B, C), ih htail hh, by simp [hA]⟩
    · have hh : A * B' * C = ps.prod :=
        Nat.mul_left_cancel hprime.pos (by simpa [hB, mul_assoc, mul_left_comm, mul_comm] using h)
      exact ⟨(A, B', C), ih htail hh, by simp [hB]⟩
    · have hh : A * B * C' = ps.prod :=
        Nat.mul_left_cancel hprime.pos (by simpa [hC, mul_assoc, mul_left_comm, mul_comm] using h)
      exact ⟨(A, B, C'), ih htail hh, by simp [hC]⟩

private def localPossible (m : ℕ) (coefficients : ℕ × ℕ × ℕ) : Bool :=
  let (A, B, C) := coefficients
  (List.range m).any fun x =>
    ((List.range m).any fun y => (A * x ^ 2) % m == (B * y ^ 2 + 1) % m) &&
    ((List.range m).any fun z => (A * x ^ 2) % m == (C * z ^ 2 + 2) % m)

private theorem localPossible_of_eq {m A B C x y z : ℕ} (hm : 0 < m)
    (hy : A * x ^ 2 = B * y ^ 2 + 1) (hz : A * x ^ 2 = C * z ^ 2 + 2) :
    localPossible m (A, B, C) = true := by
  have hxMod := ((Nat.mod_modEq x m).pow 2).mul_left A
  have hyMod := (((Nat.mod_modEq y m).pow 2).mul_left B).add_right 1
  have hzMod := (((Nat.mod_modEq z m).pow 2).mul_left C).add_right 2
  rw [hy] at hxMod
  have hyEq := hxMod.trans hyMod.symm
  rw [← hy, hz] at hxMod
  have hzEq := hxMod.trans hzMod.symm
  simp only [localPossible, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    beq_iff_eq]
  exact ⟨x % m, Nat.mod_lt _ hm, ⟨y % m, Nat.mod_lt _ hm, hyEq⟩,
    ⟨z % m, Nat.mod_lt _ hm, hzEq⟩⟩

private def testModuli : List ℕ := [3, 5, 7, 8, 11, 13, 17]

private theorem sieve26 :
    ∀ t ∈ allocations [2, 7, 17, 19, 23],
      testModuli.all (fun m => localPossible m t) = true → t ∈ coefficients26 := by
  decide +kernel

/-- The unbounded factorial equation at n = 26 reduces to six simultaneous systems. -/
theorem solution26_local {a : ℕ} (h : Solution a 26) :
    ∃ (t : ℕ × ℕ × ℕ) (x y z : ℕ), t ∈ coefficients26 ∧
      a = t.1 * x ^ 2 ∧ a - 1 = t.2.1 * y ^ 2 ∧ a - 2 = t.2.2 * z ^ 2 := by
  obtain ⟨ha, w, hw⟩ := solution26_iff_block.mp h
  obtain ⟨A, B, C, x, y, z, hABC, hA, hB, hC⟩ :=
    squarefree_split_even (by omega) squarefree104006 (by decide) hw
  have hB' : A * x ^ 2 = B * y ^ 2 + 1 := by omega
  have hC' : A * x ^ 2 = C * z ^ 2 + 2 := by omega
  have hmem : (A, B, C) ∈ allocations [2, 7, 17, 19, 23] :=
    mem_allocations (by decide +kernel) hABC
  have hall : testModuli.all (fun m => localPossible m (A, B, C)) = true := by
    apply List.all_eq_true.mpr
    intro m hm
    apply localPossible_of_eq (m := m) ?_ hB' hC'
    have hpos : ∀ k ∈ testModuli, 0 < k := by decide +kernel
    exact hpos m hm
  exact ⟨(A, B, C), x, y, z, sieve26 _ hmem hall, hA, hB, hC⟩

end ThreeFactorials
