module

public import NajmanTrbovic.Models
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-! Arithmetic of the primitive squareclasses in equation (2). -/

@[expose] public section

namespace NajmanTrbovic

/-- An integral squareclass of a nonzero specialization at a primitive rational coordinate. -/
def Represents (N : Level) (D : ℤ) : Prop :=
  Squarefree D ∧ D ≠ 1 ∧ ∃ m n s : ℤ, m.gcd n = 1 ∧ n ≠ 0 ∧ s ≠ 0 ∧ N.form m n = D * s ^ 2

def quadraticDiscriminant (D : ℤ) : ℤ := if D % 4 = 1 then D else 4 * D

/-- The elementary discriminant test for ramification of a prime. -/
def Unramified (D : ℤ) (p : ℕ) : Prop := ¬(p : ℤ) ∣ quadraticDiscriminant D

theorem unramified_two {D : ℤ} : Unramified D 2 ↔ D % 4 = 1 := by
  unfold Unramified quadraticDiscriminant
  split <;> rename_i h
  · omega
  · push_cast
    omega

theorem unramified_odd {D : ℤ} {p : ℕ} (hp : p.Prime) (h₂ : p ≠ 2) :
    Unramified D p ↔ ¬(p : ℤ) ∣ D := by
  unfold Unramified quadraticDiscriminant
  split
  · rfl
  · have hp' : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
    have h₄ : ¬(p : ℤ) ∣ 4 := by
      intro h
      have hh : p ∣ 2 * 2 := by exact_mod_cast h
      exact h₂ ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        ((hp.dvd_mul.mp hh).elim id id))
    rw [hp'.dvd_mul, or_iff_right h₄]

def twoShape (a : ℤ) (k : ℕ) : Prop := a % 4 ^ (k + 1) = 4 ^ k

instance (a : ℤ) (k : ℕ) : Decidable (twoShape a k) :=
  inferInstanceAs (Decidable (_ = _))

def smallTwoShape (a : ℤ) : Prop := ∃ k : Fin 4, twoShape a k

instance (a : ℤ) : Decidable (smallTwoShape a) :=
  inferInstanceAs (Decidable (∃ k : Fin 4, twoShape a k))

private theorem odd_square_mod_four (s : ℤ) (hs : ¬(2 : ℤ) ∣ s) : s ^ 2 % 4 = 1 := by
  have h : s = 2 * (s / 2) + 1 := by omega
  conv_lhs => rw [h]
  rw [show (2 * (s / 2) + 1) ^ 2 = (4 : ℤ) * ((s / 2)^2 + s / 2) + 1 by ring]
  simp

private theorem unit_square_mod_four (D s : ℤ) (hs : ¬(2 : ℤ) ∣ s) :
    (D * s ^ 2) % 4 = D % 4 := by
  rw [Int.mul_emod, odd_square_mod_four s hs, mul_one, Int.emod_emod]

private theorem twoShape_mul_four (a : ℤ) (k : ℕ) :
    twoShape (4 * a) (k + 1) ↔ twoShape a k := by
  have hm : (4 * a) % 4 ^ (k + 1 + 1) = 4 * (a % 4 ^ (k + 1)) := by
    rw [pow_succ' (4 : ℤ) (k + 1), Int.mul_emod_mul_of_pos _ _ (by decide : (0 : ℤ) < 4)]
  unfold twoShape
  rw [hm, pow_succ' (4 : ℤ) k]
  omega

theorem mod_four_eq_one_of_twoShape {D s : ℤ} (hD : Squarefree D) {k : ℕ}
    (h : twoShape (D * s ^ 2) k) : D % 4 = 1 := by
  induction k generalizing s with
  | zero =>
    change (D * s ^ 2) % 4 = 1 at h
    have hs : ¬(2 : ℤ) ∣ s := by
      rintro ⟨t, rfl⟩
      rw [show D * (2 * t) ^ 2 = 4 * (D * t ^ 2) by ring] at h
      simp at h
    rwa [unit_square_mod_four D s hs] at h
  | succ k ih =>
    have h4 : (4 : ℤ) ∣ D * s ^ 2 := by
      have hm : (D * s ^ 2) ≡ 4 ^ (k + 1) [ZMOD 4 ^ (k + 1 + 1)] := by
        change _ % _ = _ % _
        have he : (4 : ℤ) ^ (k + 1) < 4 ^ (k + 1 + 1) := calc
          _ < (4 : ℤ) ^ (k + 1) * 4 := by nlinarith [show 0 < (4 : ℤ) ^ (k + 1) by positivity]
          _ = _ := (pow_succ _ _).symm
        rw [h, Int.emod_eq_of_lt (by positivity) he]
      have hg := hm.of_dvd (dvd_pow_self 4 (by omega : k + 1 + 1 ≠ 0))
      exact Int.modEq_zero_iff_dvd.mp (hg.trans
        (Int.modEq_zero_iff_dvd.mpr (dvd_pow_self 4 (by omega : k + 1 ≠ 0))))
    have hs : (2 : ℤ) ∣ s := by
      by_contra hn
      have he := Int.emod_eq_zero_of_dvd h4
      rw [unit_square_mod_four D s hn] at he
      exact (Int.squarefree_iff_prime_sq_not_dvd.mp hD 2 Nat.prime_two)
        (Int.dvd_of_emod_eq_zero he)
    obtain ⟨t, rfl⟩ := hs
    rw [show D * (2 * t) ^ 2 = 4 * (D * t ^ 2) by ring, twoShape_mul_four] at h
    exact ih h

private theorem shape_or_four_pow_dvd {D : ℤ} (hD : D % 4 = 1) (k : ℕ) (s : ℤ) :
    (∃ i < k, twoShape (D * s ^ 2) i) ∨ (4 : ℤ) ^ k ∣ D * s ^ 2 := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    by_cases h : (2 : ℤ) ∣ s
    · obtain ⟨t, rfl⟩ := h
      rw [show D * (2 * t) ^ 2 = 4 * (D * t ^ 2) by ring]
      rcases ih t with ⟨i, hi, hs⟩ | ht
      · exact Or.inl ⟨i + 1, by omega, (twoShape_mul_four _ _).mpr hs⟩
      · exact Or.inr (by rw [pow_succ']; exact mul_dvd_mul_left 4 ht)
    · exact Or.inl ⟨0, by omega, (unit_square_mod_four D s h).trans hD⟩

theorem smallTwoShape_of_mod_four_eq_one {D s : ℤ} (hD : D % 4 = 1)
    (h : ¬ (256 : ℤ) ∣ D * s ^ 2) : smallTwoShape (D * s ^ 2) := by
  rcases shape_or_four_pow_dvd hD 4 s with ⟨i, hi, hs⟩ | hd
  · exact ⟨⟨i, hi⟩, hs⟩
  · exact (h hd).elim

theorem smallTwoShape_congr {a b : ℤ} (h : a ≡ b [ZMOD 256]) :
    smallTwoShape a ↔ smallTwoShape b := by
  unfold smallTwoShape
  apply exists_congr
  intro k
  have hd : (4 : ℤ) ^ (k.val + 1) ∣ 256 := by
    fin_cases k <;> decide
  change a % (4 : ℤ) ^ (k.val + 1) = _ ↔ b % (4 : ℤ) ^ (k.val + 1) = _
  rw [(h.of_dvd hd).eq]

theorem prime_dvd_of_odd_valuation {p e : ℕ} (hp : p.Prime) {D s : ℤ} (hD : Squarefree D)
    (hs : s ≠ 0) (he : e % 2 = 1) (h₁ : (p : ℤ)^e ∣ D * s ^ 2)
    (h₂ : ¬(p : ℤ)^(e+1) ∣ D * s ^ 2) : (p : ℤ) ∣ D := by
  let : Fact p.Prime := ⟨hp⟩
  have hne : D * s ^ 2 ≠ 0 := mul_ne_zero hD.ne_zero (pow_ne_zero _ hs)
  have hl := ((padicValInt_dvd_iff e _).mp h₁).resolve_left hne
  have hu : ¬ e + 1 ≤ padicValInt p (D * s ^ 2) := fun h =>
    h₂ ((padicValInt_dvd_iff (e+1) _).mpr (Or.inr h))
  rw [padicValInt.mul hD.ne_zero (pow_ne_zero _ hs), pow_two, padicValInt.mul hs hs] at hl hu
  by_contra hn
  rw [padicValInt.eq_zero_of_not_dvd hn] at hl hu
  omega

end NajmanTrbovic
