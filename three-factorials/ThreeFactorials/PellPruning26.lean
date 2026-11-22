module

public import ThreeFactorials.Approximation26

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-! Exact finite Pell checks after a bound on the middle square variable. -/

@[expose] public section

namespace ThreeFactorials

open Pell

private def unit322 : Solution₁ 322 := Solution₁.mk 323 18 (by decide)

private def unit38 : Solution₁ 38 := Solution₁.mk 37 6 (by decide)

private theorem unit322_fundamental : IsFundamental unit322 := by
  apply fundamental_of_denominator_bound (by decide) (by decide) (by decide)
  intro x y hx hy he
  exact denominator_bound (r := 305) (s := 17) (p := 18) (q := 1) (L := 1)
    he (by omega) hy (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private theorem unit38_fundamental : IsFundamental unit38 := by
  apply fundamental_of_denominator_bound (by decide) (by decide) (by decide)
  intro x y hx hy he
  have h := denominator_bound (r := 6) (s := 1) (p := 7) (q := 1) (L := 1)
    he (by omega) hy (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  exact denominator_bound (r := 6) (s := 1) (p := 31) (q := 5) (L := 2)
    he (by omega) hy h (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

private def pellResidues (d u v m : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1 % m, 0)
  | k + 1 =>
    let (x, y) := pellResidues d u v m k
    ((u * x + d * (v * y)) % m, (u * y + x * v) % m)

private theorem pellResidues_eq {d : ℤ} (f : Solution₁ d) (p : ℤ) (e : ℕ) :
    pellResidues d f.x f.y p e = ((f ^ e).x % p, (f ^ e).y % p) := by
  induction e with
  | zero => simp [pellResidues]
  | succ e ih =>
    rw [pellResidues, ih, pow_succ', Solution₁.x_mul, Solution₁.y_mul]
    refine Prod.ext ?_ ?_
    · exact (((Int.mod_modEq _ _).mul_left f.x).add
        (((Int.mod_modEq _ _).mul_left f.y).mul_left d)).eq
    · have h := (((Int.mod_modEq ((f ^ e).y) p).mul_left f.x).add
        ((Int.mod_modEq ((f ^ e).x) p).mul_right f.y)).eq
      simpa only [mul_comm ((f ^ e).x) f.y] using h

private def tracePasses (d u v b : ℤ) (e : ℕ) (test : ℕ × ℕ) : Bool :=
  let x := (pellResidues d u v test.1 e).1
  (List.range test.2).any fun t => (b * (t : ℤ) ^ 2) % test.1 == x

private theorem tracePasses_of_eq {d b : ℤ} {f : Solution₁ d} {e y : ℕ} {p r : ℕ}
    (hr : 0 < r) (hd : (p : ℤ) ∣ b * (r : ℤ)) (he : (f ^ e).x = b * (y : ℤ) ^ 2) :
    tracePasses d f.x f.y b e (p, r) = true := by
  unfold tracePasses
  rw [pellResidues_eq, he, List.any_eq_true]
  refine ⟨y % r, List.mem_range.mpr (Nat.mod_lt _ hr), ?_⟩
  apply beq_iff_eq.mpr
  have hm : ((y % r : ℕ) : ℤ) ≡ (y : ℤ) [ZMOD (r : ℤ)] :=
    Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _)
  exact (((hm.pow 2).mul_left' (c := b)).of_dvd hd).eq

private def tests322 : List (ℕ × ℕ) := [(361, 19), (29, 29), (137, 137), (139, 139), (127, 127), (97, 97)]

private def tests38 : List (ℕ × ℕ) := [(529, 23), (29, 29), (149, 149), (109, 109), (53, 53)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem sieve322 :
    ∀ e ∈ List.range 500, tests322.all (tracePasses 322 323 18 323 e) = true → e = 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
private theorem sieve38 :
    ∀ e ∈ List.range 140, tests38.all (tracePasses 38 37 6 2737 e) = true → e = 2 := by
  decide +kernel

private theorem pell_x_ge_power {d : ℤ} (hd : 0 ≤ d) {f : Solution₁ d} (hx : 0 < f.x)
    (hy : 0 < f.y) (n : ℕ) : f.x ^ n ≤ (f ^ n).x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hy' : 0 ≤ (f ^ n).y := by
      cases n with
      | zero => simp
      | succ n => exact (Solution₁.y_pow_succ_pos hx hy n).le
    rw [pow_succ', pow_succ', Solution₁.x_mul]
    exact (mul_le_mul_of_nonneg_left ih hx.le).trans
      (le_add_of_nonneg_right (mul_nonneg hd (mul_nonneg hy.le hy')))

private theorem index_lt {d : ℤ} {f : Solution₁ d} (hd : 0 ≤ d) (hy : 0 < f.y)
    {B L k e y s cutoff : ℕ} (hx : (2 : ℤ) ^ s ≤ f.x)
    (hL : (L : ℤ) < 2 ^ k) (hcut : 0 < cutoff)
    (he : (f ^ e).x = (B : ℤ) * (y : ℤ) ^ 2)
    (hbound : B * y ≤ L ^ cutoff) (hB : 0 < B)
    {limit : ℕ} (hl : k * (2 * cutoff) ≤ s * limit) : e < limit := by
  have hx' : 0 < f.x := lt_of_lt_of_le (by positivity) hx
  have hpow : (2 : ℤ) ^ (s * e) ≤ (f ^ e).x := by
    rw [pow_mul]
    exact (pow_le_pow_left₀ (by positivity) hx e).trans (pell_x_ge_power hd hx' hy e)
  have hsq : (B : ℤ) * (y : ℤ) ^ 2 ≤ ((B : ℤ) * (y : ℤ)) ^ 2 := by
    rw [mul_pow, ← one_mul ((B : ℤ) * (y : ℤ) ^ 2)]
    have hB' : (1 : ℤ) ≤ B := by exact_mod_cast hB
    nlinarith only [mul_le_mul_of_nonneg_right hB' (show 0 ≤ (B : ℤ) * (y : ℤ) ^ 2 by positivity)]
  have hBound : (B : ℤ) * (y : ℤ) ≤ (L : ℤ) ^ cutoff := by exact_mod_cast hbound
  have ht' : ((B : ℤ) * (y : ℤ)) ^ 2 ≤ (L : ℤ) ^ (2 * cutoff) := by
    rw [mul_comm 2 cutoff, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hBound 2
  have hlt : (L : ℤ) ^ (2 * cutoff) < (2 : ℤ) ^ (k * (2 * cutoff)) := by
    rw [pow_mul (2 : ℤ) k (2 * cutoff)]
    exact pow_lt_pow_left₀ hL (by positivity) (Nat.mul_ne_zero (by decide : (2 : ℕ) ≠ 0) hcut.ne')
  by_contra! hlim
  have hh := pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2)
    (hl.trans (Nat.mul_le_mul_left s hlim))
  exact (hpow.trans_eq he |>.trans (hsq.trans ht')).not_gt (hlt.trans_le hh)

private theorem middle_coordinates {a b c : ℕ} {x y z : ℕ}
    (hx : a * x ^ 2 = b * y ^ 2 + 1) (hz : c * z ^ 2 + 1 = b * y ^ 2) :
    ((b : ℤ) * (y : ℤ) ^ 2) ^ 2 - ((a * c : ℕ) : ℤ) * ((x : ℤ) * (z : ℤ)) ^ 2 = 1 := by
  have hx' : (a : ℤ) * (x : ℤ) ^ 2 = (b : ℤ) * (y : ℤ) ^ 2 + 1 := by exact_mod_cast hx
  have hz' : (c : ℤ) * (z : ℤ) ^ 2 + 1 = (b : ℤ) * (y : ℤ) ^ 2 := by exact_mod_cast hz
  push_cast
  linear_combination -((b : ℤ) * (y : ℤ) ^ 2 - 1) * hx' -
    (a : ℤ) * (x : ℤ) ^ 2 * hz'

/-- All solutions of the first system in the finite range supplied by the Padé estimate. -/
theorem first_system_of_bound {x y z : ℕ} (hy : 0 < y)
    (hx : x ^ 2 = 323 * y ^ 2 + 1) (hz : 322 * z ^ 2 + 1 = 323 * y ^ 2)
    (hb : 323 * y ≤ errorBase 323 ^ approximationCutoff 323) : x = 18 := by
  have he := middle_coordinates (a := 1) (by simpa using hx) hz
  let g := Solution₁.mk (d := 322) (323 * (y : ℤ) ^ 2) ((x : ℤ) * (z : ℤ)) he
  obtain ⟨e, hg⟩ := unit322_fundamental.eq_pow_of_nonneg (a := g)
    (by dsimp [g]; positivity) (by dsimp [g]; positivity)
  have hg' : (unit322 ^ e).x = 323 * (y : ℤ) ^ 2 := by rw [← hg]; rfl
  have hlim : e < 500 := index_lt (f := unit322) (s := 8) (k := 15)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hg' hb (by decide) (by decide)
  have hall : tests322.all (tracePasses 322 323 18 323 e) = true := by
    apply List.all_eq_true.mpr
    intro p hp
    have hc : ∀ p ∈ tests322, 0 < p.2 ∧ (p.1 : ℤ) ∣ 323 * (p.2 : ℤ) := by decide +kernel
    obtain ⟨hp₀, hp₁⟩ := hc p hp
    exact tracePasses_of_eq (f := unit322) hp₀ hp₁ hg'
  have hre := sieve322 e (List.mem_range.mpr hlim) hall
  rw [hre, pow_one] at hg'
  change (323 : ℤ) = 323 * (y : ℤ) ^ 2 at hg'
  have hys' : (y : ℤ) ^ 2 = 1 := by omega
  have hys : y ^ 2 = 1 := by exact_mod_cast hys'
  rw [hys] at hx
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) (hx.trans (by decide))

/-- All solutions of the second system in the finite range supplied by the Padé estimate. -/
theorem second_system_of_bound {x y z : ℕ} (hy : 0 < y)
    (hx : 2 * x ^ 2 = 2737 * y ^ 2 + 1) (hz : 19 * z ^ 2 + 1 = 2737 * y ^ 2)
    (hb : 2737 * y ≤ errorBase 2737 ^ approximationCutoff 2737) : x = 37 := by
  have he := middle_coordinates hx hz
  let g := Solution₁.mk (d := 38) (2737 * (y : ℤ) ^ 2) ((x : ℤ) * (z : ℤ)) he
  obtain ⟨e, hg⟩ := unit38_fundamental.eq_pow_of_nonneg (a := g)
    (by dsimp [g]; positivity) (by dsimp [g]; positivity)
  have hg' : (unit38 ^ e).x = 2737 * (y : ℤ) ^ 2 := by rw [← hg]; rfl
  have hlim : e < 140 := index_lt (f := unit38) (s := 5) (k := 21)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hg' hb (by decide) (by decide)
  have hall : tests38.all (tracePasses 38 37 6 2737 e) = true := by
    apply List.all_eq_true.mpr
    intro p hp
    have hc : ∀ p ∈ tests38, 0 < p.2 ∧ (p.1 : ℤ) ∣ 2737 * (p.2 : ℤ) := by decide +kernel
    obtain ⟨hp₀, hp₁⟩ := hc p hp
    exact tracePasses_of_eq (f := unit38) hp₀ hp₁ hg'
  rw [sieve38 e (List.mem_range.mpr hlim) hall] at hg'
  change (2737 : ℤ) = 2737 * (y : ℤ) ^ 2 at hg'
  have hys' : (y : ℤ) ^ 2 = 1 := by omega
  have hys : y ^ 2 = 1 := by exact_mod_cast hys'
  rw [hys] at hx
  have hxs : x ^ 2 = 37 ^ 2 := Nat.mul_left_cancel (by decide : 0 < 2) hx
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) hxs

/-- The two simultaneous approximation estimates imply the complete case at 26. -/
theorem case26_iff_of_pade (first : PadeApproximations 323) (second : PadeApproximations 2737)
    (a : ℕ) : Solution a 26 ↔ a = 324 ∨ a = 2738 := by
  constructor
  · intro h
    obtain ⟨x, y, z, _, hy, _, hs⟩ := solution26_remaining h
    have ha' : 29 < a := h.2.1
    have hab : a = a - 1 + 1 := by omega
    have hbc : a - 1 = a - 2 + 1 := by omega
    rcases hs with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
    · left
      have hx : x ^ 2 = 323 * y ^ 2 + 1 := by rw [← ha, ← hb]; exact hab
      have hz : 322 * z ^ 2 + 1 = 323 * y ^ 2 := by rw [← hb, ← hc]; exact hbc.symm
      have hbound := middle_bound_of_pade (a := 1) (x₀ := 18) (z₀ := 1)
        (Or.inl rfl) hy (by decide) (by decide) (by simpa using hx) hz first
      simpa [first_system_of_bound hy hx hz hbound] using ha
    · right
      have hx : 2 * x ^ 2 = 2737 * y ^ 2 + 1 := by rw [← ha, ← hb]; exact hab
      have hz : 19 * z ^ 2 + 1 = 2737 * y ^ 2 := by rw [← hb, ← hc]; exact hbc.symm
      have hbound := middle_bound_of_pade (x₀ := 37) (z₀ := 12)
        (Or.inr rfl) hy (by decide) (by decide) hx hz second
      simpa [second_system_of_bound hy hx hz hbound] using ha
  · rintro (rfl | rfl)
    · exact solution324_26
    · exact solution2738_26

private theorem middle_size_of_a_bound {m a y : ℕ} (hm : m = 323 ∨ m = 2737)
    (ha : a ≤ 10 ^ 190) (he : a - 1 = m * y ^ 2) :
    m * y ≤ errorBase m ^ approximationCutoff m := by
  have hcheck : m * 10 ^ 190 ≤ (errorBase m ^ approximationCutoff m) ^ 2 := by
    rcases hm with rfl | rfl <;> decide
  apply (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2 ≠ 0)).mp
  calc
    (m * y) ^ 2 = m * (a - 1) := by rw [he]; ring
    _ ≤ m * 10 ^ 190 := Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans ha)
    _ ≤ _ := hcheck

/-- Unconditional classification with a finite bound on the largest factorial index. -/
theorem case26_iff_below {a : ℕ} (hsize : a ≤ 10 ^ 190) :
    Solution a 26 ↔ a = 324 ∨ a = 2738 := by
  constructor
  · intro h
    obtain ⟨x, y, z, _, hy, _, hs⟩ := solution26_remaining h
    have ha' : 29 < a := h.2.1
    have hab : a = a - 1 + 1 := by omega
    have hbc : a - 1 = a - 2 + 1 := by omega
    rcases hs with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
    · left
      have hx : x ^ 2 = 323 * y ^ 2 + 1 := by rw [← ha, ← hb]; exact hab
      have hz : 322 * z ^ 2 + 1 = 323 * y ^ 2 := by rw [← hb, ← hc]; exact hbc.symm
      simpa [first_system_of_bound hy hx hz (middle_size_of_a_bound (Or.inl rfl) hsize hb)] using ha
    · right
      have hx : 2 * x ^ 2 = 2737 * y ^ 2 + 1 := by rw [← ha, ← hb]; exact hab
      have hz : 19 * z ^ 2 + 1 = 2737 * y ^ 2 := by rw [← hb, ← hc]; exact hbc.symm
      simpa [second_system_of_bound hy hx hz (middle_size_of_a_bound (Or.inr rfl) hsize hb)] using ha
  · rintro (rfl | rfl)
    · exact solution324_26
    · exact solution2738_26

end ThreeFactorials
