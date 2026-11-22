module

public import Mathlib.Data.Nat.Squarefree

import Mathlib.Tactic

/-! A fourth power of a positive Pell unit has nonsquare trace. -/

@[expose] public section

namespace ThreeFactorials

private theorem odd_of_pow_mod_two {a k : ℕ} (h : a ^ k % 2 = 1) (hk : k ≠ 0) :
    a % 2 = 1 := by
  by_contra! he
  have hz : a % 2 = 0 := by omega
  have hmod := (Nat.mod_modEq a 2).pow k
  simp [Nat.ModEq, hz, h, hk] at hmod

private theorem coprime_factor_pow {a b c k : ℕ} (hcop : a.Coprime b) (he : a * b = c ^ k) :
    ∃ x : ℕ, a = x ^ k := by
  apply exists_eq_pow_of_mul_eq_pow ?_ he
  rw [gcd_eq_nat_gcd, hcop.gcd_eq_one]
  exact isUnit_one

/-- The only possible fourth power in a solution of `r⁴ − 2w² = 1` is 1. -/
private theorem quartic_two {r w : ℕ} (he : r ^ 4 = 2 * w ^ 2 + 1) : r = 1 := by
  have hr : r % 2 = 1 := odd_of_pow_mod_two (by omega : r ^ 4 % 2 = 1) (by decide)
  have hrpos : 1 ≤ r := by omega
  obtain ⟨t, ht⟩ : ∃ t : ℕ, r = 2 * t + 1 := ⟨r / 2, by omega⟩
  let m := 2 * (t ^ 2 + t) + 1
  have hm : 2 * m = r ^ 2 + 1 := by dsimp [m]; rw [ht]; ring
  have hmOdd : m % 2 = 1 := by dsimp [m]; omega
  have hrs : 1 ≤ r ^ 2 := by simpa using pow_le_pow_left' hrpos 2
  have hc : (r ^ 2 - 1).Coprime m := by
    by_contra hc
    obtain ⟨p, hp, hd₁, hd₂⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hd₃ : p ∣ 2 * m := dvd_mul_of_dvd_right hd₂ _
    rw [hm] at hd₃
    have hd := Nat.dvd_sub hd₃ hd₁
    rw [show r ^ 2 + 1 - (r ^ 2 - 1) = 2 by omega] at hd
    have hp2 : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hp.ne_one
    subst p
    exact (by omega : ¬2 ∣ m) hd₂
  have hprod : (r ^ 2 - 1) * m = w ^ 2 := by
    have hcast : (2 : ℤ) * ((r : ℤ) ^ 2 - 1) * (m : ℤ) = 2 * (w : ℤ) ^ 2 := by
      have he' : (r : ℤ) ^ 4 = 2 * (w : ℤ) ^ 2 + 1 := by exact_mod_cast he
      have hm' : 2 * (m : ℤ) = (r : ℤ) ^ 2 + 1 := by exact_mod_cast hm
      linear_combination he' + ((r : ℤ) ^ 2 - 1) * hm'
    apply Nat.mul_left_cancel (by decide : 0 < 2)
    zify [hrs]
    exact (by simpa [mul_assoc] using hcast)
  obtain ⟨s, hs⟩ := coprime_factor_pow hc hprod
  have hs' : r ^ 2 = s ^ 2 + 1 := by omega
  have hslt : s < r := by
    by_contra! hb
    have := pow_le_pow_left' hb 2
    omega
  have hgap := pow_le_pow_left' (show s + 1 ≤ r by omega) 2
  have hs0 : s = 0 := by nlinarith only [hgap, hs']
  have hr2 : r ^ 2 = 1 := by simpa [hs0] using hs'
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) (by simpa using hr2)

private theorem no_quartic_from_factors {u a b : ℕ} (hu : 1 < u)
    (h₁ : 2 * a + b + 1 = 4 * u ^ 2) (h₂ : a * b = u ^ 4) : False := by
  have hc : a.Coprime b := by
    by_contra hc
    obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hpu : p ∣ u := hp.dvd_of_dvd_pow (h₂ ▸ dvd_mul_of_dvd_left hpa b)
    have hpd : p ∣ 4 * u ^ 2 := dvd_mul_of_dvd_right (hpu.trans (dvd_pow_self u (by decide))) _
    rw [← h₁] at hpd
    have hpa' := Nat.dvd_add (dvd_mul_of_dvd_right hpa 2) hpb
    have hf := Nat.dvd_sub hpd hpa'
    exact hp.not_dvd_one (by simpa using hf)
  obtain ⟨x, hx⟩ := coprime_factor_pow hc h₂
  obtain ⟨y, hy⟩ := coprime_factor_pow hc.symm (by simpa [mul_comm] using h₂)
  have hxy : x * y = u := by
    apply Nat.pow_left_injective (by decide : 4 ≠ 0)
    simpa [hx, hy, mul_pow] using h₂
  have h₁' : 2 * (x : ℤ) ^ 4 + (y : ℤ) ^ 4 + 1 = 4 * ((x : ℤ) * (y : ℤ)) ^ 2 := by
    rw [hx, hy, ← hxy] at h₁
    exact_mod_cast h₁
  let w : ℤ := (y : ℤ) ^ 2 - (x : ℤ) ^ 2
  have hq : (y : ℤ) ^ 4 = 2 * (w.natAbs : ℤ) ^ 2 + 1 := by
    rw [Int.natCast_natAbs, sq_abs]
    dsimp [w]
    linear_combination -h₁'
  have hy1 := quartic_two (show y ^ 4 = 2 * w.natAbs ^ 2 + 1 by exact_mod_cast hq)
  have hx1 : x = 1 := by
    have hw : w = 0 := by simpa [hy1] using hq
    have hx2 : x ^ 2 = 1 := by
      have hx2' : (x : ℤ) ^ 2 = 1 := by dsimp [w] at hw; rw [hy1] at hw; norm_num at hw; omega
      exact_mod_cast hx2'
    exact Nat.pow_left_injective (by decide : 2 ≠ 0) (by simpa using hx2)
  simp [hx1, hy1] at hxy
  omega

/-- Cohn's elementary exclusion of a square trace at a fourth power. -/
theorem no_square_fourth_trace {u v : ℕ} (hu : 1 < u) :
    v ^ 2 + 8 * u ^ 2 ≠ 8 * u ^ 4 + 1 := by
  intro he
  have hvOdd : v % 2 = 1 := odd_of_pow_mod_two (by omega : v ^ 2 % 2 = 1) (by decide)
  let L := 4 * u ^ 2 - 1
  have hL : L + 1 = 4 * u ^ 2 := by
    have h := pow_pos (show 0 < u by omega) 2
    dsimp [L]
    omega
  have hL2 : L ^ 2 = v ^ 2 + 8 * u ^ 4 := by
    have hL' : (L : ℤ) + 1 = 4 * (u : ℤ) ^ 2 := by exact_mod_cast hL
    have he' : (v : ℤ) ^ 2 + 8 * (u : ℤ) ^ 2 = 8 * (u : ℤ) ^ 4 + 1 := by exact_mod_cast he
    have h' : (L : ℤ) ^ 2 = (v : ℤ) ^ 2 + 8 * (u : ℤ) ^ 4 := by
      linear_combination ((L : ℤ) + 4 * (u : ℤ) ^ 2 - 1) * hL' - he'
    exact_mod_cast h'
  have hv : v < L := by
    by_contra! hd
    have hpos := pow_pos (show 0 < u by omega) 4
    have h := pow_le_pow_left' hd 2
    omega
  let P := L + v
  let Q := L - v
  have hsum : P + Q = 2 * L := by dsimp [P, Q]; omega
  have hprod : P * Q = 8 * u ^ 4 := by
    have hL2' : (L : ℤ) ^ 2 = (v : ℤ) ^ 2 + 8 * (u : ℤ) ^ 4 := by exact_mod_cast hL2
    have hprod' : ((L : ℤ) + v) * ((L : ℤ) - v) = 8 * (u : ℤ) ^ 4 := by
      linear_combination hL2'
    exact_mod_cast (show (P : ℤ) * (Q : ℤ) = 8 * (u : ℤ) ^ 4 by
      simpa [P, Q, Nat.cast_sub hv.le] using hprod')
  have hpar : (P % 4 = 0 ∧ Q % 4 = 2) ∨ (Q % 4 = 0 ∧ P % 4 = 2) := by
    dsimp [P, Q]
    omega
  obtain ⟨a, b, ha, heq⟩ :
      ∃ a b : ℕ, 2 * a + b + 1 = 4 * u ^ 2 ∧ 8 * (a * b) = P * Q := by
    rcases hpar with hpar | hpar
    · have hP : P = 4 * (P / 4) := by omega
      have hQ : Q = 2 * (Q / 2) := by omega
      refine ⟨P / 4, Q / 2, by omega, ?_⟩
      calc
        _ = (4 * (P / 4)) * (2 * (Q / 2)) := by ring
        _ = _ := by rw [← hP, ← hQ]
    · have hQ : Q = 4 * (Q / 4) := by omega
      have hP : P = 2 * (P / 2) := by omega
      refine ⟨Q / 4, P / 2, by omega, ?_⟩
      calc
        _ = (2 * (P / 2)) * (4 * (Q / 4)) := by ring
        _ = _ := by rw [← hP, ← hQ]
  exact no_quartic_from_factors hu ha (by omega)

end ThreeFactorials
