module

public import NajmanTrbovic.LocalSquareclasses
public import NajmanTrbovic.NormObstruction

import Mathlib.Tactic

/-! Prime-power computations for the local assertions in Table 2. -/

@[expose] public section

namespace NajmanTrbovic

private theorem lower_precision {p k e j a : ℕ} {D s : ℤ}
    (h : D*s^2 ≡ (a : ℤ) [ZMOD (p : ℤ)^k]) (he : p^e ∣ a) (hej : e+j ≤ k) :
    D*s^2 ≡ (p : ℤ)^e * ((a/p^e : ℕ) : ℤ) [ZMOD (p : ℤ)^(e+j)] := by
  have ha : (p : ℤ)^e * ((a/p^e : ℕ) : ℤ) = (a : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' he
  rw [ha]
  exact h.of_dvd (pow_dvd_pow _ hej)

inductive OddLocalCase where
  | n26p13 | n28p7 | n30p5 | n35p5 | n39p3 | n50p5
  deriving DecidableEq

def OddLocalCase.level : OddLocalCase → Level
  | .n26p13 => .n26
  | .n28p7 => .n28
  | .n30p5 => .n30
  | .n35p5 => .n35
  | .n39p3 => .n39
  | .n50p5 => .n50

def OddLocalCase.prime : OddLocalCase → ℕ
  | .n26p13 => 13
  | .n28p7 => 7
  | .n30p5 | .n35p5 | .n50p5 => 5
  | .n39p3 => 3

def OddLocalCase.precision : OddLocalCase → ℕ
  | .n39p3 => 4
  | _ => 2

private def OddCert (p k a : ℕ) : Prop := ∃ e : Fin k,
  p^e.val ∣ a ∧ ¬p ∣ a/p^e.val ∧
    (e.val % 2 = 1 ∨ FiniteSquare p ((a/p^e.val : ℕ) : ℤ))

private instance (p k a : ℕ) : Decidable (OddCert p k a) := by
  unfold OddCert
  infer_instance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem odd_charts (C : OddLocalCase) : ∀ x : Fin (C.prime^C.precision),
    let t : ZMod (C.prime^C.precision) := x.val
    OddCert C.prime C.precision (C.level.form t 1).val ∧
      OddCert C.prime C.precision (C.level.form 1 t).val := by
  cases C <;> decide +kernel

private theorem square_cast_of_oddCert {D s : ℤ} (hd : Squarefree D) {p k a : ℕ}
    (hp : p.Prime) (h : D*s^2 ≡ (a : ℤ) [ZMOD (p : ℤ)^k]) (hc : OddCert p k a) :
    IsSquare (D : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, he, hunit, hpar⟩ := hc
  have hu : ¬(p : ℤ) ∣ ((a/p^e.val : ℕ) : ℤ) := by exact_mod_cast hunit
  have hloc := squareclass_of_prime_power_residue hp (k := 1) (by decide) hd hu
    (lower_precision h he e.isLt)
  by_cases hodd : e.val % 2 = 1
  · rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hloc.1 hodd)]
    exact IsSquare.zero
  · obtain ⟨t, ht⟩ := hpar.resolve_left hodd
    obtain ⟨_, w, _, hw, hw'⟩ := hloc.2 (by omega)
    rw [pow_one] at hw'
    have heq := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hw'
    push_cast at heq
    have hw₀ : (w : ZMod p) ≠ 0 := fun hz => hw ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp hz)
    refine ⟨(t.val : ZMod p) / (w : ZMod p), ?_⟩
    rw [← pow_two, div_pow, eq_div_iff (pow_ne_zero _ hw₀), heq]
    exact_mod_cast ht

theorem table2_odd_local_not_inert (C : OddLocalCase) {D : ℤ}
    (hD : Represents C.level D) : IsSquare (D : ZMod C.prime) := by
  have hp : C.prime.Prime := by cases C <;> decide
  have hk : 0 < C.precision := by cases C <;> decide
  obtain ⟨x, s, h | h⟩ := normalized_squareclass hD hp hk
  · exact square_cast_of_oddCert hD.1 hp h (odd_charts C x).1
  · exact square_cast_of_oddCert hD.1 hp h (odd_charts C x).2

inductive TwoConclusion where
  | notInert | split | odd
  deriving DecidableEq

def TwoConclusion.holds (c : TwoConclusion) (D : ℤ) : Prop :=
  match c with
  | .notInert => D % 8 = 1 ∨ D % 8 = 2 ∨ D % 8 = 6
  | .split => D % 8 = 1
  | .odd => D % 2 = 1

inductive TwoCase where
  | n22 | n26 | n29 | n30 | n33 | n35 | n39 | n40 | n46 | n48 | n50
  deriving DecidableEq

def TwoCase.level : TwoCase → Level
  | .n22 => .n22
  | .n26 => .n26
  | .n29 => .n29
  | .n30 => .n30
  | .n33 => .n33
  | .n35 => .n35
  | .n39 => .n39
  | .n40 => .n40
  | .n46 => .n46
  | .n48 => .n48
  | .n50 => .n50

def TwoCase.conclusion : TwoCase → TwoConclusion
  | .n22 => .notInert
  | .n30 | .n33 | .n40 | .n46 | .n48 => .split
  | _ => .odd

private def TwoCert (c : TwoConclusion) (a : ℕ) : Prop := ∃ i : Fin 7,
  let e := i.val
  (e%2 = 0 ∧ a % 2^(e+1) = 2^e ∧ c = .odd) ∨
  (e%2 = 0 ∧ a % 2^(e+3) = 2^e) ∨
  (e%2 = 1 ∧ a % 2^(e+1) = 2^e ∧ c = .notInert)

private instance (c : TwoConclusion) (a : ℕ) : Decidable (TwoCert c a) := by
  unfold TwoCert
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem two_charts (C : TwoCase) : ∀ x : Fin 512,
    let t : ZMod 512 := x.val
    TwoCert C.conclusion (C.level.form t 1).val ∧ TwoCert C.conclusion (C.level.form 1 t).val := by
  cases C <;> decide +kernel

private theorem two_congr {a e j : ℕ} {D s : ℤ} (h : D*s^2 ≡ (a : ℤ) [ZMOD 512])
    (he : a % 2^(e+j) = 2^e) (heb : e+j ≤ 9) :
    D*s^2 ≡ (2 : ℤ)^e*1 [ZMOD (2 : ℤ)^(e+j)] := by
  rw [mul_one]
  apply (h.of_dvd (show (2 : ℤ)^(e+j) ∣ 512 from pow_dvd_pow _ heb)).trans
  have ha : (a : ℤ) % (2 : ℤ)^(e+j) = (2 : ℤ)^e := by exact_mod_cast he
  change _ % _ = _ % _
  rw [ha, ← ha, Int.emod_emod]

private theorem odd_square_zmod8 {z : ℤ} (hz : ¬(2 : ℤ) ∣ z) : (z : ZMod 8)^2 = 1 := by
  let f := ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)
  have h : ∀ x : ZMod 8, f x ≠ 0 → x^2 = 1 := by decide +kernel
  apply h
  rw [map_intCast]
  exact fun h0 => hz ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp h0)

private theorem two_result {D s : ℤ} (hd : Squarefree D) {c : TwoConclusion} {a : ℕ}
    (h : D*s^2 ≡ (a : ℤ) [ZMOD 512]) (hc : TwoCert c a) : c.holds D := by
  obtain ⟨i, ⟨he, ha, rfl⟩ | ⟨he, ha⟩ | ⟨he, ha, rfl⟩⟩ := hc
  · have h₂ := squareclass_of_prime_power_residue Nat.prime_two (k := 1) (by decide) hd
      (by decide : ¬(2 : ℤ) ∣ 1) (two_congr h ha (by have := i.isLt; omega))
    have hh := (h₂.2 he).1
    change D%2=1
    omega
  · have h₂ := squareclass_of_prime_power_residue Nat.prime_two (k := 3) (by decide) hd
      (by decide : ¬(2 : ℤ) ∣ 1) (two_congr h ha (by have := i.isLt; omega))
    obtain ⟨_, w, _, hw, hh⟩ := h₂.2 he
    change D*w^2 ≡ 1 [ZMOD 8] at hh
    have heq := (ZMod.intCast_eq_intCast_iff (D*w^2) 1 8).mpr hh
    rw [Int.cast_mul, Int.cast_pow, odd_square_zmod8 hw, mul_one] at heq
    have hD := (ZMod.intCast_eq_intCast_iff' D 1 8).mp heq
    change D % 8 = 1 at hD
    cases c
    · exact Or.inl hD
    · exact hD
    · change D%2=1
      omega
  · have h₂ := squareclass_of_prime_power_residue Nat.prime_two (k := 1) (by decide) hd
      (by decide : ¬(2 : ℤ) ∣ 1) (two_congr h ha (by have := i.isLt; omega))
    have hh := h₂.1 he
    have h4 : ¬ (4 : ℤ) ∣ D := Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
    change D % 8 = 1 ∨ D % 8 = 2 ∨ D % 8 = 6
    omega

theorem table2_two (C : TwoCase) {D : ℤ} (hD : Represents C.level D) : C.conclusion.holds D := by
  obtain ⟨x, s, h | h⟩ := normalized_squareclass hD Nat.prime_two (k := 9) (by decide)
  · exact two_result hD.1 h (two_charts C x).1
  · exact two_result hD.1 h (two_charts C x).2

end NajmanTrbovic
