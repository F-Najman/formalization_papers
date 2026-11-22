module

public import NajmanTrbovic.Table2Reciprocity

import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-! The strengthened mod-5 assertions for levels 30 and 35. -/

@[expose] public section

namespace NajmanTrbovic

inductive ModFiveCase where
  | n30 | n35
  deriving DecidableEq

def ModFiveCase.normCase : ModFiveCase → NormCase
  | .n30 => .n30_5
  | .n35 => .n35_5

private theorem ramified_factor_square (C : ModFiveCase) {m n : ℤ} (hg : m.gcd n = 1)
    {q : ℕ} (hq : q.Prime) (h₂ : q ≠ 2) (h : (q : ℤ) ∣ C.normCase.level.form m n) :
    IsSquare (q : ZMod 5) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact q.Prime := ⟨hq⟩
  apply (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := q) (by decide) h₂).mpr
  by_contra hn
  have hns : ¬IsSquare (C.normCase.radicand : ZMod q) := by
    cases C <;> simpa [ModFiveCase.normCase, NormCase.radicand] using hn
  exact (form_nonzero_at_prime hq (norm_root_free C.normCase hq h₂ hns) hg)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr h)

private theorem form_val_mod {N : Level} {q : ℕ} [NeZero q] (m n : ℤ) :
    N.form m n ≡ ((N.form (m : ZMod q) (n : ZMod q)).val : ℤ) [ZMOD q] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
  rw [form_mod, Int.cast_natCast, ZMod.natCast_zmod_val]

private theorem primitive_mod {p q : ℕ} (hp : p.Prime) (hd : p ∣ q) {m n : ℤ} (h : m.gcd n = 1) :
    let f := ZMod.castHom hd (ZMod p)
    f (m : ZMod q) ≠ 0 ∨ f (n : ZMod q) ≠ 0 := by
  dsimp only
  rw [map_intCast, map_intCast]
  by_contra! h'
  exact not_both_dvd hp h ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp h'.1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp h'.2⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked_mod32 (C : ModFiveCase) : ∀ a b : ZMod 32,
    let f := ZMod.castHom (by decide : 2 ∣ 32) (ZMod 2)
    f a ≠ 0 ∨ f b ≠ 0 → let v := (C.normCase.level.form a b).val
    v%2=1 ∨ v=16 := by
  cases C <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem checked_mod25 (C : ModFiveCase) : ∀ a b : ZMod 25,
    let f := ZMod.castHom (by decide : 5 ∣ 25) (ZMod 5)
    f a ≠ 0 ∨ f b ≠ 0 → let v := (C.normCase.level.form a b).val
    v%5=1 ∨ v=5 := by
  cases C <;> decide +kernel

private theorem square_factor_mod5 (C : ModFiveCase) {m n s D : ℤ} (hd : Squarefree D)
    (hs : s ≠ 0) (hg : m.gcd n = 1) (he : C.normCase.level.form m n = D*s^2) :
    IsSquare (s : ZMod 5) := by
  let w : ℕ := (C.normCase.level.form (m : ZMod 32) (n : ZMod 32)).val
  have hw := checked_mod32 C (m : ZMod 32) (n : ZMod 32)
    (primitive_mod Nat.prime_two (by decide) hg)
  have hm : D*s^2 ≡ (w : ℤ) [ZMOD 32] := by
    rw [← he]
    exact form_val_mod _ _
  have ht : ∃ t : ℤ, ¬(2 : ℤ) ∣ t ∧ (s = t ∨ s = 4*t) := by
    rcases hw with h | h
    · refine ⟨s, ?_, Or.inl rfl⟩
      intro hs'
      have hf : (2 : ℤ) ∣ D*s^2 := dvd_mul_of_dvd_right (dvd_trans hs' (dvd_pow_self _ (by decide))) _
      have hv := (hm.of_dvd (by decide : (2 : ℤ) ∣ 32)).eq
      change D*s^2 % 2 = (w : ℤ) % 2 at hv
      change w%2=1 at h
      have h' : (w : ℤ)%2=1 := by exact_mod_cast h
      rw [Int.emod_eq_zero_of_dvd hf, h'] at hv
      exact (by decide : (0 : ℤ) ≠ 1) hv
    · change w = 16 at h
      rw [h] at hm
      have hloc := squareclass_of_prime_power_residue (e := 4) (k := 1) Nat.prime_two
        (by decide) hd (by decide : ¬(2 : ℤ) ∣ 1) (by simpa using hm)
      obtain ⟨_, t, ht, ht', _⟩ := hloc.2 (by decide)
      exact ⟨t, ht', Or.inr (by simpa using ht)⟩
  obtain ⟨t, ht, hh⟩ := ht
  have ht₀ : t ≠ 0 := by rcases hh with h | h <;> intro h₀ <;> simp [h,h₀] at hs
  have htS : IsSquare (t : ZMod 5) := by
    apply square_of_prime_divisors ht₀
    · intro _
      exact ⟨2, by decide +kernel⟩
    · intro q hq hqD
      have hq2 : q ≠ 2 := by rintro rfl; exact ht hqD
      have hqs : (q : ℤ) ∣ s := by
        rcases hh with rfl | h
        · exact hqD
        · rw [h]; exact dvd_mul_of_dvd_right hqD _
      apply ramified_factor_square C hg hq hq2
      rw [he]
      exact dvd_mul_of_dvd_right (dvd_trans hqs (dvd_pow_self _ (by decide))) _
  rcases hh with rfl | h
  · exact htS
  · rw [h, Int.cast_mul]
    exact (show IsSquare (4 : ZMod 5) from ⟨2, by decide +kernel⟩).mul htS

/-- The (N=30,35) refinements in Table 2. -/
theorem table2_mod_five (C : ModFiveCase) {D : ℤ} (hD : Represents C.normCase.level D) :
    D%5 = 0 ∨ D%5 = 1 := by
  obtain ⟨hd, _, m, n, s, hg, _, hs, he⟩ := hD
  let w : ℕ := (C.normCase.level.form (m : ZMod 25) (n : ZMod 25)).val
  have hw := checked_mod25 C (m : ZMod 25) (n : ZMod 25)
    (primitive_mod (by decide : Nat.Prime 5) (by decide) hg)
  have hm : D*s^2 ≡ (w : ℤ) [ZMOD 25] := by
    rw [← he]
    exact form_val_mod _ _
  rcases hw with h | h
  · right
    have hv := (hm.of_dvd (by decide : (5 : ℤ) ∣ 25)).eq
    change D*s^2 % 5 = (w : ℤ) % 5 at hv
    change w%5=1 at h
    have hh : (w : ℤ)%5=1 := by exact_mod_cast h
    have hcon : D*s^2 ≡ 1 [ZMOD 5] := hv.trans hh
    have hz := (ZMod.intCast_eq_intCast_iff (D*s^2) 1 5).mpr hcon
    push_cast at hz
    have hs' : (s : ZMod 5) ≠ 0 := by
      intro hn
      simp [hn] at hz
      exact (by decide +kernel : (0 : ZMod 5) ≠ 1) hz
    have hv' : (s : ZMod 5)^2 = 1 := by
      obtain ⟨y, hy⟩ := square_factor_mod5 C hd hs hg he
      have hcert : ∀ x y : ZMod 5, x = y*y → x≠0 → x^2=1 := by decide +kernel
      exact hcert _ y hy hs'
    rw [hv', mul_one] at hz
    exact (ZMod.intCast_eq_intCast_iff' D 1 5).mp hz
  · left
    change w=5 at h
    rw [h] at hm
    have hloc := squareclass_of_prime_power_residue (p := 5) (e := 1) (k := 1)
      (by decide) (by decide) hd (by decide : ¬(5 : ℤ) ∣ 1) (by simpa using hm)
    exact Int.emod_eq_zero_of_dvd (hloc.1 (by decide))

end NajmanTrbovic
