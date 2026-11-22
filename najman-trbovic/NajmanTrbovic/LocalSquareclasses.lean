module

public import NajmanTrbovic.Table7

import Mathlib.Tactic

/-! Squareclasses in the two projective charts modulo a prime power. -/

@[expose] public section

namespace NajmanTrbovic

/-- A primitive represented squareclass can be tested on either one of the two normalized charts. -/
theorem normalized_squareclass {N : Level} {D : ℤ} (hD : Represents N D)
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    ∃ (x : Fin (p^k)) (s : ℤ), let v : ZMod (p^k) := x.val
      D*s^2 ≡ ((N.form v 1).val : ℤ) [ZMOD (p : ℤ)^k] ∨
      D*s^2 ≡ ((N.form 1 v).val : ℤ) [ZMOD (p : ℤ)^k] := by
  obtain ⟨_, _, m, n, s, hg, _, _, he⟩ := hD
  let q := p^k
  let : NeZero q := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hF : N.form (m : ZMod q) (n : ZMod q) = (D : ZMod q) * (s : ZMod q)^2 := by
    rw [← form_mod, he, Int.cast_mul, Int.cast_pow]
  have hscaled (c : ZMod q) : N.form (c*(m : ZMod q)) (c*(n : ZMod q)) =
      (D : ZMod q) * (c ^ ((N.coefficients.length-1)/2) * (s : ZMod q))^2 := by
    rw [form_scale, hF]
    ring
  have convert_val (v w : ZMod q) (h : v = (D : ZMod q) * w^2) :
      D * (w.val : ℤ)^2 ≡ (v.val : ℤ) [ZMOD (p : ℤ)^k] := by
    have hc : ((q : ℕ) : ℤ) = (p : ℤ)^k := by simp [q]
    rw [← hc]
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, ZMod.natCast_zmod_val] using h.symm
  by_cases hn : (p : ℤ) ∣ n
  · have hm : ¬(p : ℤ) ∣ m := fun h => not_both_dvd hp hg ⟨h, hn⟩
    obtain ⟨u, hu⟩ := isUnit_cast_of_not_dvd hp hk hm
    have h₁ : (↑u⁻¹ : ZMod q)*(m : ZMod q) = 1 := by rw [← hu]; simp
    obtain ⟨t, ht⟩ := residue_cases ((↑u⁻¹ : ZMod q)*(n : ZMod q))
    have h := hscaled ↑u⁻¹
    rw [h₁, ← ht] at h
    exact ⟨t, _, Or.inr (convert_val _ _ h)⟩
  · obtain ⟨u, hu⟩ := isUnit_cast_of_not_dvd hp hk hn
    have h₁ : (↑u⁻¹ : ZMod q)*(n : ZMod q) = 1 := by rw [← hu]; simp
    obtain ⟨t, ht⟩ := residue_cases ((↑u⁻¹ : ZMod q)*(m : ZMod q))
    have h := hscaled ↑u⁻¹
    rw [h₁, ← ht] at h
    exact ⟨t, _, Or.inl (convert_val _ _ h)⟩

/-- Removing an exact prime power from a squareclass leaves a unit. At even valuation the
remaining unit is the radicand times a unit square. -/
theorem squareclass_of_prime_power_residue {p e k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {D s u : ℤ} (hD : Squarefree D) (hu : ¬(p : ℤ) ∣ u)
    (h : D*s^2 ≡ (p : ℤ)^e*u [ZMOD (p : ℤ)^(e+k)]) :
    (e % 2 = 1 → (p : ℤ) ∣ D) ∧
    (e % 2 = 0 → ¬(p : ℤ) ∣ D ∧ ∃ t : ℤ,
      s = (p : ℤ)^(e/2)*t ∧ ¬(p : ℤ) ∣ t ∧ D*t^2 ≡ u [ZMOD (p : ℤ)^k]) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp h
  let v := u - (p : ℤ)^k*c
  have hf : D*s^2 = (p : ℤ)^e*v := by
    dsimp [v]
    rw [pow_add] at hc
    linear_combination -hc
  have hv : ¬(p : ℤ) ∣ v := by
    intro hv
    have hd := dvd_add hv (dvd_mul_of_dvd_left (dvd_pow_self (p : ℤ) hk.ne') c)
    apply hu
    simpa [v] using hd
  have hv₀ : v ≠ 0 := fun he => hv (he.symm ▸ dvd_zero _)
  have hp₀ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hs₀ : s ≠ 0 := by
    rintro rfl
    apply mul_ne_zero (pow_ne_zero _ hp₀) hv₀
    simpa using hf.symm
  have hpow (z : ℤ) (n : ℕ) : padicValInt p (z^n) = n * padicValInt p z := by
    simp [padicValInt, Int.natAbs_pow, padicValNat.pow]
  have hval : padicValInt p D + 2*padicValInt p s = e := by
    have hh := congrArg (padicValInt p) hf
    rw [padicValInt.mul hD.ne_zero (pow_ne_zero _ hs₀), hpow,
      padicValInt.mul (pow_ne_zero _ hp₀) hv₀, hpow, padicValInt_self,
      padicValInt.eq_zero_of_not_dvd hv, mul_one, add_zero] at hh
    exact hh
  have hd : padicValInt p D ≤ 1 := by
    by_contra! ht
    exact Int.squarefree_iff_prime_sq_not_dvd.mp hD p hp
      ((padicValInt_dvd_iff 2 D).mpr (Or.inr (by omega)))
  constructor
  · intro ho
    have hh : (p : ℤ)^1 ∣ D := (padicValInt_dvd_iff 1 D).mpr (Or.inr (by omega))
    simpa using hh
  · intro he
    have hDval : padicValInt p D = 0 := by omega
    have hD' : ¬ (p : ℤ) ∣ D := by
      intro hdiv
      have hd' := (padicValInt_dvd_iff 1 D).mp (by simpa using hdiv)
      exact (hd'.resolve_left hD.ne_zero).not_gt (by rw [hDval]; decide)
    obtain ⟨t, ht⟩ := padicValInt_dvd (p := p) s
    have hex : e = 2 * padicValInt p s := by omega
    have ht' : D*t^2 = v := by
      apply mul_left_cancel₀ (pow_ne_zero e hp₀)
      calc
        _ = D*((p : ℤ)^padicValInt p s*t)^2 := by
          rw [mul_pow, ← pow_mul, Nat.mul_comm (padicValInt p s), ← hex]
          ring
        _ = D*s^2 := congrArg (fun v : ℤ => D*v^2) ht.symm
        _ = _ := hf
    have hmod : D*t^2 ≡ u [ZMOD (p : ℤ)^k] := by
      rw [ht']
      apply Int.modEq_iff_dvd.mpr
      exact ⟨c, by dsimp [v]; ring⟩
    have hts : s = (p : ℤ)^(e/2)*t := by rw [show e/2 = padicValInt p s by omega]; exact ht
    exact ⟨hD', t, hts, (fun hdiv => hv (ht' ▸ dvd_mul_of_dvd_right
      (dvd_trans hdiv (dvd_pow_self t (by decide : 2 ≠ 0))) D)), hmod⟩

end NajmanTrbovic
