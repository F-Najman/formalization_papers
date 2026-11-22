module

public import NajmanTrbovic.Squareclasses
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Roots

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Simple-root lifting and infinitude of squareclasses on an arithmetic progression. -/

@[expose] public section

namespace NajmanTrbovic

open Polynomial
open scoped BigOperators

def ExactOne (p : ℕ) (z : ℤ) : Prop := (p : ℤ) ∣ z ∧ ¬(p : ℤ)^2 ∣ z

instance (p : ℕ) (z : ℤ) : Decidable (ExactOne p z) := by unfold ExactOne; infer_instance

theorem eval_congr (f : ℤ[X]) {n : ℕ} {x y : ℤ} (h : x ≡ y [ZMOD n]) :
    f.eval x ≡ f.eval y [ZMOD n] := by
  have he := (ZMod.intCast_eq_intCast_iff x y n).mpr h
  change Int.castRingHom (ZMod n) x = Int.castRingHom (ZMod n) y at he
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
  change Int.castRingHom (ZMod n) (f.eval x) = Int.castRingHom (ZMod n) (f.eval y)
  simp only [← eval_map_apply, he]

theorem exactOne_congr {p : ℕ} {x y : ℤ} (h : x ≡ y [ZMOD (p : ℤ)^2]) :
    ExactOne p x ↔ ExactOne p y := by
  have hd : (p : ℤ) ∣ (p : ℤ)^2 := dvd_pow_self _ (by decide)
  have dvd_iff (m : ℤ) (hm : x ≡ y [ZMOD m]) : m ∣ x ↔ m ∣ y := by
    simp only [← Int.modEq_zero_iff_dvd]
    exact ⟨fun h₀ => hm.symm.trans h₀, fun h₀ => hm.trans h₀⟩
  exact and_congr (dvd_iff _ (h.of_dvd hd)) (not_congr (dvd_iff _ h))

/-- A simple root admits a lift with exact valuation one, even when the step is a unit multiple
of the prime. This version allows us to preserve a previously prescribed congruence. -/
theorem simple_root_lift (f : ℤ[X]) {p : ℕ} (hp : p.Prime) (x step : ℤ)
    (hstep : ¬(p : ℤ) ∣ step) (hx : (p : ℤ) ∣ f.eval x)
    (hderiv : ¬(p : ℤ) ∣ f.derivative.eval x) :
    ExactOne p (f.eval x) ∨ ExactOne p (f.eval (x + (p : ℤ) * step)) := by
  by_cases h : (p : ℤ)^2 ∣ f.eval x
  · right
    obtain ⟨c, he⟩ := f.exists_mul_sq_add_linear_part_eq_eval_add x ((p : ℤ) * step)
    have h₀ : (p : ℤ)^2 ∣ c * ((p : ℤ) * step)^2 := by
      use c * step ^ 2
      ring
    have h₁ : (p : ℤ) ∣ f.derivative.eval x * ((p : ℤ) * step) := ⟨f.derivative.eval x * step, by ring⟩
    refine ⟨he ▸ dvd_add (dvd_add (dvd_trans (dvd_pow_self _ (by decide)) h₀) h₁) hx, ?_⟩
    intro h₂
    have h₃ : (p : ℤ)^2 ∣ f.derivative.eval x * ((p : ℤ) * step) := by
      convert dvd_sub (dvd_sub (he ▸ h₂) h) h₀ using 1
      ring
    obtain ⟨b, hb⟩ := h₃
    have hq : (p : ℤ) ∣ f.derivative.eval x * step := by
      use b
      apply mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)
      linear_combination hb
    have hp' : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
    exact (hp'.dvd_mul.mp hq).elim hderiv hstep
  · exact Or.inl ⟨hx, h⟩

private theorem squareclass_of_exactOne {p : ℕ} (hp : p.Prime) {z : ℤ} (hz : ExactOne p z) :
    ∃ D s : ℤ, Squarefree D ∧ s ≠ 0 ∧ D * s^2 = z ∧ (p : ℤ) ∣ D := by
  obtain ⟨s, D, hs, hD⟩ := exists_sq_mul_squarefree z
  rw [mul_comm] at hs
  have hs₀ : s ≠ 0 := by
    rintro rfl
    simp at hs
    exact hz.2 (hs ▸ dvd_zero _)
  have h := prime_dvd_of_odd_valuation (e := 1) hp hD hs₀ (by decide)
  exact ⟨D, s, hD, hs₀, hs, h (by simpa [hs] using hz.1) (by simpa [hs] using hz.2)⟩

/-- A fixed valuation-one progression of a nonconstant polynomial yields infinitely many
squareclasses if the polynomial admits an integral Bézout certificate with its derivative. -/
theorem infinite_squareclasses (f : ℤ[X]) (hf : f.natDegree ≠ 0) {p : ℕ} (hp : p.Prime)
    (a : ℤ) (ha : ExactOne p (f.eval a)) (U V : ℤ[X]) (c : ℤ) (hc : c ≠ 0)
    (hBezout : U*f + V*f.derivative = Polynomial.C c) :
    Set.Infinite {D : ℤ | Squarefree D ∧ (p : ℤ) ∣ D ∧
      ∃ x s : ℤ, s ≠ 0 ∧ f.eval x = D * s^2} := by
  classical
  let S := {D : ℤ | Squarefree D ∧ (p : ℤ) ∣ D ∧
    ∃ x s : ℤ, s ≠ 0 ∧ f.eval x = D * s^2}
  change S.Infinite
  intro hfin
  let M : ℤ := (p : ℤ) * c * ∏ D ∈ hfin.toFinset, D
  have hM : M ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (by exact_mod_cast hp.ne_zero) hc)
    apply Finset.prod_ne_zero_iff.mpr
    intro D hD
    exact ((hfin.mem_toFinset.mp hD : D ∈ S).1).ne_zero
  have ha₀ : f.eval a ≠ 0 := by
    intro hz
    exact ha.2 (hz.symm ▸ dvd_zero _)
  let b : ℤ := f.eval a * (M * (p : ℤ)^2)
  have hb : b ≠ 0 := mul_ne_zero ha₀ (mul_ne_zero hM (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)))
  let g := f.comp (Polynomial.C b * X + Polynomial.C a)
  have hg : g.natDegree ≠ 0 := by
    dsimp [g]
    rw [natDegree_comp, natDegree_add_C, natDegree_C_mul_X _ hb, mul_one]
    exact hf
  have avoids (r : ℤ) : ∀ᶠ t in Filter.cofinite, g.eval t ≠ r := by
    have hne : g - Polynomial.C r ≠ 0 := by
      intro hh
      exact hg (by rw [sub_eq_zero.mp hh, natDegree_C])
    simpa only [eval_sub, eval_C, sub_ne_zero] using (eventually_eval_ne_zero_cofinite hne)
  obtain ⟨t, ht, ht'⟩ := ((avoids (f.eval a)).and (avoids (-f.eval a))).exists
  let x : ℤ := a + b * t
  have hx : g.eval t = f.eval x := by simp [g, x, add_comm]
  obtain ⟨k, hk⟩ := f.exists_mul_sq_add_linear_part_eq_eval_add a (b*t)
  let v : ℤ := 1 + M * ((p : ℤ)^2*t*f.derivative.eval a + (p : ℤ)^4*f.eval a*M*t^2*k)
  have hv : f.eval x = f.eval a * v := by
    dsimp [x, v, b] at hk ⊢
    linear_combination -hk
  have hv₁ : v.natAbs ≠ 1 := by
    intro h
    have hpm : v = 1 ∨ v = -1 := by omega
    rcases hpm with h1 | h1
    · exact ht (by rw [hx, hv, h1, mul_one])
    · exact ht' (by rw [hx, hv, h1, mul_neg_one])
  obtain ⟨q, hq, hqv⟩ := Nat.exists_prime_and_dvd hv₁
  have hqv' : (q : ℤ) ∣ v := by
    simpa [← Int.natAbs_dvd_natAbs] using hqv
  have hqnM : ¬ (q : ℤ) ∣ M := by
    intro hh
    have hex : (q : ℤ) ∣ v - M * ((p : ℤ)^2*t*f.derivative.eval a + (p : ℤ)^4*f.eval a*M*t^2*k) :=
      dvd_sub hqv' (dvd_mul_of_dvd_left hh _)
    have h1 : v - M * ((p : ℤ)^2*t*f.derivative.eval a + (p : ℤ)^4*f.eval a*M*t^2*k) = 1 := by
      simp [v]
    rw [h1] at hex
    exact hq.not_dvd_one (by exact_mod_cast hex)
  have hqnp : ¬(q : ℤ) ∣ (p : ℤ) := fun h => hqnM (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)
  have hqnc : ¬(q : ℤ) ∣ c := fun h => hqnM (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)
  have hxq : (q : ℤ) ∣ f.eval x := hv.symm ▸ dvd_mul_of_dvd_right hqv' _
  have hderiv : ¬(q : ℤ) ∣ f.derivative.eval x := by
    intro h
    apply hqnc
    have heq := congrArg (Polynomial.eval x) hBezout
    simp only [eval_add, eval_mul, eval_C] at heq
    rw [← heq]
    exact dvd_add (dvd_mul_of_dvd_right hxq _) (dvd_mul_of_dvd_right h _)
  have hstep : ¬(q : ℤ) ∣ (p : ℤ)^2 := by
    have hq' : Prime (q : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hq)
    simpa only [pow_two, hq'.dvd_mul, or_self] using hqnp
  have hxmod : x ≡ a [ZMOD (p : ℤ)^2] := by
    apply Int.modEq_iff_dvd.mpr
    use -f.eval a * M * t
    dsimp [x, b]
    ring
  have lift : ∃ y : ℤ, y ≡ a [ZMOD (p : ℤ)^2] ∧ ExactOne q (f.eval y) := by
    rcases simple_root_lift f hq x ((p : ℤ)^2) hstep hxq hderiv with h | h
    · exact ⟨x, hxmod, h⟩
    · refine ⟨x + (q : ℤ)*(p : ℤ)^2, ?_, h⟩
      apply Int.ModEq.trans _ hxmod
      apply Int.modEq_iff_dvd.mpr
      use -(q : ℤ)
      ring
  obtain ⟨y, hym, hyq⟩ := lift
  have hyp : ExactOne p (f.eval y) := by
    have he : f.eval y ≡ f.eval a [ZMOD (p : ℤ)^2] := by
      have hcast : ((p ^ 2 : ℕ) : ℤ) = (p : ℤ)^2 := by norm_cast
      rw [← hcast] at hym ⊢
      exact eval_congr f hym
    exact (exactOne_congr he).mpr ha
  obtain ⟨D, s, hD, hs, hs', hprime⟩ := squareclass_of_exactOne hp hyp
  have hDmem : D ∈ S := ⟨hD, hprime, y, s, hs, hs'.symm⟩
  have hqD : (q : ℤ) ∣ D := by
    rw [← hs'] at hyq
    exact prime_dvd_of_odd_valuation (e := 1) hq hD hs (by decide)
      (by simpa using hyq.1) (by simpa using hyq.2)
  exact hqnM (dvd_mul_of_dvd_right
    (dvd_trans hqD (Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.mpr hDmem))) _)

end NajmanTrbovic
