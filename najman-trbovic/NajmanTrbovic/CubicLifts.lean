module

public import NajmanTrbovic.CubicRoots
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms

import Mathlib.Tactic

/-! Hensel lifts on the two projective charts of the cubic fibers. -/

@[expose] public section

noncomputable section

namespace NajmanTrbovic.Cubic

open Polynomial

private theorem norm_lt_one_iff_reduction {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) :
    ‖a‖ < 1 ↔ PadicInt.toZMod a = 0 := by
  rw [PadicInt.norm_lt_one_iff_dvd, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker]

theorem hensel_lift {p : ℕ} [Fact p.Prime] (F : (ℤ_[p])[X]) (r₀ : ZMod p)
    (h₀ : (F.map PadicInt.toZMod).eval r₀ = 0)
    (h₁ : (F.map PadicInt.toZMod).derivative.eval r₀ ≠ 0) :
    ∃ b : ℤ_[p], F.eval b = 0 ∧ PadicInt.toZMod b = r₀ := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let a : ℤ_[p] := r₀.val
  have ha : PadicInt.toZMod a = r₀ := by simp [a]
  have hF : ‖F.eval a‖ < 1 := by
    apply (norm_lt_one_iff_reduction _).mpr
    rw [← eval_map_apply, ha]
    exact h₀
  have hD : ‖F.derivative.eval a‖ = 1 := by
    apply le_antisymm (PadicInt.norm_le_one _)
    by_contra! hl
    apply h₁
    rw [derivative_map, ← ha, eval_map_apply]
    exact (norm_lt_one_iff_reduction _).mp hl
  have hh : ‖F.aeval a‖ < ‖F.derivative.aeval a‖^2 := by
    simp [aeval_def, hD, hF]
  obtain ⟨b, hb, hd, _, _⟩ := hensels_lemma hh
  simp only [aeval_def, Algebra.algebraMap_self, eval₂_id] at hb hd
  rw [hD] at hd
  have hz := (norm_lt_one_iff_reduction _).mp hd
  rw [map_sub, sub_eq_zero, ha] at hz
  exact ⟨b, hb, hz⟩

def finiteChart {R : Type*} [CommRing R] (u w : R) : R[X] :=
  C (r u w) * (X * (X+1)) + C (u*w*(u+w)) * r X 1

def infinityChart {R : Type*} [CommRing R] (u w : R) : R[X] :=
  C (r u w) * (X * (1+X)) + C (u*w*(u+w)) * r 1 X

theorem finite_eval {R : Type*} [CommRing R] (u w v : R) :
    (finiteChart u w).eval v = fibre u w v 1 := by
  simp [finiteChart, fibre, r, mul_comm]

private theorem infinity_eval {R : Type*} [CommRing R] (u w z : R) :
    (infinityChart u w).eval z = fibre u w 1 z := by
  simp [infinityChart, fibre, r, mul_comm]

theorem map_finite {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u w : R) :
    (finiteChart u w).map f = finiteChart (f u) (f w) := by
  simp [finiteChart, r, map_ofNat]

private theorem map_infinity {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u w : R) :
    (infinityChart u w).map f = infinityChart (f u) (f w) := by
  simp [infinityChart, r, map_ofNat]

/-- At a residual pole, the two affine roots and the point at infinity lift to distinct
projective points. The reductions of their normalized coordinates are (0,-1,0). -/
theorem hensel_at_pole {p : ℕ} [Fact p.Prime] (u w : ℤ_[p])
    (hc : PadicInt.toZMod u * PadicInt.toZMod w * (PadicInt.toZMod u + PadicInt.toZMod w) = 0)
    (hr : r (PadicInt.toZMod u) (PadicInt.toZMod w) ≠ 0) :
    ∃ a b c : ℤ_[p], fibre u w a 1 = 0 ∧ fibre u w b 1 = 0 ∧ fibre u w 1 c = 0 ∧
      PadicInt.toZMod a = 0 ∧ PadicInt.toZMod b = -1 ∧ PadicInt.toZMod c = 0 := by
  have hf : (finiteChart u w).map PadicInt.toZMod =
      C (r (PadicInt.toZMod u) (PadicInt.toZMod w)) * (X*(X+1)) := by
    rw [map_finite]
    simp [finiteChart, hc]
  have hi : (infinityChart u w).map PadicInt.toZMod =
      C (r (PadicInt.toZMod u) (PadicInt.toZMod w)) * (X*(1+X)) := by
    rw [map_infinity]
    simp [infinityChart, hc]
  obtain ⟨a, ha, ha₀⟩ := hensel_lift (finiteChart u w) 0
    (by simp [hf]) (by simpa [hf, derivative_mul, derivative_add] using hr)
  obtain ⟨b, hb, hb₀⟩ := hensel_lift (finiteChart u w) (-1)
    (by simp [hf]) (by simpa [hf, derivative_mul, derivative_add] using hr)
  obtain ⟨c, hc', hc₀⟩ := hensel_lift (infinityChart u w) 0
    (by simp [hi]) (by simpa [hi, derivative_mul, derivative_add] using hr)
  exact ⟨a, b, c, (finite_eval _ _ _).symm.trans ha, (finite_eval _ _ _).symm.trans hb,
    (infinity_eval _ _ _).symm.trans hc', ha₀, hb₀, hc₀⟩

theorem hensel_at_two (u w : ℤ_[2]) (h : PadicInt.toZMod u ≠ 0 ∨ PadicInt.toZMod w ≠ 0) :
    ∃ a b c : ℤ_[2], fibre u w a 1 = 0 ∧ fibre u w b 1 = 0 ∧ fibre u w 1 c = 0 ∧
      PadicInt.toZMod a = 0 ∧ PadicInt.toZMod b = -1 ∧ PadicInt.toZMod c = 0 := by
  have aux : ∀ x y : ZMod 2, x ≠ 0 ∨ y ≠ 0 → x*y*(x+y) = 0 ∧ r x y ≠ 0 := by
    decide +kernel
  exact hensel_at_pole u w (aux _ _ h).1 (aux _ _ h).2

private theorem derivative_nonzero {p : ℕ} [Fact p.Prime] (h7 : (7 : ZMod p) ≠ 0)
    {v : ZMod p} (h : r v 1 = 0) : (r (X : (ZMod p)[X]) 1).derivative.eval v ≠ 0 := by
  intro hd
  have he : (r (X : (ZMod p)[X]) 1).derivative.eval v = 3*v^2+2*v-2 := by
    simp [r, derivative_add, derivative_sub, derivative_pow, derivative_mul]
  rw [he] at hd
  apply h7
  dsimp [r] at h
  linear_combination (-6*v-1)*h + (2*v^2+v-3)*hd

/-- At the residual cyclotomic fibers, all three distinct affine roots lift to p-adic roots. -/
theorem hensel_at_cyclotomic_fibre {p : ℕ} [Fact p.Prime] (u w : ℤ_[p])
    (hp7 : p % 7 = 1 ∨ p % 7 = 6) (hr : r (PadicInt.toZMod u) (PadicInt.toZMod w) = 0)
    (hc : PadicInt.toZMod u * PadicInt.toZMod w * (PadicInt.toZMod u + PadicInt.toZMod w) ≠ 0) :
    ∃ a b c : ℤ_[p], fibre u w a 1 = 0 ∧ fibre u w b 1 = 0 ∧ fibre u w c 1 = 0 ∧
      PadicInt.toZMod a ≠ PadicInt.toZMod b ∧ PadicInt.toZMod a ≠ PadicInt.toZMod c ∧
      PadicInt.toZMod b ≠ PadicInt.toZMod c := by
  have hp : p.Prime := Fact.out
  have h7 : (7 : ZMod p) ≠ 0 := by
    change ((7 : ℕ) : ZMod p) ≠ 0
    intro h
    have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp
      ((ZMod.natCast_eq_zero_iff 7 p).mp h)
    subst p
    norm_num at hp7
  obtain ⟨a₀, b₀, c₀, hab, hac, hbc, hsplit⟩ := r_splits_mod_prime hp hp7
  have lift (v : ZMod p) (h : r v 1 = 0) : ∃ z : ℤ_[p], fibre u w z 1 = 0 ∧ PadicInt.toZMod z = v := by
    have hf : (finiteChart u w).map PadicInt.toZMod =
        C (PadicInt.toZMod u * PadicInt.toZMod w * (PadicInt.toZMod u + PadicInt.toZMod w)) *
          r (X : (ZMod p)[X]) 1 := by
      rw [map_finite]
      simp [finiteChart, hr]
    have he : (r (X : (ZMod p)[X]) 1).eval v = r v 1 := by simp [r]
    obtain ⟨z, hz, hz'⟩ := hensel_lift (finiteChart u w) v
      (by rw [hf, eval_mul, he, h, mul_zero])
      (by simpa [hf, derivative_mul] using mul_ne_zero hc (derivative_nonzero h7 h))
    exact ⟨z, (finite_eval _ _ _).symm.trans hz, hz'⟩
  obtain ⟨a, ha, ha'⟩ := lift a₀ (by simp [hsplit])
  obtain ⟨b, hb, hb'⟩ := lift b₀ (by simp [hsplit])
  obtain ⟨c, hc', hc''⟩ := lift c₀ (by simp [hsplit])
  exact ⟨a, b, c, ha, hb, hc', by simpa [ha', hb'] using hab,
    by simpa [ha', hc''] using hac, by simpa [hb', hc''] using hbc⟩

end NajmanTrbovic.Cubic
