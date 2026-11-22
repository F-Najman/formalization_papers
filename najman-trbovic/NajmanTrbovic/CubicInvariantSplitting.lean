module

public import NajmanTrbovic.CubicFieldModel

import NajmanTrbovic.Homogeneous
import Mathlib.Tactic

/-! For the descended family, nonintegrality of the actual j-invariant gives the
p-adic splitting of the cubic field defined by the explicit fiber. -/

@[expose] public section

noncomputable section

namespace NajmanTrbovic.Cubic

open Polynomial
open scoped TensorProduct

private def g2h {R : Type*} [CommRing R] (u w : R) : R := homogeneous u w [1, 1, 1]

private def g6h {R : Type*} [CommRing R] (u w : R) : R :=
  homogeneous u w [1, 5, 12, 9, 2, 1, 1]

private def g12h {R : Type*} [CommRing R] (u w : R) : R :=
  homogeneous u w [1, 8, 25, 34, 6, -30, -17, 6, 0, -4, 3, 4, 1]

private def projectiveNumerator {R : Type*} [CommRing R] (u w : R) : R :=
  (g2h u w)^3 * g6h u w * (g12h u w)^3

private theorem map_projectiveNumerator {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (u w : R) : f (projectiveNumerator u w) = projectiveNumerator (f u) (f w) := by
  simp [projectiveNumerator, g2h, g6h, g12h, map_homogeneous, map_ofNat]

private theorem projectiveNumerator_scale {R : Type*} [CommRing R] (c u w : R) :
    projectiveNumerator (c*u) (c*w) = c^48 * projectiveNumerator u w := by
  simp only [projectiveNumerator, g2h, g6h, g12h, homogeneous_scale,
    List.length_cons, List.length_nil]
  ring

private theorem projectiveNumerator_at_one {R : Type*} [CommRing R] (u : R) :
    projectiveNumerator u 1 = denominator u * g12 u^3 := by
  simp only [projectiveNumerator, g2h, g6h, g12h, homogeneous, one_pow, mul_one, mul_zero,
    add_zero, denominator, g2, g6, g12]
  ring

private theorem projectiveDenominator_scale {R : Type*} [CommRing R] (c u w : R) :
    projectiveDenominator (c*u) (c*w) = c^48 * projectiveDenominator u w := by
  unfold projectiveDenominator r
  ring

private theorem map_projectiveDenominator {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u w : R) : f (projectiveDenominator u w) = projectiveDenominator (f u) (f w) := by
  simp [projectiveDenominator, r, map_ofNat]

private theorem finiteChart_scale {R : Type*} [CommRing R] (c u w : R) :
    finiteChart (c*u) (c*w) = C (c^3)*finiteChart u w := by
  have hr : r (c*u) (c*w) = c^3 * r u w := by unfold r; ring
  have hc : (c*u)*(c*w)*(c*u+c*w) = c^3*(u*w*(u+w)) := by ring
  rw [finiteChart, hr, hc, finiteChart, map_mul, map_mul]
  ring

private theorem jDenominator_ne_zero (x : ℚ) [(descended x).IsElliptic]
    (hd : denominator x ≠ 0) : jDenominator x ≠ 0 := by
  intro h
  have hΔ := (descended_invariants x hd).2
  rw [h, zero_div] at hΔ
  exact (descended x).isUnit_Δ.ne_zero hΔ

private theorem rational_coordinates (x : ℚ) (hj : jDenominator x ≠ 0) :
    x.num.gcd (x.den : ℤ) = 1 ∧ (x.den : ℚ) * x = (x.num : ℚ) ∧
      x.num * (x.den : ℤ) * (x.num + x.den) ≠ 0 := by
  have hw : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hux : (x.den : ℚ)*x = (x.num : ℚ) := by
    rw [mul_comm]
    exact ((div_eq_iff hw).mp x.num_div_den).symm
  have hx : x*(x+1) ≠ 0 := by
    intro h
    rcases mul_eq_zero.mp h with h | h <;> simp [jDenominator, h] at hj
  have hc : (x.num : ℚ)*(x.den : ℚ)*((x.num : ℚ)+x.den) ≠ 0 := by
    rw [← hux, show (x.den : ℚ)*x*x.den*((x.den : ℚ)*x+x.den) =
      (x.den : ℚ)^3*(x*(x+1)) by ring]
    exact mul_ne_zero (pow_ne_zero _ hw) hx
  exact ⟨by simpa [Int.gcd_def] using x.reduced, hux, by exact_mod_cast hc⟩

private theorem j_eq_projective_ratio {p : ℕ} [Fact p.Prime] (x : ℚ) [(descended x).IsElliptic]
    (hd : denominator x ≠ 0) {u w : ℤ} (hux : (w : ℚ)*x = (u : ℚ)) (hw : (w : ℚ) ≠ 0) :
    ((projectiveNumerator (u : ℤ_[p]) (w : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) /
      ((projectiveDenominator (u : ℤ_[p]) (w : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) = (descended x).j := by
  have huxp : (w : ℚ_[p])*(x : ℚ_[p]) = (u : ℚ_[p]) := by exact_mod_cast hux
  have hwp : (w : ℚ_[p]) ≠ 0 := by exact_mod_cast hw
  rw [descended_j x hd (jDenominator_ne_zero x hd)]
  have hpnum : ((projectiveNumerator (u : ℤ_[p]) (w : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) =
      projectiveNumerator (u : ℚ_[p]) (w : ℚ_[p]) := by
    simpa only [PadicInt.Coe.ringHom_apply, PadicInt.coe_intCast] using map_projectiveNumerator
      (PadicInt.Coe.ringHom (p := p)) (u : ℤ_[p]) (w : ℤ_[p])
  have hpden : ((projectiveDenominator (u : ℤ_[p]) (w : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) =
      projectiveDenominator (u : ℚ_[p]) (w : ℚ_[p]) := by
    simpa only [PadicInt.Coe.ringHom_apply, PadicInt.coe_intCast] using map_projectiveDenominator
      (PadicInt.Coe.ringHom (p := p)) (u : ℤ_[p]) (w : ℤ_[p])
  rw [hpnum, hpden]
  calc
    _ = projectiveNumerator ((w : ℚ_[p])*(x : ℚ_[p])) ((w : ℚ_[p])*1) /
        projectiveDenominator ((w : ℚ_[p])*(x : ℚ_[p])) ((w : ℚ_[p])*1) := by rw [huxp, mul_one]
    _ = denominator (x : ℚ_[p]) * g12 (x : ℚ_[p]) ^ 3 / jDenominator (x : ℚ_[p]) := by
      rw [projectiveNumerator_scale, projectiveDenominator_scale, projectiveNumerator_at_one]
      simp only [projectiveDenominator, jDenominator, one_pow, mul_one]
      exact mul_div_mul_left _ _ (pow_ne_zero _ hwp)
    _ = _ := by push_cast [denominator, g2, g6, g12, jDenominator, r]; rfl

/-- For a cubic field generated by a point of the explicit fiber, a nonintegral
j-invariant in the descended family gives complete p-adic splitting at the primes
of Proposition 3.1. -/
theorem cubic_tensor_splits_of_nonintegral_j {p : ℕ} [Fact p.Prime] {K : Type*} [Field K]
    [Algebra ℚ K] [FiniteDimensional ℚ K] (hK : Module.finrank ℚ K = 3) (x : ℚ)
    [(descended x).IsElliptic] (hd : denominator x ≠ 0) (α : K)
    (hα : α ∉ Set.range (algebraMap ℚ K)) (hF : (finiteChart x 1).aeval α = 0)
    (hp : p = 2 ∨ p % 7 = 1 ∨ p % 7 = 6)
    (hj : 1 < ‖((descended x).j : ℚ_[p])‖) :
    Nonempty ((ℚ_[p] ⊗[ℚ] K) ≃ₐ[ℚ_[p]] (Fin 3 → ℚ_[p])) := by
  let u : ℤ := x.num
  let w : ℤ := x.den
  obtain ⟨hg, hux, hc⟩ := rational_coordinates x (jDenominator_ne_zero x hd)
  change u.gcd w = 1 at hg
  change (w : ℚ)*x = (u : ℚ) at hux
  change u*w*(u+w) ≠ 0 at hc
  have hw : (w : ℚ) ≠ 0 := by
    have hw' : w ≠ 0 := by dsimp [w]; exact_mod_cast x.den_nz
    exact_mod_cast hw'
  have hF' : (finiteChart (u : ℚ) (w : ℚ)).aeval α = 0 := by
    calc
      _ = (finiteChart ((w : ℚ)*x) ((w : ℚ)*1)).aeval α := by rw [hux, mul_one]
      _ = 0 := by rw [finiteChart_scale, map_mul, hF, mul_zero]
  apply cubic_tensor_splits_of_nonintegral_ratio hK u w hg hc α hα hF' hp
    (projectiveNumerator (u : ℤ_[p]) (w : ℤ_[p]))
  rw [j_eq_projective_ratio x hd hux hw]
  exact hj

private theorem two_valuation_eq_zero {a : ℤ_[2]} (ha : PadicInt.toZMod a ≠ 0) :
    a.valuation = 0 := by
  have ha₀ : a ≠ 0 := by intro h; simp [h] at ha
  by_contra! h
  apply ha
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
  simpa only [pow_one] using (PadicInt.mem_span_pow_iff_le_valuation a ha₀ 1).mpr (by omega)

/-- The explicit descended model has a pole of positive order divisible by 14 at 2.
This is the j-valuation calculation in Proposition 3.4. -/
theorem valuation_j_at_two (x : ℚ) [(descended x).IsElliptic] (hd : denominator x ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ ((descended x).j : ℚ_[2]).valuation = -14 * (k : ℤ) := by
  obtain ⟨hg, hux, hc⟩ := rational_coordinates x (jDenominator_ne_zero x hd)
  let u : ℤ := x.num
  let w : ℤ := x.den
  change u.gcd w = 1 at hg
  have hux' : (w : ℚ)*x = (u : ℚ) := by exact_mod_cast hux
  have hw : (w : ℚ) ≠ 0 := by
    have hw' : w ≠ 0 := by dsimp [w]; exact_mod_cast x.den_nz
    exact_mod_cast hw'
  have hc' : (u : ℤ_[2])*(w : ℤ_[2])*((u : ℤ_[2])+w) ≠ 0 := by exact_mod_cast hc
  let a : ℤ_[2] := u
  let b : ℤ_[2] := w
  let t := a*b*(a+b)
  have ht : t ≠ 0 := hc'
  have hprim : PadicInt.toZMod a ≠ 0 ∨ PadicInt.toZMod b ≠ 0 := by
    dsimp [a,b]
    exact primitive_padic_reduction hg
  have htest : ∀ s t : ZMod 2, s ≠ 0 ∨ t ≠ 0 →
      r s t = 1 ∧ projectiveNumerator s t = 1 ∧ s*t*(s+t) = 0 := by
    decide +kernel
  obtain ⟨hr, hn, ht₀⟩ := htest _ _ hprim
  have hr' : PadicInt.toZMod (r a b) = 1 := by simpa [r, map_ofNat] using hr
  have hn' : PadicInt.toZMod (projectiveNumerator a b) = 1 := by
    exact (map_projectiveNumerator (PadicInt.toZMod (p := 2)) a b).trans hn
  have htv : 0 < t.valuation := by
    have hzero : PadicInt.toZMod t = 0 := by simpa [t] using ht₀
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p] at hzero
    exact (PadicInt.mem_span_pow_iff_le_valuation t ht 1).mp (by simpa only [pow_one] using hzero)
  have hnonzero : (1 : ZMod 2) ≠ 0 := by decide +kernel
  have hrv : (r a b).valuation = 0 := two_valuation_eq_zero (by rw [hr']; exact hnonzero)
  have hnv : (projectiveNumerator a b).valuation = 0 := two_valuation_eq_zero (by rw [hn']; exact hnonzero)
  have hr₀ : r a b ≠ 0 := by intro h; simp [h] at hr'
  have hn₀ : projectiveNumerator a b ≠ 0 := by intro h; simp [h] at hn'
  have hden : projectiveDenominator a b = t^14 * (r a b)^2 := by
    simp only [projectiveDenominator, t, mul_pow]
  have hdv : (projectiveDenominator a b).valuation = 14*t.valuation := by
    rw [hden, PadicInt.valuation_mul (pow_ne_zero _ ht) (pow_ne_zero _ hr₀),
      PadicInt.valuation_pow, PadicInt.valuation_pow, hrv, mul_zero, add_zero]
  refine ⟨t.valuation, htv, ?_⟩
  rw [← j_eq_projective_ratio x hd hux' hw]
  change (((projectiveNumerator a b : ℤ_[2]) : ℚ_[2]) /
    ((projectiveDenominator a b : ℤ_[2]) : ℚ_[2])).valuation = _
  have hd₀ : projectiveDenominator a b ≠ 0 := by rw [hden]; exact mul_ne_zero (pow_ne_zero _ ht) (pow_ne_zero _ hr₀)
  rw [div_eq_mul_inv, Padic.valuation_mul (PadicInt.coe_ne_zero.mpr hn₀)
    (inv_ne_zero (PadicInt.coe_ne_zero.mpr hd₀)), Padic.valuation_inv, PadicInt.valuation_coe,
    PadicInt.valuation_coe, hnv, hdv]
  push_cast
  ring

end NajmanTrbovic.Cubic
