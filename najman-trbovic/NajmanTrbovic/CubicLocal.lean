module

public import NajmanTrbovic.CubicLifts

import Mathlib.Tactic

/-! A local splitting statement for the explicit cubic, in projective coordinates. -/

@[expose] public section

namespace NajmanTrbovic.Cubic

def projectiveDenominator {R : Type*} [CommRing R] (u w : R) : R :=
  u^14 * w^14 * (u+w)^14 * (r u w)^2

def DistinctReductions {p : ℕ} [Fact p.Prime] (a b : ℤ_[p] × ℤ_[p]) : Prop :=
  PadicInt.toZMod a.1 * PadicInt.toZMod b.2 - PadicInt.toZMod b.1 * PadicInt.toZMod a.2 ≠ 0

def ThreeProjectiveLifts {p : ℕ} [Fact p.Prime] (u w : ℤ_[p]) : Prop :=
  ∃ a b c : ℤ_[p] × ℤ_[p], fibre u w a.1 a.2 = 0 ∧ fibre u w b.1 b.2 = 0 ∧
    fibre u w c.1 c.2 = 0 ∧ DistinctReductions a b ∧ DistinctReductions a c ∧ DistinctReductions b c

private theorem root_ne_at_pole {K : Type*} [Field K] {u w : K} (hw : u ≠ 0 ∨ w ≠ 0)
    (hc : u*w*(u+w) = 0) : r u w ≠ 0 := by
  rcases mul_eq_zero.mp hc with h | h
  · rcases mul_eq_zero.mp h with rfl | rfl
    · simpa [r] using hw
    · simpa [r] using hw
  · have hw' : w ≠ 0 := by
      intro hz
      have huz : u = 0 := by simpa [hz] using h
      exact hw.elim (fun hn => hn huz) (fun hn => hn hz)
    have hu : u = -w := eq_neg_of_add_eq_zero_left h
    rw [hu, show r (-w) w = w^3 by unfold r; ring]
    exact pow_ne_zero _ hw'

private theorem three_of_pole {p : ℕ} [Fact p.Prime] (u w : ℤ_[p])
    (hw : PadicInt.toZMod u ≠ 0 ∨ PadicInt.toZMod w ≠ 0)
    (hc : PadicInt.toZMod u * PadicInt.toZMod w * (PadicInt.toZMod u + PadicInt.toZMod w) = 0) :
    ThreeProjectiveLifts u w := by
  obtain ⟨a, b, c, ha, hb, hc', ha₀, hb₀, hc₀⟩ := hensel_at_pole u w hc (root_ne_at_pole hw hc)
  exact ⟨(a, 1), (b, 1), (1, c), ha, hb, hc', by simp [DistinctReductions, ha₀, hb₀],
    by simp [DistinctReductions, ha₀, hc₀], by simp [DistinctReductions, hb₀, hc₀]⟩

theorem threeProjectiveLifts_at_two (u w : ℤ_[2])
    (hw : PadicInt.toZMod u ≠ 0 ∨ PadicInt.toZMod w ≠ 0) : ThreeProjectiveLifts u w := by
  obtain ⟨a, b, c, ha, hb, hc, ha₀, hb₀, hc₀⟩ := hensel_at_two u w hw
  exact ⟨(a, 1), (b, 1), (1, c), ha, hb, hc, by simp [DistinctReductions, ha₀, hb₀],
    by simp [DistinctReductions, ha₀, hc₀], by simp [DistinctReductions, hb₀, hc₀]⟩

/-- For the explicit model, a nonintegral ratio with the projective j-denominator forces
three distinct projective p-adic lifts at the indicated odd primes. -/
theorem threeProjectiveLifts_of_nonintegral_ratio {p : ℕ} [Fact p.Prime]
    (u w numerator : ℤ_[p]) (hw : PadicInt.toZMod u ≠ 0 ∨ PadicInt.toZMod w ≠ 0)
    (hp : p % 7 = 1 ∨ p % 7 = 6)
    (h : 1 < ‖(numerator : ℚ_[p]) / ((projectiveDenominator u w : ℤ_[p]) : ℚ_[p])‖) :
    ThreeProjectiveLifts u w := by
  have hz : PadicInt.toZMod (projectiveDenominator u w) = 0 := by
    by_contra hn
    have hb : ‖projectiveDenominator u w‖ = 1 := by
      apply le_antisymm (PadicInt.norm_le_one _)
      by_contra! hlt
      apply hn
      have hh := (PadicInt.norm_lt_one_iff_dvd _).mp hlt
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
        Ideal.mem_span_singleton]
      exact hh
    rw [norm_div, PadicInt.norm_coe, PadicInt.norm_coe, hb, div_one] at h
    exact (PadicInt.norm_le_one _).not_gt h
  let a := PadicInt.toZMod u
  let b := PadicInt.toZMod w
  have he : a^14 * b^14 * (a+b)^14 * (r a b)^2 = 0 := by
    simpa [projectiveDenominator, r, a, b, map_ofNat] using hz
  by_cases hc : a*b*(a+b) = 0
  · exact three_of_pole u w hw hc
  · have hr : r a b = 0 := by
      by_contra hn
      obtain ⟨ha, hb, hab⟩ : a ≠ 0 ∧ b ≠ 0 ∧ a+b ≠ 0 := by
        simpa [mul_ne_zero_iff, and_assoc] using hc
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb))
        (pow_ne_zero _ hab)) (pow_ne_zero _ hn) he
    obtain ⟨x, y, z, hx, hy, hz', hxy, hxz, hyz⟩ := hensel_at_cyclotomic_fibre u w hp hr hc
    exact ⟨(x, 1), (y, 1), (z, 1), hx, hy, hz', by simpa [DistinctReductions, sub_ne_zero] using hxy,
      by simpa [DistinctReductions, sub_ne_zero] using hxz,
      by simpa [DistinctReductions, sub_ne_zero] using hyz⟩

end NajmanTrbovic.Cubic
