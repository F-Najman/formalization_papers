module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Data.ZMod.Basic

import Mathlib.Tactic

/-! The corrected descended invariants and projective fibers of equation (4). -/

@[expose] public section

namespace NajmanTrbovic.Cubic

def r {R : Type*} [Ring R] (u w : R) : R := u ^ 3 + u ^ 2 * w - 2 * u * w ^ 2 - w ^ 3

def fibre {R : Type*} [Ring R] (u w v z : R) : R :=
  r u w * (v * z * (v + z)) + r v z * (u * w * (u + w))

theorem fibre_at_zero {R : Type*} [CommRing R] (v z : R) :
    fibre 0 1 v z = -(v * z * (v + z)) := by simp [fibre, r]

theorem fibre_at_neg_one {R : Type*} [CommRing R] (v z : R) :
    fibre (-1) 1 v z = v * z * (v + z) := by simp [fibre, r]; ring

theorem fibre_at_infinity {R : Type*} [CommRing R] (v z : R) :
    fibre 1 0 v z = v * z * (v + z) := by simp [fibre, r]

theorem fibre_at_root {R : Type*} [CommRing R] {u w : R} (hr : r u w = 0) (v z : R) :
    fibre u w v z = r v z * (u * w * (u + w)) := by simp [fibre, hr]

theorem fibre_at_two {u w : ZMod 2} (hp : u ≠ 0 ∨ w ≠ 0) (v z : ZMod 2) :
    fibre u w v z = v * z * (v + z) := by
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hneg : (-1 : ZMod 2) = 1 := by decide
  rcases hcases u with rfl | rfl <;> rcases hcases w with rfl | rfl
  · simp at hp
  · rw [fibre_at_zero, neg_eq_neg_one_mul, hneg, one_mul]
  · exact fibre_at_infinity _ _
  · conv_lhs => rw [← hneg]
    exact fibre_at_neg_one _ _

def g2 {R : Type*} [Ring R] (u : R) : R := u^2 + u + 1

def g6 {R : Type*} [Ring R] (u : R) : R :=
  u^6 + u^5 + 2*u^4 + 9*u^3 + 12*u^2 + 5*u + 1

def g12 {R : Type*} [Ring R] (u : R) : R :=
  u^12 + 4*u^11 + 3*u^10 - 4*u^9 + 6*u^7 - 17*u^6 - 30*u^5 + 6*u^4 + 34*u^3 +
    25*u^2 + 8*u + 1

def denominator {R : Type*} [Ring R] (u : R) : R := g2 u ^ 3 * g6 u

def jDenominator {R : Type*} [Ring R] (u : R) : R := u^14 * (u+1)^14 * (r u 1)^2

def a2Numerator {R : Type*} [Ring R] (u : R) : R :=
  -u^2 - 6*u^3 - 19*u^4 - 34*u^5 - 35*u^6 - 22*u^7 - 10*u^8 - 4*u^9 - u^10

def a4Numerator {R : Type*} [Ring R] (u : R) : R :=
  u^6 + 10*u^7 + 46*u^8 + 126*u^9 + 226*u^10 + 280*u^11 + 253*u^12 +
    182*u^13 + 116*u^14 + 66*u^15 + 29*u^16 + 8*u^17 + u^18

def a6Numerator {R : Type*} [Ring R] (u : R) : R := (u * (u + 1)) ^ 12

/-- The descended Weierstrass equation in the review. Its invariants are evaluated below. -/
def descended {K : Type*} [Field K] (u : K) : WeierstrassCurve K :=
  ⟨1, a2Numerator u / denominator u, 0,
    a4Numerator u / denominator u ^ 2, a6Numerator u / denominator u ^ 3⟩

private theorem weighted_invariants {K : Type*} [Field K] (d a b c : K) (hd : d ≠ 0) :
    (⟨1, a / d, 0, b / d ^ 2, c / d ^ 3⟩ : WeierstrassCurve K).c₄ =
      ((d + 4 * a)^2 - 48 * b) / d^2 ∧
    (⟨1, a / d, 0, b / d ^ 2, c / d ^ 3⟩ : WeierstrassCurve K).Δ =
      (-(d + 4 * a)^2 * ((d + 4 * a) * c - b^2) - 64*b^3 - 432*c^2 +
        72*(d + 4*a)*b*c) / d^6 := by
  constructor <;>
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈] <;> field_simp <;> ring

set_option maxHeartbeats 0 in
theorem descended_invariants {K : Type*} [Field K] (u : K) (hd : denominator u ≠ 0) :
    (descended u).c₄ = g12 u / denominator u ∧
    (descended u).Δ = jDenominator u / denominator u ^ 4 := by
  obtain ⟨h₄, hΔ⟩ := weighted_invariants (denominator u) (a2Numerator u) (a4Numerator u) (a6Numerator u) hd
  change (descended u).c₄ = _ at h₄
  change (descended u).Δ = _ at hΔ
  constructor
  · rw [h₄]
    have h : (denominator u + 4 * a2Numerator u)^2 - 48 * a4Numerator u = g12 u * denominator u := by
      simp only [denominator, a2Numerator, a4Numerator, g2, g6, g12]
      ring
    rw [h]
    field_simp
  · rw [hΔ]
    have h : -(denominator u + 4*a2Numerator u)^2 *
        ((denominator u + 4*a2Numerator u)*a6Numerator u - a4Numerator u^2) -
        64*a4Numerator u^3 - 432*a6Numerator u^2 +
        72*(denominator u + 4*a2Numerator u)*a4Numerator u*a6Numerator u =
        jDenominator u * denominator u ^ 2 := by
      simp only [denominator, a2Numerator, a4Numerator, a6Numerator, g2, g6, jDenominator, r]
      ring
    rw [h]
    field_simp

noncomputable section

theorem descended_j {K : Type*} [Field K] (u : K) [(descended u).IsElliptic]
    (hd : denominator u ≠ 0) (hj : jDenominator u ≠ 0) :
    (descended u).j = denominator u * g12 u ^ 3 / jDenominator u := by
  obtain ⟨h₄, hΔ⟩ := descended_invariants u hd
  rw [WeierstrassCurve.j_eq, h₄, hΔ]
  field_simp

end

end NajmanTrbovic.Cubic
