module

public import NajmanTrbovic.CubicModel
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

import Mathlib.Tactic

/-! The j-invariant of the original marked Weierstrass model on the symmetric
affine equation of X₁(2,14). The comparison is valid on both coordinate projections. -/

@[expose] public section

namespace NajmanTrbovic.Cubic

def markedSumTerm {R : Type*} [CommRing R] (u v : R) : R := (u+v)^2*(u+v+2)

def markedDenominator {R : Type*} [CommRing R] (u v : R) : R :=
  markedSumTerm u v - 2*u*v*(u+v+1)

def markedTNumerator {R : Type*} [CommRing R] (u v : R) : R := (u-v)*(u+v)*(u+v+2)

def markedA2Numerator {R : Type*} [CommRing R] (u v : R) : R :=
  markedTNumerator u v ^ 2 + 2*markedSumTerm u v*markedDenominator u v - 2*markedDenominator u v ^ 2

def markedA4Numerator {R : Type*} [CommRing R] (u v : R) : R :=
  -(markedTNumerator u v ^ 2 - markedDenominator u v ^ 2)*(markedDenominator u v - markedSumTerm u v)^2

/-- The marked equation used in Section 3, with the factor `u - v` canceled in `q*t`. -/
def markedCurve {F : Type*} [Field F] (u v : F) : WeierstrassCurve F :=
  ⟨0, markedA2Numerator u v / markedDenominator u v ^ 2, 0, markedA4Numerator u v / markedDenominator u v ^ 4, 0⟩

theorem markedDenominator_eq {F : Type*} [Field F] (u v : F) :
    markedDenominator u v = u^3 + u^2*v + 2*u^2 + u*v^2 + 2*u*v + v^3 + 2*v^2 := by
  unfold markedDenominator markedSumTerm
  ring

/-- Comparison with the parameters of the original Derickx–Sutherland equation. -/
theorem markedCurve_eq_original {F : Type*} [Field F] (u v : F) (huv : u ≠ v)
    (hd : markedDenominator u v ≠ 0) :
    let q := (u+v)/(v-u)
    let t := markedTNumerator u v / markedDenominator u v
    markedCurve u v = ⟨0, t^2-2*q*t-2, 0, -(t^2-1)*(q*t+1)^2, 0⟩ := by
  dsimp only
  have hqt : (u+v)/(v-u)*(markedTNumerator u v / markedDenominator u v) =
      -markedSumTerm u v / markedDenominator u v := by
    unfold markedTNumerator markedSumTerm
    field_simp [sub_ne_zero.mpr huv.symm]
    ring
  have ht : (markedTNumerator u v / markedDenominator u v)^2 =
      markedTNumerator u v^2 / markedDenominator u v^2 := div_pow ..
  have eA : markedA2Numerator u v / markedDenominator u v ^ 2 =
      (markedTNumerator u v / markedDenominator u v)^2 -
        2*((u+v)/(v-u))*(markedTNumerator u v / markedDenominator u v)-2 := by
    rw [mul_assoc, hqt, ht]
    unfold markedA2Numerator
    field_simp
    ring
  have eB : markedA4Numerator u v / markedDenominator u v ^ 4 =
      -((markedTNumerator u v / markedDenominator u v)^2-1) *
        (((u+v)/(v-u))*(markedTNumerator u v / markedDenominator u v)+1)^2 := by
    rw [hqt, ht]
    unfold markedA4Numerator
    field_simp
    ring
  unfold markedCurve
  rw [eA, eB]

theorem markedCurve_swap {F : Type*} [Field F] (u v : F) : markedCurve u v = markedCurve v u := by
  have hs : markedSumTerm u v = markedSumTerm v u := by unfold markedSumTerm; ring
  have hd : markedDenominator u v = markedDenominator v u := by unfold markedDenominator; rw [hs]; ring
  have ht : markedTNumerator u v ^ 2 = markedTNumerator v u ^ 2 := by unfold markedTNumerator; ring
  unfold markedCurve markedA2Numerator markedA4Numerator
  rw [hs, hd, ht]

theorem marked_invariants {F : Type*} [Field F] (u v : F) (hd : markedDenominator u v ≠ 0) :
    (markedCurve u v).c₄ = 16*(markedA2Numerator u v ^ 2 - 3*markedA4Numerator u v) /
      markedDenominator u v ^ 4 ∧
    (markedCurve u v).Δ = 16*(markedA4Numerator u v ^ 2 *
      (markedA2Numerator u v ^ 2 - 4*markedA4Numerator u v)) / markedDenominator u v ^ 12 := by
  constructor <;>
    simp only [markedCurve, WeierstrassCurve.c₄, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, zero_mul, mul_zero,
      zero_add, add_zero, zero_pow (by decide : 2 ≠ 0)] <;>
    field_simp <;> ring

theorem marked_j {F : Type*} [Field F] [CharZero F] (u v : F) [(markedCurve u v).IsElliptic] :
    (markedCurve u v).j = 256*(markedA2Numerator u v ^ 2 - 3*markedA4Numerator u v)^3 /
      (markedA4Numerator u v ^ 2 * (markedA2Numerator u v ^ 2 - 4*markedA4Numerator u v)) ∧
    markedA4Numerator u v ^ 2 * (markedA2Numerator u v ^ 2 - 4*markedA4Numerator u v) ≠ 0 := by
  have hd : markedDenominator u v ≠ 0 := by
    intro h
    apply (markedCurve u v).isUnit_Δ.ne_zero
    simp [markedCurve, h, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  obtain ⟨h₄, hΔ⟩ := marked_invariants u v hd
  have hdisc : markedA4Numerator u v ^ 2 * (markedA2Numerator u v ^ 2 - 4*markedA4Numerator u v) ≠ 0 := by
    intro h
    apply (markedCurve u v).isUnit_Δ.ne_zero
    rw [hΔ, h, mul_zero, zero_div]
  refine ⟨?_, hdisc⟩
  rw [WeierstrassCurve.j_eq, hΔ, h₄]
  have h16 : (16 : F) ≠ 0 := by norm_num
  field_simp [h16, hdisc]
  ring

end NajmanTrbovic.Cubic
