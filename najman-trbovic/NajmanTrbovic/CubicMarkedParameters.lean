module

public import NajmanTrbovic.CubicMarkedEquation

import Mathlib.Tactic

/-! The explicit coordinate change between the symmetric equation and the
Derickx–Sutherland polynomial in the marked Weierstrass parameters. -/

@[expose] public section

namespace NajmanTrbovic.Cubic

def markedParameters {F : Type*} [Field F] (u v : F) : F × F :=
  ((u+v)/(v-u), markedTNumerator u v / markedDenominator u v)

def parameterDenominator {R : Type*} [CommRing R] (q t : R) : R := 2*q + (q^2+1)*t

def parameterNumerator {R : Type*} [CommRing R] (q t : R) : R := 4*q + (3*q^2+1)*t

def affineCoordinates {F : Type*} [Field F] (q t : F) : F × F :=
  (-parameterNumerator q t * (q-1)/(2*q*parameterDenominator q t),
   -parameterNumerator q t * (q+1)/(2*q*parameterDenominator q t))

/-- The parameter polynomial in Derickx–Sutherland, §3.1. -/
def markedParameterPolynomial {R : Type*} [CommRing R] (q t : R) : R :=
  7*q^12*t^4 + 56*q^11*t^3 + 70*q^10*t^4 + 112*q^10*t^2 + 208*q^9*t^3 + 64*q^9*t -
    111*q^8*t^4 + 144*q^8*t^2 - 624*q^7*t^3 - 156*q^6*t^4 - 1104*q^6*t^2 -
    512*q^5*t^3 - 832*q^5*t - 55*q^4*t^4 - 592*q^4*t^2 - 256*q^4 -
    136*q^3*t^3 - 256*q^3*t - 10*q^2*t^4 - 96*q^2*t^2 - 16*q*t^3 - t^4

set_option maxHeartbeats 0 in
private theorem homogeneous_parameter_identity {R : Type*} [CommRing R] (q t : R) :
    let n := parameterNumerator q t
    let d := parameterDenominator q t
    fibre (-n*(q-1)) (2*q*d) (-n*(q+1)) (2*q*d) =
      4*q^2*d*n*markedParameterPolynomial q t := by
  simp only [parameterNumerator, parameterDenominator, fibre, r, markedParameterPolynomial]
  ring

theorem affine_equation_of_marked_parameters {F : Type*} [Field F] [CharZero F]
    (q t : F) (hq : q ≠ 0) (hd : parameterDenominator q t ≠ 0)
    (h : markedParameterPolynomial q t = 0) :
    fibre (affineCoordinates q t).1 1 (affineCoordinates q t).2 1 = 0 := by
  let c := 2*q*parameterDenominator q t
  let u := (affineCoordinates q t).1
  let v := (affineCoordinates q t).2
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hq) hd
  have hu : c*u = -parameterNumerator q t*(q-1) := by
    change c * (-parameterNumerator q t * (q-1) / c) = _
    rw [mul_comm, div_mul_cancel₀ _ hc]
  have hv : c*v = -parameterNumerator q t*(q+1) := by
    change c * (-parameterNumerator q t * (q+1) / c) = _
    rw [mul_comm, div_mul_cancel₀ _ hc]
  have he : c^6*fibre u 1 v 1 = fibre (c*u) c (c*v) c := by unfold fibre r; ring
  rw [hu, hv, homogeneous_parameter_identity, h, mul_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hc)

theorem marked_parameters_inverse {F : Type*} [Field F] [CharZero F] (u v : F)
    (huv : u ≠ v) (hu : u ≠ 0) (hv : v ≠ 0) (hs : u+v ≠ 0)
    (hL : markedDenominator u v ≠ 0) :
    let qt := markedParameters u v
    qt.1 ≠ 0 ∧ parameterDenominator qt.1 qt.2 ≠ 0 ∧ affineCoordinates qt.1 qt.2 = (u,v) := by
  let q := (u+v)/(v-u)
  let t := markedTNumerator u v / markedDenominator u v
  have hdiff : v-u ≠ 0 := sub_ne_zero.mpr huv.symm
  have hq : q ≠ 0 := div_ne_zero hs hdiff
  have hde : parameterDenominator q t = 4*u*v*(u+v)/((v-u)*markedDenominator u v) := by
    dsimp [parameterDenominator, q, t, markedTNumerator]
    field_simp
    unfold markedDenominator markedSumTerm
    ring
  have hd : parameterDenominator q t ≠ 0 := by
    rw [hde]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hu) hv) hs)
      (mul_ne_zero hdiff hL)
  have hne : -parameterNumerator q t = (u+v)*parameterDenominator q t := by
    rw [hde]
    dsimp [parameterNumerator, q, t, markedTNumerator]
    field_simp
    unfold markedDenominator markedSumTerm
    ring
  change q ≠ 0 ∧ parameterDenominator q t ≠ 0 ∧ affineCoordinates q t = (u,v)
  refine ⟨hq, hd, ?_⟩
  have hxu : (u+v)*(q-1) = 2*q*u := by dsimp [q]; field_simp; ring
  have hxv : (u+v)*(q+1) = 2*q*v := by dsimp [q]; field_simp; ring
  have hc : 2*q*parameterDenominator q t ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hq) hd
  apply Prod.ext
  · change (-parameterNumerator q t*(q-1))/(2*q*parameterDenominator q t) = u
    apply (div_eq_iff hc).mpr
    rw [hne, mul_right_comm, hxu]
    ring
  · change (-parameterNumerator q t*(q+1))/(2*q*parameterDenominator q t) = v
    apply (div_eq_iff hc).mpr
    rw [hne, mul_right_comm, hxv]
    ring

theorem affine_coordinates_recover_marked_equation {F : Type*} [Field F] [CharZero F]
    (q t : F) (hq : q ≠ 0) (hd : parameterDenominator q t ≠ 0) (hD : q^2-1 ≠ 0)
    (hn : parameterNumerator q t ≠ 0) :
    let uv := affineCoordinates q t
    markedParameters uv.1 uv.2 = (q,t) ∧
      markedCurve uv.1 uv.2 = ⟨0,t^2-2*q*t-2,0,-(t^2-1)*(q*t+1)^2,0⟩ := by
  let u := (affineCoordinates q t).1
  let v := (affineCoordinates q t).2
  let c := 2*q*parameterDenominator q t
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hq) hd
  have hdiff : v-u = -2*parameterNumerator q t/c := by
    dsimp [u, v, affineCoordinates, c]
    ring
  have hneq : v-u ≠ 0 := by
    rw [hdiff]
    exact div_ne_zero (mul_ne_zero (by norm_num) hn) hc
  have hL : markedDenominator u v = 8*q^2*(q^2-1)*parameterNumerator q t^2/c^3 := by
    simp only [u, v, affineCoordinates, markedDenominator, markedSumTerm, c]
    field_simp
    simp only [parameterNumerator, parameterDenominator]
    ring
  have hL₀ : markedDenominator u v ≠ 0 := by
    rw [hL]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hq)) hD)
      (pow_ne_zero _ hn)) (pow_ne_zero _ hc)
  have hq' : (u+v)/(v-u) = q := by
    apply (div_eq_iff hneq).mpr
    rw [hdiff]
    dsimp [u, v, affineCoordinates, c]
    ring
  have ht' : markedTNumerator u v / markedDenominator u v = t := by
    apply (div_eq_iff hL₀).mpr
    rw [hL]
    simp only [u, v, affineCoordinates, markedTNumerator, c]
    field_simp
    simp only [parameterNumerator, parameterDenominator]
    ring
  change markedParameters u v = (q,t) ∧ _
  exact ⟨Prod.ext hq' ht', by
    rw [markedCurve_eq_original u v (sub_ne_zero.mp hneq).symm hL₀, hq', ht']⟩

end NajmanTrbovic.Cubic
