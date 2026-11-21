module

public import GaussianQuartics.FieldClassification
public import GaussianQuartics.PointGroups
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

import Mathlib.Tactic

/-!
# Gaussian-integer quartic equations

Theorem 1(i), Theorem 1(ii), and both signs of Theorem 2 of Filip Najman's
*The Diophantine equation x⁴ ± y⁴ = iz² in Gaussian integers*.
-/

@[expose] public section

namespace GaussianQuartics

/-- The imaginary unit in mathlib's Gaussian integers. -/
def intI : GaussianInt := ⟨0, 1⟩

@[simp] theorem intI_sq : intI ^ 2 = -1 := by
  apply Zsqrtd.ext <;> decide

/-- The canonical inclusion of the Gaussian integers into the Gaussian rationals. -/
def toGaussianRat : GaussianInt →+* GaussianRat where
  toFun x := ⟨x.re, x.im⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := by
    apply QuadraticAlgebra.ext <;>
      simp [Zsqrtd.re_add, Zsqrtd.im_add]
  map_mul' x y := by
    apply QuadraticAlgebra.ext <;>
      simp [Zsqrtd.re_mul, Zsqrtd.im_mul]

theorem toGaussianRat_injective : Function.Injective toGaussianRat := by
  intro x y h
  have hr : (x.re : ℚ) = (y.re : ℚ) := congrArg QuadraticAlgebra.re h
  have hi : (x.im : ℚ) = (y.im : ℚ) := congrArg QuadraticAlgebra.im h
  exact Zsqrtd.ext (by exact_mod_cast hr) (by exact_mod_cast hi)

@[simp] theorem toGaussianRat_intI : toGaussianRat intI = I := rfl

@[simp] theorem toGaussianRat_trivial (x y z : GaussianInt) :
    Trivial (toGaussianRat x) (toGaussianRat y) (toGaussianRat z) ↔ Trivial x y z := by
  simp only [Trivial, ← map_mul, ← map_zero toGaussianRat, toGaussianRat_injective.eq_iff]

/-- Primitivity means that all common divisors of the three coordinates are units. -/
def Primitive (x y z : GaussianInt) : Prop :=
  ∀ d : GaussianInt, d ∣ x → d ∣ y → d ∣ z → IsUnit d

/-- The list of four Gaussian units. -/
def UnitChoice (x : GaussianInt) : Prop :=
  x = 1 ∨ x = -1 ∨ x = intI ∨ x = -intI

theorem unitChoice_iff_isUnit (x : GaussianInt) : UnitChoice x ↔ IsUnit x := by
  have norm_iff : x.norm = 1 ↔ IsUnit x :=
    Zsqrtd.norm_eq_one_iff' (by decide) x
  constructor
  · intro h
    apply norm_iff.mp
    rcases h with h | h | h | h <;> rw [h] <;> decide
  · intro h
    have hnorm : x.re ^ 2 + x.im ^ 2 = 1 := by
      have hn := norm_iff.mpr h
      rw [Zsqrtd.norm_def] at hn
      linear_combination hn
    have one_le_sq (a : ℤ) (ha : a ≠ 0) : 1 ≤ a ^ 2 := by
      rcases lt_or_gt_of_ne ha with ha | ha
      · nlinarith [mul_nonneg_of_nonpos_of_nonpos ha.le (show a + 1 ≤ 0 by omega)]
      · nlinarith [mul_nonneg ha.le (show 0 ≤ a - 1 by omega)]
    by_cases hr : x.re = 0
    · rw [hr, zero_pow (by decide), zero_add] at hnorm
      have hs : x.im ^ 2 = (1 : ℤ) ^ 2 := by rwa [one_pow]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hi | hi
      · exact Or.inr (Or.inr (Or.inl (Zsqrtd.ext hr hi)))
      · exact Or.inr (Or.inr (Or.inr (Zsqrtd.ext hr hi)))
    · have hi : x.im = 0 := by
        by_contra hi
        linarith [one_le_sq _ hr, one_le_sq _ hi]
      rw [hi, zero_pow (by decide), add_zero] at hnorm
      have hs : x.re ^ 2 = (1 : ℤ) ^ 2 := by rwa [one_pow]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hr' | hr'
      · exact Or.inl (Zsqrtd.ext hr' hi)
      · exact Or.inr (Or.inl (Zsqrtd.ext hr' hi))

private theorem unitChoice_sq {x : GaussianInt} (h : UnitChoice x) :
    x ^ 2 = 1 ∨ x ^ 2 = -1 := by
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)
  · exact Or.inr intI_sq
  · exact Or.inr (by simp)

private theorem unitChoice_fourth {x : GaussianInt} (h : UnitChoice x) : x ^ 4 = 1 := by
  rw [show x ^ 4 = (x ^ 2) ^ 2 by ring]
  rcases unitChoice_sq h with hx | hx
  · rw [hx, one_pow]
  · rw [hx]
    ring

/-- Theorem 1(i) of the paper. -/
theorem theorem1i {x y z : GaussianInt} (h : x ^ 4 - y ^ 4 = intI * z ^ 2) :
    Trivial x y z := by
  apply (toGaussianRat_trivial x y z).mp
  apply rat_minus_i_trivial
  simpa only [map_sub, map_pow, map_mul, toGaussianRat_intI] using congrArg toGaussianRat h

/-- The complete family of nontrivial solutions before imposing primitivity. -/
theorem gaussian_int_plus_i_iff {x y z : GaussianInt} (ht : ¬ Trivial x y z) :
    x ^ 4 + y ^ 4 = intI * z ^ 2 ↔ ScaledPlusSolution intI x y z := by
  refine ⟨?_, eq_of_scaled_plus_solution intI_sq⟩
  intro h
  have ht' : ¬ Trivial (toGaussianRat x) (toGaussianRat y) (toGaussianRat z) :=
    fun ht' => ht ((toGaussianRat_trivial x y z).mp ht')
  have hp := (rat_plus_i_iff ht').mp (by
    simpa only [map_add, map_pow, map_mul, toGaussianRat_intI] using congrArg toGaussianRat h)
  simpa only [ScaledPlusSolution, ← toGaussianRat_intI, ← map_neg, ← map_mul, ← map_add,
    ← map_one toGaussianRat, ← map_pow, toGaussianRat_injective.eq_iff] using hp

/-- Theorem 1(ii) of the paper, including the converse. -/
theorem theorem1ii {x y z : GaussianInt} :
    (¬ Trivial x y z ∧ Primitive x y z ∧ x ^ 4 + y ^ 4 = intI * z ^ 2) ↔
      UnitChoice x ∧ UnitChoice y ∧ (z = intI * (1 + intI) ∨ z = -(intI * (1 + intI))) := by
  constructor
  · rintro ⟨ht, hprimitive, h⟩
    obtain ⟨hx, hz⟩ := (gaussian_int_plus_i_iff ht).mp h
    have hdvdX : y ∣ x := by
      rcases hx with h | h | h | h
      · exact ⟨1, by simpa using h⟩
      · exact ⟨-1, by simpa using h⟩
      · exact ⟨intI, by simpa only [mul_comm y intI] using h⟩
      · exact ⟨-intI, by rw [h]; ring⟩
    have hdvdZ : y ∣ z := by
      rcases hz with h | h
      · exact ⟨intI * (1 + intI) * y, by rw [h]; ring⟩
      · exact ⟨-(intI * (1 + intI) * y), by rw [h]; ring⟩
    have hyUnit := hprimitive y hdvdX dvd_rfl hdvdZ
    have hiUnit := (unitChoice_iff_isUnit intI).mp (Or.inr (Or.inr (Or.inl rfl)))
    have hxUnit : IsUnit x := by
      rcases hx with rfl | rfl | rfl | rfl
      · exact hyUnit
      · exact hyUnit.neg
      · exact hiUnit.mul hyUnit
      · exact (hiUnit.mul hyUnit).neg
    have hyChoice := (unitChoice_iff_isUnit y).mpr hyUnit
    refine ⟨(unitChoice_iff_isUnit x).mpr hxUnit, hyChoice, ?_⟩
    rcases unitChoice_sq hyChoice with hy | hy <;>
      rcases hz with hz | hz
    · exact Or.inl (by simpa [hy] using hz)
    · exact Or.inr (by simpa [hy] using hz)
    · exact Or.inr (by simpa [hy] using hz)
    · exact Or.inl (by simpa [hy] using hz)
  · rintro ⟨hx, hy, hz⟩
    have hxUnit := (unitChoice_iff_isUnit x).mp hx
    have hyUnit := (unitChoice_iff_isUnit y).mp hy
    have hFactor : intI * (1 + intI) ≠ 0 := by
      intro hzero
      exact two_ne_zero (by simpa [hzero] using (imaginary_factor intI_sq).symm)
    have hz0 : z ≠ 0 := by
      rcases hz with rfl | rfl
      · exact hFactor
      · exact neg_ne_zero.mpr hFactor
    refine ⟨mul_ne_zero (mul_ne_zero hxUnit.ne_zero hyUnit.ne_zero) hz0,
      fun _ hd _ _ => isUnit_of_dvd_unit hd hxUnit, ?_⟩
    calc
      x ^ 4 + y ^ 4 = 2 := by rw [unitChoice_fourth hx, unitChoice_fourth hy]; ring
      _ = intI * z ^ 2 := by rcases hz with rfl | rfl <;> simpa using (imaginary_factor intI_sq).symm

/-- Theorem 2 of the paper, plus sign. -/
theorem theorem2_plus {x y z : GaussianInt} (h : x ^ 4 + y ^ 4 = z ^ 2) :
    Trivial x y z := by
  apply (toGaussianRat_trivial x y z).mp
  apply rat_hilbert_plus
  simpa only [map_add, map_pow] using congrArg toGaussianRat h

/-- Theorem 2 of the paper, minus sign. -/
theorem theorem2_minus {x y z : GaussianInt} (h : x ^ 4 - y ^ 4 = z ^ 2) :
    Trivial x y z := by
  apply (toGaussianRat_trivial x y z).mp
  apply rat_hilbert_minus
  simpa only [map_sub, map_pow] using congrArg toGaussianRat h

end GaussianQuartics
