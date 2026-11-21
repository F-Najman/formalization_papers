module

public import GaussianQuartics.RationalCurves
public import Mathlib.Algebra.QuadraticAlgebra.Basic

import Mathlib.Tactic

/-! The two elliptic-curve point calculations over the Gaussian rationals. -/

@[expose] public section

namespace GaussianQuartics

/-- The Gaussian rationals, with generator satisfying `I² = -1`. -/
abbrev GaussianRat := QuadraticAlgebra ℚ (-1) 0

instance : Fact (¬ IsSquare (-1 : ℚ)) := ⟨by
  rintro ⟨q, hq⟩
  nlinarith [sq_nonneg q]⟩

/-- The imaginary unit in the Gaussian rationals. -/
def I : GaussianRat := QuadraticAlgebra.omega

@[simp] theorem I_sq : I ^ 2 = -1 := by
  apply QuadraticAlgebra.ext <;>
    norm_num [I, pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem I_ne_zero : I ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.im h
  norm_num [I] at this

private theorem coordinates {A : ℚ} {x y : GaussianRat}
    (h : y ^ 2 = x ^ 3 + QuadraticAlgebra.C A * x) :
    y.re ^ 2 - y.im ^ 2 = x.re ^ 3 - 3 * x.re * x.im ^ 2 + A * x.re ∧
    2 * y.re * y.im = x.im * (3 * x.re ^ 2 - x.im ^ 2 + A) := by
  have hr := congrArg QuadraticAlgebra.re h
  have hi := congrArg QuadraticAlgebra.im h
  simp only [pow_succ, pow_zero, one_mul, QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_C, QuadraticAlgebra.im_C, mul_zero, zero_mul, add_zero] at hr hi
  exact ⟨by linear_combination hr, by linear_combination hi⟩

private theorem real_x {A u v r s : ℚ}
    (affine : ∀ {x y : ℚ}, y ^ 2 = x ^ 3 + A * x → y = 0)
    (hr : r ^ 2 - s ^ 2 = u ^ 3 - 3 * u * v ^ 2 + A * u)
    (hi : 2 * r * s = v * (3 * u ^ 2 - v ^ 2 + A)) (hv : v = 0) :
    r = 0 ∧ s = 0 := by
  have hrs : r * s = 0 := by
    rw [hv] at hi
    linarith
  rcases mul_eq_zero.mp hrs with hr0 | hs0
  · refine ⟨hr0, affine (x := -u) ?_⟩
    rw [hr0, hv] at hr
    linear_combination -hr
  · refine ⟨affine (x := u) ?_, hs0⟩
    rw [hs0, hv] at hr
    linear_combination hr

/-- In coordinates, the line through a point and its conjugate has rational slope
`s/v`. The third intersection has abscissa `c = (s/v)² - 2u` and is a rational
point on the curve. Its ordinate is zero by the rational-point calculation. -/
private theorem conjugate_chord {A u v r s : ℚ}
    (affine : ∀ {x y : ℚ}, y ^ 2 = x ^ 3 + A * x → y = 0)
    (hr : r ^ 2 - s ^ 2 = u ^ 3 - 3 * u * v ^ 2 + A * u)
    (hi : 2 * r * s = v * (3 * u ^ 2 - v ^ 2 + A)) (hv : v ≠ 0) :
    let c := (s / v) ^ 2 - 2 * u
    c ^ 3 + A * c = 0 ∧ (u - c) ^ 2 + v ^ 2 = 3 * c ^ 2 + A := by
  let m := s / v
  let k := r - m * u
  let c := m ^ 2 - 2 * u
  change c ^ 3 + A * c = 0 ∧ (u - c) ^ 2 + v ^ 2 = 3 * c ^ 2 + A
  have hs : m * v = s := div_mul_cancel₀ s hv
  rw [← hs] at hr hi
  have hi' : 3 * u ^ 2 - v ^ 2 + A = 2 * m * r := by
    apply mul_left_cancel₀ hv
    linear_combination -hi
  have hReal : u ^ 3 - 3 * u * v ^ 2 + A * u - (m * u + k) ^ 2 + m ^ 2 * v ^ 2 = 0 := by
    dsimp only [k]
    linear_combination -hr
  have hImag : 3 * u ^ 2 - v ^ 2 + A - 2 * m * (m * u + k) = 0 := by
    dsimp only [k]
    linear_combination hi'
  have hthird : (m * c + k) ^ 2 = c ^ 3 + A * c := by
    dsimp only [c]
    linear_combination -hReal - (m ^ 2 - 3 * u) * hImag
  have hthirdY := affine hthird
  constructor
  · simpa [hthirdY] using hthird.symm
  · have hline : r = m * (u - c) := by
      dsimp only [k] at hthirdY
      linear_combination hthirdY
    rw [hline] at hi'
    dsimp only [c]
    linear_combination -hi'

/-- Apply the conjugate chord to ((-x,iy)) as well. -/
private theorem rotated_chord {A u v r s : ℚ}
    (affine : ∀ {x y : ℚ}, y ^ 2 = x ^ 3 + A * x → y = 0)
    (hr : r ^ 2 - s ^ 2 = u ^ 3 - 3 * u * v ^ 2 + A * u)
    (hi : 2 * r * s = v * (3 * u ^ 2 - v ^ 2 + A)) (hv : v ≠ 0) :
    let d := (r / v) ^ 2 + 2 * u
    d ^ 3 + A * d = 0 ∧ (-u - d) ^ 2 + v ^ 2 = 3 * d ^ 2 + A := by
  have result := conjugate_chord (u := -u) (v := -v) (r := -s) (s := r)
    affine (by linear_combination -hr) (by linear_combination -hi) (neg_ne_zero.mpr hv)
  simpa [div_neg, neg_sq] using result

private theorem y_zero_of_slopes {v r s : ℚ} (hv : v ≠ 0)
    (hsum : (s / v) ^ 2 + (r / v) ^ 2 = 0) : (⟨r, s⟩ : GaussianRat) = 0 := by
  have hr0 : r / v = 0 := by nlinarith [sq_nonneg (s / v)]
  have hs0 : s / v = 0 := by nlinarith [sq_nonneg (r / v)]
  exact QuadraticAlgebra.ext ((div_eq_zero_iff.mp hr0).resolve_right hv)
    ((div_eq_zero_iff.mp hs0).resolve_right hv)

/-- Every affine point of `Y² = X³ + X` over `ℚ(i)` has ordinate zero. -/
theorem gaussian_plus_y_eq_zero {x y : GaussianRat}
    (h : y ^ 2 = x ^ 3 + x) : y = 0 := by
  rcases x with ⟨u, v⟩
  rcases y with ⟨r, s⟩
  have affine {x y : ℚ} (h : y ^ 2 = x ^ 3 + 1 * x) : y = 0 :=
    rational_plus_y_eq_zero (by simpa using h)
  obtain ⟨hr, hi⟩ := coordinates (A := 1) (by simpa using h)
  by_cases hv : v = 0
  · obtain ⟨hr0, hs0⟩ := real_x @affine hr hi hv
    exact QuadraticAlgebra.ext hr0 hs0
  · have hc := (conjugate_chord @affine hr hi hv).1
    have hd := (rotated_chord @affine hr hi hv).1
    have only_zero (b : ℚ) (hb : b ^ 3 + b = 0) : b = 0 := by
      have hprod : b * (b ^ 2 + 1) = 0 := by linear_combination hb
      exact (mul_eq_zero.mp hprod).resolve_right (by positivity)
    have hc0 := only_zero _ (by simpa using hc)
    have hd0 := only_zero _ (by simpa using hd)
    exact y_zero_of_slopes hv (by linear_combination hc0 + hd0)

/-- The nonzero ordinates of `Y² = X³ - X` over `ℚ(i)` occur at `X = ±i`. -/
theorem gaussian_minus_y_eq_zero_or_x {x y : GaussianRat}
    (h : y ^ 2 = x ^ 3 - x) : y = 0 ∨ x = I ∨ x = -I := by
  rcases x with ⟨u, v⟩
  rcases y with ⟨r, s⟩
  have affine {x y : ℚ} (h : y ^ 2 = x ^ 3 + (-1) * x) : y = 0 :=
    rational_minus_y_eq_zero (by simpa [sub_eq_add_neg] using h)
  obtain ⟨hr, hi⟩ := coordinates (A := -1) (x := ⟨u, v⟩) (y := ⟨r, s⟩) (by
    rw [QuadraticAlgebra.C_neg, QuadraticAlgebra.C_one, neg_one_mul, ← sub_eq_add_neg]
    exact h)
  by_cases hv : v = 0
  · obtain ⟨hr0, hs0⟩ := real_x @affine hr hi hv
    exact Or.inl (QuadraticAlgebra.ext hr0 hs0)
  let c := (s / v) ^ 2 - 2 * u
  let d := (r / v) ^ 2 + 2 * u
  obtain ⟨hc, hnc⟩ := conjugate_chord @affine hr hi hv
  obtain ⟨hd, hnd⟩ := rotated_chord @affine hr hi hv
  change c ^ 3 + (-1) * c = 0 at hc
  change (u - c) ^ 2 + v ^ 2 = 3 * c ^ 2 + (-1) at hnc
  change d ^ 3 + (-1) * d = 0 at hd
  change (-u - d) ^ 2 + v ^ 2 = 3 * d ^ 2 + (-1) at hnd
  have root_sq (b a : ℚ) (hb : b ^ 3 + (-1) * b = 0)
      (hn : (a - b) ^ 2 + v ^ 2 = 3 * b ^ 2 + (-1)) : b ^ 2 = 1 := by
    have hprod : b * (b ^ 2 - 1) = 0 := by linear_combination hb
    rcases mul_eq_zero.mp hprod with hb0 | hb1
    · rw [hb0] at hn
      nlinarith [sq_nonneg (a - 0), sq_nonneg v]
    · linarith
  have hc1 := root_sq c u hc hnc
  have hd1 := root_sq d (-u) hd hnd
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hc1.trans hd1.symm) with hcd | hcd
  · rw [← hcd] at hnd
    have huc : u * c = 0 := by linear_combination (-1 / 4 : ℚ) * (hnc - hnd)
    have hu : u = 0 := (mul_eq_zero.mp huc).resolve_right (by
      intro hc0
      norm_num [hc0] at hc1)
    have hv1 : v ^ 2 = 1 := by
      rw [hu] at hnc
      linear_combination hnc + 2 * hc1
    have hvCases := sq_eq_sq_iff_eq_or_eq_neg.mp (hv1.trans (by norm_num : (1 : ℚ) = 1 ^ 2))
    rcases hvCases with hvPos | hvNeg
    · exact Or.inr (Or.inl (QuadraticAlgebra.ext hu hvPos))
    · exact Or.inr (Or.inr (QuadraticAlgebra.ext hu hvNeg))
  · have hsum : (s / v) ^ 2 + (r / v) ^ 2 = 0 := by
      dsimp only [c, d] at hcd
      linear_combination hcd
    exact Or.inl (y_zero_of_slopes hv hsum)

end GaussianQuartics
