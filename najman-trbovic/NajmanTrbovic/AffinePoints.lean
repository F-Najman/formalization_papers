module

public import NajmanTrbovic.Table7
public import Mathlib.Data.Rat.Lemmas

import Mathlib.Tactic

/-! Equivalence between primitive squareclasses and rational points on the affine twists. -/

@[expose] public section

namespace NajmanTrbovic

theorem exists_int_of_mul_square_eq {D A : ℤ} (hD : Squarefree D) {q : ℚ}
    (hq : (D : ℚ) * q ^ 2 = (A : ℚ)) : ∃ s : ℤ, (s : ℚ) = q := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hone : q.den = 1 := by
    by_contra hn
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn
    have he := hq
    rw [← q.num_div_den, div_pow, ← mul_div_assoc] at he
    have hz : D * q.num ^ 2 = A * (q.den : ℤ) ^ 2 := by
      exact_mod_cast (div_eq_iff (pow_ne_zero 2 hden)).mp he
    have ha := congrArg Int.natAbs hz
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at ha
    have hprod : p ^ 2 ∣ D.natAbs * q.num.natAbs ^ 2 := by
      rw [ha]
      exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpd 2) _
    have hc : Nat.Coprime (p ^ 2) (q.num.natAbs ^ 2) :=
      ((q.reduced.coprime_dvd_right hpd).symm.pow_left 2).pow_right 2
    have hdv := hc.dvd_of_dvd_mul_right hprod
    exact (Nat.squarefree_iff_prime_squarefree.mp (Int.squarefree_natAbs.mpr hD) p hp)
      (by simpa [pow_two] using hdv)
  refine ⟨q.num, ?_⟩
  simpa [hone] using q.num_div_den

/-- A rational point on the affine twist with nonzero square coordinate. -/
def RationalTwistPoint (N : Level) (D : ℤ) : Prop :=
  ∃ x y : ℚ, y ≠ 0 ∧ N.form x 1 = (D : ℚ) * y ^ 2

/-- Clearing an even-degree denominator preserves the represented squareclass. -/
theorem represents_iff_rational_twist {N : Level} {D : ℤ} :
    Represents N D ↔ Squarefree D ∧ D ≠ 1 ∧ RationalTwistPoint N D := by
  let d := (N.coefficients.length - 1) / 2
  constructor
  · rintro ⟨hd, hD, m, n, s, _, hn, hs, h⟩
    refine ⟨hd, hD, (m : ℚ) / (n : ℚ), (s : ℚ) / (n : ℚ)^d, ?_, ?_⟩
    · exact div_ne_zero (by exact_mod_cast hs) (pow_ne_zero _ (by exact_mod_cast hn))
    · have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
      have he : N.form (m : ℚ) (n : ℚ) = (D : ℚ) * (s : ℚ) ^ 2 := by
        calc
          _ = ((N.form m n : ℤ) : ℚ) := (form_cast (Int.castRingHom ℚ) N m n).symm
          _ = _ := by rw [h]; push_cast; rfl
      have hl := form_scale N ((n : ℚ)⁻¹) (m : ℚ) (n : ℚ)
      rw [inv_mul_cancel₀ hn', he] at hl
      rw [div_eq_mul_inv, mul_comm (m : ℚ)]
      rw [hl, div_pow, inv_pow]
      ring
  · rintro ⟨hd, hD, x, y, hy, hxy⟩
    let s₀ : ℚ := (x.den : ℚ)^d * y
    let a : ℤ := N.form x.num (x.den : ℤ)
    have hs₀ : s₀ ≠ 0 := mul_ne_zero (pow_ne_zero _ (by exact_mod_cast x.den_nz)) hy
    have hxn : (x.den : ℚ) * x = (x.num : ℚ) := by
      rw [mul_comm]
      exact x.mul_den_eq_num
    have hs : (D : ℚ) * s₀ ^ 2 = (a : ℚ) := by
      have h := form_scale N (x.den : ℚ) x 1
      rw [hxn, mul_one, hxy] at h
      have hl : (a : ℚ) = N.form (x.num : ℚ) (x.den : ℚ) := by
        exact form_cast (Int.castRingHom ℚ) N x.num (x.den : ℤ)
      rw [hl, h]
      dsimp [s₀, d]
      ring
    obtain ⟨s, hs'⟩ := exists_int_of_mul_square_eq hd hs
    refine ⟨hd, hD, x.num, x.den, s, ?_, by exact_mod_cast x.den_nz, ?_, ?_⟩
    · simpa [Int.gcd] using x.reduced
    · intro h
      apply hs₀
      simp [← hs', h]
    · rw [← hs'] at hs
      exact_mod_cast hs.symm

theorem table7_iff_rational_twist {N : Level} {p : ℕ} (hp : p.Prime) (h100 : p ≤ 100) :
    p ∈ N.table7 ↔ ∀ D : ℤ, Squarefree D → D ≠ 1 → RationalTwistPoint N D → Unramified D p := by
  rw [table7_iff hp h100]
  simp only [represents_iff_rational_twist, and_imp]

end NajmanTrbovic
