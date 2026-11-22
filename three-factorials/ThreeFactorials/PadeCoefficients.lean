module

public import ThreeFactorials.PadeBinomial
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Arithmetic of the coefficients for the three nodes −1, 0, 1. -/

@[expose] public section

namespace ThreeFactorials

open Finset

def nodeOffset (j : Fin 3) : ℤ := (j.val : ℤ) - 1

def poleOrder (k : ℕ) (i j : Fin 3) : ℕ := k + if i = j then 1 else 0

def gapExponent (j l : Fin 3) (n : ℕ) : ℕ :=
  if (nodeOffset j - nodeOffset l).natAbs = 2 then n else 0

def gapSign (j l : Fin 3) (n : ℕ) : ℤ :=
  if nodeOffset j < nodeOffset l then (-1) ^ n else 1

def polePairNumerator (k : ℕ) (i j : Fin 3) (r t : ℕ) : ℤ :=
  Ring.choose (-(poleOrder k i (j + 1) : ℤ)) r *
    gapSign j (j + 1) (poleOrder k i (j + 1) + r) *
    Ring.choose (-(poleOrder k i (j + 2) : ℤ)) t *
    gapSign j (j + 2) (poleOrder k i (j + 2) + t)

def polePairDenom (k : ℕ) (i j : Fin 3) (r t : ℕ) : ℕ :=
  gapExponent j (j + 1) (poleOrder k i (j + 1) + r) +
    gapExponent j (j + 2) (poleOrder k i (j + 2) + t)

noncomputable def padeTerm (m k : ℕ) (i j : Fin 3) (h r t : ℕ) : ℚ :=
  Ring.choose ((k : ℚ) + 1 / 2) h * (m + (nodeOffset j : ℚ)) ^ (k - h) *
    (polePairNumerator k i j r t : ℚ) / 2 ^ polePairDenom k i j r t

noncomputable def padeCoefficient (m k : ℕ) (i j : Fin 3) : ℚ :=
  ∑ u ∈ antidiagonal (poleOrder k i j - 1), ∑ v ∈ antidiagonal u.2,
    padeTerm m k i j u.1 v.1 v.2

private theorem denom_le {k h r t : ℕ} {i j : Fin 3} (hk : 0 < k)
    (hs : h + (r + t) = poleOrder k i j - 1) :
    h + polePairDenom k i j r t ≤ (if j = 1 then k else 2 * k) ∧ h ≤ k := by
  fin_cases i <;> fin_cases j <;>
    simp [polePairDenom, poleOrder, gapExponent, nodeOffset, Fin.add_def] at hs ⊢ <;> omega

private theorem clear_term_denom {m k h r t : ℕ} {i j : Fin 3} (hk : 0 < k)
    (hs : h + (r + t) = poleOrder k i j - 1) :
    (8 ^ k * padeTerm m k i j h r t : ℚ) ∈ (Int.castRingHom ℚ).range := by
  obtain ⟨u, hu⟩ := half_choose_integral k h
  have he := denom_le hk hs
  have he' : h + polePairDenom k i j r t ≤ 2 * k :=
    he.1.trans (by split <;> omega)
  have hle : 2 * h + polePairDenom k i j r t ≤ 3 * k := by
    have := he.2
    omega
  let e := polePairDenom k i j r t
  use (2 : ℤ) ^ (3 * k - (2 * h + e)) * u * ((m : ℤ) + nodeOffset j) ^ (k - h) *
    polePairNumerator k i j r t
  change (((2 : ℤ) ^ (3 * k - (2 * h + e)) * u * ((m : ℤ) + nodeOffset j) ^ (k - h) *
    polePairNumerator k i j r t : ℤ) : ℚ) = _
  push_cast
  rw [hu, show (4 : ℚ) ^ h = 2 ^ (2 * h) by rw [pow_mul]; norm_num,
    show (8 : ℚ) ^ k = 2 ^ (3 * k) by rw [pow_mul]; norm_num, padeTerm]
  rw [← mul_div_assoc]
  change _ = _ / 2 ^ e
  apply (eq_div_iff (by positivity : (2 : ℚ) ^ e ≠ 0)).2
  calc
    _ = (2 : ℚ) ^ ((3 * k - (2 * h + e)) + 2 * h + e) *
        (Ring.choose ((k : ℚ) + 1 / 2) h * (m + (nodeOffset j : ℚ)) ^ (k - h) *
          (polePairNumerator k i j r t : ℚ)) := by rw [pow_add, pow_add]; ring
    _ = _ := by
      have hE : (3 * k - (2 * h + e)) + 2 * h + e = 3 * k := by
        change 2 * h + e ≤ 3 * k at hle
        omega
      rw [hE]

/-- The entire matrix becomes integral after multiplication by `8^k`. -/
theorem pade_entry_integral (m k : ℕ) (hk : 0 < k) (i j : Fin 3) :
    ∃ p : ℤ, (p : ℚ) = 8 ^ k * padeCoefficient m k i j := by
  change (_ : ℚ) ∈ (Int.castRingHom ℚ).range
  unfold padeCoefficient
  simp only [Finset.mul_sum]
  apply Subring.sum_mem
  intro u hu
  apply Subring.sum_mem
  intro v hv
  have ha := Finset.mem_antidiagonal.mp hu
  have hb := Finset.mem_antidiagonal.mp hv
  exact clear_term_denom hk (by omega)

theorem descPochhammer_smeval_prod {K : Type*} [Field K] [CharZero K] (x : K) (h : ℕ) :
    (descPochhammer ℤ h).smeval x = ∏ j ∈ range h, (x - j) := by
  induction h with
  | zero => simp [descPochhammer_zero]
  | succ h ih =>
    rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih, Finset.prod_range_succ]
    simp [Polynomial.smeval_natCast]

/-- Clearing the factorial denominator gives a product of odd integers. -/
theorem half_choose_odd_numerator (k h : ℕ) :
    (2 : ℚ) ^ h * (h.factorial : ℚ) * Ring.choose ((k : ℚ) + 1 / 2) h =
      ((∏ j ∈ range h, (2 * (k : ℤ) + 1 - 2 * (j : ℤ))) : ℤ) := by
  rw [Ring.choose_eq_smul, smul_eq_mul, ← mul_assoc, mul_assoc ((2 : ℚ) ^ h),
    mul_inv_cancel₀ (by exact_mod_cast h.factorial_ne_zero), mul_one]
  rw [descPochhammer_smeval_prod]
  calc
    _ = (∏ _ ∈ range h, (2 : ℚ)) * ∏ j ∈ range h, ((k : ℚ) + 1 / 2 - j) := by simp
    _ = _ := by
      rw [← Finset.prod_mul_distrib]
      push_cast
      exact Finset.prod_congr rfl (fun j _ => by ring)

private def colExp (k : ℕ) (j : Fin 3) : ℕ := if j = 1 then k else 2 * k

private def colScale (k : ℕ) (j : Fin 3) : ℚ := 2 ^ colExp k j * (k.factorial : ℚ)

private theorem center_denom (k : ℕ) (i : Fin 3) (r t : ℕ) :
    polePairDenom k i 1 r t = 0 := by simp [polePairDenom, gapExponent, nodeOffset, Fin.add_def]

private theorem diag_denom (k : ℕ) (j : Fin 3) :
    k + polePairDenom k j j 0 0 = colExp k j := by
  fin_cases j <;> simp [polePairDenom, gapExponent, poleOrder, nodeOffset, Fin.add_def, colExp, two_mul]

private theorem gapSign_cast_mod_two (j l : Fin 3) (r : ℕ) : (gapSign j l r : ZMod 2) = 1 := by
  unfold gapSign
  split <;> simp [show (-1 : ZMod 2) = 1 by decide]

private theorem pole_pair_cast_mod_two (k : ℕ) (j : Fin 3) :
    (polePairNumerator k j j 0 0 : ZMod 2) = 1 := by
  simp [polePairNumerator, gapSign_cast_mod_two]

private theorem outer_offset_even {m : ℕ} (hm : m % 2 = 1) {j : Fin 3} (hj : j ≠ 1) :
    (((m : ℤ) + nodeOffset j : ℤ) : ZMod 2) = 0 := by
  apply (ZMod.intCast_eq_intCast_iff _ (0 : ℤ) 2).2
  fin_cases j
  · change (m : ℤ) - 1 ≡ 0 [ZMOD 2]
    unfold Int.ModEq
    omega
  · exact (hj rfl).elim
  · change (m : ℤ) + (2 - 1) ≡ 0 [ZMOD 2]
    unfold Int.ModEq
    omega

private theorem scaled_term_bit {m k h r t : ℕ} {i j : Fin 3} (hm : m % 2 = 1) (hk : 0 < k)
    (hs : h + (r + t) = poleOrder k i j - 1) :
    ∃ b : ℤ, (b : ℚ) = colScale k j * padeTerm m k i j h r t ∧
      (b : ZMod 2) = if h = k then 1 else 0 := by
  let e := polePairDenom k i j r t
  let J := colExp k j
  let U : ℤ := ∏ j' ∈ range h, (2 * (k : ℤ) + 1 - 2 * (j' : ℤ))
  obtain ⟨hle, hhk⟩ := denom_le hk hs
  obtain ⟨s, hsFact⟩ := Nat.factorial_dvd_factorial hhk
  let b : ℤ := (2 : ℤ) ^ (J - (h + e)) * s * U *
    ((m : ℤ) + nodeOffset j) ^ (k - h) * polePairNumerator k i j r t
  refine ⟨b, ?_, ?_⟩
  · have hu : (U : ℚ) = (2 : ℚ) ^ h * (h.factorial : ℚ) * Ring.choose ((k : ℚ) + 1 / 2) h :=
      (half_choose_odd_numerator k h).symm
    dsimp only [b, colScale, padeTerm]
    push_cast
    rw [hu, ← mul_div_assoc]
    change _ = _ / 2 ^ e
    apply (eq_div_iff (by positivity : (2 : ℚ) ^ e ≠ 0)).2
    have hfact : (k.factorial : ℚ) = (h.factorial : ℚ) * (s : ℚ) := by exact_mod_cast hsFact
    rw [hfact]
    have hpow : (2 : ℚ) ^ (J - (h + e)) * 2 ^ h * 2 ^ e = 2 ^ J := by
      rw [← pow_add, ← pow_add]
      congr 1
      change h + e ≤ J at hle
      omega
    linear_combination
      ((s : ℚ) * (h.factorial : ℚ) * Ring.choose ((k : ℚ) + 1 / 2) h *
        (m + (nodeOffset j : ℚ)) ^ (k - h) * (polePairNumerator k i j r t : ℚ)) * hpow
  · by_cases hh : h = k
    · subst h
      have hij : i = j := by
        by_contra hi
        simp only [poleOrder, ite_eq_right hi, add_zero] at hs
        omega
      subst i
      have hr : r = 0 := by simp [poleOrder] at hs; omega
      have ht : t = 0 := by simp [poleOrder] at hs; omega
      subst r
      subst t
      have hJ : J = k + e := (diag_denom k j).symm
      have hs' : s = 1 := by
        apply Nat.mul_left_cancel (Nat.factorial_pos k)
        simpa using hsFact.symm
      have hU : (U : ZMod 2) = 1 := by
        simp [U, show (2 : ZMod 2) = 0 by decide]
      simp [b, hJ, hs', hU, pole_pair_cast_mod_two]
    · have hpos : 0 < k - h := by omega
      by_cases hj : j = 1
      · subst j
        have he0 : e = 0 := center_denom _ _ _ _
        have hJ : J = k := by simp [J, colExp]
        simp [b, he0, hJ, hh, zero_pow hpos.ne', show (2 : ZMod 2) = 0 by decide]
      · simp [b, hh, outer_offset_even hm hj, zero_pow hpos.ne']

private theorem col_scaled_row {m k : ℕ} (hm : m % 2 = 1) (hk : 0 < k) (i j : Fin 3) :
    ∃ b : ℤ, (b : ℚ) = colScale k j * padeCoefficient m k i j ∧
      (b : ZMod 2) = if i = j then 1 else 0 := by
  classical
  have hterm (u : ℕ × ℕ) (v : ℕ × ℕ)
      (hu : u ∈ antidiagonal (poleOrder k i j - 1)) (hv : v ∈ antidiagonal u.2) :=
    scaled_term_bit hm hk (i := i) (j := j) (h := u.1) (r := v.1) (t := v.2)
      (by rw [mem_antidiagonal.mp hv]; exact mem_antidiagonal.mp hu)
  let B (u v : ℕ × ℕ) : ℤ :=
    if hu : u ∈ antidiagonal (poleOrder k i j - 1) then
      if hv : v ∈ antidiagonal u.2 then Classical.choose (hterm u v hu hv) else 0
    else 0
  refine ⟨∑ u ∈ antidiagonal (poleOrder k i j - 1), ∑ v ∈ antidiagonal u.2, B u v, ?_, ?_⟩
  · push_cast
    unfold padeCoefficient
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
    simpa only [B, dite_eq_left hu, dite_eq_left hv] using (Classical.choose_spec (hterm u v hu hv)).1
  · push_cast
    have hv (u : ℕ × ℕ) (hu : u ∈ antidiagonal (poleOrder k i j - 1)) :
        (∑ v ∈ antidiagonal u.2, (B u v : ZMod 2)) =
          ∑ v ∈ antidiagonal u.2, (if u.1 = k then (1 : ZMod 2) else 0) := by
      apply Finset.sum_congr rfl
      intro v hv
      simpa only [B, dite_eq_left hu, dite_eq_left hv] using (Classical.choose_spec (hterm u v hu hv)).2
    calc
      _ = ∑ u ∈ antidiagonal (poleOrder k i j - 1),
          ∑ v ∈ antidiagonal u.2, (if u.1 = k then (1 : ZMod 2) else 0) :=
        Finset.sum_congr rfl hv
      _ = _ := by
        by_cases hi : i = j
        · subst i
          simp only [poleOrder, ↓reduceIte, Nat.add_sub_cancel]
          rw [Finset.sum_eq_single (k, 0)]
          · simp
          · intro u hu hne
            have he := Finset.mem_antidiagonal.mp hu
            have hu₁ : u.1 ≠ k := by
              intro hh
              apply hne
              exact Prod.ext hh (by rw [hh] at he; omega)
            simp [hu₁]
          · simp
        · simp only [poleOrder, hi, ↓reduceIte, add_zero]
          apply Finset.sum_eq_zero
          intro u hu
          have hu' := Finset.mem_antidiagonal.mp hu
          have hu₁ : u.1 ≠ k := by omega
          simp [hu₁]

/-- Independence of the Padé forms follows from a column rescaling that gives the
identity matrix modulo 2. -/
theorem pade_matrix_det_ne_zero {m k : ℕ} (hm : m % 2 = 1) (hk : 0 < k) :
    Matrix.det (padeCoefficient m k : Matrix (Fin 3) (Fin 3) ℚ) ≠ 0 := by
  classical
  let A : Matrix (Fin 3) (Fin 3) ℚ := padeCoefficient m k
  choose B hB h₂ using fun i j => col_scaled_row hm hk i j
  let B' : Matrix (Fin 3) (Fin 3) ℤ := B
  have hscale : B'.map (Int.castRingHom ℚ) =
      A * Matrix.diagonal (colScale k) := by
    ext i j
    change ((B i j : ℤ) : ℚ) = _
    rw [Matrix.mul_diagonal, hB, mul_comm]
  have hmod : B'.map (Int.castRingHom (ZMod 2)) = 1 := by
    ext i j
    change ((B i j : ℤ) : ZMod 2) = _
    simpa [Matrix.one_apply] using h₂ i j
  have hdet : B'.det ≠ 0 := by
    intro hb
    have hc := (Int.castRingHom (ZMod 2)).map_det B'
    change (Int.castRingHom (ZMod 2)) B'.det = (B'.map (Int.castRingHom (ZMod 2))).det at hc
    rw [hb, map_zero, hmod, Matrix.det_one] at hc
    exact zero_ne_one hc
  intro h
  have hh := (Int.castRingHom ℚ).map_det B'
  change (Int.castRingHom ℚ) B'.det = (B'.map (Int.castRingHom ℚ)).det at hh
  change A.det = 0 at h
  rw [hscale, Matrix.det_mul, h, zero_mul] at hh
  change (B'.det : ℚ) = 0 at hh
  exact hdet (by exact_mod_cast hh)

end ThreeFactorials
