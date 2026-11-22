module

public import ThreeFactorials.Case26Local
public import ThreeFactorials.QuarticPell
public import Mathlib.NumberTheory.Pell

import Mathlib.Tactic

/-! Three of the six locally soluble systems are excluded by Pell-unit residues. -/

@[expose] public section

namespace ThreeFactorials

open Pell

/-- Bound the denominator of a positive Pell solution between two adjacent fractions. -/
theorem denominator_bound {d u v r s p q L : ℤ}
    (he : u ^ 2 - d * v ^ 2 = 1) (hu : 0 < u) (hv : 0 < v) (hL : L ≤ v)
    (hp : 0 < p) (hq : 0 < q) (hs : 0 < s) (hr : 0 ≤ r)
    (hlower : r ^ 2 < d * s ^ 2) (hupper : q ^ 2 < (p ^ 2 - d * q ^ 2) * L ^ 2)
    (hLpos : 0 < L) (hadjacent : p * s - r * q = 1) : s + q ≤ v := by
  have hnorm : 0 ≤ p ^ 2 - d * q ^ 2 := by
    by_contra! h
    linarith [mul_neg_of_neg_of_pos h (sq_pos_of_pos hLpos), sq_nonneg q]
  have hlo : r * v < u * s := by
    have hh := mul_lt_mul_of_pos_right hlower (sq_pos_of_pos hv)
    have hi := mul_pos (sq_pos_of_pos hs) (show (0 : ℤ) < 1 by decide)
    have hc := congrArg (fun t : ℤ => t * s ^ 2) he
    apply (sq_lt_sq₀ (mul_nonneg hr hv.le) (mul_nonneg hu.le hs.le)).mp
    nlinarith only [hh, hi, hc]
  have hhi : u * q < p * v := by
    have hh := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hLpos.le hv.le).mpr hL) hnorm
    have hc := congrArg (fun t : ℤ => t * q ^ 2) he
    apply (sq_lt_sq₀ (mul_nonneg hu.le hq.le) (mul_nonneg hp.le hv.le)).mp
    nlinarith only [hupper, hh, hc]
  have h₁ := mul_le_mul_of_nonneg_right (show 1 ≤ u * s - r * v by omega) hq.le
  have h₂ := mul_le_mul_of_nonneg_right (show 1 ≤ p * v - u * q by omega) hs.le
  have hdet := congrArg (fun t : ℤ => t * v) hadjacent
  nlinarith only [h₁, h₂, hdet]

theorem fundamental_of_denominator_bound {d : ℤ} {f : Solution₁ d}
    (hd : 0 < d) (hf₁ : 1 < f.x) (hf₂ : 0 < f.y)
    (bound : ∀ u v : ℤ, 1 < u → 0 < v → u ^ 2 - d * v ^ 2 = 1 → f.y ≤ v) :
    IsFundamental f := by
  refine ⟨hf₁, hf₂, fun {g} hg => ?_⟩
  have hgy : 0 < (g.y.natAbs : ℤ) := by
    exact_mod_cast Int.natAbs_pos.mpr (Solution₁.y_ne_zero_of_one_lt_x hg)
  have he : g.x ^ 2 - d * (g.y.natAbs : ℤ) ^ 2 = 1 := by
    rw [Int.natCast_natAbs, sq_abs]
    exact g.prop
  have hy := bound g.x (g.y.natAbs : ℤ) hg hgy he
  apply (sq_le_sq₀ (by omega) (by omega)).mp
  rw [f.prop_x, show g.x ^ 2 = 1 + d * (g.y.natAbs : ℤ) ^ 2 by linarith]
  exact add_le_add_right (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hf₂.le hgy.le).mpr hy) hd.le) _

private def unit3059 : Solution₁ 3059 :=
  Solution₁.mk 6863751 124100 (by norm_num)

private def unit5474 : Solution₁ 5474 :=
  Solution₁.mk 5475 74 (by norm_num)

private theorem unit3059_fundamental : IsFundamental unit3059 := by
  apply fundamental_of_denominator_bound (by norm_num) (by decide) (by decide)
  intro u v hu hv he
  have h₀ : (1 : ℤ) ≤ v := by omega
  have h₁ := denominator_bound (r := 55) (s := 1) (p := 56) (q := 1) he
    (by omega) hv h₀ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h₂ := denominator_bound (r := 719) (s := 13) (p := 166) (q := 3) he
    (by omega) hv h₁ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h₃ := denominator_bound (r := 8075) (s := 146) (p := 7356) (q := 133) he
    (by omega) hv h₂ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h₄ := denominator_bound (r := 47731) (s := 863) (p := 39656) (q := 717) he
    (by omega) hv h₃ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h₅ := denominator_bound (r := 47731) (s := 863) (p := 278311) (q := 5032) he
    (by omega) hv h₄ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h₆ := denominator_bound (r := 2115595) (s := 38251) (p := 516966) (q := 9347) he
    (by omega) hv h₅ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact denominator_bound (r := 2115595) (s := 38251) (p := 4748156) (q := 85849) he
    (by omega) hv h₆ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem unit5474_fundamental : IsFundamental unit5474 := by
  apply fundamental_of_denominator_bound (by norm_num) (by decide) (by decide)
  intro u v hu hv he
  exact denominator_bound (r := 5401) (s := 73) (p := 74) (q := 1) he
    (by omega) hv (show (1 : ℤ) ≤ v by omega) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The norm-one unit `645 + 2√104006`. -/
def unit104006 : Solution₁ 104006 := Solution₁.mk 645 2 (by norm_num)

theorem pell104006_fundamental : IsFundamental unit104006 := by
  apply fundamental_of_denominator_bound (by norm_num) (by decide) (by decide)
  intro u v hu hv he
  exact denominator_bound (r := 322) (s := 1) (p := 323) (q := 1) he
    (by omega) hv (show (1 : ℤ) ≤ v by omega) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem trace_pow {d : ℤ} (f : Solution₁ d) {m : ℕ} (R : ZMod m → Prop)
    (h₁ : R 1) (hstep : ∀ t : ZMod m, R t → R ((f.x : ZMod m) * t))
    (hvanish : ((d * f.y : ℤ) : ZMod m) = 0) (i : ℕ) :
    R (((f ^ i).x : ℤ) : ZMod m) := by
  induction i with
  | zero => simpa using h₁
  | succ i ih =>
    have hx : (((f ^ (i + 1)).x : ℤ) : ZMod m) =
        (f.x : ZMod m) * (((f ^ i).x : ℤ) : ZMod m) := by
      simp only [Int.cast_mul] at hvanish
      simp only [pow_succ', Solution₁.x_mul, Int.cast_add, Int.cast_mul]
      rw [← mul_assoc, hvanish, zero_mul, add_zero]
    exact hx ▸ (hstep _ ih)

private theorem trace3059_mod4 (i : ℕ) :
    (((unit3059 ^ i).x : ℤ) : ZMod 4) = 1 ∨
      (((unit3059 ^ i).x : ℤ) : ZMod 4) = 3 := by
  refine trace_pow unit3059 (m := 4) (fun t => t = 1 ∨ t = 3) (Or.inl rfl) ?_ (by decide) i
  rintro t (rfl | rfl)
  · right
    decide
  · left
    decide

private theorem trace3059_mod17 (i : ℕ) :
    (((unit3059 ^ i).x : ℤ) : ZMod 17) = 1 := by
  refine trace_pow unit3059 (m := 17) (· = 1) rfl ?_ (by decide) i
  rintro t rfl
  decide

private theorem trace5474_mod23 (i : ℕ) :
    (((unit5474 ^ i).x : ℤ) : ZMod 23) = 1 := by
  refine trace_pow unit5474 (m := 23) (· = 1) rfl ?_ (by decide) i
  rintro t rfl
  decide

private theorem trace_period_four {d : ℤ} (f : Solution₁ d) (m : ℕ)
    (hx : ((f ^ 4).x : ZMod m) = 1) (hy : ((f ^ 4).y : ZMod m) = 0) (i : ℕ) :
    ((f ^ i).x : ZMod m) = ((f ^ (i % 4)).x : ZMod m) := by
  have hperiod (j r : ℕ) : ((f ^ (4 * j + r)).x : ZMod m) = ((f ^ r).x : ZMod m) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show 4 * (j + 1) + r = 4 + (4 * j + r) by omega, pow_add, Solution₁.x_mul]
      simp [hx, hy, ih]
  have hi : 4 * (i / 4) + i % 4 = i := by omega
  simpa only [hi] using hperiod (i / 4) (i % 4)

private theorem trace_pow_four {d : ℤ} (f : Solution₁ d) :
    (f ^ 4).x = 8 * f.x ^ 4 - 8 * f.x ^ 2 + 1 := by
  have hd (g : Solution₁ d) : (g ^ 2).x = 2 * g.x ^ 2 - 1 := by
    rw [pow_two, Solution₁.x_mul]
    linear_combination -g.prop
  rw [show f ^ 4 = (f ^ 2) ^ 2 by rw [← pow_mul], hd, hd]
  ring

/-- The positive-ordinate quartic Pell equation needed for n = 26 has no solution. -/
theorem quartic104006_no_solution {y w : ℕ} (hw : 0 < w) :
    y ^ 4 ≠ 104006 * w ^ 2 + 1 := by
  intro he
  have hy : 0 < y := by
    by_contra! hz
    simp [Nat.eq_zero_of_le_zero hz] at he
  have he' : ((y : ℤ) ^ 2) ^ 2 - 104006 * (w : ℤ) ^ 2 = 1 := by
    have hh : (y : ℤ) ^ 4 = 104006 * (w : ℤ) ^ 2 + 1 := by exact_mod_cast he
    linear_combination hh
  let g := Solution₁.mk (d := 104006) ((y : ℤ) ^ 2) w he'
  obtain ⟨i, hi⟩ := pell104006_fundamental.eq_pow_of_nonneg (a := g)
    (by dsimp [g]; positivity) (by simp [g])
  have hi0 : i ≠ 0 := by
    rintro rfl
    have hp := congrArg Solution₁.y hi
    simp [g] at hp
    omega
  have h8 : (y : ZMod 8) ^ 2 = ((unit104006 ^ (i % 4)).x : ZMod 8) := by
    simpa [← hi, g] using trace_period_four unit104006 8 (by decide) (by decide) i
  have h3 : (y : ZMod 3) ^ 2 = ((unit104006 ^ (i % 4)).x : ZMod 3) := by
    simpa [← hi, g] using trace_period_four unit104006 3 (by decide) (by decide) i
  have hm : i % 4 = 0 := by
    have hor : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
    rcases hor with h | h | h | h
    · exact h
    · rw [h, show ((unit104006 ^ (1 : ℕ)).x : ZMod 8) = 5 by decide] at h8
      exact ((by decide +kernel : ∀ t : ZMod 8, t ^ 2 ≠ 5) y h8).elim
    · rw [h, show ((unit104006 ^ (2 : ℕ)).x : ZMod 3) = 2 by decide] at h3
      exact ((by decide +kernel : ∀ t : ZMod 3, t ^ 2 ≠ 2) y h3).elim
    · rw [h, show ((unit104006 ^ (3 : ℕ)).x : ZMod 8) = 5 by decide] at h8
      exact ((by decide +kernel : ∀ t : ZMod 8, t ^ 2 ≠ 5) y h8).elim
  let b := unit104006 ^ (i / 4)
  have hb : g = b ^ 4 := by
    rw [hi, ← pow_mul]
    congr 1
    omega
  have hbx := Solution₁.x_pow_pos (a := unit104006) (by decide) (i / 4)
  have hby : 0 < b.y := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, i / 4 = k + 1 := ⟨i / 4 - 1, by omega⟩
    dsimp [b]
    rw [hk]
    exact Solution₁.y_pow_succ_pos (a := unit104006) (by decide) (by decide) k
  have hb1 : 1 < b.x := by
    change 0 < b.x at hbx
    nlinarith only [b.prop, sq_pos_of_pos hby, hbx]
  let u := b.x.toNat
  have hu : (u : ℤ) = b.x := Int.toNat_of_nonneg (by omega)
  have hu' : 1 < u := by omega
  have hq := congrArg Solution₁.x hb
  rw [trace_pow_four, ← hu] at hq
  change (y : ℤ) ^ 2 = 8 * (u : ℤ) ^ 4 - 8 * (u : ℤ) ^ 2 + 1 at hq
  have hq' : (y : ℤ) ^ 2 + 8 * (u : ℤ) ^ 2 = 8 * (u : ℤ) ^ 4 + 1 := by linarith
  exact no_square_fourth_trace hu' (by exact_mod_cast hq')

private theorem pell_of_consecutive {A B x y : ℤ} (h : A * x ^ 2 = B * y ^ 2 + 1) :
    (2 * (A * x ^ 2) - 1) ^ 2 - (A * B) * (2 * x * y) ^ 2 = 1 := by
  linear_combination 4 * A * x ^ 2 * h

private theorem exclude_1_3059_34 {x y z : ℕ} (hx : 0 < x)
    (hy : x ^ 2 = 3059 * y ^ 2 + 1) (hz : x ^ 2 = 34 * z ^ 2 + 2) : False := by
  have h : (x : ℤ) ^ 2 - 3059 * (y : ℤ) ^ 2 = 1 := by
    rw [sub_eq_iff_eq_add, add_comm]
    exact_mod_cast hy
  let f := Solution₁.mk (d := 3059) x y h
  obtain ⟨i, hi⟩ := unit3059_fundamental.eq_pow_of_nonneg (a := f)
    (by simpa [f] using (show (0 : ℤ) < x by exact_mod_cast hx)) (by simp [f])
  have hf := trace3059_mod4 i
  rw [← hi] at hf
  have hx' : (x : ZMod 4) = 1 ∨ (x : ZMod 4) = 3 := by simpa [f] using hf
  have hz' : (x : ZMod 4) ^ 2 = 34 * (z : ZMod 4) ^ 2 + 2 := by
    simpa using congrArg (fun t : ℕ => (t : ZMod 4)) hz
  have hm : ∀ s : ZMod 4, (1 : ZMod 4) ≠ 34 * s ^ 2 + 2 := by decide +kernel
  apply hm z
  rcases hx' with h | h
  · simpa [h] using hz'
  · rw [h, show (3 : ZMod 4) ^ 2 = 1 by decide] at hz'
    exact hz'

private theorem exclude_161_19_34 {x y z : ℕ} (hx : 0 < x)
    (hy : 161 * x ^ 2 = 19 * y ^ 2 + 1) (hz : 161 * x ^ 2 = 34 * z ^ 2 + 2) : False := by
  have hy' : 161 * (x : ℤ) ^ 2 = 19 * (y : ℤ) ^ 2 + 1 := by exact_mod_cast hy
  let f : Solution₁ 3059 := Solution₁.mk (2 * (161 * (x : ℤ) ^ 2) - 1)
    (2 * (x : ℤ) * (y : ℤ)) (pell_of_consecutive hy')
  have hx' : (0 : ℤ) < x := by exact_mod_cast hx
  obtain ⟨i, hi⟩ := unit3059_fundamental.eq_pow_of_nonneg (a := f)
    (by dsimp [f]; nlinarith [sq_pos_of_pos hx']) (by dsimp [f]; positivity)
  have hf := trace3059_mod17 i
  rw [← hi] at hf
  have hmod : 161 * (x : ZMod 17) ^ 2 = 34 * (z : ZMod 17) ^ 2 + 2 := by
    simpa using congrArg (fun t : ℕ => (t : ZMod 17)) hz
  simp only [f, Solution₁.x_mk, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_pow,
    Int.cast_natCast, Int.cast_one, hmod] at hf
  have hz0 : (34 : ZMod 17) = 0 := by decide
  rw [hz0, zero_mul, zero_add] at hf
  exact (by decide : (2 * 2 - 1 : ZMod 17) ≠ 1) hf

private theorem exclude_322_17_19 {x y : ℕ} (hx : 0 < x)
    (hy : 322 * x ^ 2 = 17 * y ^ 2 + 1) : False := by
  have hy' : 322 * (x : ℤ) ^ 2 = 17 * (y : ℤ) ^ 2 + 1 := by exact_mod_cast hy
  let f : Solution₁ 5474 := Solution₁.mk (2 * (322 * (x : ℤ) ^ 2) - 1)
    (2 * (x : ℤ) * (y : ℤ)) (pell_of_consecutive hy')
  have hx' : (0 : ℤ) < x := by exact_mod_cast hx
  obtain ⟨i, hi⟩ := unit5474_fundamental.eq_pow_of_nonneg (a := f)
    (by dsimp [f]; nlinarith [sq_pos_of_pos hx']) (by dsimp [f]; positivity)
  have hf := trace5474_mod23 i
  rw [← hi] at hf
  simp only [f, Solution₁.x_mk, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_pow,
    Int.cast_natCast, Int.cast_one] at hf
  have hx0 : (322 : ZMod 23) = 0 := by decide
  rw [hx0, zero_mul, mul_zero, zero_sub] at hf
  exact (by decide : (-1 : ZMod 23) ≠ 1) hf

/-- Pell-unit residues reduce the six local systems to three. -/
theorem solution26_pell {a : ℕ} (h : Solution a 26) :
    ∃ (t : ℕ × ℕ × ℕ) (x y z : ℕ),
      (t = (1, 323, 322) ∨ t = (2, 1, 52003) ∨ t = (2, 2737, 19)) ∧
      a = t.1 * x ^ 2 ∧ a - 1 = t.2.1 * y ^ 2 ∧ a - 2 = t.2.2 * z ^ 2 := by
  obtain ⟨t, x, y, z, ht, ha, hb, hc⟩ := solution26_local h
  have hx : 0 < x := by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp at ha
      have := h.2.1
      omega
    · exact hx
  have hy : t.1 * x ^ 2 = t.2.1 * y ^ 2 + 1 := by have := h.2.1; omega
  have hz : t.1 * x ^ 2 = t.2.2 * z ^ 2 + 2 := by have := h.2.1; omega
  simp only [coefficients26, List.mem_cons, List.not_mem_nil, or_false] at ht
  refine ⟨t, x, y, z, ?_, ha, hb, hc⟩
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact (exclude_1_3059_34 hx (by simpa using hy) (by simpa using hz)).elim
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact (exclude_161_19_34 hx hy hz).elim
  · exact (exclude_322_17_19 hx hy).elim

private theorem exclude_2_1_52003 {x y z : ℕ}
    (hx : 0 < x) (hz : 0 < z)
    (hy : 2 * x ^ 2 = y ^ 2 + 1) (he : 2 * x ^ 2 = 52003 * z ^ 2 + 2) : False := by
  have hy' : 2 * (x : ℤ) ^ 2 = (y : ℤ) ^ 2 + 1 := by exact_mod_cast hy
  have he' : 2 * (x : ℤ) ^ 2 = 52003 * (z : ℤ) ^ 2 + 2 := by exact_mod_cast he
  have hq : (y : ℤ) ^ 4 = 104006 * ((x : ℤ) * (z : ℤ)) ^ 2 + 1 := by
    linear_combination -(y ^ 2 - 1 : ℤ) * hy' + 2 * (x : ℤ) ^ 2 * (he' - hy')
  exact quartic104006_no_solution (Nat.mul_pos hx hz) (by exact_mod_cast hq)

/-- Only the two squarefree systems with known solutions can occur at n = 26. -/
theorem solution26_remaining {a : ℕ} (h : Solution a 26) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      ((a = x ^ 2 ∧ a - 1 = 323 * y ^ 2 ∧ a - 2 = 322 * z ^ 2) ∨
       (a = 2 * x ^ 2 ∧ a - 1 = 2737 * y ^ 2 ∧ a - 2 = 19 * z ^ 2)) := by
  obtain ⟨t, x, y, z, ht, ha, hb, hc⟩ := solution26_pell h
  have ha' : 29 < a := h.2.1
  have hx : 0 < x := by
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz, zero_pow (by decide), mul_zero] at ha
    omega
  have hy : 0 < y := by
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz, zero_pow (by decide), mul_zero] at hb
    omega
  have hz : 0 < z := by
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz, zero_pow (by decide), mul_zero] at hc
    omega
  refine ⟨x, y, z, hx, hy, hz, ?_⟩
  rcases ht with rfl | rfl | rfl
  · exact Or.inl ⟨by simpa using ha, hb, hc⟩
  · change a = 2 * x ^ 2 at ha
    change a - 2 = 52003 * z ^ 2 at hc
    have hb' : a - 1 = y ^ 2 := by simpa using hb
    have hab : 2 * x ^ 2 = y ^ 2 + 1 := by
      rw [← ha, ← hb']
      exact (Nat.sub_add_cancel ((by decide : 1 ≤ 29).trans ha'.le)).symm
    have hac : 2 * x ^ 2 = 52003 * z ^ 2 + 2 := by
      rw [← ha, ← hc]
      exact (Nat.sub_add_cancel ((by decide : 2 ≤ 29).trans ha'.le)).symm
    exact (exclude_2_1_52003 hx hz hab hac).elim
  · exact Or.inr ⟨ha, hb, hc⟩

/-- The first-coordinate uniqueness in Bennett's theorem on consecutive square multiples. -/
def BennettConsecutiveUnique : Prop :=
  ∀ A B C x y z u v w : ℕ,
    0 < A → 0 < B → 0 < C →
    0 < x → 0 < y → 0 < z → 0 < u → 0 < v → 0 < w →
    A * x ^ 2 = B * y ^ 2 + 1 → B * y ^ 2 = C * z ^ 2 + 1 →
    A * u ^ 2 = B * v ^ 2 + 1 → B * v ^ 2 = C * w ^ 2 + 1 →
    x = u

/-- An alternative to the integral-point route, using Bennett's uniqueness theorem. -/
theorem case26_iff_of_bennett (unique : BennettConsecutiveUnique)
    (a : ℕ) : Solution a 26 ↔ a = 324 ∨ a = 2738 := by
  constructor
  · intro h
    obtain ⟨x, y, z, hx, hy, hz, hc⟩ := solution26_remaining h
    have ha' : 29 < a := h.2.1
    have hab : a = a - 1 + 1 := by omega
    have hbc : a - 1 = a - 2 + 1 := by omega
    rcases hc with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
    · left
      have h := unique 1 323 322 x y z 18 1 1 (by decide) (by decide) (by decide) hx hy hz
        (by decide) (by decide) (by decide)
        (by rw [one_mul, ← ha, ← hb]; exact hab) (by rw [← hb, ← hc]; exact hbc)
        (by decide) (by decide)
      simpa [h] using ha
    · right
      have h := unique 2 2737 19 x y z 37 1 12 (by decide) (by decide) (by decide) hx hy hz
        (by decide) (by decide) (by decide)
        (by rw [← ha, ← hb]; exact hab) (by rw [← hb, ← hc]; exact hbc)
        (by decide) (by decide)
      simpa [h] using ha
  · rintro (rfl | rfl)
    · exact solution324_26
    · exact solution2738_26

end ThreeFactorials
