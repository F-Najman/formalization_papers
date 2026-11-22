module

public import ThreeFactorials.Classification
public import ThreeFactorials.IntervalPrimes

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Factorial

/-! The square-removal argument in the reviewed proof of Theorem 1.2(c). -/

@[expose] public section

namespace ThreeFactorials

open Finset

/-- The four forms in part (c), with the published constants. -/
inductive ForbiddenForm : ℕ → Prop
  | prime {α p : ℕ} (hp : p.Prime) (hα : α ≤ 64393) : ForbiddenForm (α * p)
  | cube {α p : ℕ} (hp : p.Prime) (hα : α ≤ 6) : ForbiddenForm (α * p ^ 3)
  | pair {α p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (hα : α ≤ 637) :
      ForbiddenForm (α * (p * q))
  | triple {α p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
      (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hα : α ≤ 6) :
      ForbiddenForm (α * (p * q * r))

private theorem supported_form {a n N α C : ℕ} {factors : List ℕ}
    (h : Solution a n) (hN : N = a ∨ N = a - 1 ∨ N = a - 2)
    (hn : 101 ≤ n) (hc : 11 ≤ (intervalPrimes n).card)
    (he : N = α * factors.prod) (hs : ∀ p ∈ factors, p ≤ n)
    (hr₁ : 1 ≤ factors.length) (hr₂ : factors.length ≤ 4)
    (hα : α ≤ C) (hC : 16 * C + 1 ≤ 101 ^ (4 - factors.length)) : False := by
  have hp : 32 ≤ n ^ factors.length :=
    (show 32 ≤ n ^ 1 by simpa using (show 32 ≤ n by omega)).trans
      (pow_le_pow_right₀ (by omega : 1 ≤ n) hr₁)
  have hm : 4 ≤ exponent n := by unfold exponent; omega
  have hbase : 16 * C + 1 ≤ n ^ (4 - factors.length) :=
    hC.trans (pow_le_pow_left' hn _)
  have hle : 16 * (α * n ^ factors.length + 2) ≤ n ^ 4 := calc
    _ ≤ (16 * C + 1) * n ^ factors.length := by
      have hh := Nat.mul_le_mul_right (n ^ factors.length) hα
      rw [Nat.mul_add, Nat.add_mul, one_mul, Nat.mul_assoc]
      omega
    _ ≤ n ^ (4 - factors.length) * n ^ factors.length := Nat.mul_le_mul_right _ hbase
    _ = n ^ 4 := by rw [← pow_add, Nat.sub_add_cancel hr₂]
  have hle' : (16 : ℚ) * ((α : ℚ) * (n : ℚ) ^ factors.length + 2) ≤ (n : ℚ) ^ 4 := by
    exact_mod_cast hle
  have h₁ : (1 : ℚ) ≤ (n : ℚ) / 2 := by
    have : (101 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  apply theorem12b_supported h hN he hs
  refine le_trans ?_ (pow_le_pow_right₀ h₁ hm)
  rw [div_pow]
  norm_num1
  exact (le_div_iff₀ (by norm_num : (0 : ℚ) < 16)).mpr (by simpa [mul_comm] using hle')

private theorem alpha_dvd_of_outside {a n N α m p : ℕ} (h : Solution a n)
    (hN : N = a ∨ N = a - 1 ∨ N = a - 2) (he : N = α * m)
    (hp : p.Prime) (hnp : n < p) (hm : Odd (m.factorization p)) : p ∣ α := by
  by_contra hn
  have hNz : N ≠ 0 := by
    have := h.2.1
    rcases hN with hN | hN | hN <;> omega
  have hz : α * m ≠ 0 := he ▸ hNz
  have hEven := outside_prime_even h hN hp hnp
  rw [he, Nat.factorization_mul (left_ne_zero_of_mul hz) (right_ne_zero_of_mul hz),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hn, zero_add] at hEven
  obtain ⟨j, hj⟩ := hm
  obtain ⟨k, hk⟩ := hEven
  omega

private theorem square_removal_bound {a n N d t s p : ℕ} (h : Solution a n)
    (hN : N = a ∨ N = a - 1 ∨ N = a - 2) (hp : p.Prime) (hnp : n < p)
    (hdf : d ∣ n.factorial) (he : block a = d * t ^ 2) (hNd : N = p ^ 2 * s) :
    d ≤ s * (N + 2) ^ 2 := by
  have hd : ¬ p ∣ d := fun h => (hp.dvd_factorial.mp (h.trans hdf)).not_gt hnp
  have hdN : p ∣ N := ⟨p * s, by rw [hNd]; ring⟩
  have hdblock : p ∣ block a := by
    unfold block
    rw [hp.dvd_mul, hp.dvd_mul]
    rcases hN with hN | hN | hN
    · exact Or.inl (Or.inl (hN ▸ hdN))
    · exact Or.inl (Or.inr (hN ▸ hdN))
    · exact Or.inr (hN ▸ hdN)
  rw [he, hp.dvd_mul] at hdblock
  have hdt := hp.dvd_of_dvd_pow (hdblock.resolve_left hd)
  obtain ⟨u, rfl⟩ := hdt
  have hpos := block_pos (show 2 < a by have := h.2.1; omega)
  have hu : 1 ≤ u := by
    by_contra! h
    have : u = 0 := by omega
    simp [this] at he
    omega
  have hub : ∀ k : ℕ, k ≤ a → k ≤ N + 2 := by
    have := h.2.1
    rcases hN with hN | hN | hN <;> omega
  have hle : block a ≤ N * (N + 2) ^ 2 := by
    have h₀ := hub a le_rfl
    have h₁ := hub (a - 1) (Nat.sub_le _ _)
    have h₂ := hub (a - 2) (Nat.sub_le _ _)
    unfold block
    rcases hN with hN | hN | hN
    · simpa [hN, pow_two, mul_assoc] using
        (Nat.mul_le_mul (Nat.mul_le_mul (le_refl a) h₁) h₂)
    · simpa [hN, pow_two, mul_assoc, mul_left_comm, mul_comm] using
        (Nat.mul_le_mul (Nat.mul_le_mul h₀ (le_refl (a - 1))) h₂)
    · simpa [hN, pow_two, mul_assoc, mul_left_comm, mul_comm] using
        (Nat.mul_le_mul (Nat.mul_le_mul h₀ h₁) (le_refl (a - 2)))
  rw [he, mul_pow] at hle
  conv at hle => rhs; lhs; rw [hNd]
  have hle' : p ^ 2 * (d * u ^ 2) ≤ p ^ 2 * (s * (N + 2) ^ 2) := by
    simpa [mul_assoc, mul_left_comm] using hle
  exact (le_mul_of_one_le_right' (pow_le_pow_left' hu 2)).trans
    (Nat.le_of_mul_le_mul_left hle' (pow_pos hp.pos 2))

private theorem sqfree_half_lt {n d k : ℕ} (hn : 101 ≤ n)
    (hc : 11 ≤ (intervalPrimes n).card) (hf : n.factorial = d * k ^ 2) :
    ((n : ℚ) / 2) ^ 11 < d := by
  have h₁ : (1 : ℚ) ≤ (n : ℚ) / 2 := by
    have : (101 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have hd : 0 < d := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    simp [Nat.factorial_ne_zero] at hf
  have hprod := Nat.le_of_dvd hd (interval_prod_dvd hf)
  have hprod' : (∏ p ∈ intervalPrimes n, (p : ℚ)) ≤ (d : ℚ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hprod
  refine (pow_le_pow_right₀ h₁ hc).trans_lt (lt_of_lt_of_le ?_ hprod')
  rw [← Finset.prod_const]
  refine Finset.prod_lt_prod_of_nonempty₀ (fun _ _ => by linarith) (fun p hp => ?_)
    (Finset.card_pos.mp (by omega))
  have hp' := (Finset.mem_filter.mp hp).2
  have : (n : ℚ) < 2 * (p : ℚ) := by exact_mod_cast (show n < 2 * p by omega)
  linarith

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem small_outside_bound :
    ∀ n ∈ List.range' 101 19, 17193117685869576969 < ∏ p ∈ intervalPrimes n, p := by
  decide +kernel

private theorem square_removed_estimate {α p s q n C : ℕ}
    (hα : α ≤ C) (he : α = p * s) (hp : 0 < p) (hq : q ≤ n) (hn : 1 ≤ n) :
    s * q * (p ^ 2 * (s * q) + 2) ^ 2 ≤ (C ^ 4 + 4 * C ^ 2 + 4 * C) * n ^ 3 := by
  have hs : s ≤ α := by rw [he]; exact Nat.le_mul_of_pos_left _ hp
  have hc₄ : α ^ 4 ≤ C ^ 4 := pow_le_pow_left' hα 4
  have hc₂ : α ^ 2 ≤ C ^ 2 := pow_le_pow_left' hα 2
  have hon : q ^ 2 ≤ n ^ 3 := (pow_le_pow_left' hq 2).trans (pow_le_pow_right₀ hn (by decide))
  have hlin : q ≤ n ^ 3 := by
    simpa using (pow_le_pow_left' hq 1).trans (pow_le_pow_right₀ hn (show 1 ≤ 3 by decide))
  calc
    _ = p * α ^ 3 * q ^ 3 + 4 * α ^ 2 * q ^ 2 + 4 * s * q := by rw [he]; ring
    _ ≤ C ^ 4 * n ^ 3 + 4 * C ^ 2 * n ^ 3 + 4 * C * n ^ 3 := by
      by_cases hz : s = 0
      · simp [hz, he]
      · have hpα : p ≤ α := by rw [he]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hz)
        have hpa : p * α ^ 3 ≤ C ^ 4 := by
          calc
            p * α ^ 3 ≤ α * α ^ 3 := Nat.mul_le_mul_right _ hpα
            _ = α ^ 4 := by ring
            _ ≤ C ^ 4 := hc₄
        exact Nat.add_le_add
          (Nat.add_le_add (Nat.mul_le_mul hpa (pow_le_pow_left' hq 3))
            (Nat.mul_le_mul (Nat.mul_le_mul_left _ hc₂) hon))
          (Nat.mul_le_mul (Nat.mul_le_mul_left _ (hs.trans hα)) hlin)
    _ = _ := by ring

private theorem other_prime_factorization {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) : q.factorization p = 0 :=
  Nat.factorization_eq_zero_of_not_dvd
    (fun h => hne (((Nat.dvd_prime hq).mp h).resolve_left hp.ne_one))

private theorem outside_pair {a n α p q : ℕ} (h : Solution a n)
    (hN : α * (p * q) = a ∨ α * (p * q) = a - 1 ∨ α * (p * q) = a - 2)
    (hn : 101 ≤ n) (hc : 11 ≤ (intervalPrimes n).card)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (hα : α ≤ 637) (hnp : n < p) : False := by
  have hodd₁ : Odd ((p * q).factorization p) := by
    rw [Nat.factorization_mul hp.ne_zero hq.ne_zero, Finsupp.add_apply,
      hp.factorization_self, other_prime_factorization hp hq hne, add_zero]
    decide
  have hodd₂ : Odd ((p * q).factorization q) := by
    rw [Nat.factorization_mul hp.ne_zero hq.ne_zero, Finsupp.add_apply,
      hq.factorization_self, other_prime_factorization hq hp hne.symm, zero_add]
    decide
  have hpα := alpha_dvd_of_outside h hN rfl hp hnp hodd₁
  have hqn : q ≤ n := by
    by_contra! hq'
    have hqα := alpha_dvd_of_outside h hN rfl hq hq' hodd₂
    have hα₀ : 0 < α := by
      have := h.2.1
      by_contra! hz
      simp [Nat.eq_zero_of_le_zero hz] at hN
      omega
    have hdiv := ((Nat.coprime_primes hp hq).mpr hne).mul_dvd_of_dvd_of_dvd hpα hqα
    have hle := Nat.le_of_dvd hα₀ hdiv
    have hlarge : 102 * 102 ≤ p * q := Nat.mul_le_mul (by omega) (by omega)
    omega
  obtain ⟨s, hs⟩ := hpα
  obtain ⟨d, k, hd, hk, hf, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Nat.factorial_pos n)
  have hf' : n.factorial = d * k ^ 2 := by simpa [mul_comm] using hf.symm
  obtain ⟨_, _, t, ht⟩ := (solution_iff_squarefree hf' hsq hk).mp h
  have hdiv : d ∣ n.factorial := ⟨k ^ 2, hf'⟩
  have hN' : α * (p * q) = p ^ 2 * (s * q) := by rw [hs]; ring
  have hub := square_removal_bound h hN hp hnp hdiv ht hN'
  rw [hN'] at hub
  have hdle : d ≤ 164650106985 * n ^ 3 := hub.trans
    (square_removed_estimate hα hs hp.pos hqn (by omega))
  have hdl : ((n : ℚ) / 2) ^ 11 < (d : ℚ) := sqfree_half_lt hn hc hf'
  have hl : (164650106985 : ℚ) * (n : ℚ) ^ 3 ≤ ((n : ℚ) / 2) ^ 11 := by
    have hn' : (101 : ℚ) ≤ n := by exact_mod_cast hn
    have h8 : (2 : ℚ) ^ 11 * 164650106985 ≤ (n : ℚ) ^ 8 :=
      (by norm_num : (2 : ℚ) ^ 11 * 164650106985 ≤ 101 ^ 8).trans
        (pow_le_pow_left₀ (by norm_num) hn' 8)
    rw [div_pow, le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ 11)]
    calc
      _ = (2 ^ 11 * 164650106985 : ℚ) * (n : ℚ) ^ 3 := by ring
      _ ≤ (n : ℚ) ^ 8 * (n : ℚ) ^ 3 := mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = _ := by ring
  exact hdl.not_ge ((by exact_mod_cast hdle :
    (d : ℚ) ≤ 164650106985 * (n : ℚ) ^ 3).trans hl)

private theorem outside_single {a n α p : ℕ} (h : Solution a n)
    (hN : α * p = a ∨ α * p = a - 1 ∨ α * p = a - 2)
    (hn : 101 ≤ n) (hc : 11 ≤ (intervalPrimes n).card)
    (hp : p.Prime) (hα : α ≤ 64393) (hnp : n < p) : False := by
  have hodd : Odd (p.factorization p) := by rw [hp.factorization_self]; decide
  obtain ⟨s, hs⟩ := alpha_dvd_of_outside h hN rfl hp hnp hodd
  obtain ⟨d, k, hd, hk, hf, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Nat.factorial_pos n)
  have hf' : n.factorial = d * k ^ 2 := by simpa [mul_comm] using hf.symm
  obtain ⟨_, _, t, ht⟩ := (solution_iff_squarefree hf' hsq hk).mp h
  have hdiv : d ∣ n.factorial := ⟨k ^ 2, hf'⟩
  have hN' : α * p = p ^ 2 * s := by rw [hs]; ring
  have hub := square_removal_bound h hN hp hnp hdiv ht hN'
  rw [hN'] at hub
  have hub' := square_removed_estimate (q := 1) (n := 1) hα hs hp.pos le_rfl le_rfl
  have hdle : d ≤ 17193117685869576969 := hub.trans (by simpa using hub')
  by_cases hn' : n ≤ 119
  · have hmem : n ∈ List.range' 101 19 := by
      rw [List.mem_range'_1]
      omega
    have hsmall := small_outside_bound n hmem
    exact hsmall.not_ge ((Nat.le_of_dvd hd (interval_prod_dvd hf')).trans hdle)
  · have hdl : ((n : ℚ) / 2) ^ 11 < d := sqfree_half_lt hn hc hf'
    have hn120 : (120 : ℚ) ≤ n := by exact_mod_cast (show 120 ≤ n by omega)
    have hle : (17193117685869576969 : ℚ) ≤ ((n : ℚ) / 2) ^ 11 :=
      (by norm_num : (17193117685869576969 : ℚ) ≤ (120 / 2) ^ 11).trans
        (pow_le_pow_left₀ (by norm_num) (by linarith) _)
    exact hdl.not_ge ((by exact_mod_cast hdle : (d : ℚ) ≤ 17193117685869576969).trans hle)

/-- Part (c) for n at least 101, including forms with primes outside the support of n!. -/
theorem theorem12c_large {a n N : ℕ} (h : Solution a n)
    (hN : N = a ∨ N = a - 1 ∨ N = a - 2) (hn : 101 ≤ n) : ¬ ForbiddenForm N := by
  have hc := interval_card_ge_eleven hn
  intro form
  have supported_of_odd {α m p : ℕ} (hN' : N = α * m) (hα : α ≤ 6) (hp : p.Prime)
      (hodd : Odd (m.factorization p)) : p ≤ n := by
    have hα₀ : 0 < α := by
      have := h.2.1
      by_contra! hz
      simp [hN', Nat.eq_zero_of_le_zero hz] at hN
      omega
    by_contra! hnp
    have := Nat.le_of_dvd hα₀ (alpha_dvd_of_outside h hN hN' hp hnp hodd)
    omega
  cases form with
  | @prime α p hp hα =>
    by_cases hpn : p ≤ n
    · exact supported_form (factors := [p]) h hN hn hc (by simp)
        (by simpa) (by simp) (by simp) hα (by norm_num)
    · exact outside_single h hN hn hc hp hα (by omega)
  | @cube α p hp hα =>
    have hpn : p ≤ n := supported_of_odd rfl hα hp (by rw [Nat.factorization_pow_self hp]; decide)
    exact supported_form (factors := [p, p, p]) h hN hn hc (by simp [pow_succ, mul_assoc])
      (by simpa) (by simp) (by simp) hα (by norm_num)
  | @pair α p q hp hq hne hα =>
    by_cases hpn : p ≤ n
    · by_cases hqn : q ≤ n
      · exact supported_form (factors := [p, q]) h hN hn hc (by simp)
          (by simp [hpn, hqn]) (by simp) (by simp) hα (by norm_num)
      · rw [mul_comm p q] at hN
        exact outside_pair h hN hn hc hq hp hne.symm hα (by omega)
    · exact outside_pair h hN hn hc hp hq hne hα (by omega)
  | @triple α p q r hp hq hr hpq hpr hqr hα =>
    have hfac (p' : ℕ) : (p * q * r).factorization p' =
        p.factorization p' + q.factorization p' + r.factorization p' := by
      rw [Nat.factorization_mul (mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero,
        Nat.factorization_mul hp.ne_zero hq.ne_zero, Finsupp.add_apply, Finsupp.add_apply]
    have hpn := supported_of_odd rfl hα hp (by
      rw [hfac, hp.factorization_self, other_prime_factorization hp hq hpq,
        other_prime_factorization hp hr hpr]; decide)
    have hqn := supported_of_odd rfl hα hq (by
      rw [hfac, hq.factorization_self, other_prime_factorization hq hp hpq.symm,
        other_prime_factorization hq hr hqr]; decide)
    have hrn := supported_of_odd rfl hα hr (by
      rw [hfac, hr.factorization_self, other_prime_factorization hr hp hpr.symm,
        other_prime_factorization hr hq hqr.symm]; decide)
    exact supported_form (factors := [p, q, r]) h hN hn hc (by simp [mul_assoc])
      (by simp [hpn, hqn, hrn]) (by simp) (by simp) hα (by norm_num)

/-- The reviewed form of part (c), using Theorem 1.1. -/
theorem theorem12c_of_classification
    (classify : ∀ a n : ℕ, n ≤ 100 → Solution a n → (a, n) ∈ solutionsUpTo100)
    {a n N : ℕ} (h : Solution a n) (hN : N = a ∨ N = a - 1 ∨ N = a - 2)
    (form : ForbiddenForm N) : (a, n) ∈ solutionsUpTo100 := by
  by_cases hn : n ≤ 100
  · exact classify a n hn h
  · have hn' : 101 ≤ n := by omega
    exact (theorem12c_large h hN hn' form).elim

end ThreeFactorials
