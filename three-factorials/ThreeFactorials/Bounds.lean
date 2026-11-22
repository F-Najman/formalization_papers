module

public import ThreeFactorials.Basic
public import Mathlib.NumberTheory.PrimeCounting

import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic

/-! The unconditional estimates in Theorem 1.2(a) and the corrected Theorem 1.2(b). -/

@[expose] public section

namespace ThreeFactorials

open Finset

/-- The primes in the half interval (n/2,n]. -/
def intervalPrimes (n : ℕ) : Finset ℕ :=
  n.primesLE.filter fun p => n / 2 < p

theorem intervalPrimes_card (n : ℕ) :
    (intervalPrimes n).card = Nat.primeCounting n - Nat.primeCounting (n / 2) := by
  have h : intervalPrimes n = n.primesLE \ (n / 2).primesLE := by
    ext p
    by_cases hp : p.Prime <;> simp [intervalPrimes, Nat.mem_primesLE, hp]
  rw [h, Finset.card_sdiff_of_subset (Nat.primesLE_mono (Nat.div_le_self n 2))]
  simp

/-- The ceiling of one third of the number of primes in the half interval. -/
def exponent (n : ℕ) : ℕ :=
  ((intervalPrimes n).card + 2) / 3

private theorem interval_factorization {p n : ℕ} (hp : p ∈ intervalPrimes n) :
    n.factorial.factorization p = 1 := by
  obtain ⟨hpMem, hpHalf⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpn, hpPrime⟩ := Nat.mem_primesLE.mp hpMem
  have hn2p : n < 2 * p := by omega
  have hp2 : 2 * p ≤ p ^ 2 := by
    simpa [pow_two, mul_comm] using Nat.mul_le_mul_left p hpPrime.two_le
  have hlog : Nat.log p n < 2 :=
    (Nat.log_lt_iff_lt_pow hpPrime.one_lt (by omega)).mpr (hn2p.trans_le hp2)
  have hquot : n / p = 1 := by
    exact Nat.div_eq_of_lt_le (by simpa using hpn) (by simpa using hn2p)
  simpa [show Finset.Ico 1 2 = {1} by decide, hquot] using
    Nat.factorization_factorial hpPrime hlog

private theorem interval_prime_dvd_block {a n p : ℕ} (ha : 2 < a)
    (hs : IsSquare (block a * n.factorial)) (hp : p ∈ intervalPrimes n) :
    p ∣ block a := by
  have hpPrime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
  by_contra h
  have heven := Nat.isSquare_iff_even_factorization.mp hs p hpPrime
  rw [Nat.factorization_mul (block_pos ha).ne' (Nat.factorial_ne_zero n),
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd h, interval_factorization hp,
    zero_add] at heven
  exact (by decide : ¬ Even (1 : ℕ)) heven

/-- Theorem 1.2(a). -/
theorem theorem12a {a n : ℕ} (h : Solution a n) :
    ((n : ℚ) / 2) ^ exponent n < a := by
  obtain ⟨hn, ha, hs⟩ := solution_iff.mp h
  by_cases hm : exponent n = 0
  · rw [hm, pow_zero]
    exact_mod_cast (show 1 < a by omega)
  let bucket (p : ℕ) : Fin 3 :=
    if p ∣ a then 0 else if p ∣ a - 1 then 1 else 2
  have hdvd {p : ℕ} (hp : p ∈ intervalPrimes n) : p ∣ block a :=
    interval_prime_dvd_block (by omega) hs hp
  have hbucket {p : ℕ} (hp : p ∈ intervalPrimes n) :
      p ∣ a - (bucket p : ℕ) := by
    have hprime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    unfold bucket
    split
    · simpa using ‹p ∣ a›
    split
    · exact ‹p ∣ a - 1›
    · have hd := hdvd hp
      rw [block, hprime.dvd_mul, hprime.dvd_mul] at hd
      exact hd.resolve_left (not_or_intro ‹¬ p ∣ a› ‹¬ p ∣ a - 1›)
  have hm' : 3 * (exponent n - 1) < (intervalPrimes n).card := by
    unfold exponent at *
    omega
  obtain ⟨j, _, hcard⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := intervalPrimes n) (t := (Finset.univ : Finset (Fin 3))) (f := bucket)
      (fun _ _ => Finset.mem_univ _) (by simpa using hm')
  let chosen := (intervalPrimes n).filter (fun p => bucket p = j)
  have hchosen : exponent n ≤ chosen.card := by
    change exponent n - 1 < chosen.card at hcard
    omega
  have hpos : 0 < a - j.val := by
    have := j.isLt
    omega
  have hcdvd : (∏ p ∈ chosen, p) ∣ a - j.val := by
    refine Finset.prod_dvd_of_isRelPrime ?_ ?_
    · intro p hp q hq hpq
      apply Nat.coprime_iff_isRelPrime.mp
      exact (Nat.coprime_primes
        (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)
        (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)).mpr hpq
    · intro p hp
      obtain ⟨hmem, heq⟩ := Finset.mem_filter.mp hp
      simpa [heq] using hbucket hmem
  have hprod : (∏ p ∈ chosen, p) ≤ a :=
    (Nat.le_of_dvd hpos hcdvd).trans (Nat.sub_le _ _)
  have h1 : (1 : ℚ) ≤ (n : ℚ) / 2 := by
    have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have hlt : ((n : ℚ) / 2) ^ chosen.card < ∏ p ∈ chosen, (p : ℚ) := by
    rw [← Finset.prod_const]
    refine Finset.prod_lt_prod_of_nonempty₀ (fun _ _ => by linarith)
      (fun p hp => ?_) (Finset.card_pos.mp (by omega))
    have hpHalf := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hn2p : n < 2 * p := by omega
    have : (n : ℚ) < 2 * (p : ℚ) := by exact_mod_cast hn2p
    linarith
  have hprod' : (∏ p ∈ chosen, (p : ℚ)) ≤ (a : ℚ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast hprod
  exact (pow_le_pow_right₀ h1 hchosen).trans_lt (hlt.trans_le hprod')

private theorem list_prod_le_pow {n : ℕ} {factors : List ℕ}
    (hs : ∀ p ∈ factors, p ≤ n) : factors.prod ≤ n ^ factors.length := by
  induction factors with
  | nil => simp
  | cons p tail ih =>
    simpa [List.prod_cons, pow_succ'] using
      Nat.mul_le_mul (hs p (List.mem_cons_self ..)) (ih (fun p hp => hs p (List.mem_cons_of_mem _ hp)))

/-- The corrected part (b). The list records the factors of N₁ with multiplicity.
The support hypothesis is that each listed factor is at most n.
The bound is written after multiplying by n to the length of the list. -/
theorem theorem12b_supported {a n N α : ℕ} {factors : List ℕ}
    (h : Solution a n) (hN : N = a ∨ N = a - 1 ∨ N = a - 2)
    (he : N = α * factors.prod) (hs : ∀ p ∈ factors, p ≤ n) :
    ¬ ((α : ℚ) * (n : ℚ) ^ factors.length + 2 ≤ ((n : ℚ) / 2) ^ exponent n) := by
  intro hbound
  have ha := h.2.1
  have hN' : a ≤ N + 2 := by rcases hN with hN | hN | hN <;> omega
  have hprod := list_prod_le_pow hs
  have hle : a ≤ α * n ^ factors.length + 2 :=
    hN'.trans (by rw [he]; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hprod) _)
  have hle' : (a : ℚ) ≤ (α : ℚ) * (n : ℚ) ^ factors.length + 2 := by exact_mod_cast hle
  exact (not_lt_of_ge (hle'.trans hbound)) (theorem12a h)

/-- The corrected part (b) in the paper's fractional form. -/
theorem theorem12b_fraction {a n N α : ℕ} {factors : List ℕ}
    (h : Solution a n) (hN : N = a ∨ N = a - 1 ∨ N = a - 2)
    (he : N = α * factors.prod) (hs : ∀ p ∈ factors, p ≤ n)
    (hr : factors.length ≤ exponent n) :
    (n : ℚ) ^ (exponent n - factors.length) / 2 ^ exponent n -
      2 / (n : ℚ) ^ factors.length < α := by
  have hn : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by have := h.1; omega)
  have hd : 0 < (n : ℚ) ^ factors.length := pow_pos hn _
  have heq :
      ((n : ℚ) ^ (exponent n - factors.length) / 2 ^ exponent n -
        2 / (n : ℚ) ^ factors.length) * (n : ℚ) ^ factors.length + 2 =
        ((n : ℚ) / 2) ^ exponent n := by
    calc
      _ = ((n : ℚ) ^ (exponent n - factors.length) * (n : ℚ) ^ factors.length) /
          2 ^ exponent n := by field_simp; ring
      _ = _ := by rw [← pow_add, Nat.sub_add_cancel hr, div_pow]
  by_contra! hbound
  exact theorem12b_supported h hN he hs
    ((add_le_add_left (mul_le_mul_of_nonneg_right hbound hd.le) 2).trans_eq heq)

/-- Outside the factorial support, a prime appears to even valuation in any of the
three factors. A prime above n is greater than 2 and can divide at most one factor. -/
theorem outside_prime_even {a n N p : ℕ} (h : Solution a n)
    (hN : N = a ∨ N = a - 1 ∨ N = a - 2) (hp : p.Prime) (hnp : n < p) :
    Even (N.factorization p) := by
  obtain ⟨hn, ha, hs⟩ := solution_iff.mp h
  have ha₀ : a ≠ 0 := by omega
  have ha₁ : a - 1 ≠ 0 := by omega
  have ha₂ : a - 2 ≠ 0 := by omega
  have hp₂ : 2 < p := by omega
  by_cases hdiv : p ∣ N
  · have hpair {u v : ℕ} (hvu : v < u) (huv : u ≤ v + 2) (hu : p ∣ u) (hv : p ∣ v) :
        False := by
      have := Nat.le_of_dvd (show 0 < u - v by omega) (Nat.dvd_sub hu hv)
      omega
    have he := Nat.isSquare_iff_even_factorization.mp hs p hp
    rw [Nat.factorization_mul (block_pos (by omega)).ne' (Nat.factorial_ne_zero n),
      Finsupp.add_apply, Nat.factorization_factorial_eq_zero_of_lt hnp, add_zero, block,
      Nat.factorization_mul (mul_ne_zero ha₀ ha₁) ha₂, Nat.factorization_mul ha₀ ha₁,
      Finsupp.add_apply, Finsupp.add_apply] at he
    rcases hN with heq | heq | heq <;> rw [heq] at hdiv ⊢
    · have hb : ¬p ∣ a - 1 := hpair (by omega) (by omega) hdiv
      have hc : ¬p ∣ a - 2 := hpair (by omega) (by omega) hdiv
      simpa [Nat.factorization_eq_zero_of_not_dvd hb, Nat.factorization_eq_zero_of_not_dvd hc]
        using he
    · have hb : ¬p ∣ a := fun hd => hpair (by omega) (by omega) hd hdiv
      have hc : ¬p ∣ a - 2 := hpair (by omega) (by omega) hdiv
      simpa [Nat.factorization_eq_zero_of_not_dvd hb, Nat.factorization_eq_zero_of_not_dvd hc]
        using he
    · have hb : ¬p ∣ a := fun hd => hpair (by omega) (by omega) hd hdiv
      have hc : ¬p ∣ a - 1 := fun hd => hpair (by omega) (by omega) hd hdiv
      simpa [Nat.factorization_eq_zero_of_not_dvd hb, Nat.factorization_eq_zero_of_not_dvd hc]
        using he
  · simp [Nat.factorization_eq_zero_of_not_dvd hdiv]

theorem outside_prime_sq_dvd {a n N p : ℕ} (h : Solution a n)
    (hN : N = a ∨ N = a - 1 ∨ N = a - 2) (hp : p.Prime) (hnp : n < p) (hdiv : p ∣ N) :
    p ^ 2 ∣ N := by
  have hNz : N ≠ 0 := by
    have := h.2.1
    rcases hN with hN | hN | hN <;> omega
  obtain ⟨k, hk⟩ := outside_prime_even h hN hp hnp
  apply (hp.pow_dvd_iff_le_factorization hNz).mpr
  have := (hp.dvd_iff_one_le_factorization hNz).mp hdiv
  omega

/-- The review's second sufficient hypothesis for part (b), given directly in terms
of the selected primes' actual exponents in N. -/
theorem theorem12b_odd {a n N α : ℕ} {factors : List ℕ}
    (h : Solution a n) (hN : N = a ∨ N = a - 1 ∨ N = a - 2)
    (he : N = α * factors.prod) (hs : ∀ p ∈ factors, p.Prime ∧ Odd (N.factorization p)) :
    ¬ ((α : ℚ) * (n : ℚ) ^ factors.length + 2 ≤ ((n : ℚ) / 2) ^ exponent n) := by
  apply theorem12b_supported h hN he
  intro p hp
  obtain ⟨hpPrime, hodd⟩ := hs p hp
  by_contra! hnp
  obtain ⟨j, hj⟩ := hodd
  obtain ⟨k, hk⟩ := outside_prime_even h hN hpPrime hnp
  omega

/-- Each prime in the upper half interval occurs in the squarefree factor of n!. -/
theorem interval_prod_dvd {n d k : ℕ} (hf : n.factorial = d * k ^ 2) :
    (∏ p ∈ intervalPrimes n, p) ∣ d := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp [Nat.factorial_ne_zero] at hf
  have hk : k ≠ 0 := by
    rintro rfl
    simp [Nat.factorial_ne_zero] at hf
  refine Finset.prod_dvd_of_isRelPrime ?_ ?_
  · intro p hp q hq hpq
    apply Nat.coprime_iff_isRelPrime.mp
    exact (Nat.coprime_primes (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1)
      (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hq).1)).mpr hpq
  · intro p hp
    have he := congrArg (fun x : ℕ => x.factorization p) hf
    rw [interval_factorization hp, Nat.factorization_mul hd (pow_ne_zero _ hk),
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] at he
    exact ((Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1)
      |>.dvd_iff_one_le_factorization hd).mpr (by omega)

end ThreeFactorials
