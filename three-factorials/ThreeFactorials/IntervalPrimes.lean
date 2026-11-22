module

public import ThreeFactorials.Bounds

import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

/-! An elementary prime count for the upper half interval in Theorem 1.2(c). -/

@[expose] public section

namespace ThreeFactorials

open Finset

/-- Keep the contribution of the upper half interval in the binomial estimate
from the proof of Bertrand's postulate. -/
private theorem centralBinom_bound {k : ℕ} (hk : 2 < k) :
    k.centralBinom ≤
      (2 * k) ^ Nat.sqrt (2 * k) * 4 ^ (2 * k / 3) * (2 * k) ^ (intervalPrimes (2 * k)).card := by
  let S := (2 * k).primesLE
  let low := (2 * k / 3).primesLE
  let f (p : ℕ) := p ^ k.centralBinom.factorization p
  have hkpos : 0 < 2 * k := by omega
  have hfactor : k.centralBinom = ∏ p ∈ S, f p := by
    rw [← k.prod_pow_factorization_centralBinom]
    symm
    refine Finset.prod_filter_of_ne (fun p _ hn => ?_)
    contrapose! hn
    simp [f, Nat.factorization_eq_zero_of_not_prime _ hn]
  have hlow : ∏ p ∈ S with p ≤ k, f p = ∏ p ∈ low, f p := by
    symm
    refine Finset.prod_subset ?_ ?_
    · intro p hp
      obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp hp
      exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega, hprime⟩, by omega⟩
    · intro p hp hlarge
      obtain ⟨hpS, hpk⟩ := Finset.mem_filter.mp hp
      have hprime := Nat.prime_of_mem_primesLE hpS
      have hp' : 2 * k / 3 < p := by
        by_contra! he
        exact hlarge (Nat.mem_primesLE.mpr ⟨he, hprime⟩)
      dsimp [f]
      rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hk hpk (by omega), pow_zero]
  have hhigh : S.filter (fun p => ¬p ≤ k) = intervalPrimes (2 * k) := by
    ext p
    simp [S, intervalPrimes]
  have hsmall :
      (∏ p ∈ low with p ≤ (2 * k).sqrt, f p) ≤ (2 * k) ^ (2 * k).sqrt := by
    let small := low.filter fun p => p ≤ (2 * k).sqrt
    change (∏ p ∈ small, f p) ≤ _
    have hcard : small.card ≤ (2 * k).sqrt := by
      rw [← show (Icc 1 (2 * k).sqrt).card = (2 * k).sqrt by simp]
      apply Finset.card_le_card
      intro p hp
      obtain ⟨hpl, hbound⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hpl).one_lt.le, hbound⟩
    calc
      _ ≤ ∏ _ ∈ small, (2 * k) := Finset.prod_le_prod fun _ _ =>
        Nat.pow_factorization_choose_le hkpos
      _ = (2 * k) ^ small.card := Finset.prod_const _
      _ ≤ _ := pow_le_pow_right₀ (by omega) hcard
  have hmedium :
      (∏ p ∈ low with ¬p ≤ (2 * k).sqrt, f p) ≤ 4 ^ (2 * k / 3) := by
    refine le_trans ?_ (primorial_le_four_pow (2 * k / 3))
    rw [primorial_eq_prod_primesLE]
    refine (Finset.prod_le_prod fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨hpl, hps⟩ := Finset.mem_filter.mp hp
      have hprime := Nat.prime_of_mem_primesLE hpl
      have hlarge := Nat.sqrt_lt'.mp (by omega : (2 * k).sqrt < p)
      exact (pow_le_pow_right₀ hprime.one_lt.le
        (Nat.factorization_choose_le_one hlarge)).trans_eq (pow_one p)
    · refine Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _) ?_
      exact fun _ hp _ => (Nat.prime_of_mem_primesLE hp).one_lt.le
  have hbig : (∏ p ∈ intervalPrimes (2 * k), f p) ≤ (2 * k) ^ (intervalPrimes (2 * k)).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod fun _ _ => Nat.pow_factorization_choose_le hkpos
  rw [hfactor, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ k), hlow, hhigh,
    ← Finset.prod_filter_mul_prod_filter_not low (· ≤ (2 * k).sqrt)]
  exact Nat.mul_le_mul (Nat.mul_le_mul hsmall hmedium) hbig

/-- Scale the main inequality in Bertrand's proof to allow ten additional factors. -/
private theorem scaled_bertrand {k : ℕ} (hk : 2048 ≤ k) :
    k * (2 * k) ^ ((2 * k).sqrt + 10) * 4 ^ (2 * k / 3) ≤ 4 ^ k := by
  let m := k / 4
  let s := (2 * m).sqrt
  have hm : 512 ≤ m := by dsimp [m]; omega
  have hmk : 4 * m ≤ k ∧ k ≤ 4 * m + 3 := by dsimp [m]; omega
  have hs : 32 ≤ s := Nat.le_sqrt'.mpr (by omega)
  have hsq : (2 * k).sqrt ≤ 2 * s + 2 := by
    have hms : 2 * m < (s + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have hs0 : (2 * k).sqrt < 2 * s + 3 :=
      Nat.sqrt_lt'.mpr (by nlinarith [hmk.2, hms, hs])
    omega
  have hbk : (2 * k) ^ 2 ≤ (2 * m) ^ 3 := by
    have hm' : 100 ≤ 8 * m := by omega
    calc
      _ ≤ (10 * m) ^ 2 := pow_le_pow_left' (by omega : 2 * k ≤ 10 * m) 2
      _ = 100 * m ^ 2 := by ring
      _ ≤ (8 * m) * m ^ 2 := Nat.mul_le_mul_right _ hm'
      _ = _ := by ring
  have hpow : (2 * k) ^ ((2 * k).sqrt + 10) ≤ (2 * m) ^ (4 * s) := by
    apply (sq_le_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp
    calc
      _ = ((2 * k) ^ 2) ^ ((2 * k).sqrt + 10) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm ((2 * k).sqrt + 10) 2]
      _ ≤ ((2 * m) ^ 3) ^ ((2 * k).sqrt + 10) := pow_le_pow_left' hbk _
      _ = (2 * m) ^ (3 * ((2 * k).sqrt + 10)) := by rw [pow_mul]
      _ ≤ (2 * m) ^ (8 * s) := pow_le_pow_right₀ (by omega) (by omega)
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hkm : 256 * k ≤ m ^ 4 := by
    calc
      _ ≤ 1280 * m := by omega
      _ ≤ m ^ 3 * m :=
        Nat.mul_le_mul_right _ ((by decide : 1280 ≤ 11 ^ 3).trans
          (pow_le_pow_left' (by omega : 11 ≤ m) 3))
      _ = _ := by ring
  have hexp : 2 * k / 3 ≤ 4 * (2 * m / 3) + 4 := by omega
  calc
    _ ≤ k * (2 * m) ^ (4 * s) * 4 ^ (4 * (2 * m / 3) + 4) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left k hpow) (pow_le_pow_right₀ (by decide) hexp)
    _ = (256 * k) * (2 * m) ^ (4 * s) * 4 ^ (4 * (2 * m / 3)) := by rw [pow_add]; ring
    _ ≤ m ^ 4 * (2 * m) ^ (4 * s) * 4 ^ (4 * (2 * m / 3)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hkm)
    _ = (m * (2 * m) ^ s * 4 ^ (2 * m / 3)) ^ 4 := by simp [mul_pow, pow_mul, mul_comm 4]
    _ ≤ (4 ^ m) ^ 4 := pow_le_pow_left' (bertrand_main_inequality hm) 4
    _ ≤ 4 ^ k := by
      rw [← pow_mul, mul_comm m 4]
      exact pow_le_pow_right₀ (by decide) hmk.1

private theorem interval_card_even_large {k : ℕ} (hk : 2048 ≤ k) :
    11 ≤ (intervalPrimes (2 * k)).card := by
  by_contra! hc
  have hu := centralBinom_bound (by omega : 2 < k)
  have hl := Nat.four_pow_lt_mul_centralBinom k (by omega)
  have hle : k * k.centralBinom ≤ 4 ^ k := calc
    _ ≤ k * ((2 * k) ^ (2 * k).sqrt * 4 ^ (2 * k / 3) * (2 * k) ^ 10) :=
      Nat.mul_le_mul_left k (hu.trans
        (Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by omega) (by omega))))
    _ = k * (2 * k) ^ ((2 * k).sqrt + 10) * 4 ^ (2 * k / 3) := by rw [pow_add]; ring
    _ ≤ _ := scaled_bertrand hk
  exact hl.not_ge hle

/-- A row consists of the first and last k covered, and eleven primes in
`(last, 2 * first]`. -/
private def witnesses : List (ℕ × ℕ × List ℕ) :=
  [(51, 52, [53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101]),
   (53, 58, [59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103]),
   (59, 70, [71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113]),
   (71, 88, [89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139]),
   (89, 112, [113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173]),
   (113, 162, [163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223]),
   (163, 262, [263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317]),
   (263, 460, [461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523]),
   (461, 852, [853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919]),
   (853, 1618, [1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699]),
   (1619, 3162, [3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229])]

private theorem witnesses_sound :
    ∀ row ∈ witnesses, row.2.2.Nodup ∧ row.2.2.length = 11 ∧
      ∀ p ∈ row.2.2, p.Prime ∧ row.2.1 < p ∧ p ≤ 2 * row.1 := by
  simp only [witnesses, List.mem_cons, List.not_mem_nil, or_false]
  rintro row (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals
    refine ⟨by decide, rfl, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by norm_num, by decide, by decide⟩

private def consecutiveCoverage (stop : ℕ) : ℕ → List (ℕ × ℕ × List ℕ) → Bool
  | lo, [] => decide (stop ≤ lo)
  | lo, row :: rows => decide (row.1 ≤ lo) && consecutiveCoverage stop (row.2.1 + 1) rows

private theorem consecutiveCoverage_sound {rows : List (ℕ × ℕ × List ℕ)} {stop lo k : ℕ}
    (hc : consecutiveCoverage stop lo rows = true) (hlo : lo ≤ k) (hstop : k < stop) :
    ∃ row ∈ rows, row.1 ≤ k ∧ k ≤ row.2.1 := by
  induction rows generalizing lo with
  | nil =>
    have h := of_decide_eq_true (show decide (stop ≤ lo) = true from hc)
    omega
  | cons row rows ih =>
    simp only [consecutiveCoverage, Bool.and_eq_true] at hc
    obtain ⟨hstart, htail⟩ := hc
    by_cases hl : k ≤ row.2.1
    · exact ⟨row, List.mem_cons_self, (of_decide_eq_true hstart).trans hlo, hl⟩
    · obtain ⟨w, hw, hw'⟩ := ih htail (by omega)
      exact ⟨w, List.mem_cons_of_mem _ hw, hw'⟩

private theorem interval_card_even_small {k : ℕ} (hk : 51 ≤ k) (hk' : k < 2048) :
    11 ≤ (intervalPrimes (2 * k)).card := by
  have hc : consecutiveCoverage 2048 51 witnesses = true := by decide +kernel
  obtain ⟨row, hr, hfirst, hlast⟩ := consecutiveCoverage_sound hc hk hk'
  obtain ⟨hnodup, hlength, hall⟩ := witnesses_sound row hr
  have hsubset : row.2.2.toFinset ⊆ intervalPrimes (2 * k) := by
    intro p hp
    obtain ⟨hprime, hlo, hhi⟩ := hall p (List.mem_toFinset.mp hp)
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega, hprime⟩, by omega⟩
  have hcard := Finset.card_le_card hsubset
  rwa [List.toFinset_card_of_nodup hnodup, hlength] at hcard

/-- There are at least eleven primes in `(n/2,n]` for every `n ≥ 101`. -/
theorem interval_card_ge_eleven {n : ℕ} (hn : 101 ≤ n) :
    11 ≤ (intervalPrimes n).card := by
  by_cases hn' : n = 101
  · subst n
    decide +kernel
  let k := n / 2
  have hk : 51 ≤ k := by dsimp [k]; omega
  have heven : 11 ≤ (intervalPrimes (2 * k)).card := by
    by_cases hk' : k < 2048
    · exact interval_card_even_small hk hk'
    · exact interval_card_even_large (by omega)
  refine heven.trans (Finset.card_le_card ?_)
  intro p hp
  obtain ⟨hpmem, hpHalf⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpn, hpPrime⟩ := Nat.mem_primesLE.mp hpmem
  have hk' : k = n / 2 := rfl
  exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega, hpPrime⟩, by omega⟩

end ThreeFactorials
