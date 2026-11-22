module

public import ThreeFactorials.Basic

import Mathlib.Tactic

/-! A canonical squarefree split for the even squarefree parameters. -/

@[expose] public section

namespace ThreeFactorials

/-- If the squarefree part of the three-factor product is even, the squarefree parts
of the three individual factors multiply to it. At an odd prime at most one of the
three factors is divisible by the prime. At 2, at most two are divisible and the sum
of their squarefree exponents is odd. -/
theorem squarefree_split_even {a d t : ℕ} (ha : 2 < a) (hd : Squarefree d)
    (hd2 : 2 ∣ d) (h : block a = d * t ^ 2) :
    ∃ A B C x y z : ℕ, A * B * C = d ∧
      a = A * x ^ 2 ∧ a - 1 = B * y ^ 2 ∧ a - 2 = C * z ^ 2 := by
  obtain ⟨A, x, hA, hx, hAx, hfA⟩ := Nat.sq_mul_squarefree_of_pos (show 0 < a by omega)
  obtain ⟨B, y, hB, hy, hBy, hfB⟩ :=
    Nat.sq_mul_squarefree_of_pos (show 0 < a - 1 by omega)
  obtain ⟨C, z, hC, hz, hCz, hfC⟩ :=
    Nat.sq_mul_squarefree_of_pos (show 0 < a - 2 by omega)
  have hAt : A ∣ a := ⟨x ^ 2, by rw [← hAx, mul_comm]⟩
  have hBt : B ∣ a - 1 := ⟨y ^ 2, by rw [← hBy, mul_comm]⟩
  have hCt : C ∣ a - 2 := ⟨z ^ 2, by rw [← hCz, mul_comm]⟩
  have ht : t ≠ 0 := by
    intro ht
    have hp := block_pos ha
    rw [ht, zero_pow (by decide), mul_zero] at h
    omega
  have heq : (A * B * C) * (x * y * z) ^ 2 = d * t ^ 2 := by
    calc
      (A * B * C) * (x * y * z) ^ 2 = (x ^ 2 * A) * (y ^ 2 * B) * (z ^ 2 * C) := by ring
      _ = d * t ^ 2 := by rw [hAx, hBy, hCz, ← block, h]
  refine ⟨A, B, C, x, y, z, ?_, ?_, ?_, ?_⟩
  · apply Nat.eq_of_factorization_eq (by positivity) hd.ne_zero
    intro p
    have hbalance := congrArg (fun k : ℕ => k.factorization p) heq
    simp only [Nat.factorization_mul (by positivity : A * B * C ≠ 0)
        (by positivity : (x * y * z) ^ 2 ≠ 0),
      Nat.factorization_mul (by positivity : A * B ≠ 0) hC.ne',
      Nat.factorization_mul hA.ne' hB.ne',
      Nat.factorization_mul hd.ne_zero (pow_ne_zero _ ht),
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] at hbalance
    simp only [Nat.factorization_mul (by positivity : A * B ≠ 0) hC.ne',
      Nat.factorization_mul hA.ne' hB.ne', Finsupp.add_apply]
    by_cases hp : p.Prime
    · have hA1 := hfA.natFactorization_le_one p
      have hB1 := hfB.natFactorization_le_one p
      have hC1 := hfC.natFactorization_le_one p
      have hd1 := hd.natFactorization_le_one p
      have forbids {u v : ℕ} (hu : u ≠ 0) (hv : v ≠ 0)
          (hn : ¬ (p ∣ u ∧ p ∣ v)) :
          ¬ (0 < u.factorization p ∧ 0 < v.factorization p) := by
        rintro ⟨hu', hv'⟩
        exact hn ⟨(hp.dvd_iff_one_le_factorization hu).mpr hu',
          (hp.dvd_iff_one_le_factorization hv).mpr hv'⟩
      have hAB : ¬ (0 < A.factorization p ∧ 0 < B.factorization p) := by
        apply forbids hA.ne' hB.ne'
        rintro ⟨hpa, hpb⟩
        have hdiv := Nat.dvd_sub (hpa.trans hAt) (hpb.trans hBt)
        rw [show a - (a - 1) = 1 by omega] at hdiv
        exact hp.not_dvd_one hdiv
      have hBC : ¬ (0 < B.factorization p ∧ 0 < C.factorization p) := by
        apply forbids hB.ne' hC.ne'
        rintro ⟨hpb, hpc⟩
        have hdiv := Nat.dvd_sub (hpb.trans hBt) (hpc.trans hCt)
        rw [show a - 1 - (a - 2) = 1 by omega] at hdiv
        exact hp.not_dvd_one hdiv
      by_cases hp2 : p = 2
      · have hd' : d.factorization p = 1 :=
          Nat.factorization_eq_one_of_squarefree hd hp (by simpa [hp2] using hd2)
        omega
      · have hAC : ¬ (0 < A.factorization p ∧ 0 < C.factorization p) := by
          apply forbids hA.ne' hC.ne'
          rintro ⟨hpa, hpc⟩
          have hdiv := Nat.dvd_sub (hpa.trans hAt) (hpc.trans hCt)
          rw [show a - (a - 2) = 2 by omega] at hdiv
          exact hp2 (le_antisymm (Nat.le_of_dvd (by decide) hdiv) hp.two_le)
        omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  · simpa only [mul_comm] using hAx.symm
  · simpa only [mul_comm] using hBy.symm
  · simpa only [mul_comm] using hCz.symm

end ThreeFactorials
