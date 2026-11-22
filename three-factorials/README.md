# Products of three factorials in Lean

A partial Lean 4 / Mathlib formalization of

> A. Dujella, F. Najman, N. Saradha, T. N. Shorey, *Products of three factorials*, Publ. Math. Debrecen **85**
> (2014), 123–130, [doi:10.5486/PMD.2014.5835](https://doi.org/10.5486/PMD.2014.5835),
> [PDF](https://web.math.pmf.unizg.hr/~fnajman/bnss.pdf).

The formalization was guided by an AI review of the paper (November 2026, not published), so that only correct
claims are proved; "the review" below refers to it. In particular, the proof of Theorem 1.2(b) uses that every
prime P_i in the statement is at most a₃, which can fail (for example N = 2738 = 2·37² at a₃ = 26); the Lean
versions of part (b) add a hypothesis that excludes this. Some results take a step that is not formalized as an
explicit premise; these premises are named below. No `sorry`; every result depends only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. About 3,300 lines of Lean, on Lean v4.35.0 and Mathlib v4.35.0,
using Lean's module system.

The Lean code was written by Codex (an AI coding agent) at the author's request. The statements have not yet been
reviewed by the author.

## Theorem 1.1 at $a_3=26$

- `case26_iff` proves that $a_1=324$ and $a_1=2738$ are the only solutions at
  $a_3=26$. `solution324_26` and `solution2738_26` verify the two solutions.
- `solution26_remaining` proves that the squarefree coefficients of
  $a_1,a_1-1,a_1-2$ must be $(1,323,322)$ or $(2,2737,19)$. Lean checks the
  congruence sieve, the fundamental units used to exclude three other systems,
  and the exclusion of the quartic Pell case. The quartic case uses residues
  modulo 3 and 8 and the elementary factorization argument for the trace at a
  fourth power. [Elementary quartic argument](https://jtnb.centre-mersenne.org/item/JTNB_2002__14_2_629_0.pdf)
- `unique_first_system` and `unique_second_system` prove that the two
  remaining squarefree systems have unique positive solutions $(18,1,1)$ and
  $(37,1,12)$, respectively. The proof builds simultaneous Padé approximants
  to $\sqrt{1-1/m}$ and $\sqrt{1+1/m}$ for $m=323,2737$. Lean checks the
  integrality of the coefficients, the matrix determinant via reduction
  modulo 2, and the norms of the contour integrals. The resulting denominator
  bound gives finite Pell index ranges, which a residue sieve resolves in
  Lean. [Padé residue formula, Bennett §2](https://personal.math.ubc.ca/~bennett/B-Binom.pdf)
- `case26_iff_of_bennett` gives an alternative implication with the first-coordinate
  uniqueness in Bennett's Theorem 1.2 as an explicit premise. The two known
  solutions have square variables $(18,1,1)$ and $(37,1,12)$.
  [Bennett's theorem](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/88/4/110738/on-consecutive-integers-of-the-form-ax-by-and-cz)
- `case26_iff_of_integral_points` proves the same classification with
  `IntegralPoints26Complete` as an explicit premise. Lean verifies the equation
  at each of the 13 points up to sign on $Y^2=X^3-104006^2X$, and it verifies
  the filtering back to $a_1$. `Replay26.m` reproduces the expanded review's
  separate Magma calculation and checks the exact table, with the rank and
  saturation flags both true.

For the full Theorem 1.1, Lean verifies all seven listed solutions in
`solutionsUpTo100_sound`.
The unbounded exclusion direction for $a_3\le100$ remains open in this project.

## Theorem 1.2

- `theorem12a` proves part (a).
- `theorem12b_fraction` proves the fractional bound of part (b) with the
  review's prime-support restriction. `theorem12b_odd` proves its scaled form
  under the alternative hypothesis that each selected prime occurs in $N$
  with odd valuation. `prime_support_counterexample` verifies the review's
  example $2738=2\cdot37^2$ at $a_3=26$. It concerns the proof's
  prime-support assertion. The unrestricted published part (b) remains
  unresolved in the review.
- `theorem12c_large` proves all four exclusions for $a_3\ge101$, with the
  original constants and the review's square-removal argument for primes
  greater than $a_3$. The needed prime count is proved by an elementary
  extension of mathlib's binomial-coefficient proof of Bertrand's postulate.
  `theorem12c_of_classification` gives part (c) with its original exceptions
  using the remaining completeness direction of Theorem 1.1 as a premise.

`auxiliary_quartic_six` also verifies the review's quartic example
$3^4-5\cdot4^2=1$ at $a_3=6$.

## Build and audit

With Elan installed, run the following commands from the project directory.

```sh
lake exe cache get
lake build
lake env lean CheckAxioms.lean
```

The project pins Lean 4.35.0 and mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The audit prints the axiom
dependencies of the public results. The conditional theorems above take their
premises as explicit arguments. Magma is optional and only used for the
separate replay.

```sh
magma -bn Replay26.m
```

## License

Apache-2.0 (see [`LICENSE`](../LICENSE) at the root of this repository).
