# Products of three factorials in Lean

A partial Lean 4 / Mathlib formalization of

> A. Dujella, F. Najman, N. Saradha, T. N. Shorey, *Products of three factorials*, Publ. Math. Debrecen **85**
> (2014), 123–130, [doi:10.5486/PMD.2014.5835](https://doi.org/10.5486/PMD.2014.5835),
> [PDF](https://web.math.pmf.unizg.hr/~fnajman/bnss.pdf).

* **Theorem 1.1 at a₃ = 26, unconditionally:** a₁!(a₁ − 3)!26! is a square only for a₁ = 324 and a₁ = 2738. For
  the rest of Theorem 1.1 (a₃ ≤ 100), only the easy direction is proved: the seven listed pairs are solutions.
* **Theorem 1.2:** part (a); part (b) in two corrected forms (see below); part (c) for a₃ ≥ 101. Part (c) with its
  exceptions, for all a₃, is proved assuming the completeness of Theorem 1.1.
* **21 compared theorems, all proved.** No `sorry`. Every result depends only on the standard axioms `propext`,
  `Classical.choice` and `Quot.sound`. Three theorems take an unformalized step as an explicit premise; they are
  marked *conditional* below.
* [`Challenge.lean`](Challenge.lean) states all of them, with `sorry` as proofs, together with every definition they
  use, over Mathlib alone (308 lines). [Comparator](https://github.com/leanprover/comparator) checks that the library
  proves exactly these statements about exactly these definitions.
* About 3,300 lines of Lean, on Lean v4.35.0 and Mathlib v4.35.0, using Lean's module system.

The Lean code was written by OpenAI's GPT-6.2 Sol (in Codex) at the author's request. It was asked to prove only
correct claims, guided by an AI review of the paper (November 2026, not published); "the review" below refers to it.
The Comparator challenge, the checks and the Palomar metadata were added afterwards, and two AI reviewer agents
reviewed the statements. The author has not yet reviewed the statements. See
[`formalization.yaml`](formalization.yaml) for the details.

**Where the formalization differs from the paper.**

* The proof of Theorem 1.2(b) uses that every prime Pᵢ in the statement is at most a₃. This can fail: 2738 = 2·37²
  is a value of a₁ at a₃ = 26 (`prime_support_counterexample`). This is a gap in the proof, not a counterexample
  to part (b) itself, which is not formalized as printed. The two Lean versions of part (b) change its hypothesis:
  `theorem12b_fraction` assumes that every factor is at most a₃ (and is then a direct consequence of part (a));
  `theorem12b_odd` assumes that the factors are primes whose exponent in N (rather than in N₁) is odd.
* The paper says that for a₃ ≤ 100 equation (8) has a solution in positive integers only for a₃ = 3, 4, 18. It also
  has one for a₃ = 6: 6! = 5·12² and 3⁴ − 5·4² = 1 (`auxiliary_quartic_six`).
* For a₃ = 26 the paper uses the integral points on an elliptic curve, computed with Magma. The unconditional Lean
  proof instead solves the two remaining Pell systems with simultaneous Padé approximations. The paper's route is
  formalized with the completeness of the integral points as a premise.

## Results

The statements are in [`Challenge.lean`](Challenge.lean); the proofs are in the library
[`ThreeFactorials`](ThreeFactorials.lean). Here a = a₁ and n = a₃, and `Solution a n` is equation (3) of the paper,
a!(a − 3)!n! = y², with a − 3 > n > 1 (so, as in the paper, products such as 6!·3!·5! with a₃ ≥ a₁ − 3 are not
solutions).

| paper | statement | proof | in words |
|---|---|---|---|
| equation (5) | [`solution_iff_squarefree`](Challenge.lean#L153) | [Basic.lean](ThreeFactorials/Basic.lean#L63) | if n! = d·k² with d squarefree, then (a, n) is a solution iff a(a − 1)(a − 2) = d·t² for some t |
| Theorem 1.1, a₃ = 26 | [`solution324_26`](Challenge.lean#L165), [`solution2738_26`](Challenge.lean#L167) | [Case26.lean](ThreeFactorials/Case26.lean#L32) | (324, 26) and (2738, 26) are solutions |
| Theorem 1.1, a₃ = 26 | [`case26_iff`](Challenge.lean#L220) | [Case26Final.lean](ThreeFactorials/Case26Final.lean#L108) | (a, 26) is a solution iff a = 324 or a = 2738; unconditional |
| proof of Theorem 1.1, a₃ = 26 | [`solution26_remaining`](Challenge.lean#L191) | [Pell26.lean](ThreeFactorials/Pell26.lean#L310) | a solution (a, 26) has a = x², a − 1 = 323y², a − 2 = 322z² or a = 2x², a − 1 = 2737y², a − 2 = 19z² (positive x, y, z): the congruence sieve, fundamental units, and the quartic case exclude the other systems |
| proof of Theorem 1.1, equation (8) for a₃ = 26 | [`quartic104006_no_solution`](Challenge.lean#L187) | [Pell26.lean](ThreeFactorials/Pell26.lean#L164) | y⁴ = 104006w² + 1 has no solution with w > 0 |
| (not in the paper) | [`unique_first_system`](Challenge.lean#L210) | [Case26Final.lean](ThreeFactorials/Case26Final.lean#L78) | x² = 323y² + 1, 322z² + 1 = 323y², y > 0 only for (x, y, z) = (18, 1, 1) |
| (not in the paper) | [`unique_second_system`](Challenge.lean#L215) | [Case26Final.lean](ThreeFactorials/Case26Final.lean#L93) | 2x² = 2737y² + 1, 19z² + 1 = 2737y², y > 0 only for (x, y, z) = (37, 1, 12) |
| Theorem 1.1, a₃ = 26, the paper's route | [`integralPoints26_sound`](Challenge.lean#L170) | [Case26.lean](ThreeFactorials/Case26.lean#L46) | the 13 listed points lie on Y² = X³ − 104006²X |
| | [`case26_iff_of_integral_points`](Challenge.lean#L174) | [Case26.lean](ThreeFactorials/Case26.lean#L60) | *conditional:* the same classification, assuming `IntegralPoints26Complete` (the 13 listed points are all the integral points, up to sign, on Y² = X³ − 104006²X); an alternative derivation, implied by `case26_iff` |
| Theorem 1.1, a₃ = 26, by Bennett's theorem | [`case26_iff_of_bennett`](Challenge.lean#L197) | [Pell26.lean](ThreeFactorials/Pell26.lean#L353) | *conditional:* the same classification, assuming `BennettConsecutiveUnique`, a consequence of Bennett's theorem that ax² − by² = 1, by² − cz² = 1 has at most one solution in positive integers; an alternative derivation, implied by `case26_iff` |
| Theorem 1.1, the listed solutions | [`solutionsUpTo100_sound`](Challenge.lean#L230) | [Classification.lean](ThreeFactorials/Classification.lean#L14) | the seven pairs (10, 6), (50, 3), (50, 4), (324, 26), (352, 13), (442, 18), (2738, 26) are solutions with a₃ ≤ 100 |
| Theorem 1.1 | [`theorem11_iff_of_completeness`](Challenge.lean#L234) | [Classification.lean](ThreeFactorials/Classification.lean#L27) | *conditional:* Theorem 1.1 as stated, assuming its completeness direction (every solution with a₃ ≤ 100 is listed); this adds nothing to `solutionsUpTo100_sound` |
| Theorem 1.2(a) | [`theorem12a`](Challenge.lean#L256) | [Bounds.lean](ThreeFactorials/Bounds.lean#L60) | a > (n/2)^⌈h/3⌉, where h is the number of primes in (n/2, n] |
| Theorem 1.2(b), changed hypothesis | [`theorem12b_fraction`](Challenge.lean#L260) | [Bounds.lean](ThreeFactorials/Bounds.lean#L148) | if N ∈ {a, a − 1, a − 2} is α times a product of s ≤ ⌈h/3⌉ factors, each at most n, then α > n^(⌈h/3⌉−s)/2^⌈h/3⌉ − 2/n^s |
| Theorem 1.2(b), changed hypothesis | [`theorem12b_odd`](Challenge.lean#L269) | [Bounds.lean](ThreeFactorials/Bounds.lean#L216) | the same bound, in the form α·n^s + 2 > (n/2)^⌈h/3⌉, when the factors are primes p whose exponent in N is odd |
| proof of Theorem 1.2, observation 3 | [`interval_card_ge_eleven`](Challenge.lean#L284) | [IntervalPrimes.lean](ThreeFactorials/IntervalPrimes.lean#L204) | there are at least 11 primes in (n/2, n] for n ≥ 101 |
| Theorem 1.2(c), a₃ ≥ 101 | [`theorem12c_large`](Challenge.lean#L297) | [ForbiddenForms.lean](ThreeFactorials/ForbiddenForms.lean#L253) | for n ≥ 101 no N ∈ {a, a − 1, a − 2} is αP₁ (α ≤ 64393), αP₁³ (α ≤ 6), αP₁P₂ (α ≤ 637) or αP₁P₂P₃ (α ≤ 6), with distinct primes Pᵢ (of any size) |
| Theorem 1.2(c) | [`theorem12c_of_classification`](Challenge.lean#L301) | [ForbiddenForms.lean](ThreeFactorials/ForbiddenForms.lean#L303) | *conditional:* Theorem 1.2(c) as stated, with its exceptions, assuming the completeness direction of Theorem 1.1 |
| proof of Theorem 1.2(b) | [`prime_support_counterexample`](Challenge.lean#L239) | [Classification.lean](ThreeFactorials/Classification.lean#L33) | (2738, 26) is a solution and 2738 = 2·37² with 37 > 26: a prime factor of N can exceed a₃ |
| §2, after equation (8) | [`auxiliary_quartic_six`](Challenge.lean#L243) | [Classification.lean](ThreeFactorials/Classification.lean#L38) | 6! = 5·12², 5 is squarefree, and 3⁴ = 5·4² + 1 |

Definitions used by the statements (all in [`Challenge.lean`](Challenge.lean)):

* `block a` is a(a − 1)(a − 2); `Solution a n` means 1 < n, n + 3 < a and a!(a − 3)!n! is a square.
* `CongruentPoint d x y` means y² = x³ − d²x.
* `intervalPrimes n` is the set of primes p ≤ n with ⌊n/2⌋ < p, i.e. the primes in (n/2, n]; `exponent n` is
  ⌈h/3⌉ for h its cardinality.
* `integralPoints26` is the list of 13 integral points (X, |Y|) on Y² = X³ − 104006²X found by Magma;
  `IntegralPoints26Complete` says that every integral point is on it, up to the sign of Y.
* `solutionsUpTo100` is the list of the seven pairs (a₁, a₃) of Theorem 1.1.
* `ForbiddenForm N` means that N is one of the four forms of Theorem 1.2(c), with the paper's constants and with
  distinct primes.
* `BennettConsecutiveUnique` says: for positive A, B, C, two positive solutions (x, y, z), (u, v, w) of
  Ax² = By² + 1, By² = Cz² + 1 have x = u. It follows from M. A. Bennett, *On consecutive integers of the form ax²,
  by² and cz²*, Acta Arith. 88 (1999), 363–370, [doi:10.4064/aa-88-4-363-370](https://doi.org/10.4064/aa-88-4-363-370),
  by which such a system has at most one solution in positive integers.

## Proof

* `solution26_remaining`: 26! = 104006·62270208000², so a(a − 1)(a − 2) = 104006·t². Lean checks the congruence
  sieve, the fundamental units used to exclude three other systems, and the exclusion of the quartic case
  (equation (8)). The quartic case uses residues modulo 3 and 8 and an elementary factorization argument (see
  P. Samuel, [*Résultats élémentaires sur certaines équations diophantiennes*](https://jtnb.centre-mersenne.org/item/JTNB_2002__14_2_629_0.pdf),
  J. Théor. Nombres Bordeaux 14 (2002)).
* `unique_first_system`, `unique_second_system`: simultaneous Padé approximants to √(1 − 1/m) and √(1 + 1/m) for
  m = 323, 2737 (as in M. A. Bennett, [*Simultaneous rational approximation to binomial functions*](https://personal.math.ubc.ca/~bennett/B-Binom.pdf), Trans. Amer. Math. Soc. 348 (1996), §2).
  Lean checks the integrality of the coefficients, the determinant of the matrix modulo 2, and the bounds on the
  contour integrals. The resulting bound gives finite ranges for the Pell index, which a residue sieve resolves.
* `theorem12c_large`: the paper's constants, with the review's square-removal argument for primes greater than a₃.
  The prime count `interval_card_ge_eleven` is proved by an extension of Mathlib's binomial-coefficient proof of
  Bertrand's postulate.

## Building and checking

With [elan](https://github.com/leanprover/elan) installed, from this directory:

```sh
lake exe cache get                 # Mathlib's compiled files
lake build                         # the library
lake env lean CheckAxioms.lean     # prints the axioms of the results
```

**Comparator.** [`comparator.json`](comparator.json) names the 21 compared theorems. Comparator builds
[`Challenge.lean`](Challenge.lean) and [`Solution.lean`](Solution.lean) (which imports the library), checks that
each compared theorem has the same statement in both, about the same definitions, uses no axioms other than
`propext`, `Classical.choice` and `Quot.sound`, and is accepted by the Lean kernel (and, with `--paranoid`, by
lean4lean, nanoda, con-leche and con-ron). In the pinned Lean version Comparator is part of Lake; it runs inside a
[bubblewrap](https://github.com/containers/bubblewrap) sandbox, so `bwrap` must be installed:

```sh
lake comparator --config comparator.json --paranoid
```

**Scripts** (Python 3, from this directory):

* `python3 scripts/make_challenge.py [--check]` writes `Challenge.lean` from the library sources (or checks that it is
  up to date). It copies the definitions verbatim and replaces each proof by `sorry`.
* `python3 scripts/check_statements.py` checks that the 31 declarations of the Challenge (21 statements, 10
  definitions) are, in the library, exactly as Codex wrote them (in the commit 8fe5b9a of this repository). The
  library has not been changed since.

**Magma** (optional, not used by the Lean proofs). [`Replay26.m`](Replay26.m) recomputes the integral points on
Y² = X³ − 104006²X, checks that they are the 13 points of `integralPoints26` (Magma proves the rank and the
saturation), and recovers a₁ ∈ {324, 2738}:

```sh
magma -bn Replay26.m
```

## Layout

```
Challenge.lean            the statements, with the definitions they use (generated)
Solution.lean             imports the library
comparator.json           the compared theorems
formalization.yaml        Palomar metadata
CheckAxioms.lean          #print axioms for 23 results
Replay26.m                Magma replay of the integral points for a₃ = 26
ThreeFactorials.lean      imports the library
ThreeFactorials/
  Basic.lean              the equation and its squarefree form (equation (5))
  SquarefreeSplit.lean    a(a − 1)(a − 2) = d·t², d squarefree and even, gives a = Ax², a − 1 = By², a − 2 = Cz², ABC = d
  Case26.lean             26! = 104006·62270208000², the two solutions, the integral-point route
  Case26Local.lean        the congruence sieve for a₃ = 26: six coefficient triples remain
  QuarticPell.lean        the elementary argument for the quartic case
  Pell26.lean             fundamental units, the excluded systems, y⁴ = 104006w² + 1, the Bennett route
  Approximation26.lean    from Padé approximations to a bound for the Pell index
  PellPruning26.lean      the Pell index ranges and the residue sieves for the two remaining systems
  PadeBinomial.lean       integrality of the binomial series of √(1 + 4x)
  PadeCoefficients.lean   the Padé coefficient matrix: integrality, and its determinant modulo 2
  PadeContour.lean        Cauchy integrals and the contour estimate
  PadeEstimates.lean      bounds for the Padé integrals
  PadeJets.lean           the Padé integrals equal the coefficients
  Case26Final.lean        the two remaining systems, and Theorem 1.1 at a₃ = 26
  Classification.lean     the seven solutions of Theorem 1.1, and the conditional classification
  Bounds.lean             Theorem 1.2(a), (b)
  IntervalPrimes.lean     at least 11 primes in (n/2, n] for n ≥ 101
  ForbiddenForms.lean     Theorem 1.2(c)
scripts/                  make_challenge.py, check_statements.py
```

## License

Apache-2.0 (see [`LICENSE`](../LICENSE) at the root of this repository).
