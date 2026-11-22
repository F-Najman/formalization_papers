module

public import NajmanTrbovic.CubicIntegralSplitting
public import NajmanTrbovic.AffinePointVariableChange
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.GroupTheory.Torsion

import Mathlib.Tactic

/-! A local splitting argument using the 2-division polynomial. -/

@[expose] public section

noncomputable section

namespace NajmanTrbovic.Cubic

open Polynomial WeierstrassCurve
open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
open scoped TensorProduct NumberField

private theorem cubic_simple_root {F : Type*} [Field F] (P : _root_.Cubic F)
    (ha : P.a ≠ 0) (hD : P.b ^ 2 - 3 * P.a * P.c ≠ 0) (hdisc : P.discr = 0) :
    ∃ x : F, P.toPoly.eval x = 0 ∧ P.toPoly.derivative.eval x ≠ 0 := by
  let D := P.b ^ 2 - 3 * P.a * P.c
  let n := -P.b * D - P.a * (9 * P.a * P.d - P.b * P.c)
  let m := P.a * D
  have hm : m ≠ 0 := mul_ne_zero ha hD
  have hF : P.a * n ^ 3 + P.b * n ^ 2 * m + P.c * n * m ^ 2 + P.d * m ^ 3 = 0 := by
    unfold n m D
    unfold _root_.Cubic.discr at hdisc
    linear_combination (P.a ^ 3 * (27 * P.a ^ 2 * P.d - 9 * P.a * P.b * P.c + 2 * P.b ^ 3)) * hdisc
  have hF' : 3 * P.a * n ^ 2 + 2 * P.b * n * m + P.c * m ^ 2 = P.a * D ^ 3 := by
    unfold n m D
    unfold _root_.Cubic.discr at hdisc
    linear_combination (-9 * P.a ^ 3) * hdisc
  refine ⟨n / m, ?_, ?_⟩
  · simp only [_root_.Cubic.toPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    field_simp
    linear_combination hF
  · have he : P.toPoly.derivative.eval (n / m) = D / P.a := by
      simp [_root_.Cubic.toPoly, derivative_mul, derivative_pow]
      field_simp
      linear_combination P.a * hF'
    exact he ▸ div_ne_zero hD ha

private theorem map_two_torsion_poly {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (E : WeierstrassCurve R) :
    (E.twoTorsionPolynomial.toPoly).map φ = (E.map φ).twoTorsionPolynomial.toPoly := by
  simp [_root_.Cubic.toPoly, twoTorsionPolynomial, map_b₂, map_b₄, map_b₆, map_ofNat]

private theorem simple_root_of_multiplicative_reduction {p : ℕ} [Fact p.Prime]
    (T : WeierstrassCurve ℤ_[p]) (hΔ : (T.map PadicInt.toZMod).Δ = 0)
    (hc : (T.map PadicInt.toZMod).c₄ ≠ 0) (h4 : (4 : ZMod p) ≠ 0) :
    ∃ x : ℤ_[p], T.twoTorsionPolynomial.toPoly.IsRoot x := by
  let V := T.map PadicInt.toZMod
  obtain ⟨x, h₀, h₁⟩ := cubic_simple_root V.twoTorsionPolynomial h4
    (by
      change V.b₂ ^ 2 - 3 * 4 * (2 * V.b₄) ≠ 0
      convert hc using 1
      unfold c₄
      ring)
    (by rw [twoTorsionPolynomial_discr, hΔ, mul_zero])
  rw [← map_two_torsion_poly PadicInt.toZMod T] at h₀ h₁
  obtain ⟨z, hz, _⟩ := hensel_lift _ _ h₀ h₁
  exact ⟨z, hz⟩

private def reversedTwoTorsion {R : Type*} [CommRing R] (T : WeierstrassCurve R) : R[X] :=
  C 4 + C T.b₂ * X + C (2 * T.b₄) * X ^ 2 + C T.b₆ * X ^ 3

private theorem root_in_reciprocal_chart (T : WeierstrassCurve ℤ_[2])
    (hc : (T.map PadicInt.toZMod).c₄ ≠ 0) :
    ∃ x : ℚ_[2], (T.map (PadicInt.Coe.ringHom (p := 2))).twoTorsionPolynomial.toPoly.IsRoot x := by
  have h4 : (4 : ZMod 2) = 0 := by decide
  have h24 : (24 : ZMod 2) = 0 := by decide
  have hb : PadicInt.toZMod T.b₂ ≠ 0 := by
    intro hb
    apply hc
    rw [c₄, map_b₂, hb, h24]
    simp
  obtain ⟨z, hz, _⟩ := hensel_lift (reversedTwoTorsion T) 0
    (by simpa [reversedTwoTorsion, map_ofNat] using h4)
    (by simpa [reversedTwoTorsion, derivative_mul] using hb)
  have hz₀ : z ≠ 0 := by
    rintro rfl
    norm_num [reversedTwoTorsion] at hz
  let b : ℚ_[2] := z
  have hb₀ : b ≠ 0 := PadicInt.coe_ne_zero.mpr hz₀
  have he : 4 + (T.b₂ : ℚ_[2]) * b + 2 * (T.b₄ : ℚ_[2]) * b ^ 2 + (T.b₆ : ℚ_[2]) * b ^ 3 = 0 := by
    have he' := congrArg (PadicInt.Coe.ringHom (p := 2)) hz
    simp only [reversedTwoTorsion, eval_add, eval_C, eval_mul, eval_X, eval_pow, eval_ofNat,
      map_zero, map_add, map_mul, map_pow, map_ofNat] at he'
    exact he'
  refine ⟨b⁻¹, ?_⟩
  rw [IsRoot.def, eval_toPoly_twoTorsionPolynomial, map_b₂, map_b₄, map_b₆]
  change 4 * (b⁻¹) ^ 3 + (T.b₂ : ℚ_[2]) * (b⁻¹) ^ 2 +
    2 * (T.b₄ : ℚ_[2]) * b⁻¹ + (T.b₆ : ℚ_[2]) = 0
  field_simp
  linear_combination he

private theorem integral_model_has_two_torsion_root {p : ℕ} [Fact p.Prime]
    (T : WeierstrassCurve ℤ_[p]) (hΔ : (T.map PadicInt.toZMod).Δ = 0)
    (hc : (T.map PadicInt.toZMod).c₄ ≠ 0) :
    ∃ x : ℚ_[p], (T.map (PadicInt.Coe.ringHom (p := p))).twoTorsionPolynomial.toPoly.IsRoot x := by
  by_cases hp : p = 2
  · subst p
    exact root_in_reciprocal_chart T hc
  have h4 : (4 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 4 := (CharP.cast_eq_zero_iff (ZMod p) p 4).mp h
    have hp' : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow (by simpa using hd : p ∣ 2 ^ 2)
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hp')
  obtain ⟨z, hz⟩ := simple_root_of_multiplicative_reduction T hΔ hc h4
  refine ⟨(z : ℚ_[p]), ?_⟩
  rw [← map_two_torsion_poly, IsRoot.def, eval_map]
  change eval₂ (PadicInt.Coe.ringHom (p := p)) (PadicInt.Coe.ringHom z)
    T.twoTorsionPolynomial.toPoly = 0
  rw [eval₂_at_apply, IsRoot.def.mp hz, map_zero]

private theorem toZMod_eq_zero_iff {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) :
    PadicInt.toZMod a = 0 ↔ valuation ℚ_[p] (maximalIdeal ℤ_[p])
      (algebraMap ℤ_[p] ℚ_[p] a) < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, valuation_lt_one_iff_mem]
  rfl

private theorem two_torsion_exists_of_root {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (E : WeierstrassCurve F) [E.IsElliptic] (x : F) (hx : E.twoTorsionPolynomial.toPoly.IsRoot x) :
    ∃ P : E.toAffine.Point, P ≠ 0 ∧ P + P = 0 := by
  obtain ⟨y, hy, h⟩ := (Affine.Point.isRoot_twoTorsionPolynomial_iff
    (W := E.toAffine) ⟨by norm_num⟩ E.isUnit_Δ.ne_zero x).mp hx
  exact ⟨.some x y hy, Affine.Point.some_ne_zero _, h⟩

private theorem root_of_two_torsion {F : Type*} [Field F] [DecidableEq F]
    (E : WeierstrassCurve F) (P : E.toAffine.Point) (hP : P ≠ 0) (h : P + P = 0) :
    ∃ x : F, E.twoTorsionPolynomial.toPoly.IsRoot x := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y hxy => exact ⟨x, Affine.Point.isRoot_twoTorsionPolynomial_of_add_self hxy h⟩

/-- At a prime of multiplicative reduction, the 2-division polynomial has a p-adic
root. At 2 the simple root modulo 2 lies in the reciprocal chart. -/
theorem two_torsion_polynomial_has_root_of_multiplicative_reduction {p : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve ℚ_[p]) [E.IsElliptic]
    (h : (E.minimal ℤ_[p]).HasMultiplicativeReduction ℤ_[p]) :
    ∃ x : ℚ_[p], E.twoTorsionPolynomial.toPoly.IsRoot x := by
  classical
  let W := E.minimal ℤ_[p]
  have : W.IsElliptic := by dsimp [W, minimal]; infer_instance
  let T := W.integralModel ℤ_[p]
  have hΔ : (T.map PadicInt.toZMod).Δ = 0 := by
    rw [map_Δ, toZMod_eq_zero_iff]
    have hT : algebraMap ℤ_[p] ℚ_[p] T.Δ = W.Δ := W.integralModel_Δ_eq ℤ_[p]
    rw [hT]
    exact h.badReduction
  have hc : (T.map PadicInt.toZMod).c₄ ≠ 0 := by
    intro h₀
    rw [map_c₄, toZMod_eq_zero_iff] at h₀
    have hT : algebraMap ℤ_[p] ℚ_[p] T.c₄ = W.c₄ := W.integralModel_c₄_eq ℤ_[p]
    rw [hT, h.multiplicativeReduction] at h₀
    exact lt_irrefl _ h₀
  have hW : T.map (PadicInt.Coe.ringHom (p := p)) = W := by
    ext <;> first
    | exact W.integralModel_a₁_eq ℤ_[p]
    | exact W.integralModel_a₂_eq ℤ_[p]
    | exact W.integralModel_a₃_eq ℤ_[p]
    | exact W.integralModel_a₄_eq ℤ_[p]
    | exact W.integralModel_a₆_eq ℤ_[p]
  obtain ⟨x, hx⟩ := integral_model_has_two_torsion_root T hΔ hc
  rw [hW] at hx
  obtain ⟨P, hP, hPP⟩ := two_torsion_exists_of_root W x hx
  let C := (E.exists_isMinimal ℤ_[p]).choose
  let e : E.toAffine.Point ≃+ W.toAffine.Point := C.pointEquiv
  apply root_of_two_torsion E (e.symm P)
  · simpa using hP
  · rw [← map_add, hPP, map_zero]

private theorem two_torsion_coordinates {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (V : WeierstrassCurve F) (P : V.toAffine.Point) (hP : P ≠ 0) (h : P + P = 0) :
    ∃ (x : F) (hxy : V.toAffine.Nonsingular x ((-V.a₁ * x - V.a₃) / 2)),
      P = .some x _ hxy ∧ V.twoTorsionPolynomial.toPoly.IsRoot x := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y hxy =>
    have hy' : y = V.toAffine.negY x y := by
      by_contra hn
      rw [Affine.Point.add_self_of_Y_ne hn] at h
      exact Affine.Point.some_ne_zero _ h
    change y = -y - V.a₁ * x - V.a₃ at hy'
    have hy : y = (-V.a₁ * x - V.a₃) / 2 := by
      field_simp
      linear_combination hy'
    subst y
    exact ⟨x, hxy, rfl, Affine.Point.isRoot_twoTorsionPolynomial_of_add_self hxy h⟩

private theorem distinct_two_torsion_roots {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (V : WeierstrassCurve F)
    (hT : Nonempty ((AddCommGroup.torsion V.toAffine.Point) ≃+ (ZMod 2 × ZMod 14))) :
    ∃ x : Fin 3 → F, Function.Injective x ∧ ∀ i, V.twoTorsionPolynomial.toPoly.IsRoot (x i) := by
  obtain ⟨e⟩ := hT
  let ρ := (AddCommGroup.torsion V.toAffine.Point).subtype.comp e.symm.toAddMonoidHom
  have hρ : Function.Injective ρ := Subtype.val_injective.comp e.symm.injective
  let marker : Fin 3 → (ZMod 2 × ZMod 14) := ![(1, 0), (0, 7), (1, 7)]
  have hmarker : Function.Injective marker := by
    exact (by decide +kernel : ∀ i j, marker i = marker j → i = j)
  have hm₀ (i : Fin 3) : marker i ≠ 0 := by fin_cases i <;> decide
  have hm₂ (i : Fin 3) : marker i + marker i = 0 := by fin_cases i <;> decide
  have h₀ (i : Fin 3) : ρ (marker i) ≠ 0 := fun h => hm₀ i (hρ (h.trans (map_zero ρ).symm))
  have h₂ (i : Fin 3) : ρ (marker i) + ρ (marker i) = 0 := by rw [← map_add, hm₂, map_zero]
  choose x hxy hp hx using fun i => two_torsion_coordinates V _ (h₀ i) (h₂ i)
  refine ⟨x, ?_, hx⟩
  intro i j hij
  apply hmarker (hρ ?_)
  rw [hp i, hp j]
  congr

private theorem minpoly_of_two_torsion_root {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] (hK : Module.finrank ℚ K = 3)
    (E : WeierstrassCurve ℚ) (α : K) (hα : α ∉ Set.range (algebraMap ℚ K))
    (hx : (E.map (algebraMap ℚ K)).twoTorsionPolynomial.toPoly.IsRoot α) :
    E.twoTorsionPolynomial.toPoly = minpoly ℚ α * C 4 := by
  have hm := minpoly_degree_three hK α hα
  have hi : IsIntegral ℚ α := IsIntegral.of_finite ℚ α
  have hdeg : E.twoTorsionPolynomial.toPoly.natDegree = 3 :=
    natDegree_eq_of_degree_eq_some
      (_root_.Cubic.degree_of_a_ne_zero (P := E.twoTorsionPolynomial) (by norm_num [twoTorsionPolynomial]))
  have hx' : aeval α E.twoTorsionPolynomial.toPoly = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_two_torsion_poly]
    exact hx
  obtain ⟨g, hg⟩ := minpoly.dvd ℚ α hx'
  have hf₀ : E.twoTorsionPolynomial.toPoly ≠ 0 := by intro h; simp [h] at hdeg
  have hg₀ : g ≠ 0 := by rintro rfl; simp at hg; exact hf₀ hg
  have hd : g.natDegree = 0 := by
    rw [hg, natDegree_mul (minpoly.ne_zero hi) hg₀, hm] at hdeg
    omega
  rw [eq_C_of_natDegree_le_zero hd.le] at hg
  have hc : g.coeff 0 = 4 := by
    have he := congrArg leadingCoeff hg
    have ha : E.twoTorsionPolynomial.a ≠ 0 := by norm_num [twoTorsionPolynomial]
    simpa [leadingCoeff_mul, (minpoly.monic hi).leadingCoeff,
      _root_.Cubic.leadingCoeff_of_a_ne_zero ha, twoTorsionPolynomial] using he.symm
  simpa only [hc] using hg

private theorem eval₂_of_two_torsion_factor {L : Type*} [Field L] [CharZero L] [Algebra ℚ L]
    {E : WeierstrassCurve ℚ} {A : ℚ[X]} (hf : E.twoTorsionPolynomial.toPoly = A * C 4)
    (y : L) (hy : (E.map (algebraMap ℚ L)).twoTorsionPolynomial.toPoly.IsRoot y) :
    A.eval₂ (algebraMap ℚ L) y = 0 := by
  rw [← map_two_torsion_poly, hf, IsRoot.def, eval_map, eval₂_mul, eval₂_C, map_ofNat] at hy
  exact (mul_eq_zero.mp hy).resolve_right (by norm_num)

private def embedding_of_minpoly_root {K L : Type*} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    {A : ℚ[X]} (e : AdjoinRoot A ≃ₐ[ℚ] K) (y : L) (hy : A.eval₂ (algebraMap ℚ L) y = 0) :
    K →ₐ[ℚ] L :=
  (AdjoinRoot.liftAlgHom A (Algebra.ofId ℚ L) y hy).comp e.symm.toAlgHom

/-- If the 2-torsion generates the cubic field, the paper's torsion hypothesis
forces complete splitting at every prime of multiplicative reduction. -/
theorem cubic_prime_splits_of_torsion_and_nonrational_two_torsion
    {K : Type*} [Field K] [NumberField K] [DecidableEq K]
    (hK : Module.finrank ℚ K = 3) {p : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hT : Nonempty ((AddCommGroup.torsion (E.map (algebraMap ℚ K)).toAffine.Point) ≃+
      (ZMod 2 × ZMod 14)))
    (α : K) (hα : α ∉ Set.range (algebraMap ℚ K))
    (hx : (E.map (algebraMap ℚ K)).twoTorsionPolynomial.toPoly.IsRoot α)
    (h : ((E.map (algebraMap ℚ ℚ_[p])).minimal ℤ_[p]).HasMultiplicativeReduction ℤ_[p]) :
    ∃ P : Fin 3 → Ideal (𝓞 K), Function.Injective P ∧ (∏ i, P i) = Ideal.span {(p : 𝓞 K)} ∧
      ∀ i, (P i).IsPrime ∧ Nonempty (((𝓞 K) ⧸ P i) ≃+* ZMod p) := by
  have hi : IsIntegral ℚ α := IsIntegral.of_finite ℚ α
  have htop : IntermediateField.adjoin ℚ {α} = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_le le_top
    rw [IntermediateField.finrank_top', IntermediateField.adjoin.finrank hi, hK,
      minpoly_degree_three hK α hα]
  let A := minpoly ℚ α
  have hf : E.twoTorsionPolynomial.toPoly = A * C 4 := minpoly_of_two_torsion_root hK E α hα hx
  let e : AdjoinRoot A ≃ₐ[ℚ] K := (IntermediateField.adjoinRootEquivAdjoin ℚ hi).trans
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
  have helift : e.symm α = AdjoinRoot.root A := by
    apply e.injective
    rw [AlgEquiv.apply_symm_apply]
    change α = (↑(IntermediateField.adjoinRootEquivAdjoin ℚ hi (AdjoinRoot.root A)) : K)
    rw [IntermediateField.adjoinRootEquivAdjoin_apply_root]
    rfl
  obtain ⟨z, hz⟩ := two_torsion_polynomial_has_root_of_multiplicative_reduction
    (E.map (algebraMap ℚ ℚ_[p])) h
  let φ := embedding_of_minpoly_root e z (eval₂_of_two_torsion_factor hf z hz)
  obtain ⟨x, hxinj, hxroot⟩ := distinct_two_torsion_roots (E.map (algebraMap ℚ K)) hT
  let σ (i : Fin 3) := embedding_of_minpoly_root e (x i) (eval₂_of_two_torsion_factor hf (x i) (hxroot i))
  let emb (i : Fin 3) : K →ₐ[ℚ] ℚ_[p] := φ.comp (σ i)
  have hσ (i : Fin 3) : σ i α = x i := by
    dsimp [σ, embedding_of_minpoly_root]
    rw [helift]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hEmb : Function.Injective (fun i => emb i α) := by
    intro i j hij
    apply hxinj
    have heq : σ i α = σ j α := φ.injective hij
    rwa [hσ, hσ] at heq
  obtain ⟨s⟩ := tensor_split_of_embeddings hK α emb hEmb
  obtain ⟨r⟩ := residue_algebra_of_split_tensor hK s
  exact distinct_prime_factors_of_residue_product _ r

/-- Under the original torsion and reduction hypotheses, either the 2-division
polynomial splits over ℚ or the prime splits completely in the cubic field. -/
theorem cubic_prime_splits_or_full_rational_two_torsion
    {K : Type*} [Field K] [NumberField K] [DecidableEq K]
    (hK : Module.finrank ℚ K = 3) {p : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hT : Nonempty ((AddCommGroup.torsion (E.map (algebraMap ℚ K)).toAffine.Point) ≃+
      (ZMod 2 × ZMod 14)))
    (h : ((E.map (algebraMap ℚ ℚ_[p])).minimal ℤ_[p]).HasMultiplicativeReduction ℤ_[p]) :
    (∃ x : Fin 3 → ℚ, Function.Injective x ∧ ∀ i, E.twoTorsionPolynomial.toPoly.IsRoot (x i)) ∨
    (∃ P : Fin 3 → Ideal (𝓞 K), Function.Injective P ∧ (∏ i, P i) = Ideal.span {(p : 𝓞 K)} ∧
      ∀ i, (P i).IsPrime ∧ Nonempty (((𝓞 K) ⧸ P i) ≃+* ZMod p)) := by
  classical
  let f := algebraMap ℚ K
  obtain ⟨x, hxinj, hxroot⟩ := distinct_two_torsion_roots (E.map f) hT
  by_cases hr : ∀ i, x i ∈ Set.range f
  · choose q hq using hr
    refine Or.inl ⟨q, fun i j hij => hxinj ((hq i).symm.trans ((congrArg f hij).trans (hq j))), ?_⟩
    intro i
    have hi := hxroot i
    rw [← hq i, ← map_two_torsion_poly] at hi
    exact hi.of_map f.injective
  · push Not at hr
    obtain ⟨i, hi⟩ := hr
    exact Or.inr (cubic_prime_splits_of_torsion_and_nonrational_two_torsion hK E hT
      (x i) hi (hxroot i) h)

/-- The unique order-seven subgroup over the normal field `K` is Galois stable
after extension to `L`, in particular when `L` is an algebraic closure. -/
theorem torsion_group_has_galois_stable_order_seven
    {K L : Type*} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] [Algebra K L]
    [IsScalarTower ℚ K L] [Normal ℚ K] [DecidableEq K] [DecidableEq L] (E : WeierstrassCurve ℚ)
    (hT : Nonempty ((AddCommGroup.torsion (E.map (algebraMap ℚ K)).toAffine.Point) ≃+
      (ZMod 2 × ZMod 14))) :
    ∃ Q : (E.toAffine.baseChange L).Point, addOrderOf Q = 7 ∧
      ∀ σ : L ≃ₐ[ℚ] L, Affine.Point.map (W' := E.toAffine) σ.toAlgHom Q ∈ AddSubgroup.zmultiples Q := by
  obtain ⟨e⟩ := hT
  let V := E.toAffine.baseChange K
  let ρ := (AddCommGroup.torsion V.Point).subtype.comp e.symm.toAddMonoidHom
  have hρ : Function.Injective ρ := Subtype.val_injective.comp e.symm.injective
  let Q₀ := ρ (0, 2)
  let f := IsScalarTower.toAlgHom ℚ K L
  let ι : V.Point →+ (E.toAffine.baseChange L).Point := Affine.Point.map (W' := E.toAffine) f
  have hι : Function.Injective ι := Affine.Point.map_injective f
  have h7 : (7 : ℕ) • Q₀ = 0 := by
    rw [← map_nsmul, show (7 : ℕ) • ((0, 2) : ZMod 2 × ZMod 14) = 0 by decide, map_zero]
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hQ₀ : addOrderOf Q₀ = 7 :=
    addOrderOf_eq_prime h7 (fun h => (by decide : ((0, 2) : ZMod 2 × ZMod 14) ≠ 0)
      (hρ (h.trans (map_zero ρ).symm)))
  refine ⟨ι Q₀, (addOrderOf_injective ι hι Q₀).trans hQ₀, ?_⟩
  intro σ
  let τ := σ.restrictNormal K
  let g : V.Point →+ V.Point := Affine.Point.map (W' := E.toAffine) τ.toAlgHom
  have hg : (7 : ℕ) • g Q₀ = 0 := by rw [← map_nsmul, h7, map_zero]
  have hmem : g Q₀ ∈ AddCommGroup.torsion V.Point :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨7, by decide, hg⟩
  let a := e ⟨g Q₀, hmem⟩
  have ha : ρ a = g Q₀ := congrArg Subtype.val (e.symm_apply_apply _)
  have ha7 : (7 : ℕ) • a = 0 := hρ (by rw [map_nsmul, ha, hg, map_zero])
  have hk : ∀ a : ZMod 2 × ZMod 14, (7 : ℕ) • a = 0 →
      ∃ k : Fin 7, (k.val : ℕ) • ((0, 2) : ZMod 2 × ZMod 14) = a := by
    decide +kernel
  obtain ⟨k, hk⟩ := hk a ha7
  have hσ : σ.toAlgHom.comp f = f.comp τ.toAlgHom :=
    AlgHom.ext fun x => (σ.restrictNormal_commutes K x).symm
  have hmap : Affine.Point.map (W' := E.toAffine) σ.toAlgHom (ι Q₀) = ι (g Q₀) := by
    dsimp only [ι, g]
    rw [Affine.Point.map_map, hσ, ← Affine.Point.map_map]
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨k.val, ?_⟩
  rw [natCast_zsmul, hmap, ← map_nsmul, ← ha, ← map_nsmul, hk]

/-- The local proof reduces Proposition 3.1 to integrality of the j-invariant
for a rational elliptic curve with a rational two-torsion point and a rational
cyclic subgroup of order seven. The classical calculation on `X₀(14)`
supplies this arithmetic input when `L` is an algebraic closure. -/
theorem cubic_prime_splits_of_torsion_and_integral_j_at_level_fourteen
    {K L : Type*} [Field K] [NumberField K] [DecidableEq K] [Normal ℚ K]
    [Field L] [Algebra ℚ L] [Algebra K L] [IsScalarTower ℚ K L] [DecidableEq L]
    (hK : Module.finrank ℚ K = 3) {p : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hT : Nonempty ((AddCommGroup.torsion (E.map (algebraMap ℚ K)).toAffine.Point) ≃+
      (ZMod 2 × ZMod 14)))
    (h₁₄ : (∃ x : ℚ, E.twoTorsionPolynomial.toPoly.IsRoot x) →
      (∃ Q : (E.toAffine.baseChange L).Point, addOrderOf Q = 7 ∧
        ∀ σ : L ≃ₐ[ℚ] L, Affine.Point.map (W' := E.toAffine) σ.toAlgHom Q ∈ AddSubgroup.zmultiples Q) →
      ∃ n : ℤ, E.j = n)
    (h : ((E.map (algebraMap ℚ ℚ_[p])).minimal ℤ_[p]).HasMultiplicativeReduction ℤ_[p]) :
    ∃ P : Fin 3 → Ideal (𝓞 K), Function.Injective P ∧ (∏ i, P i) = Ideal.span {(p : 𝓞 K)} ∧
      ∀ i, (P i).IsPrime ∧ Nonempty (((𝓞 K) ⧸ P i) ≃+* ZMod p) := by
  rcases cubic_prime_splits_or_full_rational_two_torsion hK E hT h with ⟨x, _, hx⟩ | hs
  · obtain ⟨n, hn⟩ := h₁₄ ⟨x 0, hx 0⟩ (torsion_group_has_galois_stable_order_seven E hT)
    have hnorm := norm_j_gt_one_of_multiplicative_reduction (E.map (algebraMap ℚ ℚ_[p])) h
    rw [map_j, hn, map_intCast] at hnorm
    exact (not_lt_of_ge (Padic.norm_int_le_one n) hnorm).elim
  · exact hs

end NajmanTrbovic.Cubic
