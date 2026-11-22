module

public import NajmanTrbovic.AffinePointVariableChange
public import NajmanTrbovic.MarkedOrderFourteen
public import NajmanTrbovic.MarkedTorsionNormalForm
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Field.ZMod

import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Tactic

/-! The explicit affine equation from torsion over a field that admits a real
embedding. The rationality of a coordinate over a cubic field is a separate
arithmetic statement. -/

@[expose] public section

noncomputable section

namespace NajmanTrbovic.Cubic

open WeierstrassCurve

section Normalization

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

private def changeTo {W V : WeierstrassCurve F} (C : VariableChange F) (h : C • W = V) :
    W.toAffine.Point ≃+ V.toAffine.Point := h ▸ C.pointEquiv

omit [CharZero F] in
private theorem changeTo_some {W V : WeierstrassCurve F} (C : VariableChange F)
    (h : C • W = V) (x y : F) (hxy : W.toAffine.Nonsingular x y) :
    ∃ h' : V.toAffine.Nonsingular (C.vcX x) (C.vcY x y),
      changeTo C h (Affine.Point.some x y hxy) = Affine.Point.some _ _ h' := by
  subst V
  exact ⟨_, rfl⟩

private theorem affine_coordinates_of_two_point (A B : F)
    (P : (⟨0,A,0,B,0⟩ : WeierstrassCurve F).toAffine.Point) (hP : P ≠ 0) (h₂ : 2 • P = 0) :
    ∃ (x : F) (h : (⟨0,A,0,B,0⟩ : WeierstrassCurve F).toAffine.Nonsingular x 0),
      P = Affine.Point.some x 0 h ∧ x^3+A*x^2+B*x = 0 := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y h =>
    have hy : y = 0 := by
      by_contra hn
      have hnot : y ≠ (⟨0,A,0,B,0⟩ : WeierstrassCurve F).toAffine.negY x y := by
        change y ≠ -y-0*x-0
        intro he
        apply hn
        linear_combination (1/2 : F)*he
      rw [two_nsmul, Affine.Point.add_self_of_Y_ne hnot] at h₂
      exact Affine.Point.some_ne_zero _ h₂
    subst y
    have he := (Affine.equation_iff x 0).mp h.1
    change 0^2+0*x*0+0*0 = x^3+A*x^2+B*x+0 at he
    exact ⟨x,h,rfl,by simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using he.symm⟩

omit [CharZero F] [DecidableEq F] in
private theorem short_translate_root (A B r : F) (h : r^3+A*r^2+B*r = 0) :
    (⟨1,r,0,0⟩ : VariableChange F) • (⟨0,A,0,B,0⟩ : WeierstrassCurve F) =
      ⟨0,A+3*r,0,B+2*r*A+3*r^2,0⟩ := by
  ext <;> simp only [variableChange_def, Units.val_one, inv_one, one_pow, one_mul,
    mul_zero, zero_add, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0)]
  linear_combination h

omit [CharZero F] [DecidableEq F] in
private theorem derivative_at_three_roots (A B r s t : F)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hr : r^3+A*r^2+B*r=0) (hs : s^3+A*s^2+B*s=0) (ht : t^3+A*t^2+B*t=0) :
    B+2*r*A+3*r^2 = (r-s)*(r-t) := by
  have e₁ : r^2+r*s+s^2+A*(r+s)+B = 0 := by
    apply (mul_eq_zero.mp (show (r-s)*(r^2+r*s+s^2+A*(r+s)+B)=0 by
      linear_combination hr-hs)).resolve_left (sub_ne_zero.mpr hrs)
  have e₂ : r^2+r*t+t^2+A*(r+t)+B = 0 := by
    apply (mul_eq_zero.mp (show (r-t)*(r^2+r*t+t^2+A*(r+t)+B)=0 by
      linear_combination hr-ht)).resolve_left (sub_ne_zero.mpr hrt)
  have e₃ : r+s+t+A = 0 := by
    apply (mul_eq_zero.mp (show (s-t)*(r+s+t+A)=0 by
      linear_combination e₁-e₂)).resolve_left (sub_ne_zero.mpr hst)
  linear_combination e₁+(r-s)*e₃

private theorem transport_to_normalized_model {W : WeierstrassCurve F}
    (C : VariableChange F) (q t : F) (hW : C • W = normalizedMarkedCurve q t)
    (T Q : W.toAffine.Point) (ho : addOrderOf Q = 14) (hind : 7 • Q ≠ T)
    (hT : ∃ ht : (normalizedMarkedCurve q t).toAffine.Nonsingular 0 0,
      changeTo C hW T = Affine.Point.some 0 0 ht)
    (hQ : ∃ hq : (normalizedMarkedCurve q t).toAffine.Nonsingular ((t+1)*(q*t+1)) (t*((t+1)*(q*t+1))),
      changeTo C hW Q = Affine.Point.some _ _ hq) :
    ∃ (u v : F), fibre u 1 v 1 = 0 ∧ C • W = markedCurve u v := by
  obtain ⟨ht, hT⟩ := hT
  obtain ⟨hq, hQ⟩ := hQ
  let e := changeTo C hW
  have h14 : addOrderOf (Affine.Point.some _ _ hq) = 14 := by
    rw [← hQ]
    change addOrderOf (e.toAddMonoidHom Q) = 14
    exact (addOrderOf_injective e.toAddMonoidHom e.injective Q).trans ho
  have hne : 7 • Affine.Point.some _ _ hq ≠ Affine.Point.some 0 0 ht := by
    rw [← hQ, ← hT, ← map_nsmul e]
    exact fun h => hind (e.injective h)
  obtain ⟨u,v,hf,he⟩ := normalized_torsion_has_affine_model q t hq ht h14 hne
  exact ⟨u,v,hf,hW.trans he.symm⟩

/-- An order-fourteen point and full two-torsion on an elliptic curve over an
ordered field supply the marked affine model. The extremal two-torsion roots
ensure a positive coefficient in the short equation used for normalization. -/
theorem torsion_tuple_has_marked_model [LinearOrder F] [IsStrictOrderedRing F]
    (E : WeierstrassCurve F) (Q : E.toAffine.Point) (hQ : addOrderOf Q = 14)
    (T : Fin 3 → E.toAffine.Point) (hT : Function.Injective T)
    (hT₀ : ∀ i, T i ≠ 0) (hT₂ : ∀ i, 2 • T i = 0) :
    ∃ (u v : F) (C : VariableChange F), fibre u 1 v 1 = 0 ∧ C • E = markedCurve u v := by
  obtain ⟨C₀,A,B,h₀⟩ := short_equation_of_two_torsion E (T 0) (hT₀ 0) (hT₂ 0)
  let W : WeierstrassCurve F := ⟨0,A,0,B,0⟩
  let e := changeTo C₀ (V := W) h₀
  let Q₀ := e Q
  let T₀ (i : Fin 3) := e (T i)
  have hQ₀ : addOrderOf Q₀ = 14 := (addOrderOf_injective e.toAddMonoidHom e.injective Q).trans hQ
  have hTinj : Function.Injective T₀ := e.injective.comp hT
  have hTne (i : Fin 3) : T₀ i ≠ 0 := by
    intro h
    exact hT₀ i (e.injective (h.trans e.map_zero.symm))
  have hTord (i : Fin 3) : 2 • T₀ i = 0 := by
    change 2 • e (T i) = 0
    rw [← map_nsmul, hT₂ i, map_zero]
  choose x hxs hxt hxpoly using
    fun i : Fin 3 => affine_coordinates_of_two_point A B (T₀ i) (hTne i) (hTord i)
  have hxinj : Function.Injective x := by
    intro i j hij
    apply hTinj
    rw [hxt i, hxt j]
    congr
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  have hij : i ≠ j := by
    intro h
    obtain ⟨k,hk,_⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide : 2 < 3)
    subst j
    apply hk
    apply hxinj
    exact le_antisymm (hj k (Finset.mem_univ k)) (hi k (Finset.mem_univ k))
  obtain ⟨k,hk,hExtreme⟩ : ∃ k : Fin 3, 7 • Q₀ ≠ T₀ k ∧
      ((∀ a, x k ≤ x a) ∨ (∀ a, x a ≤ x k)) := by
    by_cases h : 7 • Q₀ = T₀ i
    · exact ⟨j, h.trans_ne (hTinj.ne hij), Or.inr (fun a => hj a (Finset.mem_univ a))⟩
    · exact ⟨i, h, Or.inl (fun a => hi a (Finset.mem_univ a))⟩
  let l := k+1
  let m := k+2
  have hkl : k ≠ l := by dsimp [l]; fin_cases k <;> decide
  have hkm : k ≠ m := by dsimp [m]; fin_cases k <;> decide
  have hlm : l ≠ m := by dsimp [l,m]; fin_cases k <;> decide
  let a := A+3*x k
  let b := B+2*x k*A+3*x k^2
  have hb : 0 < b := by
    change 0 < B+2*x k*A+3*x k^2
    rw [derivative_at_three_roots A B (x k) (x l) (x m) (hxinj.ne hkl) (hxinj.ne hkm) (hxinj.ne hlm)
      (hxpoly k) (hxpoly l) (hxpoly m)]
    rcases hExtreme with h | h
    · exact mul_pos_of_neg_of_neg
        (sub_neg.mpr ((h l).lt_of_ne (hxinj.ne hkl)))
        (sub_neg.mpr ((h m).lt_of_ne (hxinj.ne hkm)))
    · exact mul_pos (sub_pos.mpr ((h l).lt_of_ne (hxinj.ne hkl.symm)))
        (sub_pos.mpr ((h m).lt_of_ne (hxinj.ne hkm.symm)))
  let C : VariableChange F := ⟨1,x k,0,0⟩
  let V : WeierstrassCurve F := ⟨0,a,0,b,0⟩
  have hV : C • W = V := short_translate_root A B (x k) (hxpoly k)
  let f := changeTo C hV
  let Q₁ := f Q₀
  have h14 : addOrderOf Q₁ = 14 := (addOrderOf_injective f.toAddMonoidHom f.injective Q₀).trans hQ₀
  obtain ⟨hT, eT⟩ : ∃ hT : V.toAffine.Nonsingular 0 0,
      f (T₀ k) = Affine.Point.some 0 0 hT := by
    rw [hxt k]
    simpa [C, VariableChange.vcX, VariableChange.vcY] using changeTo_some C hV (x k) 0 (hxs k)
  have hInd : 7 • Q₁ ≠ Affine.Point.some 0 0 hT := by
    rw [← eT, ← map_nsmul f]
    exact fun h => hk (f.injective h)
  cases eQ : Q₁ with
  | zero =>
    rw [eQ] at h14
    change addOrderOf (0 : V.toAffine.Point) = 14 at h14
    simp at h14
  | some X Y hXY =>
    rw [eQ] at h14 hInd
    obtain ⟨hX,hY,hm⟩ := order_fourteen_short_nonvanishing a b X Y hXY hT h14
    have hp : X^2+b ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg X) hb).ne'
    have hEq := (Affine.equation_iff X Y).mp hXY.1
    change Y^2+0*X*Y+0*Y = X^3+a*X^2+b*X+0 at hEq
    simp only [zero_mul, add_zero] at hEq
    obtain ⟨s,q,t,hW,hx,hy⟩ := normalize_second_point a b X Y hX hY hp hm hEq
    let D := VariableChange.mk s 0 0 0
    have hD : D • V = normalizedMarkedCurve q t := hW
    have hxD : D.vcX X = (t+1)*(q*t+1) := by
      change ((↑s⁻¹ : F)^2)*(X-0) = _
      rw [sub_zero, Units.val_inv_eq_inv_val, inv_pow, inv_mul_eq_div, hx]
    have hyD : D.vcY X Y = t*((t+1)*(q*t+1)) := by
      change ((↑s⁻¹ : F)^3)*(Y-0*(X-0)-0) = _
      rw [zero_mul, sub_zero, sub_zero, Units.val_inv_eq_inv_val, inv_pow, inv_mul_eq_div, hy]
    obtain ⟨u,v,hf,hD'⟩ := transport_to_normalized_model D q t hD _ _ h14 hInd
      (by simpa [D, VariableChange.vcX, VariableChange.vcY] using changeTo_some D hD 0 0 hT)
      (by simpa only [hxD,hyD] using changeTo_some D hD X Y hXY)
    refine ⟨u,v,D*C*C₀,hf,?_⟩
    rw [mul_smul, h₀, mul_smul, hV, hD']

end Normalization

open NumberField InfinitePlace

theorem cubic_has_real_embedding {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 3) : Nonempty (K →+* ℝ) := by
  classical
  have h := card_add_two_mul_card_eq_rank K
  rw [hK] at h
  have hpos : 0 < nrRealPlaces K := by omega
  obtain ⟨⟨w, hw⟩⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨w.embedding_of_isReal hw⟩

private def torsionMarkers : Fin 3 → (ZMod 2 × ZMod 14) := ![(1,0),(0,7),(1,7)]

private theorem torsionMarkers_injective : Function.Injective torsionMarkers :=
  (by decide +kernel : ∀ i j : Fin 3, torsionMarkers i = torsionMarkers j → i = j)

/-- A subgroup of type `C₂ × C₁₄` in a cubic number field gives a point of the
explicit affine equation with the same elliptic curve after a Weierstrass change. -/
theorem cubic_torsion_has_marked_model {K : Type*} [Field K] [NumberField K] [DecidableEq K]
    (hK : Module.finrank ℚ K = 3) (E : WeierstrassCurve K)
    (ρ : (ZMod 2 × ZMod 14) →+ E.toAffine.Point) (hρ : Function.Injective ρ) :
    ∃ (u v : K) (C : VariableChange K), fibre u 1 v 1 = 0 ∧ C • E = markedCurve u v := by
  obtain ⟨f⟩ := cubic_has_real_embedding hK
  let : LinearOrder K := LinearOrder.lift' f f.injective
  let : IsStrictOrderedRing K := Function.Injective.isStrictOrderedRing f (map_zero f) (map_one f)
    (map_add f) (map_mul f) (by intros; rfl) (by intros; rfl)
  let e : ZMod 14 →+ E.toAffine.Point := ρ.comp (AddMonoidHom.inr (ZMod 2) (ZMod 14))
  have he : Function.Injective e := by
    intro a b hab
    exact congrArg Prod.snd (hρ hab)
  have hne (i : Fin 3) : torsionMarkers i ≠ 0 := by fin_cases i <;> decide
  have htwo (i : Fin 3) : (2 : ℕ) • torsionMarkers i = 0 := by fin_cases i <;> decide
  have hOrd : addOrderOf (e 1) = 14 := (addOrderOf_injective e he 1).trans (ZMod.addOrderOf_one 14)
  apply torsion_tuple_has_marked_model E (e 1) hOrd (fun i => ρ (torsionMarkers i))
    (hρ.comp torsionMarkers_injective)
  · intro i hi
    exact hne i (hρ (hi.trans (map_zero ρ).symm))
  · intro i
    rw [← map_nsmul, htwo i, map_zero]

/-- The torsion-group hypothesis of Proposition 3.1 supplies an affine point
over the cubic field and the marked Weierstrass equation at that point. -/
theorem cubic_torsion_group_has_marked_model {K : Type*} [Field K] [NumberField K] [DecidableEq K]
    (hK : Module.finrank ℚ K = 3) (E : WeierstrassCurve ℚ)
    (hT : Nonempty ((AddCommGroup.torsion (E.map (algebraMap ℚ K)).toAffine.Point) ≃+
      (ZMod 2 × ZMod 14))) :
    ∃ (u v : K) (C : VariableChange K),
      fibre u 1 v 1 = 0 ∧ C • E.map (algebraMap ℚ K) = markedCurve u v := by
  obtain ⟨e⟩ := hT
  let ρ := (AddCommGroup.torsion (E.map (algebraMap ℚ K)).toAffine.Point).subtype.comp e.symm.toAddMonoidHom
  exact cubic_torsion_has_marked_model hK _ ρ (Subtype.val_injective.comp e.symm.injective)

end NajmanTrbovic.Cubic
