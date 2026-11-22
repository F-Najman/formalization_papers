module

public import NajmanTrbovic.CubicModel

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic

/-! The three distinct residual roots at the cyclotomic fibers. -/

@[expose] public section

namespace NajmanTrbovic.Cubic

private def candidate {K : Type*} [Field K] (ζ : K) (i : ℕ) := ζ^i + ζ^(7-i)

private theorem factor_at_primitive_root {K : Type*} [Field K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 7) (v z : K) :
    r v z = (v - candidate ζ 1 * z) * (v - candidate ζ 2 * z) *
      (v - candidate ζ 3 * z) := by
  let phi := ζ^6+ζ^5+ζ^4+ζ^3+ζ^2+ζ+1
  have hphi : phi = 0 := by
    apply (mul_eq_zero.mp (show (ζ-1) * phi = 0 by
      dsimp [phi]; linear_combination hζ.pow_eq_one)).resolve_left
    exact sub_ne_zero.mpr (hζ.ne_one (by decide))
  unfold r candidate
  norm_num
  dsimp [phi] at hphi
  linear_combination
    -(-(v^2)*z + z^3*(-ζ^9 + ζ^7 - ζ^6 - ζ + 1) + z^2*v*(ζ^5+ζ^3-2*ζ+2)) * hphi

private theorem candidate_injective {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 7)
    {i j : ℕ} (_hi : 0 < i) (hi' : i < 7) (hj : 0 < j) (hj' : j < 7)
    (hij : i ≠ j) (hsum : i + j ≠ 7) : candidate ζ i ≠ candidate ζ j := by
  intro h
  unfold candidate at h
  have invw (k : ℕ) (hk : k ≤ 7) : ζ^k * ζ^(7-k) = 1 := by
    rw [← pow_add, Nat.add_sub_of_le hk, hζ.pow_eq_one]
  have hprod : (ζ^i-ζ^j) * (ζ^i-ζ^(7-j)) = 0 := by
    linear_combination ζ^i * h + invw j hj'.le - invw i hi'.le
  rcases mul_eq_zero.mp hprod with he | he
  · exact hij (hζ.pow_inj hi' hj' (sub_eq_zero.mp he))
  · have he' := hζ.pow_inj hi' (by omega : 7-j < 7) (sub_eq_zero.mp he)
    exact hsum (by omega)

/-- The binary cubic (r) splits into three distinct linear factors over (mathbf F_p)
for rational primes (pequiv 1,-1mod 7). -/
theorem r_splits_mod_prime {p : ℕ} (hp : p.Prime) (h7 : p % 7 = 1 ∨ p % 7 = 6) :
    ∃ A B C : ZMod p, A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
      ∀ v z : ZMod p, r v z = (v-A*z)*(v-B*z)*(v-C*z) := by
  let : Fact p.Prime := ⟨hp⟩
  let L := AlgebraicClosure (ZMod p)
  let f := algebraMap (ZMod p) L
  let : NeZero ((7 : ℕ) : ZMod p) := ⟨by
    intro h
    have h₁ := (ZMod.natCast_eq_zero_iff 7 p).mp h
    have h₂ := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp h₁
    subst p
    norm_num at h7⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot L 7
  have hred (j : ℕ) : ζ^(j*p) = ζ^((j%7)*(p%7)%7) := by
    have he (n : ℕ) : ζ^n = ζ^(n%7) := by
      calc
        _ = ζ^(n%7 + 7*(n/7)) := congrArg (fun a : ℕ => ζ^a) (Nat.mod_add_div n 7).symm
        _ = _ := by rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    exact (he _).trans (congrArg (fun a : ℕ => ζ^a) (Nat.mul_mod j p 7))
  have fixed (i : Fin 3) : candidate ζ (i.val+1)^p = candidate ζ (i.val+1) := by
    unfold candidate
    rw [add_pow_char _ _ p, ← pow_mul, ← pow_mul, hred, hred]
    rcases h7 with h | h <;> fin_cases i <;> norm_num [h] <;> ring
  have in_range (i : Fin 3) : ∃ a : ZMod p, f a = candidate ζ (i.val+1) := by
    have hm := (Subfield.mem_bot_iff_pow_eq_self L p).mpr (fixed i)
    have hr : (⊥ : Subfield L) ≤ f.fieldRange := bot_le
    exact hr hm
  obtain ⟨a, ha⟩ := in_range 0
  obtain ⟨b, hb⟩ := in_range 1
  obtain ⟨c, hc⟩ := in_range 2
  change f a = candidate ζ 1 at ha
  change f b = candidate ζ 2 at hb
  change f c = candidate ζ 3 at hc
  have ne (i j : ℕ) (hi : 0 < i) (hi' : i < 7) (hj : 0 < j) (hj' : j < 7)
      (hij : i ≠ j) (hsum : i + j ≠ 7) {x y : ZMod p} (hx : f x = candidate ζ i)
      (hy : f y = candidate ζ j) : x ≠ y := by
    intro h
    exact candidate_injective hζ hi hi' hj hj' hij hsum (hx.symm.trans (h ▸ hy))
  refine ⟨a, b, c, ne 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha hb,
    ne 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha hc,
    ne 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hb hc, ?_⟩
  intro v z
  apply f.injective
  simpa only [r, map_add, map_sub, map_pow, map_mul, map_ofNat, ha, hb, hc] using
    factor_at_primitive_root hζ (f v) (f z)

end NajmanTrbovic.Cubic
