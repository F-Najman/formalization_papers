module

public import NajmanTrbovic.Squareclasses
public import NajmanTrbovic.Witnesses
public import Mathlib.Data.ZMod.Basic

import Mathlib.Tactic

/-! Exact ramification exclusions and witnesses for the affine non-exceptional families. -/

@[expose] public section

namespace NajmanTrbovic

theorem form_cast {R : Type*} [Ring R] (f : ℤ →+* R) (N : Level) (m n : ℤ) :
    f (N.form m n) = N.form (f m) (f n) := by
  have hf : (f : ℤ → R) = fun a : ℤ => (a : R) := by funext a; simp
  simpa [Level.form, hf] using map_homogeneous f m n N.coefficients

theorem form_mod (q : ℕ) (N : Level) (m n : ℤ) :
    ((N.form m n : ℤ) : ZMod q) = N.form (m : ZMod q) (n : ZMod q) :=
  form_cast (Int.castRingHom (ZMod q)) N m n

private theorem degree_even (N : Level) : (N.coefficients.length - 1) / 2 * 2 =
    N.coefficients.length - 1 := by cases N <;> decide

theorem form_scale {R : Type*} [CommRing R] (N : Level) (c m n : R) :
    N.form (c * m) (c * n) = (c ^ ((N.coefficients.length - 1) / 2)) ^ 2 * N.form m n := by
  unfold Level.form
  rw [homogeneous_scale, List.length_map, ← pow_mul, degree_even]

theorem isUnit_cast_of_not_dvd {p k : ℕ} (hp : p.Prime) (hk : 0 < k) {a : ℤ}
    (ha : ¬(p : ℤ) ∣ a) : IsUnit (a : ZMod (p^k)) := by
  have hh : ¬p ∣ a.natAbs := by simpa [← Int.natAbs_dvd_natAbs] using ha
  have hu := (ZMod.isUnit_natCast_iff_not_dvd_pow (d := k) hp hk).mpr hh
  rcases Int.natAbs_eq a with h | h
  · rw [h]
    simpa only [Int.cast_natCast] using hu
  · rw [h, Int.cast_neg, Int.cast_natCast]
    exact hu.neg

theorem not_both_dvd {p : ℕ} (hp : p.Prime) {m n : ℤ} (h : m.gcd n = 1) :
    ¬((p : ℤ) ∣ m ∧ (p : ℤ) ∣ n) := by
  rintro ⟨hm, hn⟩
  have hd := Int.dvd_coe_gcd hm hn
  rw [h] at hd
  exact hp.not_dvd_one (by exact_mod_cast hd)

theorem residue_cases {q : ℕ} [NeZero q] (z : ZMod q) :
    ∃ a : Fin q, (a.val : ZMod q) = z := ⟨⟨z.val, z.val_lt⟩, ZMod.natCast_zmod_val z⟩

def RootFree (N : Level) (p : ℕ) : Prop :=
  N.form (1 : ZMod p) 0 ≠ 0 ∧ ∀ x : Fin p, N.form (x.val : ZMod p) 1 ≠ 0

instance (N : Level) (p : ℕ) : Decidable (RootFree N p) := by
  unfold RootFree
  infer_instance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem table7_root_free (N : Level) : ∀ p : Fin 101,
    p.val.Prime → p.val ≠ 2 → p.val ∈ N.table7 → RootFree N p.val := by
  cases N <;> decide +kernel

theorem form_nonzero_at_prime {N : Level} {p : ℕ} (hp : p.Prime)
    (hf : RootFree N p) {m n : ℤ} (hg : m.gcd n = 1) : ((N.form m n : ℤ) : ZMod p) ≠ 0 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  rw [form_mod]
  intro hz
  by_cases hn : (n : ZMod p) = 0
  · have hm : (m : ZMod p) ≠ 0 := by
      intro he
      exact not_both_dvd hp hg ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp he,
        (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp hn⟩
    rw [hn] at hz
    have h := form_scale N (m : ZMod p) 1 0
    rw [mul_zero, mul_one] at h
    exact (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hm)) hf.1) (h.symm.trans hz)
  · let c := (n : ZMod p)⁻¹
    have hc : c * (n : ZMod p) = 1 := inv_mul_cancel₀ hn
    have h := form_scale N c (m : ZMod p) (n : ZMod p)
    rw [hc, hz, mul_zero] at h
    obtain ⟨a, ha⟩ := residue_cases (c * (m : ZMod p))
    exact hf.2 a (ha ▸ h)

private def TwoCharts (N : Level) : Prop := ∀ x : Fin 256,
  smallTwoShape ((N.form (x.val : ZMod 256) 1).val : ℤ) ∧
    smallTwoShape ((N.form (1 : ZMod 256) x.val).val : ℤ)

set_option maxRecDepth 4096 in
private instance (N : Level) : Decidable (TwoCharts N) := by
  unfold TwoCharts
  exact Nat.decidableForallFin _

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem table7_two_charts (N : Level) : 2 ∈ N.table7 → TwoCharts N := by
  cases N <;> decide +kernel

private theorem unramified_from_charts {N : Level} (hcharts : TwoCharts N) {D m n s : ℤ}
    (hD : Squarefree D) (hg : m.gcd n = 1) (h : N.form m n = D * s ^ 2) : Unramified D 2 := by
  have hf : N.form (m : ZMod 256) (n : ZMod 256) = (D : ZMod 256) * (s : ZMod 256) ^ 2 := by
    rw [← form_mod, h]
    push_cast
    rfl
  have apply_shape (f c : ZMod 256) (hs : smallTwoShape (f.val : ℤ))
      (hval : f = (D : ZMod 256) * c ^ 2) : D % 4 = 1 := by
    have hmod : (f.val : ℤ) ≡ D * (c.val : ℤ) ^ 2 [ZMOD 256] := by
      apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_mul, Int.cast_pow] using hval
    obtain ⟨k, hk⟩ := (smallTwoShape_congr hmod).mp hs
    exact mod_four_eq_one_of_twoShape hD hk
  have scaled (c : ZMod 256) : N.form (c * (m : ZMod 256)) (c * (n : ZMod 256)) =
      (D : ZMod 256) * (c ^ ((N.coefficients.length - 1) / 2) * (s : ZMod 256)) ^ 2 := by
    rw [form_scale, hf]
    ring
  apply unramified_two.mpr
  by_cases hn : (2 : ℤ) ∣ n
  · have hm : ¬(2 : ℤ) ∣ m := fun hm => not_both_dvd Nat.prime_two hg ⟨hm, hn⟩
    obtain ⟨u, hu⟩ := isUnit_cast_of_not_dvd Nat.prime_two (k := 8) (by decide) hm
    have he : (↑u⁻¹ : ZMod 256) * (m : ZMod 256) = 1 := by rw [← hu]; simp
    obtain ⟨a, ha⟩ := residue_cases ((↑u⁻¹ : ZMod 256) * (n : ZMod 256))
    have hh := scaled (↑u⁻¹)
    rw [he, ← ha] at hh
    exact apply_shape _ _ (hcharts a).2 hh
  · obtain ⟨u, hu⟩ := isUnit_cast_of_not_dvd Nat.prime_two (k := 8) (by decide) hn
    have he : (↑u⁻¹ : ZMod 256) * (n : ZMod 256) = 1 := by rw [← hu]; simp
    obtain ⟨a, ha⟩ := residue_cases ((↑u⁻¹ : ZMod 256) * (m : ZMod 256))
    have hh := scaled (↑u⁻¹)
    rw [he, ← ha] at hh
    exact apply_shape _ _ (hcharts a).1 hh

/-- Every listed prime passes the discriminant test on every non-exceptional squareclass. -/
theorem table7_unramified {N : Level} {p : ℕ} (hp : p.Prime) (h100 : p ≤ 100)
    (hmem : p ∈ N.table7) {D : ℤ} (hD : Represents N D) : Unramified D p := by
  obtain ⟨hd, _, m, n, s, hg, _, _, he⟩ := hD
  by_cases h₂ : p = 2
  · subst p
    exact unramified_from_charts (table7_two_charts N hmem) hd hg he
  · rw [unramified_odd hp h₂]
    intro hpD
    have hF : ((N.form m n : ℤ) : ZMod p) ≠ 0 :=
      form_nonzero_at_prime hp (table7_root_free N ⟨p, by omega⟩ hp h₂ hmem) hg
    rw [he, Int.cast_mul, Int.cast_pow, (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr hpD,
      zero_mul] at hF
    exact hF rfl

private def WitnessValid (N : Level) (p : ℕ) : Prop :=
  let w := table7Witness N p
  let a : ℤ := N.form w.x 1
  a ≠ 0 ∧ if p = 2 then ¬smallTwoShape a ∧ ¬ (256 : ℤ) ∣ a
    else w.valuation % 2 = 1 ∧ (p : ℤ)^w.valuation ∣ a ∧ ¬(p : ℤ)^(w.valuation+1) ∣ a

private instance (N : Level) (p : ℕ) : Decidable (WitnessValid N p) := by
  unfold WitnessValid
  infer_instance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem witness_valid (N : Level) : ∀ p : Fin 101,
    p.val.Prime → p.val ∉ N.table7 → WitnessValid N p.val := by
  cases N <;> decide +kernel

/-- Every omitted prime at most 100 has a ramified squareclass at an integer coordinate. -/
theorem table7_ramification_witness {N : Level} {p : ℕ} (hp : p.Prime) (h100 : p ≤ 100)
    (hmem : p ∉ N.table7) : ∃ D : ℤ, Represents N D ∧ ¬ Unramified D p := by
  let w := table7Witness N p
  let a : ℤ := N.form w.x 1
  have hw := witness_valid N ⟨p, by omega⟩ hp hmem
  change a ≠ 0 ∧ (if p = 2 then ¬smallTwoShape a ∧ ¬ (256 : ℤ) ∣ a
    else w.valuation % 2 = 1 ∧ (p : ℤ)^w.valuation ∣ a ∧ ¬(p : ℤ)^(w.valuation+1) ∣ a) at hw
  obtain ⟨s, D, h, hD⟩ := exists_sq_mul_squarefree a
  have hs : s ≠ 0 := by rintro rfl; simp at h; exact hw.1 h.symm
  have he : a = D * s ^ 2 := by rw [mul_comm, h]
  have hr : ¬Unramified D p := by
    by_cases h₂ : p = 2
    · subst p
      have htwo := hw.2
      rw [ite_eq_left rfl, he] at htwo
      exact fun ha => htwo.1 (smallTwoShape_of_mod_four_eq_one (unramified_two.mp ha) htwo.2)
    · have hodd := hw.2
      rw [ite_eq_right h₂, he] at hodd
      exact fun ha => (unramified_odd hp h₂).mp ha
        (prime_dvd_of_odd_valuation hp hD hs hodd.1 hodd.2.1 hodd.2.2)
  have hne : D ≠ 1 := by
    rintro rfl
    exact hr (by simp [Unramified, quadraticDiscriminant, Int.natCast_dvd, hp.not_dvd_one])
  exact ⟨D, ⟨hD, hne, w.x, 1, s, by simp, one_ne_zero, hs, he⟩, hr⟩

/-- Table 7 is exact for the squareclasses of the corrected Table 1 models. -/
theorem table7_iff {N : Level} {p : ℕ} (hp : p.Prime) (h100 : p ≤ 100) :
    p ∈ N.table7 ↔ ∀ D : ℤ, Represents N D → Unramified D p := by
  constructor
  · exact fun hmem _ => table7_unramified hp h100 hmem
  · intro h
    by_contra hmem
    obtain ⟨D, hD, hn⟩ := table7_ramification_witness hp h100 hmem
    exact hn (h D hD)

end NajmanTrbovic
