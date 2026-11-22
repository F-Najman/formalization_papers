module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.List.Basic

import Mathlib.Tactic.Ring

/-! Homogenization with the coefficients written in ascending order. -/

@[expose] public section

namespace NajmanTrbovic

def homogeneous {R : Type*} [Semiring R] (x y : R) : List R → R
  | [] => 0
  | a :: as => a * y ^ as.length + x * homogeneous x y as

theorem map_homogeneous {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    (x y : R) (c : List R) :
    f (homogeneous x y c) = homogeneous (f x) (f y) (c.map f) := by
  induction c with
  | nil => simp [homogeneous]
  | cons a c ih => simp [homogeneous, ih]

theorem homogeneous_scale {R : Type*} [CommSemiring R] (q x y : R) (c : List R) :
    homogeneous (q * x) (q * y) c = q ^ (c.length - 1) * homogeneous x y c := by
  induction c with
  | nil => simp [homogeneous]
  | cons a c ih =>
    cases c with
    | nil => simp [homogeneous]
    | cons b c =>
      change a * (q * y) ^ (c.length + 1) + (q * x) * homogeneous (q * x) (q * y) (b :: c) =
        q ^ (c.length + 1) * (a * y ^ (c.length + 1) + x * homogeneous x y (b :: c))
      rw [ih, mul_pow, pow_succ q c.length]
      simp only [List.length_cons, Nat.add_sub_cancel]
      ring

end NajmanTrbovic
