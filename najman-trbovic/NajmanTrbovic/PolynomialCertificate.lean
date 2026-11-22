module

public import Mathlib.Algebra.Ring.Int.Defs

import Mathlib.Tactic

/-! Integer coefficient lists for checking a bivariate polynomial certificate. Evaluation
commutes with the list operations, so the checked identity holds over every commutative ring. -/

@[expose] public section

namespace NajmanTrbovic.PolynomialCertificate

def addRows {A : Type*} (add : A → A → A) : List A → List A → List A
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => add a b :: addRows add as bs

def mulRows {A : Type*} (zero : A) (add mul : A → A → A) : List A → List A → List A
  | [], _ => []
  | a :: as, bs => addRows add (bs.map (mul a)) (zero :: mulRows zero add mul as bs)

def trim {A : Type*} (isZero : A → Bool) : List A → List A
  | [] => []
  | a :: as => match trim isZero as with
    | [] => if isZero a then [] else [a]
    | b :: bs => a :: b :: bs

def evalRows {A R : Type*} [Semiring R] (f : A → R) (x : R) : List A → R
  | [] => 0
  | a :: as => f a + x * evalRows f x as

private theorem eval_addRows {A R : Type*} [Semiring R] (f : A → R) (x : R)
    (add : A → A → A) (h : ∀ a b, f (add a b) = f a + f b) (as bs : List A) :
    evalRows f x (addRows add as bs) = evalRows f x as + evalRows f x bs := by
  induction as generalizing bs with
  | nil => simp [evalRows, addRows]
  | cons a as ih =>
    cases bs with
    | nil => simp [evalRows, addRows]
    | cons b bs => simp [evalRows, addRows, h, ih, add_assoc, add_left_comm, mul_add]

private theorem eval_map_mul {A R : Type*} [CommSemiring R] (f : A → R) (x : R)
    (mul : A → A → A) (h : ∀ a b, f (mul a b) = f a * f b) (a : A) (bs : List A) :
    evalRows f x (bs.map (mul a)) = f a * evalRows f x bs := by
  induction bs with
  | nil => simp [evalRows]
  | cons b bs ih => simp [evalRows, h, ih, mul_add, mul_left_comm]

private theorem eval_mulRows {A R : Type*} [CommSemiring R] (f : A → R) (x : R)
    (zero : A) (add mul : A → A → A) (hz : f zero = 0)
    (ha : ∀ a b, f (add a b) = f a + f b) (hm : ∀ a b, f (mul a b) = f a * f b)
    (as bs : List A) : evalRows f x (mulRows zero add mul as bs) =
      evalRows f x as * evalRows f x bs := by
  induction as with
  | nil => simp [evalRows, mulRows]
  | cons a as ih =>
    simp [mulRows, eval_addRows f x add ha, eval_map_mul f x mul hm, evalRows, hz, ih,
      add_mul, mul_assoc]

private theorem eval_map_neg {A R : Type*} [Ring R] (f : A → R) (x : R)
    (neg : A → A) (hn : ∀ a, f (neg a) = -f a) (as : List A) :
    evalRows f x (as.map neg) = -evalRows f x as := by
  induction as with
  | nil => simp [evalRows]
  | cons a as ih => simp [evalRows, hn, ih, add_comm]

private theorem eval_trim {A R : Type*} [Semiring R] (f : A → R) (x : R)
    (zero : A → Bool) (hz : ∀ a, zero a → f a = 0) (as : List A) :
    evalRows f x (trim zero as) = evalRows f x as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    unfold trim
    generalize hs : trim zero as = xs at ih
    cases xs with
    | nil =>
      have he : evalRows f x as = 0 := ih.symm
      by_cases ha : zero a <;> simp [ha, hz, evalRows, he]
    | cons b bs => simp only [evalRows] at ih ⊢; rw [ih]

/-- The outer list is in ascending powers of the second variable. The inner lists
are in ascending powers of the first variable. Empty lists represent zero. -/
def Coefficients := List (List ℤ)
  deriving DecidableEq

namespace Coefficients

instance : Add Coefficients := ⟨addRows (addRows (· + ·))⟩
instance : Mul Coefficients := ⟨mulRows [] (addRows (· + ·)) (mulRows 0 (· + ·) (· * ·))⟩
instance : Neg Coefficients := ⟨List.map (List.map Neg.neg)⟩
instance : Sub Coefficients := ⟨fun a b => a + -b⟩
instance (n : ℕ) : OfNat Coefficients n := ⟨[[(n : ℤ)]]⟩

instance : Pow Coefficients ℕ := ⟨fun a n => Nat.rec 1 (fun _ b => b*a) n⟩

def u : Coefficients := [[0,1]]
def v : Coefficients := [[],[1]]

def normal (p : Coefficients) : Coefficients :=
  trim List.isEmpty (p.map (trim (· == 0)))

def value {R : Type*} [Ring R] (x y : R) (p : Coefficients) : R :=
  evalRows (evalRows Int.cast x) y p

variable {R : Type*} [CommRing R] (x y : R)

theorem value_nat (n : ℕ) : value x y (OfNat.ofNat n : Coefficients) = (n : R) := by
  change (((n : ℤ) : R) + x * 0) + y * 0 = (n : R)
  simp

@[simp] theorem value_one : value x y 1 = 1 := by
  simpa only [Nat.cast_one] using value_nat x y 1

@[simp] theorem value_ofNat (n : ℕ) [n.AtLeastTwo] :
    value x y (ofNat(n) : Coefficients) = (ofNat(n) : R) :=
  value_nat x y n

@[simp] theorem value_u : value x y u = x := by simp [value, u, evalRows]
@[simp] theorem value_v : value x y v = y := by simp [value, v, evalRows]

@[simp] theorem value_add (a b : Coefficients) : value x y (a+b) = value x y a + value x y b :=
  eval_addRows (evalRows Int.cast x) y _ (eval_addRows Int.cast x _ Int.cast_add) a b

@[simp] theorem value_mul (a b : Coefficients) : value x y (a*b) = value x y a * value x y b :=
  eval_mulRows (evalRows Int.cast x) y [] _ _ rfl (eval_addRows Int.cast x _ Int.cast_add)
    (eval_mulRows Int.cast x 0 _ _ Int.cast_zero Int.cast_add Int.cast_mul) a b

@[simp] theorem value_neg (a : Coefficients) : value x y (-a) = -value x y a :=
  eval_map_neg (evalRows Int.cast x) y _ (eval_map_neg Int.cast x _ Int.cast_neg) a

@[simp] theorem value_sub (a b : Coefficients) : value x y (a-b) = value x y a - value x y b := by
  change value x y (a + -b) = _
  rw [value_add, value_neg, sub_eq_add_neg]

@[simp] theorem value_pow (a : Coefficients) (n : ℕ) : value x y (a^n) = value x y a ^ n := by
  induction n with
  | zero => change value x y 1 = _; rw [value_one, pow_zero]
  | succ n ih =>
    change value x y (a^n*a) = value x y a ^ (n+1)
    rw [value_mul, ih, pow_succ]

theorem value_normal (p : Coefficients) : value x y (normal p) = value x y p := by
  unfold value normal
  rw [eval_trim (evalRows Int.cast x) y _ (by intro a ha; cases a <;> simp [evalRows] at ha ⊢)]
  induction (p : List (List ℤ)) with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, evalRows, ih]
    rw [eval_trim Int.cast x _ (by intro s hs; simp_all)]

end Coefficients
end NajmanTrbovic.PolynomialCertificate
