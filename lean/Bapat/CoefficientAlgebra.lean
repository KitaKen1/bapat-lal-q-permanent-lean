import Bapat.Certificate
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Algebraic meaning of the certificate's coefficient operations

The polynomial semantics is proved for arbitrary coefficient lists, not only
for the known numerical answer. The concrete certificate is computed in integers.
-/

namespace Bapat.Certificate

noncomputable section

def toComplex (z : Gaussian) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

@[simp] theorem toComplex_zero : toComplex zero = 0 := by
  simp [toComplex, zero]

theorem toComplex_add (x y : Gaussian) : toComplex (add x y) = toComplex x + toComplex y := by
  simp [toComplex, add]
  ring

theorem toComplex_mul (x y : Gaussian) : toComplex (mul x y) = toComplex x * toComplex y := by
  apply Complex.ext <;>
    simp [toComplex, mul, Complex.mul_re, Complex.mul_im]

theorem toComplex_scale (a : ℤ) (x : Gaussian) :
    toComplex (scale a x) = (a : ℂ) * toComplex x := by
  simp [toComplex, scale]
  ring

/-- Interpret an ascending coefficient list as a complex polynomial. -/
def asPolynomial : List Gaussian → Polynomial ℂ
  | [] => 0
  | c :: cs => Polynomial.C (toComplex c) + Polynomial.X * asPolynomial cs

theorem asPolynomial_append_zero (xs : List Gaussian) :
    asPolynomial (xs ++ [zero]) = asPolynomial xs := by
  induction xs with
  | nil => simp [asPolynomial]
  | cons x xs ih => simp [asPolynomial, ih]

theorem asPolynomial_zero_cons (xs : List Gaussian) :
    asPolynomial (zero :: xs) = Polynomial.X * asPolynomial xs := by
  simp [asPolynomial]

/-- Every polynomial coefficient is the corresponding Gaussian-integer list entry. -/
theorem asPolynomial_coeff (xs : List Gaussian) (k : ℕ) :
    (asPolynomial xs).coeff k = toComplex (xs.getD k zero) := by
  induction xs generalizing k with
  | nil => simp [asPolynomial, List.getD]
  | cons c cs ih =>
    cases k with
    | zero => simp [asPolynomial, List.getD]
    | succ k => simp [asPolynomial, List.getD, Polynomial.coeff_X_mul, ih]

theorem asPolynomial_map_scale (a : ℤ) (xs : List Gaussian) :
    asPolynomial (xs.map (scale a)) = Polynomial.C (a : ℂ) * asPolynomial xs := by
  induction xs with
  | nil => simp [asPolynomial]
  | cons x xs ih =>
    simp [asPolynomial, toComplex_scale, Polynomial.C_mul, ih]
    ring

theorem asPolynomial_map_mul (b : Gaussian) (xs : List Gaussian) :
    asPolynomial (xs.map (mul b)) = Polynomial.C (toComplex b) * asPolynomial xs := by
  induction xs with
  | nil => simp [asPolynomial]
  | cons x xs ih =>
    simp [asPolynomial, toComplex_mul, Polynomial.C_mul, ih]
    ring

theorem asPolynomial_zipWith_add (xs ys : List Gaussian) (hlen : xs.length = ys.length) :
    asPolynomial (List.zipWith add xs ys) = asPolynomial xs + asPolynomial ys := by
  induction xs generalizing ys with
  | nil =>
    have : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    simp [this, asPolynomial]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have ht : xs.length = ys.length := Nat.succ.inj hlen
      simp [asPolynomial, toComplex_add, Polynomial.C_add, ih ys ht]
      ring

/-- The fast list update really multiplies by the intended linear factor. -/
theorem asPolynomial_mulLinear (a : ℤ) (b : Gaussian) (xs : List Gaussian) :
    asPolynomial (mulLinear a b xs) =
      (Polynomial.C (a : ℂ) + Polynomial.C (toComplex b) * Polynomial.X) * asPolynomial xs := by
  unfold mulLinear
  rw [asPolynomial_zipWith_add _ _ (by simp)]
  rw [asPolynomial_append_zero, asPolynomial_map_scale,
    asPolynomial_zero_cons, asPolynomial_map_mul]
  ring

/-- The companion update has the weighted-product recurrence in polynomial form. -/
theorem asPolynomial_weighted_update (a d : ℤ) (b : Gaussian)
    (p g : List Gaussian) (hlen : p.length = g.length + 1) :
    asPolynomial (List.zipWith add (mulLinear a b g) (p.map (mul (scale d b)))) =
      (Polynomial.C (a : ℂ) + Polynomial.C (toComplex b) * Polynomial.X) * asPolynomial g +
        Polynomial.C ((d : ℂ) * toComplex b) * asPolynomial p := by
  rw [asPolynomial_zipWith_add _ _ (by simp [mulLinear, hlen])]
  rw [asPolynomial_mulLinear, asPolynomial_map_mul, toComplex_scale]

#print axioms asPolynomial_mulLinear
#print axioms asPolynomial_weighted_update

end
end Bapat.Certificate
