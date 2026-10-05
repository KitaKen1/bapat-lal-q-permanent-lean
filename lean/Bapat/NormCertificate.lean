import Bapat.PolynomialCertificate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Indexes

/-!
# The integer values are the factorial-weighted polynomial coefficient norms

Only their connection to the permutation derivative remains outside this module.
-/

open scoped BigOperators

namespace Bapat.Certificate

noncomputable section

def polynomialNorm (degree : ℕ) (p : Polynomial ℂ) : ℝ :=
  ∑ k : Fin (degree + 1),
    ((Nat.factorial k.val * Nat.factorial (degree - k.val) : ℕ) : ℝ) *
      Complex.normSq (p.coeff k.val)

theorem coefficientNorm_eq_sum (degree : ℕ) (xs : List Gaussian) :
    (coefficientNorm degree xs : ℝ) =
      ∑ k : Fin xs.length,
        ((Nat.factorial k.val * Nat.factorial (degree - k.val) : ℕ) : ℝ) *
          Complex.normSq ((asPolynomial xs).coeff k.val) := by
  have hm : (xs.zipIdx.map fun ck =>
      ((factorial ck.2 * factorial (degree - ck.2) : ℕ) : ℤ) * normSq ck.1) =
      xs.mapIdx (fun k c => ((factorial k * factorial (degree - k) : ℕ) : ℤ) * normSq c) := by
    rw [List.mapIdx_eq_zipIdx_map]
  rw [coefficientNorm, hm, List.mapIdx_eq_ofFn, List.sum_ofFn]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rw [asPolynomial_coeff, toComplex_normSq, ← List.getElem_eq_getD (h := k.isLt) zero]
  simp [List.get_eq_getElem, factorial_eq]

theorem coefficientNorm_eq_polynomialNorm (degree : ℕ) (xs : List Gaussian)
    (hlen : xs.length = degree + 1) :
    (coefficientNorm degree xs : ℝ) = polynomialNorm degree (asPolynomial xs) := by
  have hsum := coefficientNorm_eq_sum degree xs
  rw [hlen] at hsum
  exact hsum

theorem expectedP_eq_polynomialNorm :
    (expectedP : ℝ) = polynomialNorm 144 (productPolynomial rows.zipIdx) := by
  rw [← exact_coefficients.1]
  change (coefficientNorm 144 coefficients.1 : ℝ) = _
  rw [coefficientNorm_eq_polynomialNorm 144 coefficients.1 coefficient_shape.1,
    certificate_polynomials.1]

theorem expectedS_eq_polynomialNorm :
    (expectedS : ℝ) = polynomialNorm 142 (weightedPolynomial 144 rows.zipIdx) := by
  rw [← exact_coefficients.2]
  change (coefficientNorm 142 (coefficients.2.take 143) : ℝ) = _
  rw [coefficientNorm_eq_polynomialNorm 142 (coefficients.2.take 143)
    (by simp [coefficient_shape.2.1]), certificate_weighted_truncation]

#print axioms expectedP_eq_polynomialNorm
#print axioms expectedS_eq_polynomialNorm

end
end Bapat.Certificate
