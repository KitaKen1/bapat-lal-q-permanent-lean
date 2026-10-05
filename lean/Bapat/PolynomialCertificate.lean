import Bapat.CoefficientAlgebra
import Bapat.Shape

/-!
# The complete coefficient recurrence represents the intended polynomials

This connects the integer computation to a product polynomial and its weighted
product-rule companion, for arbitrary lists of indexed rows. It does not assert
the remaining permanent / endpoint derivative identity.
-/

namespace Bapat.Certificate

noncomputable section

abbrev IndexedRow := (ℤ × ℤ × ℤ) × ℕ

def linearFactor (r : IndexedRow) : Polynomial ℂ :=
  Polynomial.C (r.1.1 : ℂ) +
    Polynomial.C (toComplex (r.1.2.1, r.1.2.2)) * Polynomial.X

def markedFactor (n : ℕ) (r : IndexedRow) : Polynomial ℂ :=
  Polynomial.C (((n : ℤ) - 1 - 2 * (r.2 : ℤ) : ℤ) : ℂ) *
    Polynomial.C (toComplex (r.1.2.1, r.1.2.2))

def productPolynomial (rs : List IndexedRow) : Polynomial ℂ :=
  (rs.map linearFactor).prod

def weightedPolynomial (n : ℕ) : List IndexedRow → Polynomial ℂ
  | [] => 0
  | r :: rs => linearFactor r * weightedPolynomial n rs +
      markedFactor n r * productPolynomial rs

theorem mulLinear_length (a : ℤ) (b : Gaussian) (xs : List Gaussian) :
    (mulLinear a b xs).length = xs.length + 1 := by
  simp [mulLinear]

theorem coefficientStep_length (n : ℕ) (st : List Gaussian × List Gaussian)
    (r : IndexedRow) (hlen : st.1.length = st.2.length + 1) :
    (coefficientStep n st r).1.length = (coefficientStep n st r).2.length + 1 := by
  simp [coefficientStep, mulLinear_length, hlen]

theorem coefficientStep_polynomials (n : ℕ) (st : List Gaussian × List Gaussian)
    (r : IndexedRow) (hlen : st.1.length = st.2.length + 1) :
    asPolynomial (coefficientStep n st r).1 = linearFactor r * asPolynomial st.1 ∧
    asPolynomial (coefficientStep n st r).2 =
      linearFactor r * asPolynomial st.2 + markedFactor n r * asPolynomial st.1 := by
  constructor
  · exact asPolynomial_mulLinear _ _ _
  · simpa [coefficientStep, linearFactor, markedFactor, Polynomial.C_mul] using
      asPolynomial_weighted_update r.1.1 ((n : ℤ) - 1 - 2 * (r.2 : ℤ))
        (r.1.2.1, r.1.2.2) st.1 st.2 hlen

/-- A full fold has the ordinary product and weighted product-rule semantics. -/
theorem foldl_polynomials (n : ℕ) (rs : List IndexedRow)
    (st : List Gaussian × List Gaussian) (hlen : st.1.length = st.2.length + 1) :
    asPolynomial (rs.foldl (coefficientStep n) st).1 =
      productPolynomial rs * asPolynomial st.1 ∧
    asPolynomial (rs.foldl (coefficientStep n) st).2 =
      productPolynomial rs * asPolynomial st.2 +
        weightedPolynomial n rs * asPolynomial st.1 := by
  induction rs generalizing st with
  | nil => simp [productPolynomial, weightedPolynomial]
  | cons r rs ih =>
    obtain ⟨hp, hg⟩ := ih (coefficientStep n st r) (coefficientStep_length n st r hlen)
    obtain ⟨hsp, hsg⟩ := coefficientStep_polynomials n st r hlen
    constructor
    · simp only [List.foldl_cons]
      rw [hp, hsp]
      simp only [productPolynomial, List.map_cons, List.prod_cons]
      ring
    · simp only [List.foldl_cons]
      rw [hg, hsp, hsg]
      simp only [productPolynomial, List.map_cons, List.prod_cons, weightedPolynomial]
      ring

/-- The particular kernel-checked lists are the intended degree-144 polynomials. -/
theorem certificate_polynomials :
    asPolynomial coefficients.1 = productPolynomial rows.zipIdx ∧
    asPolynomial coefficients.2 = weightedPolynomial 144 rows.zipIdx := by
  simpa [coefficients, asPolynomial, toComplex] using
    foldl_polynomials 144 rows.zipIdx ([(1, 0)], []) (by decide)

/-- Gaussian integer norm-squares agree with their complex interpretation. -/
theorem toComplex_normSq (z : Gaussian) : Complex.normSq (toComplex z) = (normSq z : ℝ) := by
  simp [Complex.normSq_apply, toComplex, normSq]

theorem factorial_eq (k : ℕ) : factorial k = Nat.factorial k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [factorial, Nat.factorial_succ, ih]

/-- The discarded degree-143 coefficient is exactly zero, not an approximation. -/
theorem certificate_weighted_truncation :
    asPolynomial (coefficients.2.take 143) = weightedPolynomial 144 rows.zipIdx := by
  have hdrop := coefficient_shape.2.2
  have happ : coefficients.2.take 143 ++ [zero] = coefficients.2 := by
    rw [← hdrop]
    exact List.take_append_drop 143 coefficients.2
  calc
    asPolynomial (coefficients.2.take 143) =
        asPolynomial (coefficients.2.take 143 ++ [zero]) :=
      (asPolynomial_append_zero _).symm
    _ = asPolynomial coefficients.2 := congrArg asPolynomial happ
    _ = weightedPolynomial 144 rows.zipIdx := certificate_polynomials.2

#print axioms certificate_polynomials

end
end Bapat.Certificate
