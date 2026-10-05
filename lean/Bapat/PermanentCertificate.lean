import Bapat.RankTwoPermanent
import Bapat.RankTwoReduction

/-!
# The permanent coefficient identity for the exact 144-row witness

The permanent norm identity is unconditional. The reduction in this module
takes a complementary-minor identity, proved in `Bapat.Counterexample`.
-/

open scoped BigOperators

namespace Bapat

noncomputable section

theorem gram_permanent_norm {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ) :
    (V * V.conjTranspose).permanent.re =
      Certificate.polynomialNorm n (factorPolynomial V) := by
  rw [gram_permanent_coefficients]
  simp_rw [mul_assoc, Complex.star_def, Complex.mul_conj]
  simp [Certificate.polynomialNorm]

theorem factorPolynomial_gramFactor :
    factorPolynomial gramFactor = Certificate.rowProduct Certificate.rows := by
  unfold factorPolynomial Certificate.rowProduct
  rw [← Fin.prod_univ_fun_getElem Certificate.rows Certificate.rowLinear]
  apply Fintype.prod_equiv (finCongr Certificate.rows_length.symm)
  intro i
  rw [List.getElem_eq_getD (0, 0, 0)]
  simp [gramFactor, Certificate.rowLinear, Certificate.rowA, Certificate.rowB,
    Certificate.toComplex]

theorem gramWitness_permanent : gramWitness.permanent.re = (Certificate.expectedP : ℝ) := by
  change (gramFactor * gramFactor.conjTranspose).permanent.re = _
  rw [gram_permanent_norm, factorPolynomial_gramFactor,
    ← Certificate.productPolynomial_zipIdx Certificate.rows 0,
    ← Certificate.expectedP_eq_polynomialNorm]

theorem gramWitness_permanent_exact : gramWitness.permanent = (Certificate.expectedP : ℂ) := by
  rw [← complexQPermanent_one,
    complexQPermanent_eq_real gramWitness gramWitness_posSemidef.1,
    qPermanent_one, gramWitness_permanent]
  norm_cast

/-- A scalar reduction used by the unconditional theorem in `Bapat.Counterexample`. -/
theorem not_bapatMonotonicity_of_minor_identity
    (hminor : (pairMinorSum gramWitness).re = (Certificate.expectedS : ℝ)) :
    ¬ BapatMonotonicity := by
  apply not_bapatMonotonicity_of_endpoint_identity
  have hid := endpointDerivative_pairMinorSum gramWitness
  rw [rowPairs_144_card, qPermanent_one, gramWitness_permanent, hminor] at hid
  exact hid

#print axioms gramWitness_permanent
#print axioms gramWitness_permanent_exact
#print axioms not_bapatMonotonicity_of_minor_identity

end
end Bapat
