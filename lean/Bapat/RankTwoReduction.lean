import Bapat.PairMinorIdentity
import Bapat.WedgePolynomial
import Bapat.Witness

/-!
# Rank-two minors and a coefficient-norm reduction

The general endpoint identity, Hermitian reality, scalar arithmetic, positivity
and the analytic perturbation reduction are proved. The final theorem below
takes two coefficient-norm identities as explicit hypotheses. Both identities
are proved and supplied by the final integration in `Bapat.Counterexample`.
-/

open scoped BigOperators

namespace Bapat

noncomputable section

def rowWedge {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ) (i j : Fin n) : ℂ :=
  V i 0 * V j 1 - V j 0 * V i 1

/-- The two-column Cauchy–Binet calculation needs only commutative ring algebra. -/
theorem rankTwoGram_minor {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ)
    (i j k l : Fin n) :
    (V * V.conjTranspose) i k * (V * V.conjTranspose) j l -
      (V * V.conjTranspose) i l * (V * V.conjTranspose) j k =
        rowWedge V i j * star (rowWedge V k l) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    rowWedge, star_sub, star_mul]
  ring

theorem rankTwo_pairMinorContribution {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ)
    (i j : Fin n) (σ : Equiv.Perm (Fin n)) :
    pairMinorContribution (V * V.conjTranspose) i j σ =
      if σ i < σ j then
        rowWedge V i j * star (rowWedge V (σ i) (σ j)) *
          remainingProduct (V * V.conjTranspose) σ i j
      else 0 := by
  unfold pairMinorContribution
  rw [rankTwoGram_minor]

/-- All remaining disproof work is isolated in two rank-two norm identities. -/
theorem not_bapatMonotonicity_of_rankTwo_norms
    (hper : gramWitness.permanent.re =
      Certificate.polynomialNorm 144 (Certificate.rowProduct Certificate.rows))
    (hminor : (pairMinorSum gramWitness).re =
      Certificate.polynomialNorm 142 (Certificate.wedgePolynomial Certificate.rows)) :
    ¬ BapatMonotonicity := by
  apply not_bapatMonotonicity_of_endpoint_identity
  have hid := endpointDerivative_pairMinorSum gramWitness
  rw [rowPairs_144_card, qPermanent_one, hper, hminor,
    Certificate.certificate_wedgeNorm,
    ← Certificate.productPolynomial_zipIdx Certificate.rows 0,
    ← Certificate.expectedP_eq_polynomialNorm] at hid
  exact hid

#print axioms rankTwoGram_minor
#print axioms not_bapatMonotonicity_of_rankTwo_norms

end
end Bapat
