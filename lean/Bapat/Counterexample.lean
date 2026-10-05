import Bapat.PairPolynomial
import Bapat.PermanentCertificate

/-!
# A formal disproof of the original Bapat–Lal monotonicity conjecture

The 144-row integer certificate yields a negative endpoint derivative for a
positive-semidefinite Gram matrix. A sufficiently small positive diagonal
perturbation is positive definite and still has a negative endpoint derivative.
No unproved identity or explicit quantitative perturbation bound is assumed.
-/

open scoped ComplexOrder

namespace Bapat

noncomputable section

theorem gramWitness_minorSum :
    (pairMinorSum gramWitness).re = (Certificate.expectedS : ℝ) := by
  change (pairMinorSum (gramFactor * gramFactor.conjTranspose)).re = _
  rw [pairMinorGram_norm, pairPolynomial_gramFactor]
  exact Certificate.certificate_wedgeNorm

theorem gramWitness_endpoint_identity :
    2 * endpointDerivative gramWitness =
      10296 * (Certificate.expectedP : ℝ) - (Certificate.expectedS : ℝ) := by
  have hid := endpointDerivative_pairMinorSum gramWitness
  rw [rowPairs_144_card, qPermanent_one, gramWitness_permanent, gramWitness_minorSum] at hid
  exact hid

theorem gramWitness_endpoint_negative : endpointDerivative gramWitness < 0 := by
  have hnum : (10296 : ℝ) * (Certificate.expectedP : ℝ) -
      (Certificate.expectedS : ℝ) < 0 := by
    exact_mod_cast Certificate.endpoint_numerator_negative
  have hid := gramWitness_endpoint_identity
  linarith

/-- A positive definite counterexample exists at the original dimension 144. -/
theorem exists_positive_definite_counterexample :
    ∃ ε : ℝ, 0 < ε ∧ (gramWitness + ε • 1).PosDef ∧
      ¬ (gramWitness + ε • 1).IsDiag ∧
      ¬ StrictMonoOn (qPermanent (gramWitness + ε • 1)) (Set.Icc (-1) 1) := by
  obtain ⟨ε, hε, hneg⟩ :=
    exists_positive_perturbation_negative gramWitness gramWitness_endpoint_negative
  refine ⟨ε, hε, positive_perturbation_posDef gramWitness gramWitness_posSemidef hε, ?_,
    not_strictMonoOn_of_endpoint_negative _ hneg⟩
  obtain ⟨i, j, hij, hval⟩ := gramWitness_off_diagonal
  intro hdiag
  have hzero := hdiag hij
  exact hval (by
    simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hij] using hzero)

/-- The original universal assertion is false, with no additional hypotheses. -/
theorem not_bapatMonotonicity : ¬ BapatMonotonicity :=
  not_bapatMonotonicity_of_minor_identity gramWitness_minorSum

/-- Values strictly decrease between two points of the original interval. -/
theorem exists_decreasing_pair :
    ∃ ε : ℝ, 0 < ε ∧ (gramWitness + ε • 1).PosDef ∧
      ¬ (gramWitness + ε • 1).IsDiag ∧
      ∃ q₁ ∈ Set.Icc (-1 : ℝ) 1, ∃ q₂ ∈ Set.Icc (-1 : ℝ) 1,
        q₁ < q₂ ∧ qPermanent (gramWitness + ε • 1) q₂ <
          qPermanent (gramWitness + ε • 1) q₁ := by
  classical
  obtain ⟨ε, hε, hneg⟩ :=
    exists_positive_perturbation_negative gramWitness gramWitness_endpoint_negative
  have hmono := not_monotoneOn_Icc_of_hasDerivAt_neg (by norm_num : (-1 : ℝ) < 1)
    (hasDerivAt_qPermanent_one (gramWitness + ε • 1)) hneg
  simp only [MonotoneOn, not_forall, not_le] at hmono
  obtain ⟨q₁, hq₁, q₂, hq₂, hle, hrev⟩ := hmono
  have hlt : q₁ < q₂ := by
    apply lt_of_le_of_ne hle
    intro heq
    subst q₂
    exact (lt_irrefl _) hrev
  refine ⟨ε, hε, positive_perturbation_posDef gramWitness gramWitness_posSemidef hε,
    ?_, q₁, hq₁, q₂, hq₂, hlt, hrev⟩
  obtain ⟨i, j, hij, hval⟩ := gramWitness_off_diagonal
  intro hdiag
  have hzero := hdiag hij
  exact hval (by
    simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hij] using hzero)

#print axioms gramWitness_minorSum
#print axioms gramWitness_endpoint_negative
#print axioms exists_positive_definite_counterexample
#print axioms not_bapatMonotonicity
#print axioms exists_decreasing_pair

end
end Bapat
