import Bapat.Basic
import Bapat.Certificate

/-!
# The explicit Hermitian witness and an endpoint reduction

All arithmetic and positive-semidefiniteness facts below are proved.
The final theorem in this module is an endpoint reduction. The required identity
is proved unconditionally in `Bapat.Counterexample`.
-/

open scoped BigOperators ComplexOrder

namespace Bapat

noncomputable section

def gramFactor : Matrix (Fin 144) (Fin 2) ℂ := fun i j =>
  let row := Certificate.rows.getD i.val (0, 0, 0)
  if j = 0 then (row.1 : ℂ) else
    (row.2.1 : ℂ) + (row.2.2 : ℂ) * Complex.I

def gramWitness : Matrix (Fin 144) (Fin 144) ℂ :=
  gramFactor * gramFactor.conjTranspose

theorem gramWitness_posSemidef : gramWitness.PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose gramFactor

theorem gramWitness_zero_one : gramWitness 0 1 = 9795 - 1288 * Complex.I := by
  apply Complex.ext <;>
    norm_num [gramWitness, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, gramFactor, Certificate.rows, List.getD,
      Complex.mul_re, Complex.mul_im]

theorem gramWitness_off_diagonal :
    ∃ i j : Fin 144, i ≠ j ∧ gramWitness i j ≠ 0 := by
  refine ⟨0, 1, by decide, ?_⟩
  intro hzero
  have hreal := congrArg Complex.re hzero
  rw [gramWitness_zero_one] at hreal
  norm_num at hreal

def explicitPositiveWitness : Matrix (Fin 144) (Fin 144) ℂ :=
  (10 ^ 70 : ℝ) • gramWitness + 1

theorem explicitPositiveWitness_posDef : explicitPositiveWitness.PosDef := by
  apply Matrix.PosDef.posSemidef_add
  · exact gramWitness_posSemidef.smul (by norm_num)
  · exact Matrix.PosDef.one

/-- Once the rank-two identity is supplied, all remaining disproof steps are finished. -/
theorem not_bapatMonotonicity_of_endpoint_identity
    (hidentity : 2 * endpointDerivative gramWitness =
      10296 * (Certificate.expectedP : ℝ) - (Certificate.expectedS : ℝ)) :
    ¬ BapatMonotonicity := by
  have hnum : (10296 : ℝ) * (Certificate.expectedP : ℝ) -
      (Certificate.expectedS : ℝ) < 0 := by
    exact_mod_cast Certificate.endpoint_numerator_negative
  have hneg : endpointDerivative gramWitness < 0 := by linarith
  exact not_bapatMonotonicity_of_psd_endpoint_negative gramWitness
    gramWitness_posSemidef hneg gramWitness_off_diagonal

#print axioms gramWitness_posSemidef
#print axioms explicitPositiveWitness_posDef
#print axioms not_bapatMonotonicity_of_endpoint_identity

end
end Bapat
