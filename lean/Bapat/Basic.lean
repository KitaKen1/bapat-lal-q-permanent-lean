import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The ordered q-permanent and a shortcut at the endpoint

The real-valued definition is the real part of the usual complex q-permanent.
For Hermitian matrices the usual polynomial is real-valued. Taking the real part
avoids imposing an order on arbitrary complex polynomial values.

References: Bapat–Lal (1994), doi:10.1016/0024-3795(94)90497-9;
da Fonseca (2018), arXiv:1804.02231, Conjecture 1.
-/

open scoped BigOperators ComplexOrder

namespace Bapat

noncomputable section

/-- Number of inversions, with the order on `Fin n` fixed. -/
def inversions {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun ij : Fin n × Fin n => ij.1 < ij.2 ∧ σ ij.2 < σ ij.1).card

/-- Real part of the permutation monomial. -/
def termRe {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  (∏ i, A i (σ i)).re

/-- Real part of the ordered q-permanent. -/
def qPermanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), q ^ inversions σ * termRe A σ

/-- Explicit finite sum for the derivative at `q = 1`. -/
def endpointDerivative {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), (inversions σ : ℝ) * termRe A σ

/-- The original universal monotonicity assertion. -/
def BapatMonotonicity : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
    A.PosDef → ¬ A.IsDiag → StrictMonoOn (qPermanent A) (Set.Icc (-1) 1)

theorem hasDerivAt_qPermanent_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (qPermanent A) (endpointDerivative A) 1 := by
  classical
  apply HasDerivAt.fun_sum
  intro σ _
  simpa using ((hasDerivAt_id (1 : ℝ)).pow (inversions σ)).mul_const (termRe A σ)

/-- A negative derivative even at the right endpoint rules out monotonicity. -/
theorem not_monotoneOn_Icc_of_hasDerivAt_neg {f : ℝ → ℝ} {d a b : ℝ}
    (hab : a < b) (hd : HasDerivAt f d b) (hneg : d < 0) :
    ¬ MonotoneOn f (Set.Icc a b) := by
  intro hmono
  have huniq : UniqueDiffWithinAt ℝ (Set.Icc a b) b :=
    (uniqueDiffOn_Icc hab) b ⟨hab.le, le_rfl⟩
  have heq := hd.hasDerivWithinAt.derivWithin huniq
  have hnonneg := hmono.derivWithin_nonneg (x := b)
  rw [heq] at hnonneg
  exact (not_lt_of_ge hnonneg) hneg

theorem not_strictMonoOn_of_endpoint_negative {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hneg : endpointDerivative A < 0) :
    ¬ StrictMonoOn (qPermanent A) (Set.Icc (-1) 1) := by
  intro hmono
  exact not_monotoneOn_Icc_of_hasDerivAt_neg (by norm_num)
    (hasDerivAt_qPermanent_one A) hneg hmono.monotoneOn

theorem endpointDerivative_perturb_continuous {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun ε : ℝ => endpointDerivative (H + ε • 1)) := by
  unfold endpointDerivative termRe
  fun_prop

/-- No explicit perturbation size or second derivative bound is needed. -/
theorem exists_positive_perturbation_negative {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hneg : endpointDerivative H < 0) :
    ∃ ε : ℝ, 0 < ε ∧ endpointDerivative (H + ε • 1) < 0 := by
  have hcont := (endpointDerivative_perturb_continuous H).continuousAt (x := 0)
  have hnear : ∀ᶠ ε : ℝ in nhds 0, endpointDerivative (H + ε • 1) < 0 :=
    hcont.eventually_lt continuousAt_const (by simpa using hneg)
  exact hnear.exists_gt

theorem positive_perturbation_posDef {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) : (H + ε • 1).PosDef :=
  Matrix.PosDef.posSemidef_add hH
    ((Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℂ).PosDef).smul hε)

/-- The analytic part of the disproof reduces to one endpoint inequality. -/
theorem not_bapatMonotonicity_of_psd_endpoint_negative {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef)
    (hneg : endpointDerivative H < 0)
    (hoff : ∃ i j : Fin n, i ≠ j ∧ H i j ≠ 0) : ¬ BapatMonotonicity := by
  obtain ⟨ε, hε, hnegε⟩ := exists_positive_perturbation_negative H hneg
  have hpd := positive_perturbation_posDef H hH hε
  have hnd : ¬ (H + ε • 1).IsDiag := by
    obtain ⟨i, j, hij, hval⟩ := hoff
    intro hdiag
    have hzero := hdiag hij
    exact hval (by simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hij] using hzero)
  intro hconj
  exact not_strictMonoOn_of_endpoint_negative (H + ε • 1) hnegε
    (hconj n _ hpd hnd)

#print axioms not_bapatMonotonicity_of_psd_endpoint_negative

end
end Bapat
