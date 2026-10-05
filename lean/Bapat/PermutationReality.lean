import Bapat.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Complex.BigOperators

/-!
# Permutation inversion and the real-valued Hermitian q-permanent

The real-part definition used by the analytic reduction agrees with the usual
complex q-permanent on every Hermitian matrix, for every real q.
-/

open scoped BigOperators

namespace Bapat

noncomputable section

theorem inversions_symm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    inversions σ.symm = inversions σ := by
  classical
  have h : inversions σ = inversions σ.symm := by
    unfold inversions
    apply Finset.card_bij (fun p _ => (σ p.2, σ p.1))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨hp.2, by simpa using hp.1⟩
    · intro p _ r _ heq
      apply Prod.ext
      · exact σ.injective (congrArg Prod.snd heq)
      · exact σ.injective (congrArg Prod.fst heq)
    · intro r hr
      refine ⟨(σ.symm r.2, σ.symm r.1), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
        exact ⟨hr.2, by simpa using hr.1⟩
      · simp
  exact h.symm

def complexTerm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (σ : Equiv.Perm (Fin n)) : ℂ := ∏ i, A i (σ i)

theorem star_complexTerm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (σ : Equiv.Perm (Fin n)) :
    star (complexTerm A σ) = complexTerm A σ.symm := by
  classical
  simp only [complexTerm, star_prod]
  exact Fintype.prod_equiv σ _ _ (fun i => by simpa using hA.apply (σ i) i)

def complexQPermanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), (q ^ inversions σ : ℝ) * complexTerm A σ

theorem complexQPermanent_re {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) :
    (complexQPermanent A q).re = qPermanent A q := by
  simp only [complexQPermanent, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    qPermanent, complexTerm, termRe]

theorem star_complexQPermanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (q : ℝ) : star (complexQPermanent A q) = complexQPermanent A q := by
  classical
  unfold complexQPermanent
  simp only [star_sum, star_mul, star_complexTerm A hA,
    Complex.star_def, Complex.conj_ofReal]
  have hbij : Function.Bijective (fun σ : Equiv.Perm (Fin n) => σ.symm) :=
    (show Function.Involutive (fun σ : Equiv.Perm (Fin n) => σ.symm) from
      fun σ => σ.symm_symm).bijective
  simpa only [inversions_symm, mul_comm] using hbij.sum_comp
    (fun σ : Equiv.Perm (Fin n) => (q ^ inversions σ : ℝ) * complexTerm A σ)

theorem complexQPermanent_im {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (q : ℝ) : (complexQPermanent A q).im = 0 := by
  have h := congrArg Complex.im (star_complexQPermanent A hA q)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

/-- This establishes the exact correspondence with the statement in the manuscript. -/
theorem complexQPermanent_eq_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (q : ℝ) : complexQPermanent A q = (qPermanent A q : ℂ) := by
  apply Complex.ext
  · simpa using complexQPermanent_re A q
  · simpa using complexQPermanent_im A hA q

theorem complexQPermanent_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    complexQPermanent A 1 = A.permanent := by
  classical
  calc
    complexQPermanent A 1 = A.transpose.permanent := by
      simp [complexQPermanent, complexTerm, Matrix.permanent, Matrix.transpose_apply]
    _ = A.permanent := Matrix.permanent_transpose A

theorem qPermanent_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    qPermanent A 1 = A.permanent.re := by
  rw [← complexQPermanent_re, complexQPermanent_one]

#print axioms complexQPermanent_eq_real

end
end Bapat
