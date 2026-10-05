import Bapat.ColorCount
import Bapat.PermutationReality
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators

/-! # Two-coordinate polynomial coefficients and the Gram permanent -/

open scoped BigOperators

namespace Bapat

noncomputable section

def colorMonomial {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ) (f : Fin n → Fin 2) : ℂ :=
  ∏ i, V i (f i)

def colorCoefficient {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ) (k : ℕ) : ℂ :=
  ∑ f : Fin n → Fin 2, if colorCount f 1 = k then colorMonomial V f else 0

def factorPolynomial {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ) : Polynomial ℂ :=
  ∏ i, (Polynomial.C (V i 0) + Polynomial.C (V i 1) * Polynomial.X)

theorem colorCount_eq_sum {n : ℕ} (f : Fin n → Fin 2) :
    colorCount f 1 = ∑ i, if f i = 1 then 1 else 0 := by
  classical
  rw [colorCount, Fintype.card_subtype, Finset.card_filter]

theorem factorPolynomial_colorSum {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ) :
    factorPolynomial V = ∑ f : Fin n → Fin 2,
      Polynomial.C (colorMonomial V f) * Polynomial.X ^ colorCount f 1 := by
  classical
  have h := Fintype.prod_sum (fun i (c : Fin 2) =>
    Polynomial.C (V i c) * Polynomial.X ^ (if c = 1 then 1 else 0))
  have hprod : ∀ f : Fin n → Fin 2,
      (∏ i, Polynomial.C (V i (f i)) * Polynomial.X ^ (if f i = 1 then 1 else 0)) =
        Polynomial.C (colorMonomial V f) * Polynomial.X ^ colorCount f 1 := by
    intro f
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      ← colorCount_eq_sum, ← map_prod]
    rfl
  have hzero : (0 : Fin 2) ≠ 1 := by decide
  simp only [Fin.sum_univ_two, if_neg hzero, ite_true, pow_zero, pow_one, mul_one] at h
  simpa only [factorPolynomial, hprod] using h

theorem factorPolynomial_coeff {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ) (k : ℕ) :
    (factorPolynomial V).coeff k = colorCoefficient V k := by
  rw [factorPolynomial_colorSum]
  simp [Polynomial.finsetSum_coeff, colorCoefficient, eq_comm]

theorem sum_color_permutations {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ)
    (f : Fin n → Fin 2) :
    (∑ σ : Equiv.Perm (Fin n), colorMonomial V (f ∘ σ)) =
      ∑ g : Fin n → Fin 2,
        (if colorCount f 1 = colorCount g 1 then
          (colorCount f 1).factorial * (n - colorCount f 1).factorial else 0 : ℕ) *
            colorMonomial V g := by
  classical
  have h := Fintype.sum_fiberwise' (fun σ : Equiv.Perm (Fin n) => f ∘ σ)
    (colorMonomial V)
  simpa [colorMatching_card_ite, nsmul_eq_mul] using h.symm

theorem colorMonomial_permute {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ)
    (f : Fin n → Fin 2) (σ : Equiv.Perm (Fin n)) :
    (∏ i, V (σ i) (f i)) = colorMonomial V (f ∘ σ.symm) := by
  classical
  exact Fintype.prod_equiv σ _ _ (fun i => by simp)

theorem gram_permanent_colorSum {n : ℕ} (U W : Matrix (Fin n) (Fin 2) ℂ) :
    (U * W.conjTranspose).permanent =
      ∑ f : Fin n → Fin 2,
        (∑ g : Fin n → Fin 2,
          (if colorCount f 1 = colorCount g 1 then
            (colorCount f 1).factorial * (n - colorCount f 1).factorial else 0 : ℕ) *
              colorMonomial U g) * star (colorMonomial W f) := by
  classical
  unfold Matrix.permanent
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [Fintype.prod_sum, Finset.prod_mul_distrib, ← star_prod,
    colorMonomial_permute]
  change (∑ σ : Equiv.Perm (Fin n), ∑ f : Fin n → Fin 2,
    colorMonomial U (f ∘ σ.symm) * star (colorMonomial W f)) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  rw [← Finset.sum_mul]
  have hinv : (∑ σ : Equiv.Perm (Fin n), colorMonomial U (f ∘ σ.symm)) =
      ∑ σ : Equiv.Perm (Fin n), colorMonomial U (f ∘ σ) :=
    (show Function.Involutive (fun σ : Equiv.Perm (Fin n) => σ.symm) from
      fun σ => σ.symm_symm).bijective.sum_comp (fun σ => colorMonomial U (f ∘ σ))
  rw [hinv, sum_color_permutations]

theorem colorCount_le {n : ℕ} (f : Fin n → Fin 2) : colorCount f 1 ≤ n := by
  classical
  simpa [colorCount] using Fintype.card_subtype_le (fun i : Fin n => f i = 1)

def colorDegree {n : ℕ} (f : Fin n → Fin 2) : Fin (n + 1) :=
  ⟨colorCount f 1, Nat.lt_succ_of_le (colorCount_le f)⟩

theorem gram_permanent_coefficients {n : ℕ} (U W : Matrix (Fin n) (Fin 2) ℂ) :
    (U * W.conjTranspose).permanent = ∑ k : Fin (n + 1),
      ((k.val.factorial * (n - k.val).factorial : ℕ) : ℂ) *
        (factorPolynomial U).coeff k.val * star ((factorPolynomial W).coeff k.val) := by
  classical
  rw [gram_permanent_colorSum]
  have hinner : ∀ f : Fin n → Fin 2,
      (∑ g : Fin n → Fin 2,
        (if colorCount f 1 = colorCount g 1 then
          (colorCount f 1).factorial * (n - colorCount f 1).factorial else 0 : ℕ) *
            colorMonomial U g) =
      ((colorCount f 1).factorial * (n - colorCount f 1).factorial : ℕ) *
        colorCoefficient U (colorCount f 1) := by
    intro f
    simp [colorCoefficient, Finset.mul_sum, mul_ite, eq_comm]
  simp_rw [hinner]
  rw [← Finset.sum_fiberwise Finset.univ colorDegree]
  simp_rw [factorPolynomial_coeff]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_filter]
  simp only [colorCoefficient, star_sum, apply_ite, star_zero,
    Finset.mul_sum, Finset.sum_mul, ite_mul]
  apply Finset.sum_congr rfl
  intro f _
  have hiff : colorDegree f = k ↔ colorCount f 1 = k.val := Fin.ext_iff
  by_cases hf : colorCount f 1 = k.val <;> simp [hiff, hf]

#print axioms gram_permanent_coefficients

end
end Bapat
