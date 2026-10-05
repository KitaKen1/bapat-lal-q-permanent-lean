import Bapat.PermutationReality
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring

/-!
# The endpoint identity using paired permutations

We index the complementary bijections by full permutations with ascending images
of the two selected rows. This avoids constructing submatrix index equivalences.
Each ordered row pair contributes a 2-by-2 determinant times the complementary
product. Swapping its two rows pairs ascents with descents.
-/

open scoped BigOperators

namespace Bapat

noncomputable section

def rowPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 < p.2

theorem inversions_eq_filterCard {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (rowPairs n |>.filter fun p => σ p.2 < σ p.1).card = inversions σ := by
  classical
  simp [rowPairs, inversions, Finset.filter_filter]

def remainingProduct {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) : ℂ :=
  ∏ k ∈ (Finset.univ.erase i).erase j, A k (σ k)

theorem complexTerm_split {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    complexTerm A σ = A i (σ i) * A j (σ j) * remainingProduct A σ i j := by
  classical
  have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i := by simp [hij.symm]
  unfold complexTerm remainingProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ hj]
  ring

theorem remainingProduct_swap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    remainingProduct A (σ * Equiv.swap i j) i j = remainingProduct A σ i j := by
  classical
  apply Finset.prod_congr rfl
  intro k hk
  have hkj := Finset.ne_of_mem_erase hk
  have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]

def pairMinorContribution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) (σ : Equiv.Perm (Fin n)) : ℂ :=
  if σ i < σ j then
    (A i (σ i) * A j (σ j) - A i (σ j) * A j (σ i)) *
      remainingProduct A σ i j
  else 0

theorem pairMinorContribution_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) (hij : i ≠ j) (σ : Equiv.Perm (Fin n)) :
    pairMinorContribution A i j σ =
      (if σ i < σ j then complexTerm A σ else 0) -
        (if σ i < σ j then complexTerm A (σ * Equiv.swap i j) else 0) := by
  classical
  by_cases h : σ i < σ j
  · simp only [pairMinorContribution, if_pos h]
    rw [complexTerm_split A σ i j hij,
      complexTerm_split A (σ * Equiv.swap i j) i j hij, remainingProduct_swap]
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring
  · simp [pairMinorContribution, h]

theorem ascent_swapped_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    (∑ σ : Equiv.Perm (Fin n),
      if σ i < σ j then complexTerm A (σ * Equiv.swap i j) else 0) =
      ∑ σ : Equiv.Perm (Fin n), if σ j < σ i then complexTerm A σ else 0 := by
  classical
  simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right] using
    (Group.mulRight_bijective (Equiv.swap i j)).sum_comp
      (fun σ : Equiv.Perm (Fin n) => if σ j < σ i then complexTerm A σ else 0)

theorem pairMinor_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) (hij : i ≠ j) :
    (∑ σ : Equiv.Perm (Fin n), pairMinorContribution A i j σ) =
      ∑ σ : Equiv.Perm (Fin n),
        (complexTerm A σ - 2 * (if σ j < σ i then complexTerm A σ else 0)) := by
  classical
  simp_rw [pairMinorContribution_eq A i j hij]
  rw [Finset.sum_sub_distrib, ascent_swapped_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  have hne : σ i ≠ σ j := fun h => hij (σ.injective h)
  rcases lt_or_gt_of_ne hne with h | h
  · simp [h, not_lt_of_ge h.le]
  · simp [h, not_lt_of_ge h.le]
    ring

/-- The minors are represented by ascending images and complementary bijections. -/
def pairMinorSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ p ∈ rowPairs n, ∑ σ : Equiv.Perm (Fin n), pairMinorContribution A p.1 p.2 σ

def complexEndpointDerivative {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), (inversions σ : ℂ) * complexTerm A σ

theorem descent_pair_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (σ : Equiv.Perm (Fin n)) :
    (∑ p ∈ rowPairs n, if σ p.2 < σ p.1 then complexTerm A σ else 0) =
      (inversions σ : ℂ) * complexTerm A σ := by
  classical
  rw [← Finset.sum_filter]
  simp [inversions_eq_filterCard, nsmul_eq_mul]

theorem pairMinorSum_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    pairMinorSum A = (rowPairs n).card * complexQPermanent A 1 -
      2 * complexEndpointDerivative A := by
  classical
  unfold pairMinorSum
  have hpair : ∀ p ∈ rowPairs n,
      (∑ σ : Equiv.Perm (Fin n), pairMinorContribution A p.1 p.2 σ) =
        ∑ σ : Equiv.Perm (Fin n),
          (complexTerm A σ - 2 * (if σ p.2 < σ p.1 then complexTerm A σ else 0)) := by
    intro p hp
    exact pairMinor_sum A p.1 p.2 (Finset.mem_filter.mp hp).2.ne
  simp_rw [Finset.sum_congr rfl hpair]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum, descent_pair_sum]
  simp [complexQPermanent, complexEndpointDerivative, Finset.mul_sum, nsmul_eq_mul]

/-- The general matrix derivative identity, before the rank-two norm calculation. -/
theorem endpointDerivative_pairMinorSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    2 * endpointDerivative A = (rowPairs n).card * qPermanent A 1 - (pairMinorSum A).re := by
  have h : 2 * complexEndpointDerivative A =
      (rowPairs n).card * complexQPermanent A 1 - pairMinorSum A := by
    rw [pairMinorSum_eq]
    ring
  have hre := congrArg Complex.re h
  simpa [complexEndpointDerivative, endpointDerivative, complexTerm, termRe,
    complexQPermanent_re] using hre

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rowPairs_144_card : (rowPairs 144).card = 10296 := by decide +kernel

#print axioms endpointDerivative_pairMinorSum
#print axioms rowPairs_144_card

end
end Bapat
