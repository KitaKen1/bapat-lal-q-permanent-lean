import Bapat.RankTwoPermanent
import Bapat.RankTwoReduction
import Mathlib.Data.Fintype.EquivFin

/-! # Complementary bijections, without enumeration of full permutations -/

open scoped BigOperators

namespace Bapat

noncomputable section

abbrev PairComplement {n : ℕ} (i j : Fin n) := {x : Fin n // x ≠ i ∧ x ≠ j}

def restrictPair {n : ℕ} {i j k l : Fin n} (σ : Equiv.Perm (Fin n))
    (hi : σ i = k) (hj : σ j = l) : PairComplement i j ≃ PairComplement k l where
  toFun x := ⟨σ x, by
    constructor
    · intro h; exact x.property.1 (σ.injective (h.trans hi.symm))
    · intro h; exact x.property.2 (σ.injective (h.trans hj.symm))⟩
  invFun y := ⟨σ.symm y, by
    constructor
    · intro h; exact y.property.1 (by simpa [h, hi] using (σ.apply_symm_apply y).symm)
    · intro h; exact y.property.2 (by simpa [h, hj] using (σ.apply_symm_apply y).symm)⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

def extendPair {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (e : PairComplement i j ≃ PairComplement k l) : Equiv.Perm (Fin n) where
  toFun x := if hi : x = i then k else if hj : x = j then l else e ⟨x, hi, hj⟩
  invFun y := if hk : y = k then i else if hl : y = l then j else e.symm ⟨y, hk, hl⟩
  left_inv x := by
    by_cases hi : x = i
    · subst x; simp
    by_cases hj : x = j
    · subst x; simp [hij.symm, hkl.symm]
    · simp only [dif_neg hi, dif_neg hj]
      have h := (e ⟨x, hi, hj⟩).property
      simp only [dif_neg h.1, dif_neg h.2]
      change (e.symm (e ⟨x, hi, hj⟩)).val = x
      simp
  right_inv y := by
    by_cases hk : y = k
    · subst y; simp
    by_cases hl : y = l
    · subst y; simp [hij.symm, hkl.symm]
    · simp only [dif_neg hk, dif_neg hl]
      have h := (e.symm ⟨y, hk, hl⟩).property
      simp only [dif_neg h.1, dif_neg h.2]
      change (e (e.symm ⟨y, hk, hl⟩)).val = y
      simp

theorem extendPair_left {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (e : PairComplement i j ≃ PairComplement k l) : extendPair hij hkl e i = k := by
  simp [extendPair]

theorem extendPair_right {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (e : PairComplement i j ≃ PairComplement k l) : extendPair hij hkl e j = l := by
  simp [extendPair, hij.symm]

theorem extendPair_complement {n : ℕ} {i j k l : Fin n}
    (hij : i ≠ j) (hkl : k ≠ l) (e : PairComplement i j ≃ PairComplement k l)
    (x : PairComplement i j) : extendPair hij hkl e x = e x := by
  simp [extendPair, x.property.1, x.property.2]

def pairMatchingEquiv {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) :
    {σ : Equiv.Perm (Fin n) // σ i = k ∧ σ j = l} ≃
      (PairComplement i j ≃ PairComplement k l) where
  toFun σ := restrictPair σ.val σ.property.1 σ.property.2
  invFun e := ⟨extendPair hij hkl e, extendPair_left hij hkl e, extendPair_right hij hkl e⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hi : x = i
    · subst x; simp [extendPair_left, σ.property.1]
    by_cases hj : x = j
    · subst x; simp [extendPair_right, σ.property.2]
    · change extendPair hij hkl (restrictPair σ.val σ.property.1 σ.property.2) x = σ.val x
      simp [extendPair, hi, hj, restrictPair]
  right_inv e := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact extendPair_complement hij hkl e x

theorem pairComplement_card {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Fintype.card (PairComplement i j) = n - 2 := by
  classical
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter fun x : Fin n => x ≠ i ∧ x ≠ j) =
      (Finset.univ.erase i).erase j := by ext; simp [and_comm]
  rw [hset, Finset.card_erase_of_mem (by simp [hij.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

def pairComplementFin {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    PairComplement i j ≃ Fin (n - 2) :=
  Fintype.equivFinOfCardEq (pairComplement_card i j hij)

def pairMatchingFinEquiv {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) :
    {σ : Equiv.Perm (Fin n) // σ i = k ∧ σ j = l} ≃ Equiv.Perm (Fin (n - 2)) :=
  (pairMatchingEquiv hij hkl).trans
    (Equiv.equivCongr (pairComplementFin i j hij) (pairComplementFin k l hkl))

theorem remainingProduct_subtype {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    remainingProduct A σ i j = ∏ x : PairComplement i j, A x (σ x) := by
  classical
  unfold remainingProduct
  exact Finset.prod_subtype _ (by intro x; simp [and_comm]) _

def complementMatrix {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ)
    (i j : Fin n) (hij : i ≠ j) : Matrix (Fin (n - 2)) (Fin 2) ℂ :=
  fun a c => V ((pairComplementFin i j hij).symm a) c

def complementPolynomial {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ)
    (i j : Fin n) : Polynomial ℂ :=
  ∏ x ∈ (Finset.univ.erase i).erase j,
    (Polynomial.C (V x 0) + Polynomial.C (V x 1) * Polynomial.X)

theorem factorPolynomial_complementMatrix {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ)
    (i j : Fin n) (hij : i ≠ j) :
    factorPolynomial (complementMatrix V i j hij) = complementPolynomial V i j := by
  classical
  unfold factorPolynomial complementPolynomial complementMatrix
  rw [Finset.prod_subtype (p := fun x : Fin n => x ≠ i ∧ x ≠ j)
    ((Finset.univ.erase i).erase j) (by intro x; simp [and_comm])]
  exact Fintype.prod_equiv (pairComplementFin i j hij).symm _ _ (by intro x; rfl)

theorem remainingGram_matching_sum {n : ℕ} (U W : Matrix (Fin n) (Fin 2) ℂ)
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l) :
    (∑ σ : Equiv.Perm (Fin n), if σ i = k ∧ σ j = l then
      remainingProduct (U * W.conjTranspose) σ i j else 0) =
    (complementMatrix U i j hij * (complementMatrix W k l hkl).conjTranspose).permanent := by
  classical
  rw [← Finset.sum_filter,
    Finset.sum_subtype (p := fun σ : Equiv.Perm (Fin n) => σ i = k ∧ σ j = l)
      _ (by intro σ; simp)]
  rw [← Matrix.permanent_transpose]
  unfold Matrix.permanent
  apply Fintype.sum_equiv (pairMatchingFinEquiv hij hkl)
  intro σ
  rw [remainingProduct_subtype]
  apply Fintype.prod_equiv (pairComplementFin i j hij)
  intro x
  simp [Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    complementMatrix, pairMatchingFinEquiv, pairMatchingEquiv,
    pairComplementFin, Equiv.equivCongr, restrictPair]

theorem remainingGram_matching_coefficients {n : ℕ}
    (U W : Matrix (Fin n) (Fin 2) ℂ) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) :
    (∑ σ : Equiv.Perm (Fin n), if σ i = k ∧ σ j = l then
      remainingProduct (U * W.conjTranspose) σ i j else 0) =
      ∑ d : Fin (n - 2 + 1), ((d.val.factorial * (n - 2 - d.val).factorial : ℕ) : ℂ) *
        (complementPolynomial U i j).coeff d.val *
          star ((complementPolynomial W k l).coeff d.val) := by
  rw [remainingGram_matching_sum U W i j k l hij hkl, gram_permanent_coefficients,
    factorPolynomial_complementMatrix, factorPolynomial_complementMatrix]

#print axioms pairMatchingFinEquiv
#print axioms remainingGram_matching_coefficients

theorem imagePair_sum {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (∑ q ∈ rowPairs n, if σ i = q.1 ∧ σ j = q.2 then
      star (rowWedge V q.1 q.2) * remainingProduct (V * V.conjTranspose) σ i j else 0) =
      if σ i < σ j then
        star (rowWedge V (σ i) (σ j)) * remainingProduct (V * V.conjTranspose) σ i j
      else 0 := by
  classical
  by_cases h : σ i < σ j
  · rw [if_pos h]
    refine (Finset.sum_eq_single (σ i, σ j) ?_ ?_).trans ?_
    · intro q _ hq
      have hm : ¬ (σ i = q.1 ∧ σ j = q.2) := by
        intro hm; exact hq (Prod.ext hm.1.symm hm.2.symm)
      simp [hm]
    · intro hm; exact (hm (by simp [rowPairs, h])).elim
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro q hq
    have hm : ¬ (σ i = q.1 ∧ σ j = q.2) := by
      intro hm
      exact h (by simpa [hm.1, hm.2] using (Finset.mem_filter.mp hq).2)
    simp [hm]

theorem pairMinorGram_pairs {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ) :
    pairMinorSum (V * V.conjTranspose) =
      ∑ p ∈ rowPairs n, rowWedge V p.1 p.2 *
        ∑ q ∈ rowPairs n, star (rowWedge V q.1 q.2) *
          ∑ σ : Equiv.Perm (Fin n), if σ p.1 = q.1 ∧ σ p.2 = q.2 then
            remainingProduct (V * V.conjTranspose) σ p.1 p.2 else 0 := by
  classical
  unfold pairMinorSum
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [rankTwo_pairMinorContribution]
  have hfactor : ∀ σ : Equiv.Perm (Fin n),
      (if σ p.1 < σ p.2 then rowWedge V p.1 p.2 *
        star (rowWedge V (σ p.1) (σ p.2)) *
          remainingProduct (V * V.conjTranspose) σ p.1 p.2 else 0) =
      rowWedge V p.1 p.2 * (if σ p.1 < σ p.2 then
        star (rowWedge V (σ p.1) (σ p.2)) *
          remainingProduct (V * V.conjTranspose) σ p.1 p.2 else 0) := by
    intro σ; split_ifs <;> ring
  simp_rw [hfactor]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [← imagePair_sum V]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

def pairPolynomial {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ) : Polynomial ℂ :=
  ∑ p ∈ rowPairs n, Polynomial.C (rowWedge V p.1 p.2) * complementPolynomial V p.1 p.2

theorem pairPolynomial_coeff {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ) (d : ℕ) :
    (pairPolynomial V).coeff d = ∑ p ∈ rowPairs n,
      rowWedge V p.1 p.2 * (complementPolynomial V p.1 p.2).coeff d := by
  classical
  simp [pairPolynomial, Polynomial.finsetSum_coeff]

theorem pairMinorGram_coefficients {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ) :
    pairMinorSum (V * V.conjTranspose) =
      ∑ d : Fin (n - 2 + 1), ((d.val.factorial * (n - 2 - d.val).factorial : ℕ) : ℂ) *
        (pairPolynomial V).coeff d.val * star ((pairPolynomial V).coeff d.val) := by
  classical
  have hexpand : pairMinorSum (V * V.conjTranspose) =
      ∑ p ∈ rowPairs n, ∑ q ∈ rowPairs n, ∑ d : Fin (n - 2 + 1),
        ((d.val.factorial * (n - 2 - d.val).factorial : ℕ) : ℂ) *
          (rowWedge V p.1 p.2 * (complementPolynomial V p.1 p.2).coeff d.val) *
            star (rowWedge V q.1 q.2 * (complementPolynomial V q.1 q.2).coeff d.val) := by
    rw [pairMinorGram_pairs]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [remainingGram_matching_coefficients V V p.1 p.2 q.1 q.2
      (Finset.mem_filter.mp hp).2.ne (Finset.mem_filter.mp hq).2.ne]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [star_mul]
    ring
  rw [hexpand]
  conv_lhs => arg 2; ext p; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [pairPolynomial_coeff, star_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  exact Finset.sum_comm

theorem pairMinorGram_norm {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ) :
    (pairMinorSum (V * V.conjTranspose)).re =
      Certificate.polynomialNorm (n - 2) (pairPolynomial V) := by
  rw [pairMinorGram_coefficients]
  simp_rw [mul_assoc, Complex.star_def, Complex.mul_conj]
  simp [Certificate.polynomialNorm]

#print axioms pairMinorGram_norm

end
end Bapat
