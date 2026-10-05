import Bapat.ComplementPermanent
import Mathlib.Order.Interval.Finset.Fin

/-! # Ordered row pairs reduce to the weighted product rule -/

open scoped BigOperators

namespace Bapat

noncomputable section

set_option maxRecDepth 10000

def deletedFactorPolynomial {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ)
    (i : Fin n) : Polynomial ℂ :=
  ∏ x ∈ Finset.univ.erase i,
    (Polynomial.C (V x 0) + Polynomial.C (V x 1) * Polynomial.X)

theorem deletedFactorPolynomial_ite {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ)
    (i : Fin n) : deletedFactorPolynomial V i =
      ∏ x, if x = i then 1 else
        (Polynomial.C (V x 0) + Polynomial.C (V x 1) * Polynomial.X) := by
  classical
  unfold deletedFactorPolynomial
  simp only [Finset.prod_ite, Finset.prod_const_one, one_mul]
  have hs : (Finset.univ.filter fun x : Fin n => ¬x = i) = Finset.univ.erase i := by
    ext x; simp
  rw [hs]

theorem pairPolynomial_term {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ)
    (i j : Fin n) (hij : i ≠ j) :
    Polynomial.C (rowWedge V i j) * complementPolynomial V i j =
      Polynomial.C (V j 1) * deletedFactorPolynomial V j -
        Polynomial.C (V i 1) * deletedFactorPolynomial V i := by
  classical
  unfold deletedFactorPolynomial
  rw [← Finset.mul_prod_erase _ _ (show i ∈ (Finset.univ : Finset (Fin n)).erase j by
    simp [hij]),
    ← Finset.mul_prod_erase _ _ (show j ∈ (Finset.univ : Finset (Fin n)).erase i by
    simp [hij.symm])]
  have hs : ((Finset.univ : Finset (Fin n)).erase j).erase i =
      (Finset.univ.erase i).erase j := by ext x; simp [and_comm]
  rw [hs]
  simp only [rowWedge, Polynomial.C_sub, Polynomial.C_mul, complementPolynomial]
  ring

theorem ordered_pair_differences {n : ℕ} (T : Fin n → Polynomial ℂ) :
    (∑ p ∈ rowPairs n, (T p.2 - T p.1)) =
      ∑ i, Polynomial.C (2 * (i.val : ℂ) + 1 - (n : ℂ)) * T i := by
  classical
  unfold rowPairs
  rw [Finset.sum_filter]
  have hit : ∀ i j : Fin n, (if i < j then T j - T i else 0) =
      (if i < j then T j else 0) - (if i < j then T i else 0) := by
    intro i j; split_ifs <;> simp
  simp_rw [hit]
  rw [Finset.sum_sub_distrib]
  simp_rw [Fintype.sum_prod_type]
  conv_lhs => arg 1; rw [Finset.sum_comm]
  have hlo : ∀ j : Fin n, (∑ i : Fin n, if i < j then T j else 0) = j.val • T j := by
    intro j
    rw [← Finset.sum_filter]
    have hs : (Finset.univ.filter fun i : Fin n => i < j) = Finset.Iio j := by ext; simp
    rw [hs, Finset.sum_const, Fin.card_Iio]
  have hhi : ∀ i : Fin n, (∑ j : Fin n, if i < j then T i else 0) =
      (n - 1 - i.val) • T i := by
    intro i
    rw [← Finset.sum_filter]
    have hs : (Finset.univ.filter fun j : Fin n => i < j) = Finset.Ioi i := by ext; simp
    rw [hs, Finset.sum_const, Fin.card_Ioi]
  simp_rw [hlo, hhi]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi_lt := i.isLt
  have hc : ((n - 1 - i.val : ℕ) : ℂ) = (n : ℂ) - 1 - (i.val : ℂ) := by
    have hn : 1 ≤ n := by omega
    have hi : i.val ≤ n - 1 := by omega
    rw [Nat.cast_sub hi, Nat.cast_sub hn, Nat.cast_one]
  simp only [nsmul_eq_mul, ← Polynomial.C_eq_natCast]
  rw [hc, ← sub_mul, ← Polynomial.C_sub]
  congr 2
  ring

theorem pairPolynomial_weighted {n : ℕ} (V : Matrix (Fin n) (Fin 2) ℂ) :
    pairPolynomial V = ∑ i,
      Polynomial.C (2 * (i.val : ℂ) + 1 - (n : ℂ)) *
        (Polynomial.C (V i 1) * deletedFactorPolynomial V i) := by
  classical
  unfold pairPolynomial
  have ht : ∀ p ∈ rowPairs n,
      Polynomial.C (rowWedge V p.1 p.2) * complementPolynomial V p.1 p.2 =
        Polynomial.C (V p.2 1) * deletedFactorPolynomial V p.2 -
          Polynomial.C (V p.1 1) * deletedFactorPolynomial V p.1 := by
    intro p hp
    exact pairPolynomial_term V p.1 p.2 (Finset.mem_filter.mp hp).2.ne
  rw [Finset.sum_congr rfl ht]
  exact ordered_pair_differences (fun i => Polynomial.C (V i 1) * deletedFactorPolynomial V i)

namespace Certificate

def deletedListProduct (rs : List Row) (i : Fin rs.length) : Polynomial ℂ :=
  ∏ j : Fin rs.length, if j = i then 1 else rowLinear rs[j.val]

theorem deletedListProduct_cons_zero (r : Row) (rs : List Row) :
    deletedListProduct (r :: rs) 0 = rowProduct rs := by
  simp [deletedListProduct, Fin.prod_univ_succ, rowProduct,
    Fin.prod_univ_fun_getElem]

theorem deletedListProduct_cons_succ (r : Row) (rs : List Row) (i : Fin rs.length) :
    deletedListProduct (r :: rs) i.succ = rowLinear r * deletedListProduct rs i := by
  have hn : (0 : Fin (rs.length + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  simp [deletedListProduct, Fin.prod_univ_succ, hn]

theorem weightedBy_expansion (w : ℤ) (rs : List Row) :
    weightedBy w rs = ∑ i : Fin rs.length,
      Polynomial.C ((w - 2 * (i.val : ℤ) : ℤ) : ℂ) *
        Polynomial.C (rowB rs[i.val]) * deletedListProduct rs i := by
  induction rs generalizing w with
  | nil => simp [weightedBy]
  | cons r rs ih =>
    rw [weightedBy]
    change _ = ∑ i : Fin (rs.length + 1),
      Polynomial.C ((w - 2 * (i.val : ℤ) : ℤ) : ℂ) *
        Polynomial.C (rowB (r :: rs)[i.val]) * deletedListProduct (r :: rs) i
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, sub_zero,
      List.getElem_cons_zero, deletedListProduct_cons_zero,
      List.getElem_cons_succ, Fin.val_succ, deletedListProduct_cons_succ]
    rw [ih, Finset.mul_sum, add_comm]
    apply congrArg (fun z : Polynomial ℂ =>
      Polynomial.C (w : ℂ) * Polynomial.C (rowB r) * rowProduct rs + z)
    apply Finset.sum_congr rfl
    intro i _
    have hw : (w - 2) - 2 * (i.val : ℤ) = w - 2 * ((i.val + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [hw]
    ring

end Certificate

theorem gramFactor_rowA (i : Fin Certificate.rows.length) :
    gramFactor (finCongr Certificate.rows_length i) 0 =
      Certificate.rowA Certificate.rows[i.val] := by
  unfold gramFactor Certificate.rowA
  rw [List.getElem_eq_getD (0, 0, 0)]
  simp

theorem gramFactor_rowB (i : Fin Certificate.rows.length) :
    gramFactor (finCongr Certificate.rows_length i) 1 =
      Certificate.rowB Certificate.rows[i.val] := by
  unfold gramFactor Certificate.rowB
  rw [List.getElem_eq_getD (0, 0, 0)]
  simp [Certificate.toComplex]

theorem deletedListProduct_rows (i : Fin Certificate.rows.length) :
    Certificate.deletedListProduct Certificate.rows i =
      deletedFactorPolynomial gramFactor (finCongr Certificate.rows_length i) := by
  classical
  rw [deletedFactorPolynomial_ite]
  unfold Certificate.deletedListProduct
  apply Fintype.prod_equiv (finCongr Certificate.rows_length)
  intro j
  have he : finCongr Certificate.rows_length j = finCongr Certificate.rows_length i ↔ j = i :=
    (finCongr Certificate.rows_length).injective.eq_iff
  simp only [he, gramFactor_rowA, gramFactor_rowB, Certificate.rowLinear]

theorem weightedBy_rows_expansion : Certificate.weightedBy 143 Certificate.rows =
    ∑ i : Fin 144, Polynomial.C (((143 : ℤ) - 2 * (i.val : ℤ) : ℤ) : ℂ) *
      Polynomial.C (gramFactor i 1) * deletedFactorPolynomial gramFactor i := by
  rw [Certificate.weightedBy_expansion]
  apply Fintype.sum_equiv (finCongr Certificate.rows_length)
  intro i
  rw [gramFactor_rowB, deletedListProduct_rows]
  rfl

theorem pairPolynomial_gramFactor :
    pairPolynomial gramFactor = Certificate.wedgePolynomial Certificate.rows := by
  classical
  rw [Certificate.wedgePolynomial_eq_weightedBy, Certificate.rows_length]
  change pairPolynomial gramFactor = -Certificate.weightedBy 143 Certificate.rows
  rw [pairPolynomial_weighted, weightedBy_rows_expansion, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    Nat.cast_ofNat, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul,
    Polynomial.C_ofNat, Polynomial.C_1]
  ring

#print axioms pairPolynomial_gramFactor

#print axioms pairPolynomial_weighted
#print axioms Certificate.weightedBy_expansion

end
end Bapat
