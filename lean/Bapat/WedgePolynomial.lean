import Bapat.NormCertificate
import Mathlib.Algebra.Polynomial.Derivative

/-!
# A product-rule shortcut for the ordered wedge polynomial

The pairwise 2-by-2 determinants can be aggregated recursively. Their sum is
minus the weighted polynomial g. The proof uses a product derivative and list
induction, avoiding a quadratic reindexing of products with two erased indices.
-/

namespace Bapat.Certificate

noncomputable section

abbrev Row := ℤ × ℤ × ℤ

def rowA (r : Row) : ℂ := r.1
def rowB (r : Row) : ℂ := toComplex (r.2.1, r.2.2)
def rowLinear (r : Row) : Polynomial ℂ := Polynomial.C (rowA r) +
  Polynomial.C (rowB r) * Polynomial.X

def rowProduct (rs : List Row) : Polynomial ℂ := (rs.map rowLinear).prod

theorem rowProduct_cons (r : Row) (rs : List Row) :
    rowProduct (r :: rs) = rowLinear r * rowProduct rs := by simp [rowProduct]

theorem productPolynomial_zipIdx (rs : List Row) (start : ℕ) :
    productPolynomial (rs.zipIdx start) = rowProduct rs := by
  unfold productPolynomial rowProduct
  have hmap : (rs.zipIdx start).map linearFactor = rs.map rowLinear := by
    calc
      (rs.zipIdx start).map linearFactor =
          ((rs.zipIdx start).map Prod.fst).map rowLinear := by
        rw [List.map_map]
        rfl
      _ = rs.map rowLinear := by rw [List.zipIdx_map_fst]
  rw [hmap]

theorem rowLinear_derivative (r : Row) :
    (rowLinear r).derivative = Polynomial.C (rowB r) := by
  simp [rowLinear]

/-- The weighted product rule, with an arbitrary initial integer weight. -/
def weightedBy (weight : ℤ) : List Row → Polynomial ℂ
  | [] => 0
  | r :: rs => rowLinear r * weightedBy (weight - 2) rs +
      Polynomial.C (weight : ℂ) * Polynomial.C (rowB r) * rowProduct rs

theorem weightedBy_shift (w d : ℤ) (rs : List Row) :
    weightedBy (w + d) rs = weightedBy w rs +
      Polynomial.C (d : ℂ) * (rowProduct rs).derivative := by
  induction rs generalizing w with
  | nil => simp [weightedBy, rowProduct]
  | cons r rs ih =>
    have hw : w + d - 2 = (w - 2) + d := by ring
    simp only [weightedBy, rowProduct_cons, Polynomial.derivative_mul,
      rowLinear_derivative]
    rw [hw, ih]
    simp only [Int.cast_add, Polynomial.C_add]
    ring

theorem weightedPolynomial_zipIdx (n : ℕ) (rs : List Row) (start : ℕ) :
    weightedPolynomial n (rs.zipIdx start) =
      weightedBy ((n : ℤ) - 1 - 2 * (start : ℤ)) rs := by
  induction rs generalizing start with
  | nil => simp [weightedPolynomial, weightedBy]
  | cons r rs ih =>
    simp only [List.zipIdx_cons, weightedPolynomial, weightedBy]
    rw [ih, productPolynomial_zipIdx]
    have hw : (n : ℤ) - 1 - 2 * ((start + 1 : ℕ) : ℤ) =
        ((n : ℤ) - 1 - 2 * (start : ℤ)) - 2 := by push_cast; ring
    rw [hw]
    rfl

/-- Cross terms from a fixed first row, preserving the order of the remaining list. -/
def crossPolynomial (r : Row) : List Row → Polynomial ℂ
  | [] => 0
  | s :: rs => Polynomial.C (rowA r * rowB s - rowA s * rowB r) * rowProduct rs +
      rowLinear s * crossPolynomial r rs

/-- Aggregate every ordered row pair once, including its complementary product. -/
def wedgePolynomial : List Row → Polynomial ℂ
  | [] => 0
  | r :: rs => rowLinear r * wedgePolynomial rs + crossPolynomial r rs

theorem crossPolynomial_eq_derivative (r : Row) (rs : List Row) :
    crossPolynomial r rs = rowLinear r * (rowProduct rs).derivative -
      Polynomial.C (rs.length : ℂ) * Polynomial.C (rowB r) * rowProduct rs := by
  induction rs with
  | nil => simp [crossPolynomial, rowProduct]
  | cons s rs ih =>
    simp only [crossPolynomial, ih, rowProduct_cons, List.length_cons,
      Nat.cast_add, Nat.cast_one, Polynomial.derivative_mul, rowLinear_derivative,
      Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_add, Polynomial.C_1]
    simp only [rowLinear]
    ring

theorem wedgePolynomial_eq_weightedBy (rs : List Row) :
    wedgePolynomial rs = -weightedBy ((rs.length : ℤ) - 1) rs := by
  induction rs with
  | nil => simp [wedgePolynomial, weightedBy]
  | cons r rs ih =>
    have hw : ((rs.length : ℤ) - 1) + (-1) = (rs.length : ℤ) - 2 := by ring
    have hshift := weightedBy_shift ((rs.length : ℤ) - 1) (-1) rs
    rw [hw] at hshift
    simp only [Int.cast_neg, Int.cast_one, Polynomial.C_neg, Polynomial.C_1,
      neg_one_mul, ← sub_eq_add_neg] at hshift
    simp only [wedgePolynomial, ih, crossPolynomial_eq_derivative,
      List.length_cons, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, weightedBy]
    rw [hshift]
    norm_cast
    ring

/-- The manuscript's F = -g identity, now proved for the actual ordered data. -/
theorem certificate_wedgePolynomial :
    wedgePolynomial rows = -weightedPolynomial 144 rows.zipIdx := by
  rw [wedgePolynomial_eq_weightedBy, weightedPolynomial_zipIdx]
  apply congrArg (fun w : ℤ => -weightedBy w rows)
  rw [rows_length]
  norm_num

theorem certificate_wedgeNorm : polynomialNorm 142 (wedgePolynomial rows) = (expectedS : ℝ) := by
  rw [certificate_wedgePolynomial, expectedS_eq_polynomialNorm]
  simp [polynomialNorm, Polynomial.coeff_neg]

#print axioms certificate_wedgePolynomial
#print axioms certificate_wedgeNorm

end
end Bapat.Certificate
