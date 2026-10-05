import Bapat.Statement
import Bapat.Counterexample

/-!
# The exact proposed Formal Conjectures target

The target is Conjecture 1 in Section 4 of C. M. da Fonseca,
*The mu-permanent revisited*, arXiv:1804.02231.
All quantifiers are outside `answer(False)`. Positive definiteness includes
Hermitian symmetry in Mathlib.
-/

open scoped ComplexOrder

namespace BapatLal

noncomputable section

theorem qPermanent_re {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) :
    (A.qPermanent q).re = Bapat.qPermanent A q := by
  change (Bapat.complexQPermanent A q).re = _
  exact Bapat.complexQPermanent_re A q

/-- The negative answer to the original Bapat–Lal monotonicity question. -/
theorem qPermanentMonotonicity :
    answer(False) ↔
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
        A.PosDef → ¬ A.IsDiag →
          StrictMonoOn (fun q : ℝ => (A.qPermanent q).re) (Set.Icc (-1) 1) := by
  constructor
  · intro h
    exact h.elim
  · intro h
    apply Bapat.not_bapatMonotonicity
    intro n A hpd hnd
    simpa only [qPermanent_re] using h n A hpd hnd

#print axioms qPermanentMonotonicity
#print axioms Bapat.exists_decreasing_pair

end
end BapatLal
