import Bapat.Main

/-!
# Disproof of da Fonseca's half-line monotonicity conjecture

Conjecture 2 in Section 4 of *The mu-permanent revisited*, arXiv:1804.02231,
asks about strict q-permanent monotonicity on a half-line (ε, ∞), with ε < -1.
We use the non-diagonal formulation explicitly stated in Lon Mitchell,
*A note on Bapat's q-permanent conjecture* (2020), Remark, p. 917,
https://doi.org/10.7153/oam-2020-14-56.
The 2018 survey omits this condition; diagonal matrices have a constant q-permanent.
Since this half-line contains [-1, 1], the same non-diagonal order-144
counterexample used for Conjecture 1 also disproves this extension.
-/

open scoped ComplexOrder

namespace BapatLal

/-- The negative answer to the non-diagonal form of da Fonseca's half-line extension. -/
theorem qPermanentHalfLineMonotonicity :
    answer(False) ↔
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
        A.PosDef → ¬ A.IsDiag →
          ∃ ε : ℝ, ε < -1 ∧
            StrictMonoOn (fun q : ℝ => (A.qPermanent q).re) (Set.Ioi ε) := by
  constructor
  · intro h
    exact h.elim
  · intro h
    apply qPermanentMonotonicity.mpr
    intro n A hpd hnd
    obtain ⟨ε, hε, hmono⟩ := h n A hpd hnd
    intro q₁ hq₁ q₂ hq₂ hlt
    exact hmono (lt_of_lt_of_le hε hq₁.1) (lt_of_lt_of_le hε hq₂.1) hlt

#print axioms qPermanentHalfLineMonotonicity

end BapatLal
