import Bapat.Main

/-!
# Disproof of da Fonseca's half-line monotonicity conjecture

Conjecture 2 in Section 4 of *The mu-permanent revisited*, arXiv:1804.02231,
asks whether each Hermitian positive definite matrix has some
ε < -1 for which its q-permanent is strictly increasing on (ε, ∞).
Since this half-line contains [-1, 1], the existing disproof of Conjecture 1
also disproves this extension.
-/

open scoped ComplexOrder

namespace BapatLal

/-- The negative answer to da Fonseca's half-line extension. -/
theorem qPermanentHalfLineMonotonicity :
    answer(False) ↔
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
        A.PosDef →
          ∃ ε : ℝ, ε < -1 ∧
            StrictMonoOn (fun q : ℝ => (A.qPermanent q).re) (Set.Ioi ε) := by
  constructor
  · intro h
    exact h.elim
  · intro h
    apply qPermanentMonotonicity.mpr
    intro n A hpd _hnd
    obtain ⟨ε, hε, hmono⟩ := h n A hpd
    intro q₁ hq₁ q₂ hq₂ hlt
    exact hmono (lt_of_lt_of_le hε hq₁.1) (lt_of_lt_of_le hε hq₂.1) hlt

#print axioms qPermanentHalfLineMonotonicity

end BapatLal
