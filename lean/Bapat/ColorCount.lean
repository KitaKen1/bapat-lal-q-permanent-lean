import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Sum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Factorial multiplicities for two-coordinate assignments

The rank-two coefficient formula counts permutations matching two colourings.
Instead of counting them from scratch, use the existing equivalence between
a function stabilizer and permutations of its fibres.
-/

namespace Bapat

noncomputable section

theorem finTwo_cases (c : Fin 2) : c = 0 ∨ c = 1 := by fin_cases c <;> simp

def colorCount {n : ℕ} (f : Fin n → Fin 2) (c : Fin 2) : ℕ :=
  Fintype.card {i // f i = c}

theorem colorCount_zero {n : ℕ} (f : Fin n → Fin 2) :
    colorCount f 0 = n - colorCount f 1 := by
  classical
  have hiff : ∀ i, f i = 0 ↔ ¬ f i = 1 := by
    intro i
    rcases finTwo_cases (f i) with h | h <;> simp [h]
  calc
    colorCount f 0 = Fintype.card {i // ¬ f i = 1} :=
      Fintype.card_congr (Equiv.subtypeEquivRight hiff)
    _ = n - colorCount f 1 := by simp [Fintype.card_subtype_compl, colorCount]

theorem colorCount_comp {n : ℕ} (f : Fin n → Fin 2)
    (σ : Equiv.Perm (Fin n)) (c : Fin 2) : colorCount (f ∘ σ) c = colorCount f c := by
  classical
  exact Fintype.card_congr (Equiv.subtypeEquiv σ (fun _ => Iff.rfl))

/-- A compatible permutation exists when the two coordinate counts agree. -/
theorem exists_colorMatching {n : ℕ} (f g : Fin n → Fin 2)
    (h : colorCount f 1 = colorCount g 1) :
    ∃ σ : Equiv.Perm (Fin n), f ∘ σ = g := by
  classical
  have hc : ∀ c, colorCount g c = colorCount f c := by
    intro c
    rcases finTwo_cases c with heq | heq
    · simpa [heq, colorCount_zero] using congrArg (n - ·) h.symm
    · simpa [heq] using h.symm
  let e (c : Fin 2) : {i // g i = c} ≃ {i // f i = c} :=
    Fintype.equivOfCardEq (hc c)
  let σ : Equiv.Perm (Fin n) :=
    (Equiv.sigmaFiberEquiv g).symm.trans
      ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv f))
  refine ⟨σ, funext fun i => ?_⟩
  exact (e (g i) ⟨i, rfl⟩).property

/-- A single matching identifies all matchings with the function stabilizer. -/
def colorMatchingEquiv {n : ℕ} {ι : Type*} (f g : Fin n → ι)
    (σ₀ : Equiv.Perm (Fin n)) (h₀ : f ∘ σ₀ = g) :
    {σ : Equiv.Perm (Fin n) // f ∘ σ = g} ≃
      {τ : Equiv.Perm (Fin n) // f ∘ τ = f} where
  toFun σ := ⟨σ.val * σ₀.symm, by
    funext i
    change f (σ.val (σ₀.symm i)) = f i
    calc
      _ = g (σ₀.symm i) := congrFun σ.property _
      _ = f i := by rw [← h₀]; simp⟩
  invFun τ := ⟨τ.val * σ₀, by
    funext i
    change f (τ.val (σ₀ i)) = g i
    calc
      _ = f (σ₀ i) := congrFun τ.property _
      _ = g i := congrFun h₀ _⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    simp [Equiv.Perm.mul_apply]
  right_inv τ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    simp [Equiv.Perm.mul_apply]

/-- The k!(n-k)! multiplicity in the permanent coefficient formula. -/
theorem colorMatching_card {n : ℕ} (f g : Fin n → Fin 2)
    (h : colorCount f 1 = colorCount g 1) :
    Fintype.card {σ : Equiv.Perm (Fin n) // f ∘ σ = g} =
      (colorCount f 1).factorial * (n - colorCount f 1).factorial := by
  classical
  obtain ⟨σ₀, h₀⟩ := exists_colorMatching f g h
  rw [Fintype.card_congr (colorMatchingEquiv f g σ₀ h₀),
    DomMulAct.stabilizer_card, Fin.prod_univ_two]
  change (colorCount f 0).factorial * (colorCount f 1).factorial = _
  rw [colorCount_zero, Nat.mul_comm]

theorem colorMatching_card_ite {n : ℕ} (f g : Fin n → Fin 2) :
    Fintype.card {σ : Equiv.Perm (Fin n) // f ∘ σ = g} =
      if colorCount f 1 = colorCount g 1 then
        (colorCount f 1).factorial * (n - colorCount f 1).factorial
      else 0 := by
  classical
  by_cases h : colorCount f 1 = colorCount g 1
  · simpa [h] using colorMatching_card f g h
  · have hempty : IsEmpty {σ : Equiv.Perm (Fin n) // f ∘ σ = g} := ⟨fun σ => by
      have heq := colorCount_comp f σ.val 1
      rw [σ.property] at heq
      exact h heq.symm⟩
    simp [h]

#print axioms colorMatching_card_ite

end
end Bapat
