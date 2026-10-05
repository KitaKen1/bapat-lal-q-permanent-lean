# Pull request edit draft

**Title:** Formalize q-permanent Conjectures 1 and 2 and record their disproofs

This PR makes two contributions:

1. **Formalization.** It adds the Bapat–Lal q-permanent monotonicity question and da Fonseca's half-line extension, stated as Conjectures 1 and 2 in Section 4 of [da Fonseca, *The mu-permanent revisited*](https://arxiv.org/abs/1804.02231), in `FormalConjectures/Arxiv/1804.02231/QPermanentMonotonicity.lean`. The file defines the inversion count and q-permanent.
2. **Formal disproof.** It records both negative answers as `research solved`, with `formal_proof` links to the kernel-checked Conjecture 1 counterexample, which refutes both statements. The proof establishes a strict decrease for a non-diagonal Hermitian positive definite complex matrix of order 144.

### 1. Formalization

Conjecture 1 asks whether, for every non-diagonal Hermitian positive definite matrix A, its q-permanent is strictly increasing as q ranges over [-1, 1]. It originates in Bapat and Lal, *Inequalities for the q-permanent*, Linear Algebra Appl. 197–198 (1994), 397–409 ([DOI](https://doi.org/10.1016/0024-3795(94)90497-9)).

Conjecture 2 asks whether every non-diagonal Hermitian positive definite matrix has some ε < −1 such that its q-permanent is strictly increasing on (ε, ∞). We use the non-diagonal formulation explicitly stated in [Mitchell (2020), Remark, p. 917](https://doi.org/10.7153/oam-2020-14-56). The 2018 survey omits this hypothesis; diagonal matrices have a constant q-permanent, so including them would make the strict-monotonicity claim trivially false.

The two definitions are:

```lean
def Equiv.Perm.inversionCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1).card


noncomputable def Matrix.qPermanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), (q ^ σ.inversionCount : ℝ) * ∏ i, A i (σ i)
```

`inversionCount` counts pairs of indices whose order is reversed by the permutation. `qPermanent` sums the products of matrix entries selected by each permutation, weighted by q to that inversion count. Mathlib's `Matrix.PosDef` includes Hermitian symmetry; for a Hermitian matrix and real q, the q-permanent is real, so `.re` represents its value in the real-valued monotonicity statement.

### 2. Formal disproof

KitaKen1 (Kenta Kitamura) prepared the statements and the external Lean proofs for Conjectures 1 and 2. The external project uses the same two definitions and FC's `answer` elaborator, and proves the following targets:

```lean
theorem qPermanentMonotonicity :
    answer(False) ↔
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
        A.PosDef → ¬ A.IsDiag →
          StrictMonoOn (fun q : ℝ => (A.qPermanent q).re) (Set.Icc (-1) 1)

theorem qPermanentHalfLineMonotonicity :
    answer(False) ↔
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
        A.PosDef → ¬ A.IsDiag →
          ∃ ε : ℝ, ε < -1 ∧
            StrictMonoOn (fun q : ℝ => (A.qPermanent q).re) (Set.Ioi ε)
```

The disproof of Conjecture 1 starts with a rank-two Gram matrix of order 144. Exact integer identities certify that its q-permanent has a negative derivative at q = 1. Adding a sufficiently small positive multiple of the identity gives a positive definite, non-diagonal matrix while retaining a strict decrease between two points in [-1, 1].

The same counterexample refutes Conjecture 2: every half-line (ε, ∞) with ε < −1 contains [-1, 1]. Strict monotonicity on that half-line would imply the monotonicity already disproved by Conjecture 1. The module docstring cites the proof repository as `[Ki26]`, and both conjecture docstrings record the negative answer with this reference.

- [Complete proof of Conjecture 1](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/42dabed0c50511040a5c72b80c81593ba58fd82e/lean/Bapat/Main.lean#L25)
- [Published counterexample used for Conjecture 2](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/42dabed0c50511040a5c72b80c81593ba58fd82e/lean/Bapat/Main.lean#L25)
- [GitHub repository](https://github.com/KitaKen1/bapat-lal-q-permanent-lean)
- Lean4Web: [open in your browser](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fbapat-lal-q-permanent-lean%2F42dabed0c50511040a5c72b80c81593ba58fd82e%2Flean4web%2FBapatLalLean4Web.lean) — select Lean `v4.35.0-rc3`.

The revised non-diagonal Conjecture 2 proof is in the local `lean/Bapat/DaFonseca.lean` and Lean4Web files. The links above still open the published revision.

The repository checks that the shared definitions match character for character and that the compiled FC targets and the complete proofs have definitionally equal types. The main proof uses Lean `v4.33.1`; `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. The complete proofs contain no `sorry`, `admit`, `native_decide`, or project-specific mathematical axioms. The updated FC module builds with `lake --wfail build 'FormalConjectures.Arxiv.«1804.02231».QPermanentMonotonicity'`.

**AI Usage Disclosure:** This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra and GPT-6.1 sol, and Claude Code using Claude Opus 5.5.

> [!NOTE]
> Conjectures 3 and 4 are not formalized in this PR. Both are already known to be false, and their disproofs and references are recorded in the module docstring.
>
> - **Conjecture 3:** Matthew J. Colbrook's counterexample, formalized in Lean by [George Stepaniants](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7/matrix-inequalities-and-norms/MI-19/lean/Solution.lean).
> - **Conjecture 4:** at q = 1 it specializes to permanent-on-top, disproved by [Shchesnovich (2016)](https://doi.org/10.1016/j.laa.2015.10.034). [Tran Hoang Anh (2021)](https://arxiv.org/abs/2101.03428) gives a simpler counterexample.
