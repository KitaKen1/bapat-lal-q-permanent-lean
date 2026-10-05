# Pull request edit draft

**Title:** Formalize q-permanent Conjectures 1 and 2 and record their disproofs

This PR formalizes Conjectures 1 and 2 in Section 4 of
[da Fonseca, *The mu-permanent revisited*](https://arxiv.org/abs/1804.02231),
with `answer(False)` and `category research solved, AMS 15`.

[Kenta Kitamura's Lean proof repository](https://github.com/KitaKen1/bapat-lal-q-permanent-lean)
refutes Conjecture 1 with an order-144 Hermitian
positive definite non-diagonal counterexample on `[-1,1]`.
Conjecture 2 follows because every half-line `(ε,∞)` with `ε < -1`
contains `[-1,1]`. The published complete proof includes both theorem types.

The module docstring also records two related solved conjectures in Section 5:

- **Conjecture 3:** Matthew J. Colbrook's counterexample, formalized in Lean by
  [George Stepaniants, Lean formalization of MI-19 (2026)](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7/matrix-inequalities-and-norms/MI-19/lean/Solution.lean).
- **Conjecture 4:** at `q = 1` it includes permanent-on-top, disproved by
  [Shchesnovich, *The permanent-on-top conjecture is false*, Linear Algebra Appl. 490 (2016), 196–201](https://doi.org/10.1016/j.laa.2015.10.034).
  [Tran Hoang Anh, *A simple counterexample for the permanent-on-top conjecture*, arXiv:2101.03428 (2021)](https://arxiv.org/abs/2101.03428) gives a simpler example.

The two formal theorem declarations in this PR concern Conjectures 1 and 2.

Proof: https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/42dabed0c50511040a5c72b80c81593ba58fd82e/lean/Bapat/Main.lean#L25
Half-line proof: https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/42dabed0c50511040a5c72b80c81593ba58fd82e/lean/Bapat/DaFonseca.lean#L18
Repository: https://github.com/KitaKen1/bapat-lal-q-permanent-lean
Lean4Web: [open in your browser](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fbapat-lal-q-permanent-lean%2F42dabed0c50511040a5c72b80c81593ba58fd82e%2Flean4web%2FBapatLalLean4Web.lean) (v4.35.0-rc3)

Validation: `python3 lean/scripts/build_audit.py` builds both complete proof
versions, checks FC linters and the two compiled targets, and audits the
standard-three axiom closure.

AI Usage Disclosure: This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra and GPT-6.1 sol, and Claude Code using Claude Opus 5.5.

---

Local editing notes: replace the file in the existing PR branch with
`QPermanentMonotonicity.lean`, using the standard FC copyright header.
Then use **Edit** on PR #6857 to replace the title and body with the text above.
The proof links are fixed to a public commit containing both complete proofs
and the updated Lean4Web file.
