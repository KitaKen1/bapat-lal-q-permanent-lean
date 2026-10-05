# Pull request draft

**Title:** Add Bapat–Lal q-permanent monotonicity and record its negative answer

This PR adds Conjecture 1 in Section 4 of
[da Fonseca, *The mu-permanent revisited*](https://arxiv.org/abs/1804.02231).
The file defines the inversion count and q-permanent, and states the original
monotonicity question as `answer(False) ↔ …`, with `category research solved, AMS 15`.

The external Lean proof establishes this exact statement. It produces an
order-144 positive definite counterexample with a strict decrease inside
`[-1,1]`, using an exact integer certificate and a sufficiently small diagonal
perturbation. The final theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

Proof: to be filled after publication.
Repository: to be filled after publication.
Lean4Web: to be filled after publication.

Validation: `python3 lean/scripts/build_audit.py` builds both complete proofs,
compiles this statement with FC's mathematical linters, compares the definitions and compiled
target types, and audits the final axioms.

AI Usage Disclosure: This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra and GPT-6.1 sol, and Claude Code using Claude Opus 5.5.

Before submitting, fill the links and copy `QPermanentMonotonicity.lean` to
`FormalConjectures/Arxiv/1804.02231/QPermanentMonotonicity.lean` in FC,
using the standard FC copyright header.
