# Statements in the format of Formal Conjectures

[QPermanentMonotonicity.lean](QPermanentMonotonicity.lean) contains two
q-permanent conjectures in Section 4 of
[da Fonseca's survey](https://arxiv.org/abs/1804.02231), with negative answers:

1. **Conjecture 1 (Bapat–Lal):** [complete Lean proof](../lean/Bapat/Main.lean).
2. **Conjecture 2 (da Fonseca, non-diagonal form):** [complete Lean corollary](../lean/Bapat/DaFonseca.lean).

Conjecture 2 includes `¬ A.IsDiag`, following Mitchell (2020), Remark, p. 917.
The 2018 survey omits this condition, which excludes constant q-permanents.

The module docstring records the known disproofs of Conjectures 3 and 4 as
related work, with an external Lean proof for Conjecture 3 and published
mathematical references for Conjecture 4.

[PR_DRAFT.md](PR_DRAFT.md) is the local text for editing
[PR #6857](https://github.com/google-deepmind/formal-conjectures/pull/6857).
It covers the two formal statements and the related-work references.

The shared definitions are copied verbatim in
[Bapat/Statement.lean](../lean/Bapat/Statement.lean).
`python3 lean/scripts/build_audit.py` checks both complete proofs, FC linters,
compiled target types, and the standard-three axiom closure.
The FC statements use `by sorry`, with `formal_proof` links to the two
published complete Lean proofs at a fixed commit.
Run `fill_links.py` with a public commit to refresh the fixed-commit proof
and Lean4Web links after later proof updates.
