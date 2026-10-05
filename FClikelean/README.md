# Statement in the format of Formal Conjectures

[QPermanentMonotonicity.lean](QPermanentMonotonicity.lean) contains the
q-permanent definitions and the negative answer to Bapat–Lal monotonicity,
Conjecture 1 in [da Fonseca's survey](https://arxiv.org/abs/1804.02231).
It is intended for `FormalConjectures/Arxiv/1804.02231/` and has not been submitted.

The definitions are copied verbatim in [Bapat/Statement.lean](../lean/Bapat/Statement.lean).
The complete proof is [Bapat/Main.lean](../lean/Bapat/Main.lean).
The statement closes with `by sorry`, as in FC's externally linked statements;
the complete proof has no holes.

`python3 lean/scripts/build_audit.py` builds both proofs, checks the axioms,
compares the definitions and theorem types, and compiles this statement with FC linters (excluding the repository-specific copyright header).
The `formal_proof` attribute links to the complete proof at a fixed commit.
`lean/scripts/fill_links.py` updates the publication links.
[PR_DRAFT.md](PR_DRAFT.md) is the submission draft.
