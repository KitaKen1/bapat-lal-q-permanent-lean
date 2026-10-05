# Complete Lean proof

Lean `v4.33.1`, with Formal Conjectures pinned to
`89294ea02bd7cd678d59984add52cb4baef3dbf4`.

- [Bapat/Statement.lean](Bapat/Statement.lean): definitions copied from the FC-style statement.
- [Bapat/Main.lean](Bapat/Main.lean): `BapatLal.qPermanentMonotonicity`.
- [Bapat/Counterexample.lean](Bapat/Counterexample.lean): positive definite counterexample and strict decrease.
- The other `Bapat/` modules prove the coefficient, permutation, and analytic identities.

```bash
lake update
lake exe cache get
python3 scripts/build_audit.py
```

The audit also builds the Lean4Web project and checks the FC-style statement.
Results are saved to `evidence/build.log` and `evidence/build_results.json`.

`make_lean4web.py` regenerates the standalone proof. After publication,
`fill_links.py REPOSITORY_URL FULL_COMMIT_SHA` fills the proof and Lean4Web links.
