# Lean proofs of q-permanent Conjectures 1 and 2

The four q-permanent conjectures stated in [da Fonseca's survey](https://arxiv.org/abs/1804.02231) are the following.

> **Conjecture 1 (Bapat–Lal).** For every non-diagonal Hermitian positive definite
> complex matrix $`A=(a_{ij})`$ of order $`n`$, the function $`q\mapsto P_q(A)`$
> is strictly increasing on $`[-1,1]`$.

> **Conjecture 2 (da Fonseca, non-diagonal form).** For every non-diagonal
> Hermitian positive definite complex matrix $`A`$, there exists $`ε < -1`$ such
> that $`q\mapsto P_q(A)`$ is strictly increasing on $`(ε,\infty)`$.

> **Conjecture 3 (Bapat–Lal).** For every Hermitian positive semidefinite complex
> matrix $`A=(a_{ij})`$ of order $`n`$, every $`q\in[0,1]`$, and every nonempty
> subset $`S\subseteq\{1,\ldots,n\}`$,
> $`P_q(A)\geq\sum_{\sigma\in S_n,\ \sigma(S)=S}q^{\ell(\sigma)}\prod_{i=1}^{n}a_{i,\sigma(i)}`$.
> The sum is over permutations preserving $`S`$ setwise, and $`\ell(\sigma)`$
> counts inversions in the full original ordering.

> **Conjecture 4 (Bapat–Lal).** For every Hermitian positive semidefinite complex
> matrix $`A=(a_{ij})`$ of order $`n`$ and every $`q\in[0,1]`$, the largest
> eigenvalue of the q-Schur power matrix $`\Pi_q(A)`$ equals $`P_q(A)`$.
> Its rows and columns are indexed by permutations $`\sigma,\tau\in S_n`$,
> with entries $`(\Pi_q(A))_{\sigma,\tau}=q^{\ell(\tau\sigma^{-1})}\prod_{i=1}^{n}a_{\sigma(i),\tau(i)}`$.

Conjecture 2 uses the non-diagonal hypothesis explicitly stated in
[Mitchell (2020), Remark, p. 917](https://doi.org/10.7153/oam-2020-14-56).
The 2018 survey omits this condition; diagonal matrices have a constant
q-permanent and cannot satisfy strict monotonicity.

All four conjectures are false. Their disproofs and proof references are:

| Conjecture | Answer | Mathematical disproof | Lean formalization |
|---|---|---|---|
| 1 | False | This repository: order-144 counterexample | [This repository](lean/Bapat/Main.lean) |
| 2 | False | This repository: corollary of Conjecture 1 | [This repository](lean/Bapat/DaFonseca.lean) |
| 3 | False | Matthew J. Colbrook | [George Stepaniants](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7/matrix-inequalities-and-norms/MI-19/lean/Solution.lean) |
| 4 | False | [Valery S. Shchesnovich (2016)](https://doi.org/10.1016/j.laa.2015.10.034); [Tran Hoang Anh (2021), simpler example](https://arxiv.org/abs/2101.03428) | Published mathematical disproof |

This repository contributes the following:

1. **Statements in the format of Formal Conjectures.**
   [FClikelean/](FClikelean/) contains Conjectures 1 and 2 with their negative
   answers. Its module docstring and PR edit draft record the known disproofs
   of Conjectures 3 and 4 as related work.
2. **Complete Lean 4 proof of Conjecture 1.**
   [Bapat/Main.lean](lean/Bapat/Main.lean) disproves the conjecture with an
   order-144 Hermitian positive definite non-diagonal counterexample.
3. **Complete Lean 4 proof of Conjecture 2.**
   [Bapat/DaFonseca.lean](lean/Bapat/DaFonseca.lean) derives the negative answer
   by restricting any proposed half-line monotonicity to $`[-1,1]`$.

**Try it in Lean4Web:** [open the complete proof in one file](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fbapat-lal-q-permanent-lean%2F2d1f9c72f7303f4d8ed4037861df4fa53064b43e%2Flean4web%2FBapatLalLean4Web.lean) (Lean **v4.35.0-rc3**).

## Formal Conjectures targets

[FClikelean/QPermanentMonotonicity.lean](FClikelean/QPermanentMonotonicity.lean)
contains the two statements for Conjectures 1 and 2 with
`category research solved, AMS 15`.
Conjectures 1 and 2 are included in [PR #6857](https://github.com/google-deepmind/formal-conjectures/pull/6857).
Conjecture 2 is a corollary of the same order-144 counterexample.
The module docstring and [PR edit draft](FClikelean/PR_DRAFT.md) cite the known
solutions of Conjectures 3 and 4 as related work.

The Conjecture 1 target is:

```lean
theorem BapatLal.qPermanentMonotonicity :
    answer(False) ↔
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
        A.PosDef → ¬ A.IsDiag →
          StrictMonoOn (fun q : ℝ => (A.qPermanent q).re) (Set.Icc (-1) 1)
```

The complete proof in `lean/Bapat/Main.lean` has this exact statement and name.
The answer sits outside all quantifiers.

The Conjecture 2 target is:

```lean
theorem BapatLal.qPermanentHalfLineMonotonicity :
    answer(False) ↔
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ),
        A.PosDef → ¬ A.IsDiag →
          ∃ ε : ℝ, ε < -1 ∧
            StrictMonoOn (fun q : ℝ => (A.qPermanent q).re) (Set.Ioi ε)
```

Its complete proof is [Bapat/DaFonseca.lean](lean/Bapat/DaFonseca.lean).
Both targets require `¬ A.IsDiag`. The Conjecture 2 proof passes this hypothesis
to the same order-144 counterexample used for Conjecture 1.

The shared definitions are:

```lean
def Equiv.Perm.inversionCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1).card

noncomputable def Matrix.qPermanent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (q : ℝ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), (q ^ σ.inversionCount : ℝ) * ∏ i, A i (σ i)
```

The order on `Fin n` is fixed. Mathlib's `Matrix.PosDef` includes Hermitian
symmetry; `¬ A.IsDiag` supplies the non-diagonal condition. The proof establishes
that the complex q-permanent of a Hermitian matrix is real, so its real part in
the theorem expresses the original question.

The definitions in [Bapat/Statement.lean](lean/Bapat/Statement.lean) are copied
verbatim from the single FC-style statement file. The audit checks their equality
and the type of the compiled FC target. The statement uses `by sorry` for an
externally linked proof; the complete proof has no holes.
See [FClikelean/](FClikelean/) for the statement and PR draft.

## Mathematical explanation (AI generated)

This sketch follows the mathematical identities established by the Lean proof.

**Setting.** Let $`V`$ be the $`144\times2`$ matrix whose ordered rows are
$`(a_i,b_i)`$, with $`a_i\in\mathbb Z`$ and $`b_i\in\mathbb Z[i]`$, supplied in
[the certificate](lean/Bapat/Certificate.lean). Put $`H=VV^*`$ and define

```math
p(z)=\prod_{i=0}^{143}(a_i+b_i z),\qquad
 g(z)=\sum_{i=0}^{143}(143-2i)b_i\prod_{j\ne i}(a_j+b_j z).
```

For a polynomial $`f`$, use the weighted coefficient norm

```math
\|f\|_m^2=\sum_{k=0}^{m}k!(m-k)!\,|[z^k]f|^2.
```

Write $`P=\|p\|_{144}^2`$ and $`S=\|g\|_{142}^2`$.

**Lemma 1 (Gram permanent).** $`\mathrm{per}(H)=P`$.

*Proof sketch.* Expand each Gram entry into its two coordinates. Group the
resulting terms by the number $`k`$ of rows choosing the second coordinate.
There are $`k!(144-k)!`$ permutations matching each pair of such choices. The two
coefficient sums are complex conjugates, giving $`|[z^k]p|^2`$.
This identity is proved for general two-coordinate factors in
[RankTwoPermanent.lean](lean/Bapat/RankTwoPermanent.lean).

**Lemma 2 (endpoint derivative).**

```math
2\left.\frac{d}{dq}P_q(H)\right|_{q=1}=10296P-S,
\qquad 10296=\binom{144}{2}.
```

*Proof sketch.* Differentiating the permutation sum at $`q=1`$ weights each
monomial by its inversion count. For each ordered row pair, swapping the two
rows pairs ascending and descending images. Their difference is a $`2\times2`$
minor times the product over the remaining rows. This gives a general identity
between the endpoint derivative, the permanent, and the sum of paired minors.

For $`H=VV^*`$, the minors factor into row wedges. Applying Lemma 1 to the
complementary rows turns their aggregate into the weighted coefficient norm of

```math
F(z)=\sum_{i\lt j}(a_i b_j-a_j b_i)
                 \prod_{r\ne i,\;r\ne j}(a_r+b_r z).
```

The product rule gives $`F=-g`$, so its squared norm is $`S`$.
[PairMinorIdentity.lean](lean/Bapat/PairMinorIdentity.lean),
[ComplementPermanent.lean](lean/Bapat/ComplementPermanent.lean), and
[WedgePolynomial.lean](lean/Bapat/WedgePolynomial.lean) establish these steps.

**Lemma 3 (exact arithmetic).** $`P>0`$ and $`S>10300P`$.

*Proof sketch.* Multiplying the linear factors recursively computes $`p`$ and
$`g`$ over the Gaussian integers. Lean's kernel checks the resulting coefficient
lists, their weighted norms, and the final inequality. The stored $`P`$ has 768
decimal digits and $`S`$ has 772; their values are verified from the rows.
Consequently $`10296P-S<0`$, and Lemma 2 gives a negative endpoint derivative.

**Theorem (positive definite counterexample).** There are $`\varepsilon>0`$ and
$`-1\le q_1<q_2\le1`$ such that $`A=H+\varepsilon I`$ is Hermitian positive definite,
non-diagonal, and $`P_{q_2}(A)<P_{q_1}(A)`$.

*Proof sketch.* A Gram matrix is positive semidefinite, so $`H+\varepsilon I`$ is
positive definite for every positive $`\varepsilon`$. The endpoint derivative is
continuous in $`\varepsilon`$ and negative at zero, hence remains negative for
some positive $`\varepsilon`$. The entry $`H_{0,1}=9795-1288i`$ remains unchanged by
the diagonal perturbation and proves that $`A`$ is non-diagonal. A differentiable
function that is monotone on $`[-1,1]`$ has a nonnegative derivative at the right
endpoint. The negative derivative therefore yields the stated strict decrease.

**In Lean.** The main shortcuts are an endpoint derivative instead of a full
q-polynomial expansion, counts of permutations preserving two colours, and a
product-rule identity for the wedge polynomial. Polynomial coefficient
recurrences take $`O(n^2)`$ Gaussian-integer operations, rather than enumerating
$`144!`$ permutations; this count excludes the growing bit cost of arithmetic.
Continuity supplies the perturbation existentially, without a prescribed
perturbation size or a second-derivative estimate. The large certificate
computations use `decide +kernel`, and the combinatorial and analytic identities
are proved.

## Files

| Directory | Lean version | Purpose |
|---|---|---|
| [lean/](lean/) | `v4.33.1` | Complete proofs of Conjectures 1–2, with Formal Conjectures pinned to `89294ea0` |
| [lean4web/](lean4web/) | `v4.35.0-rc3` | Complete proof in one Mathlib-only file for Lean4Web |
| [FClikelean/](FClikelean/) | FC `v4.33.1` | Two FC statements, shared definitions, and PR edit draft |

The complete project's entry point is [Bapat.lean](lean/Bapat.lean); the mathematical library is in
[lean/Bapat/](lean/Bapat/). The standalone edition has about 2,100 lines and is
produced by [make_lean4web.py](lean/scripts/make_lean4web.py), which adapts the
conditional-lemma names deprecated in Lean 4.35.

The three scripts in `lean/scripts/` audit the build, generate the standalone
file, and fill publication links. Results are recorded in `lean/evidence/`.

## Verification

FC-compatible proof and audit:

```bash
cd lean
lake update
lake exe cache get
python3 scripts/build_audit.py
```

The audit builds both proof versions, checks the final axioms, compares the
shared definitions and ordered certificates, and compiles the two FC statements
with mathematical linters. It matches the complete Conjecture 1–2 proofs to their
FC targets. Results are in
[lean/evidence/build_results.json](lean/evidence/build_results.json).

For the non-diagonal Conjecture 2 revision, the changed proof and FC module
were built with `--wfail`; compiled target equality and the standard-three
axiom closure were checked. The changed Lean4Web corollary was checked on
`v4.35.0-rc3`. The full single-file build was not rerun for this revision;
the saved full-build records predate it.

Standalone Mathlib/Lean4Web version:

```bash
cd lean4web
lake update
lake exe cache get
lake --wfail build BapatLalLean4Web
```

The complete proof sources have no `sorry`, `admit`, custom axiom or
`native_decide`. The final theorems report only

```text
[propext, Classical.choice, Quot.sound]
```

The pinned Mathlib commits are `0df444a360eaa60ab8c11dca51a86af692955474`
for the FC project and `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22` for Lean4Web.
`python3 lean/scripts/fill_links.py REPOSITORY_URL FULL_COMMIT_SHA`
updates the fixed-commit proof and Lean4Web links.

## Status boundary

Proved here:

```text
The original universal complex Hermitian positive definite conjecture is false.
A counterexample exists at order 144, with A = VV* + εI for some ε > 0.
Its q-permanent strictly decreases between two points of [-1,1].
```

The formal counterexample is existential in the perturbation size and the two
comparison points. The manuscript's particular matrix `B = 10^70 H + I` is proved
positive definite, but its claimed decrease at `q₀ = 1 - 10^-70` is not formalized.
The proof also does not determine the smallest counterexample dimension or give
a counterexample restricted to real symmetric matrices.

This repository records a formal disproof from the supplied certificate.
The local FC-style file and complete Lean proofs here cover Conjectures 1 and 2.
The known solutions of Conjectures 3 and 4 are recorded in the module docstring,
PR edit draft, and related-work references.
[PR #6857](https://github.com/google-deepmind/formal-conjectures/pull/6857) contains
Conjecture 1.

## Sources

- [Bapat–Lal 1994] R. B. Bapat and A. K. Lal,
  [Inequalities for the q-permanent](https://doi.org/10.1016/0024-3795(94)90497-9),
  *Linear Algebra and its Applications* 197–198 (1994), 397–409.
- [da Fonseca 2018] C. M. da Fonseca,
  [The mu-permanent revisited](https://arxiv.org/abs/1804.02231),
  arXiv:1804.02231, Section 4, Conjectures 1–2; Section 5, Conjectures 3–4.
- [Mitchell 2020] L. Mitchell,
  [A note on Bapat's q-permanent conjecture](https://files.ele-math.com/articles/oam-14-56.pdf),
  *Operators and Matrices* 14 (2020), 915–919.
- [Formal Conjectures contribution guide](https://github.com/google-deepmind/formal-conjectures/blob/89294ea02bd7cd678d59984add52cb4baef3dbf4/CONTRIBUTING.md)
  at the pinned FC commit.
- [Ordered certificate](lean/Bapat/Certificate.lean), used by the complete proof.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra and GPT-6.1 sol, and Claude Code using Claude Opus 5.5.

## Appendix: history and related work (AI generated)

The q-permanent has $`P_{-1}(A)=\det(A)`$, $`P_0(A)=\prod_i a_{ii}`$, and
$`P_1(A)=\mathrm{per}(A)`$. Bapat–Lal monotonicity asks whether this entire
interpolation rises strictly for every non-diagonal Hermitian positive definite
matrix. [da Fonseca 2018](https://arxiv.org/abs/1804.02231) surveys its origins
and states the original conjecture separately from the extension to a larger
interval.

### Conjecture 3: Colbrook's counterexample and Stepaniants' Lean proof

Conjecture 3 asks whether the full q-permanent dominates the sum over permutations
preserving any nonempty subset. Matthew J. Colbrook supplied an order-four
positive semidefinite counterexample at $`q=7/8`$. George Stepaniants formalized
its negative answer as `NLA.MI19.not_subsetConjecture`. The module docstring and
PR edit draft cite [the public theorem at revision cd44ce9](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7/matrix-inequalities-and-norms/MI-19/lean/Solution.lean).
[OpenProblemsInNLA MI-19](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-19/README.md)
records the result as Lean verified.

### Conjecture 4: permanent-on-top at q = 1

Bapat and Lal's Conjecture 4 asserts that the largest eigenvalue of the
q-Schur power matrix is the q-permanent for $`q∈[0,1]`$. At $`q=1`$ it includes
the permanent-on-top conjecture, disproved by
[Valery S. Shchesnovich (2016)](https://doi.org/10.1016/j.laa.2015.10.034).
[Tran Hoang Anh's simpler counterexample](https://arxiv.org/abs/2101.03428)
has permanent 504 and largest eigenvalue 512 (Section 4).
The module docstring and PR edit draft cite these published mathematical proofs
as related work. The spectrum computation is supplied by the cited paper.

### Timeline

| Year | Result |
|---|---|
| 1994 | Bapat and Lal publish inequalities for the q-permanent. |
| 2016 | Shchesnovich disproves permanent-on-top, which refutes Conjecture 4 at `q = 1`. |
| 2018 | Da Fonseca's survey lists four conjectures: 1, 3, and 4 are Bapat–Lal's; 2 is da Fonseca's extension. |
| 2020 | Mitchell studies the passage between singular positive semidefinite and positive definite matrices, and proves cases of the PSD extension. |
| 2021 | Tran Hoang Anh gives the simpler permanent-on-top counterexample with permanent 504 and largest eigenvalue 512. |
| 2026 | This repository verifies the order-144 counterexample and the Conjecture 2 corollary in Lean. |

The literature establishes monotonicity for matrices of order at most three and
for tridiagonal positive definite matrices. Mitchell proves the PSD extension
for rank-one matrices and for order three, and explains how a failure for a
singular PSD matrix can lead to a positive definite counterexample.
These are earlier mathematical results, summarized in
[Mitchell's paper](https://files.ele-math.com/articles/oam-14-56.pdf).

The present proof uses a two-coordinate Gram matrix and a negative derivative
at $`q=1`$. Adding a sufficiently small positive multiple of the identity then
reaches the positive definite class required by Conjecture 1. Any half-line
$`(ε,\infty)`$ with $`ε<-1`$ contains $`[-1,1]`$, so the same counterexample
also disproves Conjecture 2.
