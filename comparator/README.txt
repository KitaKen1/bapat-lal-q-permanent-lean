Comparator verification for FC PR #6857

The proof stays at 2d1f9c72f7303f4d8ed4037861df4fa53064b43e.
Challenge.lean is an exact copy of the FC file at PR head 1612940.
Both BapatLal.qPermanentMonotonicity and
BapatLal.qPermanentHalfLineMonotonicity are listed in lean/comparator.json.

First push the comparator-verification branch to the separate PRIVATE repository:
  https://github.com/KitaKen1/bapat-lal-q-permanent
Check its Actions tab for the "Comparator verification" workflow.
The workflow also has a manual "Run workflow" trigger once uploaded.
PASS in the receipt and a successful job are required before the public run.

After the private run succeeds, push the same verification commit to a branch
of the PUBLIC proof repository. Run the workflow there and check it again.
Download the public run's comparator-* artifact. Preserve the extracted files
under lean/evidence/comparator/<run-id>/ in the public repository.
Adding only those receipt files does not trigger another verification run.

Reply to the FC review with the PUBLIC run URL, permanently saved receipt URL,
verification commit, linked proof commit, both theorem names, FC challenge
commit, and the links to this configuration and workflow.
The public receipt includes the axiom policy, source hashes, tool revisions,
environment, kernel/comparison output, and the empty proof diff.

The proof is built only inside Comparator's landrun sandbox on a fresh runner.
Only the trusted Mathlib cache is fetched beforehand. No Bapat build is cached.
The systemd launcher uses --uid/--gid because the runner has no user session;
the Comparator process runs as the unprivileged runner user with AF_UNIX blocked.
lean4export is rebuilt with the exact proof toolchain (Lean v4.33.1).
Comparator itself uses its own pinned toolchain. The builtin Lean kernel is used;
no additional external kernel (such as nanoda) is configured.

If the FC statement changes, refresh Challenge.lean, its commit and hash in
pins.json, and rerun both verifications. If proof changes become necessary,
update the FC proof links and provenance before claiming verification.

Preparation and input checks do not constitute a successful Comparator run.
Until GitHub Actions is actually run, the CI configuration remains untested.

Sources:
https://github.com/google-deepmind/formal-conjectures/pull/6857#pullrequestreview-5466490199
https://github.com/leanprover/comparator/blob/ca04cfc72b550331658ec314bf47685281bfd4bf/README.md
