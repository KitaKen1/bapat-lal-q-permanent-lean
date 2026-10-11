# Lean Comparator evidence: run 38145168157, attempt 1

The public `main` verification completed successfully on 11 October 2026.
This archive preserves its original artifact, all workflow logs, and GitHub's
API records in Git so readers can inspect them after Actions retention expires.
The records refer to the tested commit below. The later commit adding this
archive is a documentation/evidence change.

| Item | Recorded value |
|---|---|
| Repository | `KitaKen1/bapat-lal-q-permanent-lean` |
| Workflow | `Comparator verification` |
| Run / attempt | `38145168157` / `1` |
| Branch / event | `main` / `push` |
| Tested commit | `0179c028957e0214c2af1741d01088ffa5ae65d5` |
| Unchanged linked proof commit | `2d1f9c72f7303f4d8ed4037861df4fa53064b43e` |
| FC challenge revision | `161294082da9cded42153cf8718e7688c6bc022a` |
| Job | `comparator`, ID `114486881308` |
| Run / job conclusion | `success` / `success` |
| Receipt status | `PASS` |
| Artifact | `comparator-38145168157-1`, ID `11705120766` |
| Original artifact bytes | `13089` |
| Original GitHub artifact expiry | `2027-01-09T13:56:24Z` |

Original online records:
[run](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/actions/runs/38145168157),
[job](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/actions/runs/38145168157/job/114486881308),
[tested source](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/tree/0179c028957e0214c2af1741d01088ffa5ae65d5).

## What is saved

| File or directory | Contents |
|---|---|
| [comparator-38145168157-1.zip](comparator-38145168157-1.zip) | Original downloaded artifact ZIP, preserved byte for byte |
| [receipt/](receipt/) | All nine original artifact members, extracted without alteration |
| [github/run.json](github/run.json) and [attempt-1.json](github/attempt-1.json) | Original GitHub API response bodies for the run and attempt |
| [github/jobs.json](github/jobs.json) and [job-114486881308.json](github/job-114486881308.json) | Complete job list and the job's individual step conclusions |
| [github/artifacts.json](github/artifacts.json) and [artifact-11705120766.json](github/artifact-11705120766.json) | Artifact identity, tested commit, size, expiry and GitHub-reported digest |
| [github/run-38145168157-attempt-1-logs.zip](github/run-38145168157-attempt-1-logs.zip) | Complete workflow-attempt log ZIP downloaded from GitHub |
| [github/logs/](github/logs/) | Every member of the log ZIP, including setup, installation, comparison, upload and cleanup logs |
| [github/job-114486881308.log](github/job-114486881308.log) | Complete timestamped job log also downloaded from the job-log endpoint |
| [provenance.json](provenance.json) | Locally generated retrieval index: API URLs, retrieval times, selected response headers, sizes and hashes |
| [SHA256SUMS](SHA256SUMS) | Checksums for every other file in this archive, including this guide |

The attempt contained one job. Both the complete workflow log archive and that
job's full log are saved; `receipt/comparator.log` alone covers only the
Comparator invocation. API response bodies and downloaded archives/logs are
preserved as retrieved. This guide, `provenance.json` and `SHA256SUMS` were
generated locally during archival.

## How to check the result

1. Read [run.json](github/run.json), [attempt-1.json](github/attempt-1.json) and
   [job-114486881308.json](github/job-114486881308.json). Match the run ID,
   attempt, `head_sha`, `main` branch and `success` conclusions. The step named
   `Compare both FC targets, audit axioms, and replay the Lean kernel` succeeded.
2. Read [config.json](receipt/config.json). Both
   `BapatLal.qPermanentMonotonicity` and
   `BapatLal.qPermanentHalfLineMonotonicity` are targets. The permitted axioms
   are `propext`, `Classical.choice` and `Quot.sound`.
3. Read [input-check.json](receipt/input-check.json),
   [pins.json](receipt/pins.json) and [proof.diff](receipt/proof.diff).
   The input check passed; the 23 protected proof/toolchain/manifest files have
   their recorded hashes and were unchanged from the linked proof commit.
   `proof.diff` is intentionally empty. The challenge hash identifies the exact
   FC target file, which is also included as [Challenge.lean](receipt/Challenge.lean).
4. Read [comparator.log](receipt/comparator.log). Both final theorem names
   report `[propext, Classical.choice, Quot.sound]`. Its final output includes
   `Lean default kernel accepts the solution`, `Your solution is okay!` and
   `Finished with result: success`. [status.txt](receipt/status.txt) is `PASS`.
   The complete timestamped [job log](github/job-114486881308.log) includes the
   same output and the artifact upload digest.
5. Inspect [workflow.yml](receipt/workflow.yml) and the
   [launcher at the tested commit](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/blob/0179c028957e0214c2af1741d01088ffa5ae65d5/comparator/run-check.sh).
   A nonzero Comparator or log-pipeline exit fails the job. In
   [the pinned Comparator source](https://github.com/leanprover/comparator/blob/ca04cfc72b550331658ec314bf47685281bfd4bf/Main.lean),
   comparison and the axiom audit must pass before the kernel is replayed and
   `Your solution is okay!` is printed. The axiom audit has no separate success
   message; its completion follows from this control flow and final success.

These checks verify the two formal negative answers (`answer(False)`) using
the three standard axioms. They concern Conjectures 1 and 2. This run used the
builtin Lean kernel; no additional external kernel was configured.

## Check the archive's hashes

From a clone of this repository containing the archive:

```bash
cd ComparatorLog20261011
shasum -a 256 -c SHA256SUMS
```

On Linux, `sha256sum -c SHA256SUMS` is an alternative. Every entry should report
`OK`. The checksum list covers the entire archive except itself. Compare the
original artifact checksum with `digest` in
[GitHub's artifact snapshot](github/artifact-11705120766.json):

```text
sha256:4e3a7c64260c10da03fbba990c6544730d019f02f25100bb90d754bcfe589993
```

The downloaded artifact's checksum was checked against GitHub's API digest
before this archive was committed. Its extracted receipt is identical to the
ZIP members, and all extracted workflow logs match the original log ZIP members.

## Independently rerun the tested source

Use a fresh Ubuntu 24.04 machine with `git`, `curl`, Python 3, Go, `sudo` and
systemd, network access, and sufficient disk space for two Lean toolchains and
Mathlib. The launcher needs a working system systemd service manager. Clone
with full history so the pinned proof commit is available:

```bash
git clone https://github.com/KitaKen1/bapat-lal-q-permanent-lean.git comparator-reproduction
cd comparator-reproduction
git checkout --detach 0179c028957e0214c2af1741d01088ffa5ae65d5
export COMPARATOR_TOOLS="$(mktemp -d)"
python3 comparator/check-inputs.py --receipt-dir comparator-receipt
bash comparator/install-tools.sh
bash comparator/run-check.sh
cat comparator-receipt/status.txt
```

The expected status is `PASS`; confirm the same two theorem dependency reports
and final kernel/Comparator success messages in the newly generated log.
The dependency and tool source revisions are pinned in `comparator/pins.json`;
the environment used by the original run is saved in
[environment.txt](receipt/environment.txt). Downloads and operating-system
packages remain external requirements. This archive preserves the records and
source references; it does not include all tool binaries and build dependencies.

Git storage keeps these saved files beyond Actions retention while the
repository/history is retained, and readers can clone them for their own copy.
The saved API responses are unsigned snapshots. Hashes establish byte identity
with the recorded digest and detect changes relative to this committed archive;
they are not a cryptographic attestation of the historical execution. Readers
can inspect the original GitHub record while available and independently
reproduce the proof verification from the tested source afterwards.
