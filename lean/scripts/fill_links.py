"""Fill stable proof and Lean4Web links after publication."""

import argparse
from pathlib import Path
import re
from urllib.parse import quote, urlparse

ROOT = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser()
parser.add_argument("repository", help="Published repository URL, https://github.com/OWNER/REPO")
parser.add_argument("commit", help="Full 40-character commit SHA containing these files")
args = parser.parse_args()
url = urlparse(args.repository.rstrip("/"))
if url.scheme != "https" or url.netloc != "github.com" or not re.fullmatch(
    r"/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", url.path
):
    parser.error("Use an HTTPS GitHub repository URL without query or fragment")
if url.query or url.fragment or not re.fullmatch(r"[0-9a-fA-F]{40}", args.commit):
    parser.error("Use a full 40-character commit SHA and a plain repository URL")
repo = args.repository.rstrip("/")
proofs = {}
for name, filename in (("qPermanentMonotonicity", "lean/Bapat/Main.lean"),
                       ("qPermanentHalfLineMonotonicity", "lean/Bapat/DaFonseca.lean")):
    lines = (ROOT / filename).read_text().splitlines()
    line = next(i for i, s in enumerate(lines, 1) if s.startswith("theorem " + name))
    proofs[name] = f"{repo}/blob/{args.commit}/{filename}#L{line}"
proof = proofs["qPermanentMonotonicity"]
raw = f"https://raw.githubusercontent.com{url.path}/{args.commit}/lean4web/BapatLalLean4Web.lean"
live = "https://live.lean-lang.org/#url=" + quote(raw, safe="")
print(f"Proof: {proof}")
print(f"Half-line proof: {proofs['qPermanentHalfLineMonotonicity']}")
print(f"Lean4Web (select v4.35.0-rc3): {live}")
print(f'FC attribute: @[formal_proof using lean4 at "{proof}"]')
readme = ROOT / "README.md"
text = readme.read_text()
text = re.sub(r"(\*\*Try it in Lean4Web:\*\* \[open the complete proof in one file\]\()[^)]+(\))",
              lambda m: m.group(1) + live + m.group(2), text)
text = text.replace(
    "The link opens the published revision. The revised non-diagonal Conjecture 2\n"
    "is in the local [Lean4Web file](lean4web/BapatLalLean4Web.lean).\n", "")
readme.write_text(text)
fc = ROOT / "FClikelean/QPermanentMonotonicity.lean"
text = fc.read_text()
for name, proof_url in proofs.items():
    pattern = (r'@\[category research solved, AMS 15'
               r'(?:,\s*formal_proof using lean4 at "[^"]+")?\]\s*'
               + r'(?=theorem ' + re.escape(name) + r'\s*:)')
    text, count = re.subn(pattern,
        lambda _: f'@[category research solved, AMS 15,\n    formal_proof using lean4 at "{proof_url}"]\n',
        text)
    if count != 1:
        raise ValueError(f"Expected exactly one FC statement for {name}")
fc.write_text(text)
draft = ROOT / "FClikelean/PR_DRAFT.md"
text = draft.read_text()
if "This PR makes two contributions:" in text:
    # Preserve the two-part PR format and its final related-work NOTE.
    for labels, label, url in (
        (("Complete proof of Conjecture 1",), "Complete proof of Conjecture 1", proof),
        (("Complete proof of Conjecture 2", "Published counterexample used for Conjecture 2"),
         "Complete proof of Conjecture 2", proofs["qPermanentHalfLineMonotonicity"]),
        (("GitHub repository",), "GitHub repository", repo),
        (("open in your browser",), "open in your browser", live),
    ):
        pattern = r"\[(?:" + "|".join(re.escape(value) for value in labels) + r")\]\([^)]+\)"
        text, count = re.subn(pattern, lambda _: f"[{label}]({url})", text)
        if count != 1:
            raise ValueError(f"Expected exactly one draft link for {label}")
else:
    for label, url in (("Proof", proof), ("Half-line proof", proofs["qPermanentHalfLineMonotonicity"]),
                       ("Repository", repo), ("Lean4Web", live)):
        suffix = r"(?: \(local\))?" if label == "Half-line proof" else ""
        value = f"[open in your browser]({url}) (v4.35.0-rc3)" if label == "Lean4Web" else url
        text, count = re.subn(r"^" + re.escape(label) + suffix + r":.*$",
                             label + ": " + value, text, flags=re.M)
        if count != 1:
            raise ValueError(f"Expected exactly one draft link for {label}")
text = text.replace(
    "The revised non-diagonal Conjecture 2 proof is in the local `lean/Bapat/DaFonseca.lean` "
    "and Lean4Web files. The links above still open the published revision.\n\n", "")
draft.write_text(text)
fc_readme = ROOT / "FClikelean/README.md"
text = fc_readme.read_text().replace(
    "The FC statements use `by sorry`. Both `formal_proof` links currently cite the\n"
    "published Conjecture 1 proof: its non-diagonal counterexample also refutes\n"
    "Conjecture 2. The revised Conjecture 2 proof is complete locally in\n"
    "[Bapat/DaFonseca.lean](../lean/Bapat/DaFonseca.lean).",
    "The FC statements use `by sorry`, with `formal_proof` links to the two\n"
    "published complete Lean proofs at a fixed commit.")
fc_readme.write_text(text)
print("Updated the two local proof links, README, and PR draft; preserved the related-work references in the docstring and PR draft. The specified commit must already be public.")
