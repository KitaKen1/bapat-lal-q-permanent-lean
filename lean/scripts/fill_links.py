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
lines = (ROOT / "lean/Bapat/Main.lean").read_text().splitlines()
line = next(i for i, s in enumerate(lines, 1) if s.startswith("theorem qPermanentMonotonicity"))
proof = f"{repo}/blob/{args.commit}/lean/Bapat/Main.lean#L{line}"
raw = f"https://raw.githubusercontent.com{url.path}/{args.commit}/lean4web/BapatLalLean4Web.lean"
live = "https://live.lean-lang.org/#url=" + quote(raw, safe="")
print(f"Proof: {proof}")
print(f"Lean4Web (select v4.35.0-rc3): {live}")
print(f'FC attribute: @[formal_proof using lean4 at "{proof}"]')
readme = ROOT / "README.md"
text = readme.read_text()
text = re.sub(r"(\*\*Try it in Lean4Web:\*\* \[open the complete proof in one file\]\()[^)]+(\))",
              lambda m: m.group(1) + live + m.group(2), text)
readme.write_text(text)
fc = ROOT / "FClikelean/QPermanentMonotonicity.lean"
text = re.sub(r'@\[formal_proof using lean4 at "[^"]+"\]\n', "", fc.read_text())
text = text.replace("@[category research solved, AMS 15]",
                    f'@[formal_proof using lean4 at "{proof}"]\n@[category research solved, AMS 15]')
fc.write_text(text)
draft = ROOT / "FClikelean/PR_DRAFT.md"
text = draft.read_text()
for label, url in (("Proof", proof), ("Repository", repo), ("Lean4Web", live)):
    text = re.sub(r"^" + label + r":.*$", label + ": " + url, text, flags=re.M)
draft.write_text(text)
print("Updated README, FC statement, and PR draft. The specified commit must already be public.")
