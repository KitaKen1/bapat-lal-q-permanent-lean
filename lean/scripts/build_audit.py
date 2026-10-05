"""Build both complete proofs and audit the FC-style statement."""

from pathlib import Path
import ast
import datetime
import hashlib
import json
import os
import re
import subprocess
import time

LEAN = Path(__file__).resolve().parents[1]
ROOT = LEAN.parent
FC = ROOT / "FClikelean/QPermanentMonotonicity.lean"
EVIDENCE = LEAN / "evidence"
EVIDENCE.mkdir(exist_ok=True)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def require(condition, message):
    if not condition:
        raise ValueError(message)


def definition(text):
    start = text.index("/-- The number of inversions")
    return text[start:].split("namespace BapatLal", 1)[0].strip()


def target(text, name="qPermanentMonotonicity"):
    match = re.search(r"theorem " + re.escape(name) + r"\s*:\s*([\s\S]*?)\s*:= by", text)
    require(match is not None, "Missing target theorem")
    return re.sub(r"\s+", " ", match.group(1)).strip()


def uncomment(text):
    result, depth, pos = [], 0, 0
    while pos < len(text):
        if text.startswith("/-", pos):
            depth += 1
            pos += 2
        elif depth and text.startswith("-/", pos):
            depth -= 1
            pos += 2
        elif depth:
            pos += 1
        elif text.startswith("--", pos):
            end = text.find("\n", pos)
            pos = len(text) if end == -1 else end
        elif text[pos] == '"':
            pos += 1
            while pos < len(text):
                if text[pos] == "\\":
                    pos += 2
                elif text[pos] == '"':
                    pos += 1
                    break
                else:
                    pos += 1
        else:
            result.append(text[pos])
            pos += 1
    require(depth == 0, "Unclosed comment")
    return "".join(result)


main = (LEAN / "Bapat/Main.lean").read_text()
half_line = (LEAN / "Bapat/DaFonseca.lean").read_text()
web = (ROOT / "lean4web/BapatLalLean4Web.lean").read_text()
statement = FC.read_text()
require(definition(statement) == definition((LEAN / "Bapat/Statement.lean").read_text()),
        "Definitions differ from the FC statement")
require(target(statement) == target(main) == target(web), "Theorem statements differ")
require(target(statement, "qPermanentHalfLineMonotonicity") ==
        target(half_line, "qPermanentHalfLineMonotonicity") ==
        target(web, "qPermanentHalfLineMonotonicity"), "Conjecture 2 statements differ")
sources = [LEAN / "Bapat.lean", *sorted((LEAN / "Bapat").glob("*.lean")),
           ROOT / "lean4web/BapatLalLean4Web.lean"]
for path in sources:
    require(not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|opaque|constant)\b",
                          uncomment(path.read_text())), f"Proof hole or custom axiom: {path}")


def certificate(text):
    rows = re.search(r"def rows : List \(Int × Int × Int\) :=\s*(\[[\s\S]*?\])", text)
    require(rows is not None, "Missing ordered rows")
    rows = ast.literal_eval(rows.group(1))
    require(len(rows) == 144, "Wrong certificate dimension")
    return rows, [int(re.search(rf"def expected{name} : Int := (\d+)\b", text).group(1))
                  for name in ("P", "S")]


require(certificate((LEAN / "Bapat/Certificate.lean").read_text()) == certificate(web),
        "Standalone certificate differs from the main proof")
start = time.monotonic()
results, outputs = {}, {}
with (EVIDENCE / "build.log").open("w") as log:
    def run(label, args, cwd=LEAN, env=None):
        command = " ".join(args).replace(str(ROOT), ".")
        log.write(f"\n{label}: {command}\n")
        log.flush()
        proc = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True)
        output = proc.stdout + proc.stderr
        # Keep published records free of local absolute paths.
        output = output.replace(str(ROOT), ".")
        log.write(output)
        log.write(f"Exit code: {proc.returncode}\n")
        log.flush()
        results[label] = proc.returncode
        outputs[label] = output
        print(f"{label}: exit {proc.returncode}", flush=True)
        if proc.returncode:
            print(output, flush=True)
        return proc

    build = run("main_proof", ["lake", "--wfail", "build", "Bapat"])
    standalone = run("lean4web", ["lake", "--wfail", "build", "BapatLalLean4Web"], ROOT / "lean4web")
    if build.returncode == 0:
        env = os.environ.copy()
        paths = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=LEAN, text=True).strip()
        env["LEAN_PATH"] = paths + os.pathsep + str(LEAN / ".lake")
        temporary = LEAN / ".lake/FCStatement.lean"
        temporary.write_text(statement)
        linters = ["namespace", "stubs", "openClassical",
                   "ams_attribute", "category_attribute", "category_answer", "conditional_formal_proof",
                   "moduleDocstring", "latex_docstring", "imports"]
        flags = ["-DautoImplicit=false", "-Dwarn.sorry=false", "-DwarningAsError=true"]
        flags += [f"-Dweak.linter.style.{name}=true" for name in linters]
        fc = run("fc_statement", ["lean", *flags, "-R", ".lake", str(temporary),
                                  "-o", ".lake/FCStatement.olean"], env=env)
        if fc.returncode == 0:
            check = main.replace("import Bapat.Statement", "import FCStatement")
            check += "\n" + half_line.replace("import Bapat.Main\n", "").replace("/-!", "/-", 1)
            check = check.replace("namespace BapatLal", "namespace BapatFCValidation")
            check = check.replace("end BapatLal", "end BapatFCValidation")
            for name in ("qPermanentMonotonicity", "qPermanentHalfLineMonotonicity"):
                check += f'''\nrun_meta do
  let fc ← Lean.getConstInfo ``BapatLal.{name}
  let proof ← Lean.getConstInfo ``BapatFCValidation.{name}
  unless ← Lean.Meta.isDefEq fc.type proof.type do
    throwError "Compiled FC target differs from the complete proof"
  Lean.logInfo "Compiled FC target {name} and complete proof have definitionally equal types"
'''
            checker = LEAN / ".lake/FCTypeCheck.lean"
            checker.write_text(check)
            run("compiled_target", ["lean", "-DwarningAsError=true", "-R", ".lake", str(checker)], env=env)


axioms = {}
for label, output in outputs.items():
    axioms[label] = {name: [v.strip() for v in values.split(",") if v.strip()]
                    for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)}
required = {
    "main_proof": ["BapatLal.qPermanentMonotonicity", "BapatLal.qPermanentHalfLineMonotonicity"],
    "lean4web": ["BapatLal.qPermanentMonotonicity", "BapatLal.qPermanentHalfLineMonotonicity"],
    "compiled_target": ["BapatFCValidation.qPermanentMonotonicity",
                        "BapatFCValidation.qPermanentHalfLineMonotonicity"],
}
axiom_ok = all(name in axioms.get(label, {}) and set(axioms[label][name]) <= ALLOWED
               for label, names in required.items() for name in names)
ok = all(results.get(label) == 0 for label in (
    "main_proof", "lean4web", "fc_statement", "compiled_target"
)) and axiom_ok
result = {
    "status": "PASS" if ok else "FAIL",
    "checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "exit_codes": results,
    "elapsed_seconds": round(time.monotonic() - start, 2),
    "timing_note": "Includes dependency loading and cached modules.",
    "lean_version": (LEAN / "lean-toolchain").read_text().strip(),
    "lean4web_version": (ROOT / "lean4web/lean-toolchain").read_text().strip(),
    "axiom_audit_passed": axiom_ok,
    "axioms": {label: {name: axioms.get(label, {}).get(name) for name in names}
               for label, names in required.items()},
    "definitions_and_statements_match": True,
    "certificate_copies_match": True,
    "fc_targets_compiled": ["qPermanentMonotonicity", "qPermanentHalfLineMonotonicity"],
    "source_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                      for path in [*sources, FC]},
}
(EVIDENCE / "build_results.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"status": result["status"], "exit_codes": results, "axiom_audit_passed": axiom_ok}))
raise SystemExit(0 if ok else 1)
