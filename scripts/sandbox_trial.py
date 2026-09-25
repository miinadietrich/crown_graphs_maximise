#!/usr/bin/env python3
"""Run small positive and negative controls through the release validation pipeline."""
from pathlib import Path
import argparse
import json
import shutil
import subprocess
import sys
from common import ROOT, save


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work-dir", type=Path, required=True, help="New directory outside the release")
    parser.add_argument("--tools", type=Path, required=True)
    parser.add_argument("--dependency-cache", type=Path, required=True)
    parser.add_argument("--project", type=Path, default=ROOT / "lean")
    args = parser.parse_args()
    root = args.work_dir.resolve()
    if root.exists():
        parser.error("Use a new control directory")
    root.mkdir(parents=True)
    results = []
    for name, proof in [("positive", "by rfl"), ("negative", "by sorry")]:
        project = root / (name + "-source")
        project.mkdir()
        for filename in ("lean-toolchain", "lake-manifest.json"):
            shutil.copy2(args.project / filename, project / filename)
        lakefile = (args.project / "lakefile.toml").read_text().split("[[lean_lib]]", 1)[0]
        lakefile += ''.join('\n[[lean_lib]]\nname = "' + n + '"\n' for n in ("Challenge", "Solution", "TrialA", "TrialB"))
        (project / "lakefile.toml").write_text(lakefile)
        (project / "Challenge.lean").write_text("import Mathlib.Data.Finset.Card\nnamespace ReleaseTrial\ntheorem identity (n : Nat) : n = n := by rfl\nend ReleaseTrial\n")
        for mod in ("TrialA", "TrialB"):
            (project / (mod + ".lean")).write_text("import Lean\n#eval IO.sleep 1500\n")
        (project / "Solution.lean").write_text("import Mathlib.Data.Finset.Card\nimport TrialA\nimport TrialB\nnamespace ReleaseTrial\ntheorem identity (n : Nat) : n = n := " + proof + "\nend ReleaseTrial\n#print axioms ReleaseTrial.identity\n")
        save(project / "full-comparator.json", {"challenge_module": "Challenge", "solution_module": "Solution",
             "theorem_names": ["ReleaseTrial.identity"], "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"], "enable_nanoda": False})
        command = [sys.executable, str(ROOT / "scripts/validate.py"), "--project", str(project),
                   "--stage", str(root / (name + "-stage")), "--tools", str(args.tools.resolve()),
                   "--dependency-cache", str(args.dependency_cache.resolve())]
        result = subprocess.run(command)
        logfile = root / (name + "-stage/.lake/validation/comparator.log")
        text = logfile.read_text() if logfile.exists() else ""
        accepted = result.returncode == 0 if name == "positive" else result.returncode != 0 and "Illegal axiom detected: 'sorryAx'" in text
        results.append({"case": name, "command": command, "exit_code": result.returncode, "control_passed": accepted})
        save(root / "controls.json", results)
        if not accepted:
            raise SystemExit(f"{name} control failed; inspect its full output")
    print("Positive control accepted; negative control rejected for its unpermitted axiom")


if __name__ == "__main__":
    main()
