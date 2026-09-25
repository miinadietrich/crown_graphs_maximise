#!/usr/bin/env python3
"""Check a fresh release copy with pinned Comparator and collect public axiom reports."""
from pathlib import Path
import argparse
import ctypes
import json
import os
import platform
import re
import shlex
import shutil
import subprocess
import sys
import time
from common import ROOT, configuration, digest, inventory, output, save, source_pin, utc, verify_inventory
from check_axioms import audit


def comparator_acceptance(logfile, config):
    text = logfile.read_text(encoding="utf-8")
    lines = text.splitlines()
    markers = ["Building Challenge", "Lean default kernel accepts the solution", "Your solution is okay!"]
    if any(lines.count(marker) != 1 for marker in markers):
        raise RuntimeError("Missing or duplicated Comparator build/kernel/success marker")
    exports = {}
    positions = {}
    for match in re.finditer(r"^Exporting #\[([^\]]*)\] from (Challenge|Solution)$", text, re.M):
        module = match[2]
        if module in exports:
            raise RuntimeError(f"Duplicate export marker: {module}")
        exports[module] = [x.strip() for x in match[1].split(",")]
        positions[module] = match.start()
    names = config["theorem_names"]
    if set(exports) != {"Challenge", "Solution"} or exports["Challenge"] != exports["Solution"]:
        raise RuntimeError("Challenge and Solution export inventories differ")
    primitives = ["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble",
                  "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce"]
    expected = names + config["permitted_axioms"] + primitives
    if exports["Challenge"] != expected:
        raise RuntimeError("Comparator exported a different theorem list")
    if not text.index(markers[0]) < positions["Challenge"] < positions["Solution"] < text.index(markers[1]) < text.index(markers[2]):
        raise RuntimeError("Comparator phase markers are out of order")
    return {"exports": exports, "kernel_acceptance": markers[1], "success": markers[2], "log_sha256": digest(logfile)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=ROOT / "lean")
    parser.add_argument("--tools", type=Path, required=True, help="installation.json from install_tools.py")
    parser.add_argument("--stage", type=Path, required=True, help="New directory on a Linux filesystem")
    parser.add_argument("--dependency-cache", type=Path, help="Trusted pinned .lake/packages directory, mounted by read-only sandbox access")
    parser.add_argument("--copy-dependencies", action="store_true", help="Copy the supplied cache instead of linking to it")
    parser.add_argument("--prepare-only", action="store_true", help="Prepare inputs and dependencies without running Comparator")
    parser.add_argument("--prepared", action="store_true", help="Run a previously prepared stage that has never started Comparator")
    parser.add_argument("--reuse-build-from", type=Path, help="Reuse unchanged Solution compilation from a preserved failed fresh-build check")
    parser.add_argument("--challenge-change", action="append", default=[], help="Reviewed changed Challenge input relative to the Lean project; repeat for each changed file")
    args = parser.parse_args()
    if platform.system() != "Linux" or os.getuid() == 0:
        parser.error("Run as an unprivileged Linux user with a working systemd user session")
    if args.copy_dependencies and not args.dependency_cache:
        parser.error("--copy-dependencies requires --dependency-cache")
    if args.prepared and args.prepare_only:
        parser.error("Choose either --prepared or --prepare-only")
    if args.reuse_build_from and (args.prepared or args.prepare_only):
        parser.error("Compilation reuse requires a complete new check")
    if bool(args.reuse_build_from) != bool(args.challenge_change):
        parser.error("Compilation reuse requires an explicit reviewed Challenge change list")
    project = args.project.resolve(strict=True)
    stage = args.stage.resolve()
    if stage == project or project in stage.parents or stage in project.parents:
        parser.error("The fresh stage must be outside the source project")
    tools = json.loads(args.tools.read_text())
    installation_hash = digest(args.tools)
    pins = json.loads((ROOT / "tools/pins.json").read_text())
    if tools["pins"] != pins or tools["pins_sha256"] != digest(ROOT / "tools/pins.json"):
        parser.error("The installed checking tools do not match the release pins")
    def tools_identity():
        if digest(args.tools) != installation_hash:
            raise RuntimeError("Tool installation metadata changed during the run")
        for entry in list(tools["binaries"].values()) + tools["wrappers"]["files"]:
            if digest(entry["path"]) != entry["sha256"]:
                raise RuntimeError(f"Checking tool changed: {entry['path']}")
        if set(tools["sources"]) != {"comparator", "lean4export", "landrun"}:
            raise RuntimeError("Unexpected checking-tool source inventory")
        for name, source in tools["sources"].items():
            source_pin(source["path"], pins[name]["rev"],
                       ("lean-toolchain", "lakefile.toml", "lake-manifest.json") if name == "comparator" else ())
        comp = Path(tools["sources"]["comparator"]["path"])
        original = output(["git", "-c", "safe.directory=" + str(comp), "-C", comp, "show", "HEAD:lakefile.toml"])
        expected = original.replace('rev = "master"', 'rev = "' + pins["lean4export"]["rev"] + '"')
        if (comp / "lakefile.toml").read_text().strip() != expected.strip() or (comp / "lean-toolchain").read_text().strip() != pins["lean"]:
            raise RuntimeError("Comparator configuration differs from the pinned build recipe")
        packages = json.loads((comp / "lake-manifest.json").read_text())["packages"]
        if len(packages) != 1 or packages[0]["rev"] != pins["lean4export"]["rev"]:
            raise RuntimeError("Comparator dependency manifest differs from the export pin")
    tools_identity()
    runner_inputs = inventory(ROOT / "scripts")
    pins_hash = digest(ROOT / "tools/pins.json")
    if (project / "lean-toolchain").read_text().strip() != pins["lean"]:
        parser.error(f"The project must select {pins['lean']}")
    config = configuration(project)
    solution = (project / "Solution.lean").read_text(encoding="utf-8-sig")
    printed = re.findall(r"^\s*#print\s+axioms\s+(\S+)", solution, re.M)
    if set(printed) != set(config["theorem_names"]) or len(printed) != len(set(printed)):
        parser.error("Solution.lean must print exactly the configured public axiom reports")
    release_manifest = ROOT / "release-manifest.json"
    if release_manifest.exists():
        verify_inventory(ROOT, json.loads(release_manifest.read_text())["files"])
    inputs = inventory(project)
    def verify_project(path):
        verify_inventory(path, inputs)
        if inventory(path) != inputs:
            raise RuntimeError(f"Project input inventory changed: {path}")
    real = Path(tools["toolchain"])
    wrapped_lake = Path(tools["wrappers"]["path_entry"]) / "lake"
    env = dict(os.environ, ELAN_TOOLCHAIN=pins["lean"], LEAN_NUM_THREADS="1")
    results = stage / ".lake/validation"
    if args.prepared:
        previous = json.loads((results / "result.json").read_text())
        if previous.get("status") != "prepared" or (results / "comparator.log").exists():
            parser.error("This stage is not an unused prepared stage")
        expected = json.loads((results / "project-inputs.json").read_text())["files"]
        if inputs != expected:
            parser.error("The release inputs have changed since stage preparation")
        verify_project(stage)
    else:
        if stage.exists():
            parser.error("Refusing an existing stage; use a new directory or --prepared for an unused prepared stage")
        stage.mkdir(parents=True)
        for entry in inputs:
            target = stage / entry["path"]
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(project / entry["path"], target)
        results.mkdir(parents=True)
        save(results / "project-inputs.json", {"algorithm": "sha256", "files": inputs})
    report = {"status": "preparing", "started": utc(), "project": str(project), "stage": str(stage),
              "compilation_mode": "reused_project_artifacts" if args.reuse_build_from else "fresh",
              "release_manifest_sha256": digest(release_manifest) if release_manifest.exists() else None,
              "project_manifest_sha256": digest(results / "project-inputs.json"),
              "runner_inputs": {"root": str(ROOT / "scripts"), "files": runner_inputs},
              "pins_sha256": pins_hash,
              "tools_sha256": digest(args.tools), "tools": tools,
              "target_count": len(config["theorem_names"]), "commands": []}
    save(results / "result.json", report)

    def run(label, command, cwd=stage):
        command = [str(x) for x in command]
        logfile = results / (label + ".log")
        if logfile.exists():
            raise RuntimeError(f"Refusing to overwrite {logfile}")
        item = {"label": label, "command": command, "cwd": str(cwd), "started": utc(),
                "log": logfile.name, "exit_code": None}
        report["commands"].append(item); save(results / "result.json", report)
        print(f"Starting {label}; output: {logfile}", flush=True)
        start = time.monotonic()
        with logfile.open("x", encoding="utf-8") as stream:
            process = subprocess.Popen(command, cwd=cwd, env=env, stdout=stream, stderr=subprocess.STDOUT)
            item["pid"] = process.pid; save(results / "result.json", report)
            code = process.wait()
        item.update(exit_code=code, seconds=round(time.monotonic()-start, 3), finished=utc(), sha256=digest(logfile))
        save(results / "result.json", report)
        if code:
            raise RuntimeError(f"{label} failed with exit code {code}; see {logfile}")
        return logfile

    def dependencies():
        values = []
        manifest = json.loads((stage / "lake-manifest.json").read_text())
        for package in manifest["packages"]:
            if package["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", package["rev"]):
                raise RuntimeError(f"Unpinned dependency: {package}")
            values.append(source_pin(stage / ".lake/packages" / package["name"], package["rev"]))
        return values

    try:
        if not args.prepared:
            if args.dependency_cache:
                cache = args.dependency_cache.resolve(strict=True)
                if cache == stage or stage in cache.parents:
                    raise RuntimeError("The trusted cache must be outside the fresh stage")
                if args.copy_dependencies:
                    shutil.copytree(cache, stage / ".lake/packages", symlinks=True)
                else:
                    (stage / ".lake/packages").symlink_to(cache, target_is_directory=True)
            else:
                run("dependency-cache", [real / "bin/lake", "exe", "cache", "get"])
        report["dependencies_before"] = dependencies()
        verify_project(stage)
        if (stage / ".lake/build").exists():
            raise RuntimeError("Project build artifacts already exist; Comparator requires a fresh project build")
        if args.reuse_build_from:
            from build_cache import import_build_cache
            report["build_cache"] = import_build_cache(
                args.reuse_build_from, stage, inputs, tools, results, args.challenge_change, env)
            save(results / "result.json", report)
        libc = ctypes.CDLL(None, use_errno=True)
        abi = libc.syscall(444, 0, 0, 1)
        report["runtime"] = {"kernel": platform.release(), "architecture": platform.machine(),
                             "landlock_abi": abi if abi >= 0 else None, "uid": os.getuid()}
        if abi < 1:
            raise RuntimeError("Landlock is unavailable; the sandbox cannot be replaced or bypassed")
        if args.prepare_only:
            report.update(status="prepared", finished=utc())
            save(results / "result.json", report)
            print(f"Prepared {stage}; no theorem comparison has run")
            return
        bins = tools["binaries"]
        path_entry = tools["wrappers"]["path_entry"]
        sandbox_environment = {"PATH": path_entry + os.pathsep + str(real / "bin") + os.pathsep + os.environ["PATH"],
                               "COMPARATOR_LANDRUN": bins["landrun"]["path"],
                               "COMPARATOR_LEAN4EXPORT": bins["lean4export"]["path"],
                               "LEAN_NUM_THREADS": "1", "ELAN_TOOLCHAIN": pins["lean"]}
        unit = ["systemd-run", "--user", "--wait", "--pipe", "--collect",
                "--property=RestrictAddressFamilies=~AF_UNIX AF_INET AF_INET6 AF_NETLINK AF_PACKET",
                "--working-directory", str(stage)]
        for key, value in sandbox_environment.items():
            unit += ["-E", key + "=" + value]
        probe = """import socket
for family in (socket.AF_UNIX, socket.AF_INET, socket.AF_INET6):
 try:
  socket.socket(family, socket.SOCK_STREAM)
 except OSError as error:
  print('socket denied:', family, error)
 else:
  raise SystemExit('Socket sandbox allowed a forbidden address family')
"""
        run("socket-sandbox", unit + ["--", sys.executable, "-c", probe])
        shell = "export PATH=" + shlex.quote(path_entry) + ':"$PATH"; exec "$@"'
        command = unit + ["--", wrapped_lake, "env", "/bin/bash", "-c", shell,
                          "crown-comparison", bins["comparator"]["path"], "full-comparator.json"]
        report["status"] = "comparing"
        comparator_log = run("comparator", command)
        report["comparator_acceptance"] = comparator_acceptance(comparator_log, config)
        verify_project(stage)
        verify_project(project)
        report["dependencies_after"] = dependencies()
        axiom_file = results / "PublicAxioms.lean"
        axiom_file.write_text("import Solution\n" + "".join("#print axioms " + n + "\n" for n in config["theorem_names"]), encoding="utf-8")
        report["public_axioms_source_sha256"] = digest(axiom_file)
        axiom_log = run("public-axioms", unit + ["--", wrapped_lake, "env",
                         Path(tools["wrappers"]["sysroot"]) / "bin/lean", axiom_file])
        axiom_report = audit(stage / "full-comparator.json", axiom_log)
        save(results / "axioms.json", axiom_report)
        verify_project(stage)
        verify_project(project)
        tools_identity()
        verify_inventory(ROOT / "scripts", runner_inputs)
        if inventory(ROOT / "scripts") != runner_inputs or digest(ROOT / "tools/pins.json") != pins_hash:
            raise RuntimeError("Validation scripts or checking-tool pins changed during the run")
        report.update(status="success", finished=utc(), comparator_exit_code=0,
                      axiom_report_sha256=digest(results / "axioms.json"))
        save(results / "result.json", report)
        print(f"Comparator accepted all {len(config['theorem_names'])} targets; public axiom reports passed")
    except BaseException as error:
        report.update(status="failed", finished=utc(), error=str(error))
        save(results / "result.json", report)
        raise


if __name__ == "__main__":
    main()
