"""Import unchanged Solution artifacts from a documented fresh compilation."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path, PurePosixPath
import json
import os
import re
import shutil
import subprocess
import sys

from common import digest, inventory, save, utc, verify_inventory


def _challenge(path):
    path = PurePosixPath(path)
    return path.suffix == ".lean" and (
        path.stem.endswith("Challenge") or path.stem == "Specification"
        or "Specification" in path.parts[:-1])


def _idle(donor):
    for process in Path("/proc").iterdir():
        if not process.name.isdigit() or int(process.name) == os.getpid():
            continue
        try:
            cwd = (process / "cwd").resolve(strict=True)
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            continue
        if cwd == donor or donor in cwd.parents:
            raise RuntimeError(f"Donor has an active process: {process.name}")


def _unchanged(root, entries):
    if inventory(root, excluded=()) != entries:
        raise RuntimeError(f"Artifact inventory changed: {root}")


def import_build_cache(donor, stage, inputs, tools, report_dir, approved_changes, env):
    """Copy only unchanged Solution import-closure artifacts; never accept proofs.

    The caller must subsequently run the complete Comparator and axiom audit.
    The preserved fresh-build execution supplies source/build provenance; hashes
    establish continuity of its artifacts, not an independent compilation proof.
    """
    donor, stage = Path(donor).resolve(strict=True), Path(stage).resolve(strict=True)
    report_dir = Path(report_dir).resolve(strict=True)
    if donor == stage or donor in stage.parents or stage in donor.parents:
        raise RuntimeError("The donor and recipient must be disjoint directories")
    build = donor / ".lake/build"
    recipient = stage / ".lake/build"
    if recipient.exists() or recipient.is_symlink():
        raise RuntimeError("Recipient project build artifacts already exist")
    if not build.is_dir() or build.is_symlink():
        raise RuntimeError("Donor build directory must be a real directory")
    if report_dir != stage / ".lake/validation":
        raise RuntimeError("Cache provenance belongs in the recipient validation directory")
    evidence_path = report_dir / "build-cache.json"
    if evidence_path.exists():
        raise RuntimeError("Refusing to replace existing cache provenance")
    _idle(donor)
    donor_report_path = donor / ".lake/validation/result.json"
    donor_inputs_path = donor / ".lake/validation/project-inputs.json"
    donor_report = json.loads(donor_report_path.read_text())
    old_inputs = json.loads(donor_inputs_path.read_text())["files"]
    metadata_hashes = {str(p): digest(p) for p in (donor_report_path, donor_inputs_path)}
    if donor_report.get("status") != "failed" or donor_report.get("build_cache"):
        raise RuntimeError("Expected a failed comparison following an original fresh build")
    if donor_report.get("compilation_mode", "fresh") != "fresh":
        raise RuntimeError("The donor must have a documented fresh compilation")
    if donor_report.get("stage") != str(donor):
        raise RuntimeError("Donor report names a different stage")
    if donor_report.get("project_manifest_sha256") != digest(donor_inputs_path):
        raise RuntimeError("Donor input-manifest hash mismatch")
    if donor_report.get("tools") != tools:
        raise RuntimeError("Checking tools differ from the donor's pinned installation")
    for entry in list(tools["binaries"].values()) + tools["wrappers"]["files"]:
        if digest(entry["path"]) != entry["sha256"]:
            raise RuntimeError(f"Changed checking tool: {entry['path']}")
    verify_inventory(donor, old_inputs)
    if inventory(donor) != old_inputs or inventory(stage) != inputs:
        raise RuntimeError("Donor or recipient source inventory mismatch")
    old = {entry["path"]: entry for entry in old_inputs}
    new = {entry["path"]: entry for entry in inputs}
    removed = sorted(set(old) - set(new))
    if removed:
        raise RuntimeError(f"Cache reuse does not permit removed project inputs: {removed}")
    changed = sorted(path for path in old if old[path] != new[path])
    added = sorted(set(new) - set(old))
    delta = sorted(changed + added)
    approved = sorted(approved_changes)
    if not delta or delta != approved or not all(_challenge(p) for p in approved):
        raise RuntimeError(f"Source changes differ from approved Challenge changes: {delta}")
    commands = [c for c in donor_report["commands"] if c["label"] == "comparator"]
    if len(commands) != 1:
        raise RuntimeError("Donor must contain exactly one Comparator command")
    command = commands[0]
    if command.get("exit_code") in (None, 0) or command.get("cwd") != str(donor):
        raise RuntimeError("The donor comparison is not a completed failed attempt")
    if command.get("log") != "comparator.log":
        raise RuntimeError("Unexpected donor Comparator log path")
    argv = command.get("command", [])
    if tools["binaries"]["comparator"]["path"] not in argv or argv[-1:] != ["full-comparator.json"]:
        raise RuntimeError("Donor command does not invoke the pinned full Comparator")
    logfile = donor / ".lake/validation/comparator.log"
    if digest(logfile) != command.get("sha256"):
        raise RuntimeError("Donor Comparator log hash mismatch")
    text = logfile.read_text(encoding="utf-8")
    if not re.search(r"^Build completed successfully \([0-9]+ jobs\)\.$", text, re.M):
        raise RuntimeError("Donor log lacks successful fresh-build output")
    if not re.search(r"^.*\bBuilt Solution \([^\n]*\)$", text, re.M):
        raise RuntimeError("Donor log does not document compilation of Solution")
    artifacts = inventory(build, excluded=())
    if not artifacts:
        raise RuntimeError("Donor has no build artifacts")
    artifact_manifest = report_dir / "donor-build-artifacts.json"
    if artifact_manifest.exists():
        raise RuntimeError("Refusing to replace a donor artifact manifest")
    save(artifact_manifest, {"algorithm": "sha256", "files": artifacts})

    # Lake establishes its search path once. Each --deps call then runs the
    # pinned compiler on the import header, without elaborating proof bodies.
    lake = str(Path(tools["toolchain"]) / "bin/lake")
    lean = str(Path(tools["toolchain"]) / "bin/lean")
    environment_command = [lake, "env", sys.executable, "-c",
        "import json,os; print(json.dumps({k:os.environ.get(k) for k in "
        "('LEAN_PATH','LEAN_SYSROOT','LEAN_SRC_PATH')}))"]
    result = subprocess.run(environment_command, cwd=donor, env=env, text=True,
                            capture_output=True, check=True, timeout=120)
    lean_env = dict(env)
    search_environment = json.loads(result.stdout)
    for key, value in search_environment.items():
        if value is None:
            lean_env.pop(key, None)
        else:
            lean_env[key] = value
    lean_env["LEAN_NUM_THREADS"] = "1"
    source_modules = {str(PurePosixPath(p).with_suffix("")): p
                      for p in old if p.endswith(".lean")}
    project_lib = (build / "lib/lean").resolve(strict=True)
    external_roots = [(Path(tools["toolchain"]) / "lib/lean").resolve(strict=True)]
    packages = json.loads((donor / "lake-manifest.json").read_text())["packages"]
    external_roots += [(donor / ".lake/packages" / p["name"]).resolve(strict=True)
                       for p in packages]

    def dependencies(module):
        argv = [lean, "--deps", source_modules[module]]
        proc = subprocess.run(argv, cwd=donor, env=lean_env, text=True,
                              capture_output=True, check=True, timeout=120)
        dependencies = set()
        for line in proc.stdout.splitlines():
            path = Path(line)
            if not path.is_absolute() or path.suffix != ".olean":
                raise RuntimeError(f"Unexpected --deps output for {module}: {line!r}")
            path = path.resolve(strict=True)
            if project_lib in path.parents:
                dependency = path.relative_to(project_lib).with_suffix("").as_posix()
                if dependency not in source_modules:
                    raise RuntimeError(f"Project import has no inventoried source: {path}")
                dependencies.add(dependency)
            elif not any(root in path.parents for root in external_roots):
                raise RuntimeError(f"Import outside the pinned project and dependencies: {path}")
        return module, {"command": argv, "stdout": proc.stdout,
                        "stderr": proc.stderr, "imports": sorted(dependencies)}

    # Only Solution's transitive closure can contribute artifacts to the retry.
    graph, pending = {}, {"Solution"}
    with ThreadPoolExecutor(max_workers=8) as executor:
        while pending:
            futures = [executor.submit(dependencies, module) for module in sorted(pending)]
            pending = set()
            for future in as_completed(futures):
                module, record = future.result()
                if _challenge(source_modules[module]) or source_modules[module] in delta:
                    raise RuntimeError(f"Solution imports a Challenge or changed source: {module}")
                graph[module] = record
            for record in graph.values():
                pending.update(m for m in record["imports"] if m not in graph)
    selected = []
    for entry in artifacts:
        path = PurePosixPath(entry["path"])
        if path.parts[:2] == ("lib", "lean"):
            module = PurePosixPath(*path.parts[2:])
        elif path.parts[:1] == ("ir",):
            module = PurePosixPath(*path.parts[1:])
        else:
            continue
        module = module.parent / module.name.split(".", 1)[0]
        if module.as_posix() in graph:
            selected.append(entry)
    copied_paths = {entry["path"] for entry in selected}
    for module in graph:
        if f"lib/lean/{module}.olean" not in copied_paths:
            raise RuntimeError(f"Missing compiled Solution dependency: {module}")
    _idle(donor)
    recipient.mkdir(parents=True)
    for entry in selected:
        source, target = build / entry["path"], recipient / entry["path"]
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target, follow_symlinks=False)
    _unchanged(recipient, selected)
    _unchanged(build, artifacts)
    verify_inventory(donor, old_inputs)
    if inventory(donor) != old_inputs or inventory(stage) != inputs:
        raise RuntimeError("Project source inventory changed during cache import")
    for path, expected in metadata_hashes.items():
        if digest(path) != expected:
            raise RuntimeError(f"Donor metadata changed: {path}")
    if digest(logfile) != command["sha256"]:
        raise RuntimeError("Donor Comparator log changed during cache import")
    _idle(donor)
    provenance = {"created": utc(), "mode": "reused_project_artifacts",
        "donor": str(donor), "recipient": str(stage), "approved_changes": delta,
        "changed_existing_sources": changed,
        "added_sources": [new[path] for path in added],
        "donor_metadata_sha256": metadata_hashes, "donor_comparator_command": command,
        "donor_artifact_manifest": artifact_manifest.name,
        "donor_artifact_manifest_sha256": digest(artifact_manifest),
        "dependency_environment_command": environment_command,
        "dependency_environment": search_environment,
        "dependency_environment_stderr": result.stderr,
        "dependency_commands": {key: graph[key] for key in sorted(graph)},
        "copied_artifacts": selected, "copied_module_count": len(graph),
        "source_to_build_basis": "Preserved observed fresh build; artifact hashes establish continuity.",
        "scope": "Compilation reuse only; full Comparator, kernel replay and axiom audit remain required."}
    save(evidence_path, provenance)
    return {"mode": provenance["mode"], "donor": str(donor),
            "provenance": evidence_path.name, "sha256": digest(evidence_path),
            "copied_module_count": len(graph), "copied_artifact_count": len(selected)}
