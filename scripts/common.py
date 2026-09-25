"""Utilities for reproducible source and checking-tool inventories."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import subprocess
import datetime

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def save(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def output(command, cwd=None):
    return subprocess.check_output([str(x) for x in command], cwd=cwd, text=True).strip()


def source_pin(path, revision, allowed_changes=()):
    path = Path(path).resolve(strict=True)
    git = ["git", "-c", "safe.directory=" + str(path), "-C", path]
    actual = output(git + ["rev-parse", "HEAD"])
    if actual != revision:
        raise RuntimeError(f"Incorrect revision at {path}: {actual}, expected {revision}")
    changed = output(git + ["diff", "--name-only", "HEAD"]).splitlines()
    if set(changed) - set(allowed_changes):
        raise RuntimeError(f"Modified tracked source at {path}: {changed}")
    return {"path": str(path), "rev": actual, "tracked_changes": changed}


def inventory(root, excluded=(".lake", ".git", "__pycache__")):
    root = Path(root)
    entries = []
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root)
        if any(part in excluded for part in relative.parts):
            continue
        if path.is_symlink():
            raise RuntimeError(f"Source symlink is not permitted: {path}")
        if path.is_file():
            entries.append({"path": relative.as_posix(), "sha256": digest(path), "bytes": path.stat().st_size})
    return entries


def verify_inventory(root, entries):
    seen = set()
    for entry in entries:
        relative = PurePosixPath(entry["path"])
        if relative.is_absolute() or ".." in relative.parts or not relative.parts or relative.as_posix() != entry["path"] or entry["path"] in seen:
            raise RuntimeError(f"Invalid or duplicate manifest path: {entry['path']}")
        seen.add(entry["path"])
        path = (Path(root) / entry["path"]).resolve(strict=True)
        path.relative_to(Path(root).resolve())
        if digest(path) != entry["sha256"]:
            raise RuntimeError(f"Changed input: {path}")


def configuration(project):
    config = json.loads((Path(project) / "full-comparator.json").read_text())
    names = config["theorem_names"]
    if not names or len(names) != len(set(names)):
        raise RuntimeError("The theorem list must be nonempty and have no duplicates")
    if config["challenge_module"] != "Challenge" or config["solution_module"] != "Solution":
        raise RuntimeError("Expected separate Challenge and Solution modules")
    if not set(config["permitted_axioms"]) <= ALLOWED_AXIOMS:
        raise RuntimeError("The configuration permits an additional axiom")
    if config.get("definition_names") not in (None, []) or config.get("definition_holes"):
        raise RuntimeError("Definition holes are not permitted")
    if config.get("enable_nanoda") is not False:
        raise RuntimeError("This checking route requires enable_nanoda: false")
    return config
