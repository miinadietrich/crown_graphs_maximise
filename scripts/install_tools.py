#!/usr/bin/env python3
"""Install pinned comparison tools, or register existing builds of those sources."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import platform
import shutil
import subprocess
from common import ROOT, digest, output, save, source_pin, utc
from resource_control import install as install_wrappers


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, required=True, help="New installation directory")
    parser.add_argument("--toolchain", type=Path, help="Existing Lean 4.35.0-rc3 installation; otherwise use elan")
    parser.add_argument("--go", default="go", help="Go 1.27.1 executable, needed only for a new Landrun build")
    parser.add_argument("--reuse-comparator", type=Path, help="Pinned Comparator checkout with its built executable")
    parser.add_argument("--reuse-landrun-source", type=Path)
    parser.add_argument("--reuse-landrun", type=Path, help="Existing binary built from the pinned Landrun checkout")
    parser.add_argument("--compiler-jobs", type=int, default=1, choices=range(1,65), help="Maximum concurrent Lean compiler processes (default: 1)")
    args = parser.parse_args()
    if platform.system() != "Linux":
        parser.error("The comparison tools require Linux")
    prefix = args.prefix.resolve()
    if prefix.exists():
        parser.error("The installation directory already exists; preserve it and select a new path")
    if bool(args.reuse_landrun) != bool(args.reuse_landrun_source):
        parser.error("Supply both --reuse-landrun and --reuse-landrun-source")
    prefix.mkdir(parents=True)
    pins = json.loads((ROOT / "tools/pins.json").read_text())
    history = []

    def run(command, cwd=None, env=None):
        command = [str(x) for x in command]
        item = {"command": command, "cwd": str(cwd) if cwd else None, "started": utc()}
        with (prefix / "build.log").open("a", encoding="utf-8") as stream:
            stream.write(json.dumps(item) + "\n"); stream.flush()
            result = subprocess.run(command, cwd=cwd, env=env, stdout=stream, stderr=subprocess.STDOUT)
        item.update(exit_code=result.returncode, finished=utc())
        history.append(item); save(prefix / "commands.json", history)
        result.check_returncode()

    def checkout(name):
        path = prefix / name
        run(["git", "clone", "--no-checkout", pins[name]["url"], path])
        run(["git", "-C", path, "checkout", "--detach", pins[name]["rev"]])
        return path

    if args.toolchain:
        real = args.toolchain.resolve(strict=True)
    else:
        run(["elan", "toolchain", "install", pins["lean"]])
        real = Path(output(["elan", "run", pins["lean"], "lean", "--print-prefix"])).resolve()
    version = output([real / "bin/lean", "--version"])
    if "version 4.35.0-rc3" not in version:
        raise RuntimeError(f"Unexpected Lean: {version}")
    env = dict(os.environ, PATH=str(real / "bin") + os.pathsep + os.environ["PATH"],
               ELAN_TOOLCHAIN=pins["lean"], LEAN_NUM_THREADS="1")
    comp = args.reuse_comparator.resolve(strict=True) if args.reuse_comparator else checkout("comparator")
    source_pin(comp, pins["comparator"]["rev"], ("lean-toolchain", "lakefile.toml", "lake-manifest.json"))
    original = output(["git", "-C", comp, "show", "HEAD:lakefile.toml"])
    pinned_lakefile = original.replace('rev = "master"', 'rev = "' + pins["lean4export"]["rev"] + '"')
    if not args.reuse_comparator:
        (comp / "lean-toolchain").write_text(pins["lean"] + "\n", encoding="utf-8")
        (comp / "lakefile.toml").write_text(pinned_lakefile + "\n", encoding="utf-8")
        run([real / "bin/lake", "update"], cwd=comp, env=env)
        run([real / "bin/lake", "build", "lean4export", "comparator"], cwd=comp, env=env)
    if (comp / "lean-toolchain").read_text().strip() != pins["lean"]:
        raise RuntimeError("Comparator must use the release Lean toolchain")
    if (comp / "lakefile.toml").read_text().strip() != pinned_lakefile.strip():
        raise RuntimeError("Comparator Lake configuration differs from the documented pin adjustment")
    exporter = comp / ".lake/packages/lean4export"
    export_pin = source_pin(exporter, pins["lean4export"]["rev"])
    manifest = json.loads((comp / "lake-manifest.json").read_text())
    if len(manifest["packages"]) != 1 or manifest["packages"][0]["rev"] != pins["lean4export"]["rev"]:
        raise RuntimeError("Unexpected Comparator dependency manifest")
    land = args.reuse_landrun_source.resolve(strict=True) if args.reuse_landrun_source else checkout("landrun")
    land_pin = source_pin(land, pins["landrun"]["rev"])
    if args.reuse_landrun:
        land_bin = args.reuse_landrun.resolve(strict=True)
    else:
        go_version = output([args.go, "version"])
        if pins["go"]["version"] not in go_version.split():
            raise RuntimeError(f"Expected {pins['go']['version']}: {go_version}")
        land_bin = prefix / "landrun-bin"
        run([args.go, "build", "-trimpath", "-o", land_bin, "./cmd/landrun"], cwd=land,
            env=dict(env, GOTOOLCHAIN="local"))
    suffix = hashlib.sha256(str(prefix).encode()).hexdigest()[:12]
    wrappers = install_wrappers(real, real / ("crown-proof-resource-control-" + suffix), args.compiler_jobs)
    binaries = {"comparator": comp / ".lake/build/bin/comparator", "landrun": land_bin,
                "lean4export": exporter / ".lake/build/bin/lean4export", "lean": real / "bin/lean", "lake": real / "bin/lake"}
    report = {"created": utc(), "pins_sha256": digest(ROOT / "tools/pins.json"), "pins": pins,
              "lean_version": version, "toolchain": str(real), "wrappers": wrappers,
              "sources": {"comparator": source_pin(comp, pins["comparator"]["rev"],
                           ("lean-toolchain", "lakefile.toml", "lake-manifest.json")),
                          "lean4export": export_pin, "landrun": land_pin},
              "binaries": {k: {"path": str(v), "sha256": digest(v)} for k, v in binaries.items()},
              "reused_builds": bool(args.reuse_comparator or args.reuse_landrun),
              "scope": "Tool installation only; no crown theorem comparison has run"}
    save(prefix / "installation.json", report)
    print(prefix / "installation.json")


if __name__ == "__main__":
    main()
