#!/usr/bin/env python3
"""Create or check the release file manifest, excluding generated build outputs."""
import argparse
import json
from pathlib import Path
from common import ROOT, inventory, save, verify_inventory


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    target = args.root / "release-manifest.json"
    if args.check:
        value = json.loads(target.read_text())
        verify_inventory(args.root, value["files"])
        actual = [x for x in inventory(args.root, (".lake", ".git", "__pycache__", "validation-results", "build", "dist"))
                  if x["path"] not in ("release-manifest.json", "release-manifest.json.tmp")]
        if actual != value["files"]:
            raise RuntimeError("Release file inventory differs from the manifest")
        print(f"Checked {len(value['files'])} release input hashes")
    else:
        files = [x for x in inventory(args.root, (".lake", ".git", "__pycache__", "validation-results", "build", "dist"))
                 if x["path"] not in ("release-manifest.json", "release-manifest.json.tmp")]
        save(target, {"algorithm": "sha256", "files": files})
        print(f"Created manifest for {len(files)} files")


if __name__ == "__main__":
    main()
