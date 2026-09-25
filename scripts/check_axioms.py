#!/usr/bin/env python3
"""Audit the output of the public #print axioms command, separately from Comparator."""
import argparse
import json
from pathlib import Path
import re
from common import ALLOWED_AXIOMS, digest, save


def audit(config_path, log_path):
    config = json.loads(Path(config_path).read_text())
    text = Path(log_path).read_text(encoding="utf-8")
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text)
    matches += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    reports = {}
    for name, values in matches:
        if name in reports:
            raise RuntimeError(f"Duplicate axiom report: {name}")
        reports[name] = [x.strip() for x in values.split(",") if x.strip()]
    names = config["theorem_names"]
    if len(names) != len(set(names)) or set(names) != set(reports):
        raise RuntimeError(f"Axiom inventory mismatch: missing {set(names)-set(reports)}, extra {set(reports)-set(names)}")
    allowed = set(config["permitted_axioms"])
    if not allowed <= ALLOWED_AXIOMS or any(not set(values) <= allowed for values in reports.values()):
        raise RuntimeError("A public theorem uses an unpermitted axiom")
    return {"target_count": len(names), "config_sha256": digest(config_path), "log_sha256": digest(log_path),
            "reports": [{"theorem": n, "axioms": reports[n]} for n in names],
            "scope": "Public axiom reports only; Comparator acceptance is a separate required result"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("config", type=Path)
    parser.add_argument("log", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("Refusing to overwrite an earlier report")
    result = audit(args.config, args.log)
    save(args.output, result)
    print(f"All {result['target_count']} public reports use only permitted axioms")
