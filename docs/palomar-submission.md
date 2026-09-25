# Palomar submission checklist

This repository contains a Palomar-ready project under `lean/`.

The submission-specific files are:

- `lean/lean-toolchain` — `leanprover/lean4:v4.35.0-rc3`, above Palomar's current `v4.35.0-rc2` floor.
- `lean/lakefile.toml` and `lean/lake-manifest.json` — the pinned Lean dependencies.
- `lean/PalomarChallenge.lean` — the Mathlib-only, independently reviewable statement surface.
- `lean/PalomarSolution.lean` — the full proof environment.
- `lean/palomar-comparator.json` — the seven theorem targets and permitted axioms.
- `formalization.yaml` — project, provenance, review, and AI-assistance metadata.

Before submission, finish the remote build and inspect the resulting commit. Then create the GitHub release from that exact commit:

```sh
git switch codex/palomar-prep
git status
git add -A
git commit -m "Prepare Palomar submission"
git push origin codex/palomar-prep
git tag -a v0.2.0 -m "Version 0.2.0: Palomar-ready Lean formalization"
git push origin v0.2.0
git rev-parse HEAD
```

The last command supplies the 40-character commit SHA for Palomar. A GitHub Release can then be created for tag `v0.2.0`; the release page and the Palomar submission are separate records.

On `https://submit.palomar-registry.org`, use:

| Field | Value |
| --- | --- |
| Repository | `miinadietrich/crown_graphs_maximise` |
| Commit | the exact SHA printed by `git rev-parse HEAD` |
| Project path | `lean` |
| Comparator configuration | `lean/palomar-comparator.json` |
| Formalization metadata | `formalization.yaml` |
| Authorization | `I am a responsible author or maintainer` |

Sign in with the GitHub account that can read the repository. Submit only after the tag and commit are public, then retain the Palomar status URL and wait for mechanical verification and editorial review. Do not use the old `lean/Challenge.lean` or `lean/full-comparator.json` paths for this submission.
