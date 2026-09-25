# Checking tools

`pins.json` identifies the exact Lean, Comparator, lean4export, Landrun, and Go versions. The proof project's `lean/lake-manifest.json` pins every Lean library dependency. The installer selects Lean 4.33.1 and replaces Comparator's `master` requirement for lean4export with the listed commit; all checker and kernel code comes from those pinned sources.

The checking environment requires Linux with Landlock, an unprivileged user with a working systemd user session, Python 3.10 or newer, Git, a C compiler, Elan, and Go 1.27.1. Network access is needed for installation and dependency-cache retrieval. Comparison itself runs with the socket restrictions recommended by Comparator, extended to TCP/IP, Netlink, and packet sockets. Real Landrun remains enabled throughout Comparator's compilation and export phases.

Before fetching the dependency cache on Linux, a soft open-file limit of 65536 avoids exhaustion during parallel extraction. If the current limit is lower, `ulimit -n 65536` raises it when permitted by the hard limit.

From the release directory, install into a new directory:

```sh
python3 scripts/install_tools.py --prefix "$HOME/.cache/crown-proof-tools"
```

Elan installs the pinned Lean toolchain if `--toolchain` is omitted. Supply `--go /path/to/go` to select an existing Go 1.27.1 executable. For Linux amd64, the Go archive URL and SHA256 are supplied in `pins.json`; verify the checksum before extracting the archive. Tool builds, commands, hashes, and source revisions are retained in the installation directory. A failed installation is preserved; a retry uses a new directory.

To use trusted existing builds, supply all relevant paths:

```sh
python3 scripts/install_tools.py --prefix "$HOME/.cache/crown-proof-tools-reuse" \
  --toolchain /path/to/lean-4.33.1 \
  --reuse-comparator /path/to/comparator-checkout \
  --reuse-landrun-source /path/to/landrun-checkout \
  --reuse-landrun /path/to/landrun-binary
```

Source revisions, the two Comparator configuration adjustments, and executable hashes are checked and retained. Reuse assumes that the supplied binaries were built from those sources.

The installer adds a wrapper directory under the Lean installation. The compiled wrappers preserve every compiler argument and limit Lean compiler concurrency with project-local `flock` locks. Each compiler, exporter, and final kernel check may still require substantial memory. The default is one compiler process. On a machine with sufficient RAM, `--compiler-jobs 16` permits up to sixteen concurrent compiler processes; each Lean compiler process retains one worker thread. Nested compiler invocation while retaining the only available lock would deadlock.

Run the small controls first:

```sh
python3 scripts/sandbox_trial.py \
  --tools "$HOME/.cache/crown-proof-tools/installation.json" \
  --dependency-cache /path/to/trusted/.lake/packages \
  --work-dir "$HOME/crown-proof-controls"
```

The positive control must pass through Comparator. The negative control must fail because its proof uses `sorryAx`. These small controls check the runtime setup before the theorem comparison.

Create the release manifest after reviewing all input files, then launch a fresh comparison:

```sh
python3 scripts/manifest.py
python3 scripts/manifest.py --check
bash scripts/validate.sh \
  --tools "$HOME/.cache/crown-proof-tools/installation.json" \
  --stage "$HOME/crown-proof-check"
```

The stage must be new and outside `lean/`. Comparator builds Challenge and Solution from the copied release inputs, compares every target in `full-comparator.json`, verifies the permitted axiom closure, and replays the solution into the Lean kernel.

`--dependency-cache /path/to/trusted/.lake/packages` avoids another dependency download and links the trusted cache outside the sandbox's writable stage. Its package commits and tracked-source cleanliness are checked before and after comparison. The cache must already contain all required build artifacts and must remain unchanged during the run. If Lake requires a cache update, use `--copy-dependencies` with the same option to make an independent writable copy; hardlinks are not used. Without a supplied cache the script executes `lake exe cache get` before comparison, trusting the downloaded library cache as described in Comparator's documentation.

`--prepare-only` stages inputs and dependencies without comparing them. A later invocation with the same arguments and `--prepared` starts comparison only if that stage has never started Comparator and its input hashes still match. An interrupted or failed comparison requires a new stage.

Fresh compilation is the default. After a preserved fresh-build attempt, `--reuse-build-from /path/to/previous-stage` permits a new comparison to reuse unchanged Solution artifacts. Each independently reviewed changed Challenge or Specification source must be listed with `--challenge-change relative/path.lean`; the complete source delta must equal that list. Solution sources, dependencies and checking tools must be unchanged. The importer checks the original build evidence and artifact hashes, copies only the Solution import closure, and rebuilds Challenge. The full Comparator, Lean kernel replay and axiom audit run again. This option requires a new stage and cannot be combined with `--prepare-only` or `--prepared`.

Actual commands, complete output, input hashes, checking-tool hashes, return codes, and timing are preserved in `<stage>/.lake/validation/`. After Comparator succeeds, a separate generated Lean file imports Solution and executes `#print axioms` for every configured theorem. `axioms.json` checks the complete inventory against the permitted set: `propext`, `Classical.choice`, and `Quot.sound`. The final `result.json` reports `status: success` after both checks pass.

Upstream sources and licences: [Comparator (Apache-2.0)](https://github.com/leanprover/comparator), [lean4export (Apache-2.0)](https://github.com/leanprover/lean4export), [Lean (Apache-2.0)](https://github.com/leanprover/lean4), [Landrun (MIT)](https://github.com/Zouuup/landrun), and [Go (BSD-3-Clause)](https://go.dev/LICENSE).
