# Crown graph representation bounds

Lean proofs and computational certificates for *Crown graphs maximise the
representation number of bipartite graphs*, by Matthew J. Colbrook and
Catherine Drysdale.

The main result bounds the representation number of every bipartite graph on
N ≥ 9 vertices by ⌈N/4⌉ and proves that crown graphs attain the largest
representation number among bipartite graphs of the same positive even order.
The corresponding word-length statement concerns uniform representing words.

The [mathematical overview](docs/mathematics.md) gives the hypotheses, formal
statements and supporting results. The [dependency list](docs/dependencies.md)
gives source attribution and exact versions.

## Compilation

Install [elan](https://github.com/leanprover/elan), Python 3 and Git. From this
directory:

```sh
cd lean
lake exe cache get
lake build Solution
```

`lean-toolchain` selects Lean 4.35.0-rc3. Both direct dependencies and all transitive
dependencies are pinned in the Lake configuration and lockfile. The supplied
Lean modules and literal certificate data are complete compilation inputs.
Certificate replay can require several hours and substantial disk space.
The Linux checking route below limits compiler concurrency and keeps its
build products in a separate directory.

`Solution.lean` exposes the main theorems and supporting results. Its proof
closure uses only `propext`, `Classical.choice` and `Quot.sound`, or a subset.
`Challenge.lean` contains the separate theorem specifications for Comparator;
its intentional proof placeholders belong to the comparison protocol.

## Independent comparison

The [verification results](verification/README.md) include all 243 accepted
statement comparisons and the corresponding axiom reports.

The [checking tools](tools/README.md) install the pinned Comparator,
lean4export and Landrun versions and describe the Linux checking command.
The runner builds a fresh copy, compares every configured theorem and obtains
separate `#print axioms` reports. Its source manifests bind each result to the
precise checked inputs.

## Certificate validation

The standalone validation requires Python 3 and a C++17 compiler:

```sh
python3 validation/verify.py
```

The [certificate documentation](validation/README.md) describes the finite
formulae, proof formats and validation results. Runtime products are confined
to ignored build directories.

## Contents

- `lean/`: proof sources, independent statements, literal data and pinned dependencies.
- `validation/`: certificates and standalone Python/C++ validators.
- `scripts/` and `tools/`: reproducible comparison and axiom checking.
- `docs/`: theorem map and mathematical attribution.
- `formalization.yaml`: machine-readable project metadata.
- `CITATION.cff`: citation metadata.

The code and data are distributed under Apache 2.0; see [LICENSE](LICENSE) and
[NOTICE](NOTICE). Dependencies retain their own licences.
