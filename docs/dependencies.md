# Dependencies and attribution

## Lean environment

The project uses Lean 4.35.0-rc3. `lean/lean-toolchain`, `lean/lakefile.toml` and
`lean/lake-manifest.json` specify the toolchain and immutable package revisions.
The lockfile retains all transitive revisions.

| Package | Revision | Licence |
| --- | --- | --- |
| [mathlib](https://github.com/leanprover-community/mathlib4) | `c55e6e786f49471c72fbddbec5415808896aec1e` | Apache-2.0 |
| [plausible](https://github.com/leanprover-community/plausible) | `b7eb3304aeae834b12dda98993a37f6a41f6f0bb` | Apache-2.0 |
| [LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient) | `5f4d51b81cbd3f6b32b156bfad9056621a040404` | Apache-2.0 |
| [importGraph](https://github.com/leanprover-community/import-graph) | `16f02aa7642864af59f1ff0e384a015994db9118` | Apache-2.0 |
| [ProofWidgets](https://github.com/leanprover-community/ProofWidgets4) | `4be2e3d5087eeb272cf5a8853b8f9dd025ef5957` | Apache-2.0 |
| [aesop](https://github.com/leanprover-community/aesop) | `3448c0bcc5ce01b2d1546e483ec3620e32df3d0e` | Apache-2.0 |
| [Qq](https://github.com/leanprover-community/quote4) | `92c15be17b7caf78c2ad767ec40f89052d908d81` | Apache-2.0 |
| [batteries](https://github.com/leanprover-community/batteries) | `4488d40d070b9700d4d5a6aa342f0d40c31b2a2d` | Apache-2.0 |
| [Cli](https://github.com/leanprover/lean4-cli) | `6130a47896ce867c6a4a55373441e59e565bad0f` | MIT |

Mathlib at this revision specifies Lean 4.35.0-rc3. The proofs use exact
integer, rational and finite combinatorial calculations. No interval
arithmetic is used.

## Comparison tools

| Tool | Revision | Licence |
| --- | --- | --- |
| [Lean Comparator](https://github.com/leanprover/comparator) | `3927ad383f208ae977c340a91c48ac9b497d2097` | Apache-2.0 |
| [lean4export](https://github.com/leanprover/lean4export) | `15f6055e299ad5b89345e533cc2192f4cc00f659` | Apache-2.0 |
| [Landrun](https://github.com/Zouuup/landrun) | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` | MIT |

Comparator and lean4export remain pinned to these source revisions for the
repository's standalone checking scripts; their upstream toolchain files
specify 4.33.0. Palomar uses the comparator and exporter bundled with the
submitted Lean 4.35.0-rc3 toolchain.
Landrun supplies the Linux build sandbox. The comparison uses independently
compiled Challenge and Solution environments and permits only `propext`,
`Classical.choice` and `Quot.sound`.

The standalone certificate checks require Python 3.10 or later and a
GCC-compatible C++17 compiler. They use the Python standard library and the
two supplied C++ checkers; a SAT solver is not required.

## Mathematical sources

The source paper is Matthew J. Colbrook and Catherine Drysdale,
*Crown graphs maximise the representation number of bipartite graphs*.
The reference version and its source hash are specified in
[Mathematical content](mathematics.md).

The word construction develops the method of Mozhui and Krishna,
*On the conjecture of the representation number of bipartite graphs*,
arXiv:2506.01057v1, Section 2. Its attribution is retained in `Crown.Blocks`
and `Crown.BaselineLiteral`. The exact crown values are the result of
Glen, Kitaev and Pyatkin, *On the representation number of a crown graph*,
Discrete Applied Mathematics, DOI:10.1016/j.dam.2018.03.013; the Lean
development includes proofs of these values. The small-graph classification
is related to Akgün, Gent, Kitaev and Zantema, Journal of Integer Sequences
22 (2019), Article 19.2.5, Section 2, Table 1.

## Software sources

The LRAT reconstruction helpers adapt Mario Carneiro's implementation in
[`Mathlib/Tactic/Sat/FromLRAT.lean`](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Tactic/Sat/FromLRAT.lean),
copyright 2022, Apache-2.0. The helpers retain this attribution and use the
ordinary Lean kernel to check the generated theorem declarations.
Mathlib supplies the finite graph, list, order, counting and arithmetic
infrastructure used throughout the development.

The release is distributed under Apache-2.0. Upstream copyright and licence
notices remain applicable to their respective sources. In particular, the
MIT-licensed `Cli` package retains its copyright notice for mhuisi (2021),
and Landrun retains its MIT notice.
