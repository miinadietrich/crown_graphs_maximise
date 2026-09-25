# Mathematical content

This development accompanies Matthew J. Colbrook and Catherine Drysdale,
*Crown graphs maximise the representation number of bipartite graphs*,
manuscript of 24 September 2026. The reference TeX source has SHA256
`6f0509aab43d75acd1d2eed58fea9130778ae1ae03e7f685b056f2be4efdf68a`.

## Main results

For every finite simple bipartite graph on $N\geq9$ vertices, the
representation number is at most $\lceil N/4\rceil$. The vertices may have
arbitrary labels; isolated vertices, repeated neighbourhoods and disconnected
graphs are included. The two bipartition classes may have different sizes.

For every $n\geq1$, the crown graph $H_{n,n}$ attains the largest
representation number among bipartite graphs on $2n$ vertices. This maximum
is 2 for $1\leq n\leq3$, 3 for $n=4$, and $\lceil n/2\rceil$ for
$n\geq5$. For $n\geq5$, the maximum minimum length of a uniform representing
word is $2n\lceil n/2\rceil$, attained by the crown. Here uniform means that
every vertex occurs equally often.

The principal declarations are `Crown.bipartite_representation_number_bound`,
`Crown.crown_representation_number`, `Crown.crown_extremal` and
`Crown.crown_extremal_uniform_length`. The graph bounds include the existence
of a representing word. This matters because the numerical definition assigns
representation number zero to a graph having no uniform representation.

## Proof modules

Module names below are relative to the Lean project.

| Modules | Content |
| --- | --- |
| `Crown.Definitions`, `Words`, `Cyclic`, `Components` | Words, alternation, uniformity, relabelling, induced subgraphs and components |
| `Crown.Ranks`, `Orders`, `Blocks` | Starred-rank completion, implication constraints, compatible orders and the explicit representing word |
| `Crown.Orientations`, `BalancedLarge` | The orientation count and the balanced bound for at least eight pairs |
| `Crown.MatchingFive` and the matching/probability modules | Exact obstruction counts and probability bounds for five, six and seven pairs |
| `Crown.FiniteClosure`, `SixCatalogue`, `CertificateSixGraph` | The three-pair catalogue, Boolean certificate and three-uniform representation for the six-by-six case |
| `Crown.CertificateGraph` and the catalogue/certificate modules | The four-pair catalogue, Boolean certificate and four-uniform representation for the eight-by-eight case |
| `Crown.SpecialRows`, `OddRanks`, `OddSelection`, `OddGraphs` | The distinguished-coordinate argument and odd part sizes, including five by seven |
| `Crown.PartSizeBounds`, `FinalReductions`, `Main` | Reduction of arbitrary bipartition sizes to the preceding cases |
| `Crown.CrownLower`, `CrownUpper`, `CrownValues`, `SmallGraph` | Exact crown values and the small bipartite cases |

The row-to-word construction retains distinct vertices with identical rows.
The obstruction condition requires a strict inequality in every coordinate;
equality in one coordinate prevents that comparison.

## The analytical five-by-seven case

`Crown.SpecialRows.feasible_iff` extends the short-obstruction criterion to
three or more coordinates when one distinguished coordinate contains only
a star or the lowest prescribed rank. Its row-index type is unrestricted.

`Crown.OddGraphs.matrix_representable_three` proves that a Boolean bipartite
matrix with one part of size $2k-1$ and the other of size at most $2k+1$
has a $k$-uniform representation for every $k\geq3$.
`Crown.OddGraphs.five_seven` is the case $k=3$. This proof selects an isolated
padding vertex, applies the distinguished-coordinate argument and restricts
the resulting word to the original graph.

## Boolean certificates

Both finite cases include the mathematical connection between graph rows,
the obstruction catalogue and the exact formula supplied to the certificate
checker. A family obstructing every pairing would supply a satisfying
assignment, which the refutation excludes.

For three pairs, the canonical domain has 64 rows. The closure data comprise
2,517 supports and 759 cores; transport through 60 oriented-pairing
representatives gives 38,430 distinct cores. The full encoding has 39,382
variables and 222,795 clauses. The refuted subformula has 141,926 clauses and
a positive-hint LRAT proof with 3,305 additions. Each subformula clause is
connected to its original clause. Unsatisfiability of this subset implies
unsatisfiability of the full encoding.

For four pairs, 840 oriented-pairing representatives give 4,935 distinct
cores. The encoding has 10,116 variables and 38,240 clauses. Its supplied
RUP refutation is reconstructed as an LRAT proof for Lean.

The generated Lean modules reconstruct the refutations as theorem declarations
checked by the ordinary kernel. The catalogue coverage, permutation symmetry,
cardinality constraints and satisfying-assignment implications are proved
separately. The executable checks in `validation/` also regenerate the
formulas and check both certificates, using two implementations for the
four-pair RUP proof.

## Supporting statements

The public comparison interface contains 243 statements. Alongside the main
theorems, these cover word construction, rank feasibility, pairing coverage,
formula semantics, certificate bridges, exact arithmetic, small graphs and
finite traversals. The three analytical statements above are explicit
comparison targets.

The supporting histogram statements concern equality, totals and failure
entries of supplied finite lists. Completeness of the
Gosper fixed-weight-mask traversal and the increasing-tuple traversal is
proved separately as a mathematical recurrence. The revised graph proof
uses the analytical five-by-seven argument and the two Boolean certificates.

The independent statements are in `Challenge.lean` and its supporting
modules; `Solution.lean` imports the proofs and their axiom reports.
`full-comparator.json` lists the comparison targets. The permitted axioms
are `propext`, `Classical.choice` and `Quot.sound`.
