# Finite certificate validation

From this directory, run:

```sh
python3 verify.py
```

Python 3.10 or later and a GCC-compatible C++17 compiler are required. The compiler defaults to `g++`; use `--cxx /path/to/compiler` to select another executable. The Python code uses only the standard library. The package supplies all validation inputs and runs offline.

Generated checker executables, decompressed proof data and detailed output go to `build/validation/`, which is excluded from version control. Each invocation creates a fresh directory. Successful verification ends with `ALL CHECKS PASSED` and exit code zero. `report.json` contains the input hashes, executed commands, checker output and exact arithmetic results. Paths in that report are relative to this directory.

## Mathematical checks

For three pairs, the verifier checks the complete 64-row domain, 2,517 forcing supports and 759 minimal obstructions. Each support must force its designated row; each obstruction must cause a contradiction and become feasible after deletion of any row. The seed, implication-step, terminal-conflict and fixed-pair coverage conditions are checked. Induction along an implication path then covers every selected family of at most six rows. Every intermediate support remains inside the selected family.

The verifier transports these obstructions through all 60 oriented-matching representatives. It checks the rank-to-mask bijections and reconstructs the full formula with 39,382 variables, 222,795 clauses and 38,430 distinct obstructions. The historical full-formula identity uses its original CRLF serialization. Each of the 141,926 clauses in `data/pairing6.cnf` must equal its indexed clause in the full formula. Its 3,305 positive-hint LRAT additions are checked by Boolean assignments, including every unit-propagation inference and the final empty clause. Its unsatisfiability therefore implies unsatisfiability of the full formula.

For four pairs, the verifier reconstructs 840 matching representatives, 105 obstructions per matching, and their union of 4,935 obstructions. It compares the resulting 10,116-variable, 38,240-clause formula with `data/pairing8.cnf`. Both C++ checkers verify the RUP contradiction independently. All 34,482 proof lines receive syntax checks. The checkers reach a permanent contradiction after 34,481 additions; the final empty clause is redundant. Valid and invalid refutations exercise both checkers, and positive and negative controls exercise the LRAT checker.

Exact integer and rational calculations check all displayed six- and seven-pair maxima for each value of `z`, including omitted zero values, the five-pair factorial table and maximum, the triple-count maximum over `d=0,...,10`, the probabilities `1/70` and `1/315`, and the union bounds `59/70`, `6/7` and `5/11`. The paper supplies the counting arguments and the analytical five-by-seven construction.

## Files and attribution

The mathematical work and project checkers are by Matthew J. Colbrook and Catherine Drysdale. This directory is distributed under the repository's Apache-2.0 licence. `SOURCES.json` preserves the identities of the original certificate data and checker sources. `data/pairing6-provenance.json` supplies the clause-index correspondence and discovery information; its names are local to this package. The discovery computation used Z3 4.13.3.

The catalogue, encoding and arithmetic conventions follow the paper. The positive-hint checker uses Boolean assignments and is independent of the literal-set checker used during certificate preparation. The two copied C++ checkers use watched literals and occurrence counts, respectively.

These executable checks depend on Python, the C++ compiler and the operating system. They are separate from the repository's Lean kernel proofs and theorem-comparison checks. They establish the finite assertions and arithmetic described here; the paper's reductions connect those assertions to its graph theorem.

## Verification result

The packaged validator completed successfully. `verification.json` contains the command, results, interpreter version and checked input identities. `SHA256SUMS` lists the release file identities.
