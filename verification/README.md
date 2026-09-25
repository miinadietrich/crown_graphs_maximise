# Verification

Lean Comparator accepted all 243 configured statements, and the Lean kernel
accepted the exported Solution. The separate axiom audit permits only
`propext`, `Classical.choice` and `Quot.sound`.

`lean.json` contains the actual result, versions, tool hashes and source
identities. `axioms.txt` contains the 243 actual `#print axioms` reports.
`commands.json` contains the executed command sequence with installation and
build paths represented by variables. `comparator.log` contains the complete
output of the successful comparison with the same path substitutions.
`lean.json` supplies both its original and published SHA-256 hashes.
`socket-sandbox.log`, when present, contains the socket-control output on the
same basis. `lean-inputs.json` lists the checked inputs relative to `lean/`.

The comparison uses the pinned sources with the documented Lean 4.33.1
configuration adjustments. The checking executables were built from those pinned sources; their hashes are supplied in `lean.json`.

The unchanged Solution compilation was reused from a preserved fresh build. The Challenge was rebuilt, and the complete comparison, kernel replay and axiom audit ran again. `compilation.json` supplies the source, artifact and command provenance.

The standalone certificate results are in
[`validation/verification.json`](../validation/verification.json).
Reproduction commands are in the main README and the checking-tool documentation.
