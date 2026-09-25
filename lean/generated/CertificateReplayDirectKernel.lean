/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Adapted from Mathlib/Tactic/Sat/FromLRAT.lean, licensed under Apache 2.0.
Modifications copyright (c) 2026 Matthew J. Colbrook and Catherine Drysdale.
-/

import Mathlib.Tactic.Sat.FromLRAT

open Lean Elab Mathlib.Tactic.Sat Std.Internal

namespace Crown.CertificateDirectKernel

private def checkedAddDecl (decl : Declaration) : TermElabM Unit := do
  let .thmDecl _ := decl | throwError "Only theorem declarations are accepted"
  let opts ← getOptions
  let env ← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats opts).toUSize (maxRecDepth.get opts).toUSize
    decl (← readThe Core.Context).cancelTk? (doCheck := true)
  setEnv env

elab "checked_kernel_negative_control" : command => do
  Command.liftTermElabM do
    checkedAddDecl <| Declaration.thmDecl {
      name := `Crown.CertificateSix.invalidNegativeControl,
      levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }

private def checkpoint (message : String) : TermElabM Unit := do
  IO.eprintln message

private def readString (term : Syntax) : TermElabM String :=
  unsafe Term.evalTerm String (mkConst ``String) term

private def readCNF (s : String) : TermElabM (Nat × Array (Array Int)) := do
  let Parsec.ParseResult.success _ result := Parser.parseDimacs ⟨_, s.startPos⟩
    | throwError "CNF parse failed"
  return result

private partial def cacheOriginalSubtree (proofNamespace : Name) (ctx : Expr) (counts : Array Nat)
    (start stop : Nat) (node suppliedProof : Expr)
    (db : Std.HashMap Nat Mathlib.Tactic.Sat.Clause) :
    TermElabM (Std.HashMap Nat Mathlib.Tactic.Sat.Clause) := do
  if counts[start]! == counts[stop]! then return db
  let name := proofNamespace ++ Name.mkSimple s!"subsumes_{start}_{stop}"
  unless (← getEnv).contains name do
    checkedAddDecl <| Declaration.thmDecl {
      name, levelParams := [], type := mkApp2 (mkConst ``Sat.Fmla.subsumes) ctx node,
      value := suppliedProof }
  let proof := mkConst name
  if stop == start + 1 then
    let some cl := db[start + 1]? | throwError "Original clause not registered"
    let originalName := proofNamespace ++ Name.mkSimple s!"original_{start+1}"
    checkedAddDecl <| Declaration.thmDecl {
      name := originalName, levelParams := [],
      type := mkApp2 (mkConst ``Sat.Fmla.proof) ctx cl.expr,
      value := mkApp3 (mkConst ``Sat.Fmla.proof_of_subsumes) ctx cl.expr proof }
    return db.insert (start + 1) { cl with proof := mkConst originalName }
  let mid := start + (stop - start) / 2
  let left := node.appFn!.appArg!
  let right := node.appArg!
  let leftProof := mkApp4 (mkConst ``Sat.Fmla.subsumes_left) ctx left right proof
  let rightProof := mkApp4 (mkConst ``Sat.Fmla.subsumes_right) ctx left right proof
  let db ← cacheOriginalSubtree proofNamespace ctx counts start mid left leftProof db
  cacheOriginalSubtree proofNamespace ctx counts mid stop right rightProof db

private def originalClauses (proofNamespace : Name) (arr : Array (Array Int)) (ctx ctx' : Expr)
    (needed : Std.HashSet Nat) : TermElabM (Std.HashMap Nat Mathlib.Tactic.Sat.Clause) := do
  let mut db := {}
  let mut counts := #[0]
  let mut newClauses := 0
  for i in [:arr.size] do
    let ident := i + 1
    if needed.contains ident then
      let name := proofNamespace ++ Name.mkSimple s!"original_{ident}"
      let wasCached := (← getEnv).contains name
      if !wasCached then newClauses := newClauses + 1
      db := db.insert ident { lits := arr[i]!, expr := buildClause arr[i]!, proof := mkConst name }
    counts := counts.push newClauses
  let self := mkApp (mkConst ``Sat.Fmla.subsumes_self) ctx
  cacheOriginalSubtree proofNamespace ctx counts 0 arr.size ctx' self db

elab "checked_lrat_direct_kernel " prefixArg:ident ppSpace formulaArg:ident ppSpace start:num stop:num ppSpace cnf:term:max
    ppSpace learned:term:max ppSpace lrat:term:max : command => do
  let proofNamespace := prefixArg.getId
  let start := start.getNat
  let stop := stop.getNat
  Command.liftTermElabM do
    let started ← IO.monoMsNow
    checkpoint s!"Replay {start}--{stop-1}: reading original CNF"
    let (_, arr) ← readCNF (← readString cnf)
    checkpoint s!"Parsed original CNF: {arr.size} clauses"
    let (_, learnedClauses) ← readCNF (← readString learned)
    checkpoint s!"Parsed learned CNF: {learnedClauses.size} clauses"
    let lrat ← readString lrat
    let Parsec.ParseResult.success _ steps := Parser.parseLRAT ⟨_, lrat.startPos⟩
      | throwError "LRAT parse failed"
    unless steps.size == stop - start do throwError "Chunk size mismatch"
    let ctx := mkConst formulaArg.getId
    let ctx' := buildConj arr 0 arr.size
    checkpoint "Built formula expression"
    let mut needed : Std.HashSet Nat := {}
    for step in steps do
      match step with
      | .del _ => throwError "No deletions expected"
      | .add _ _ hints =>
        for hint in hints do
          if hint ≤ 0 then throwError "Only positive RUP hints are accepted"
          if hint.toNat < start then
            needed := needed.insert hint.toNat
    checkpoint s!"Input prepared: {(← IO.monoMsNow)-started} ms; {needed.size} prior references"
    let mut db ← originalClauses proofNamespace arr ctx ctx' needed
    checkpoint s!"Original clause constants checked; beginning learned-clause replay"
    for ident in needed do
      if ident ≤ arr.size then continue
      let index := ident - arr.size - 1
      unless index < learnedClauses.size do throwError "Learned-clause index out of range"
      let literals := learnedClauses[index]!
      let name := proofNamespace ++ Name.mkSimple s!"step_{ident}"
      unless (← getEnv).contains name do throwError "Previous theorem is missing: {name}"
      db := db.insert ident {
        lits := literals, expr := buildClause literals, proof := mkConst name }
    let mut expected := start
    for step in steps do
      match step with
      | .del _ => throwError "No deletions expected"
      | .add ident literals hints =>
        unless ident == expected do throwError "Unexpected step number {ident}; expected {expected}"
        checkpoint s!"Begin step {ident}: {(← IO.monoMsNow)-started} ms"
        let clause := buildClause literals
        let .ok proof := buildProofStep db literals hints ctx clause
          | throwError "LRAT reconstruction failed at step {ident}"
        checkpoint s!"Term built for step {ident}: {(← IO.monoMsNow)-started} ms"
        let name := proofNamespace ++ Name.mkSimple s!"step_{ident}"
        checkedAddDecl <| Declaration.thmDecl {
          name, levelParams := [], type := mkApp2 (mkConst ``Sat.Fmla.proof) ctx clause,
          value := proof }
        db := db.insert ident { lits := literals, expr := clause, proof := mkConst name }
        checkpoint s!"Step {ident} kernel checked: {(← IO.monoMsNow)-started} ms"
        expected := expected + 1
        if (expected - start) % 5 == 0 then
          checkpoint s!"Kernel checked {expected - start} additions through identifier {ident}"
    checkpoint s!"Kernel replay completed for LRAT identifiers {start} through {stop - 1}"

end Crown.CertificateDirectKernel
