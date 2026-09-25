/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Adapted from Mathlib/Tactic/Sat/FromLRAT.lean, licensed under Apache 2.0.
Modifications copyright (c) 2026 Matthew J. Colbrook and Catherine Drysdale.
-/

import Mathlib.Tactic.Sat.FromLRAT

open Lean Elab Mathlib.Tactic.Sat Std.Internal

namespace Crown.CertificateOriginalCache

private def checkedAddDecl (decl : Declaration) : TermElabM Unit := do
  let .thmDecl _ := decl | throwError "Only theorem declarations are accepted"
  let opts ← getOptions
  let env ← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats opts).toUSize (maxRecDepth.get opts).toUSize
    decl (← readThe Core.Context).cancelTk? (doCheck := true)
  setEnv env

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

/-- Check a contiguous interval of original clause identifiers only.
The interval controls proof scheduling, never the formula or claimed domain. -/
elab "checked_original_range " namespaceArg:ident ppSpace formulaArg:ident
    ppSpace first:num stop:num ppSpace cnf:term:max : command => do
  Command.liftTermElabM do
    let started ← IO.monoMsNow
    let (_, arr) ← readCNF (← readString cnf)
    let first := first.getNat
    let stop := stop.getNat
    unless 1 ≤ first ∧ first ≤ stop ∧ stop ≤ arr.size + 1 do
      throwError "Original clause interval is out of bounds"
    let ctx := mkConst formulaArg.getId
    let ctx' := buildConj arr 0 arr.size
    let mut needed : Std.HashSet Nat := {}
    for ident in [first:stop] do needed := needed.insert ident
    checkpoint s!"Original range {first}--{stop-1}: input prepared at {(← IO.monoMsNow)-started} ms"
    let _ ← originalClauses namespaceArg.getId arr ctx ctx' needed
    checkpoint s!"Original range {first}--{stop-1}: kernel checked at {(← IO.monoMsNow)-started} ms"

end Crown.CertificateOriginalCache
