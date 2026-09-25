import Crown.CertificateAssembly
import Lean

open Lean Elab Meta
namespace Crown.SixFormulaKernel
private def marker (message : String) : IO Unit := do
  let stream ← IO.getStderr
  stream.putStr (message ++ "\n")
  stream.flush

private def checkedAdd (decl : Declaration) : TermElabM Unit := do
  let .thmDecl _ := decl | throwError "Only theorem declarations are accepted"
  let opts ← getOptions
  let env ← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats opts).toUSize (maxRecDepth.get opts).toUSize
    decl (← readThe Core.Context).cancelTk? (doCheck := true)
  setEnv env

elab "checked_six_assembly_negative" : command => do
  Command.liftTermElabM do
    checkedAdd <| .thmDecl {
      name := `Crown.SixFormulaKernel.invalidNegativeControl,
      levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }

private def blockName (i : Nat) : Name :=
  `Crown.CertificateSixData ++ Name.mkSimple
    ("sixLiteralBlock" ++ String.ofList (List.replicate (4 - (toString i).length) '0') ++ toString i)

private partial def conjunction (xs : Array Expr) (v node : Expr) (lo hi : Nat) :
    TermElabM (Expr × Nat) := do
  unless lo < hi ∧ hi ≤ 128 do throwError "Invalid block interval"
  if hi = lo + 1 then
    let n := blockName lo
    return (mkAppN (mkConst (n.appendAfter "_satisfied")) xs, 1)
  else
    unless node.isAppOfArity ``Sat.Fmla.and 2 do
      throwError "Original formula does not have the expected conjunction shape"
    let mid := lo + (hi-lo)/2
    let f := node.getAppArgs[0]!
    let g := node.getAppArgs[1]!
    let (hf,nf) ← conjunction xs v f lo mid
    let (hg,ng) ← conjunction xs v g mid hi
    return (mkApp5 (mkConst ``Crown.CertificateAssembly.formula_and) v f g hf hg,
      nf + ng)

elab "checked_six_formula_assembly " name:ident : command => do
  marker "Six assembly command entry"
  Command.liftTermElabM do
    marker "Six assembly term context entry"
    let first ← getConstInfo ((blockName 0).appendAfter "_satisfied")
    marker "Six assembly first block type loaded"
    unless first.levelParams.isEmpty do throwError "Unexpected polymorphic block"
    let originalInfo ← getConstInfo `Crown.CertificateSix.pairing6Formula
    let .defnInfo original := originalInfo
      | throwError "Original formula is not a definition"
    unless original.levelParams.isEmpty do throwError "Unexpected polymorphic formula"
    let (target,proof) ← forallTelescope first.type fun xs conclusion => do
      marker "Six assembly forall telescope opened"
      unless xs.size = 4 do throwError "Expected exactly selector and three hypotheses"
      unless conclusion.isAppOfArity ``Sat.Valuation.satisfies_fmla 2 do
        throwError "Unexpected block conclusion"
      let v := conclusion.getAppArgs[0]!
      let (body,leafCount) ← conjunction xs v original.value 0 128
      unless leafCount = 128 do throwError "Expected exactly 128 checked blocks"
      marker "Six assembly conjunction constructed"
      let targetBody := mkApp2 (mkConst ``Sat.Valuation.satisfies_fmla) v
        (mkConst `Crown.CertificateSix.pairing6Formula)
      let target ← mkForallFVars xs targetBody
      marker "Six assembly target quantified"
      let proof ← mkLambdaFVars xs body
      marker "Six assembly proof abstracted"
      return (target,proof)
    if target.hasLooseBVars || proof.hasLooseBVars then
      throwError "Unexpected loose variables"
    marker "Checking exact six-formula conjunction in the ordinary kernel"
    checkedAdd <| .thmDecl {name := name.getId, levelParams := [], type := target, value := proof}
    marker "Exact six-formula conjunction kernel check completed"
end Crown.SixFormulaKernel
