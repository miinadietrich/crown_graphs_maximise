import Crown.CertificateCatalogue
import generated.CatalogueCoreLookup
import Lean.Elab.Command

open Lean Elab
namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

elab "checked_coverage " n:ident ppSpace p:ident ppSpace t:ident ppSpace w:ident : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Command.liftTermElabM do
    let rows ← Term.elabTerm (← `(fun m : Fin 256 =>
      rowOfMask (pairsOfEquiv $p) (maskBits m))) none
    let template ← Term.elabTerm t (some (mkApp (mkConst ``List [.zero])
      (mkApp (mkConst ``Fin) (mkNatLit 4935))))
    let witness ← Term.elabTerm w none
    let fast := mkConst ``coresFast
    let proof ← Meta.mkEqRefl (mkConst ``Bool.true)
    let value := mkApp5 (mkConst ``coverage_of_fast_check) rows fast template witness proof
    let type := mkApp4 (mkConst ``Coverage) rows fast template witness
    addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

end Crown.CertificateData
