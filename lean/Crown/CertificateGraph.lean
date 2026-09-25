import Crown.Certificate
import generated.CertificateFormula
import generated.Catalogue
import Crown.MaskGraphTransport

namespace Crown.CertificateGraph
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateValuation

theorem exists_feasible (s : Fin 256 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 8) :
    ∃ p : Pairing8, Feasible (fun m : {m // s m = true} =>
      rowOfMask (pairsOfEquiv p) (maskBits m.val)) := by
  classical
  by_contra h
  have hb : AllPairingsBad (fun m : {m // s m = true} => m.val) := by
    intro p hp
    exact h ⟨p,hp⟩
  obtain ⟨t,ht,htb,htmax⟩ := canonical_bad_selection s hs hb
  exact Crown.Certificate.pairing8_unsatisfiable
    (valuation (Crown.CertificateData.assignment t))
    (Crown.CertificateData.frozen_formula_satisfied t ht htmax
      (Crown.CertificateData.all_templates_selected t htb))

theorem matrix_representable {B : Type*} [Fintype B] [DecidableEq B]
    (hB : Fintype.card B ≤ 8) (M : Fin 8 → B → Bool) :
    KRepresentable (BalancedLarge.matrixGraph M) 4 :=
  MaskGraphTransport.matrix_of_masks (k := 4) (by decide) maskBits maskBits_surjective
    exists_feasible hB M

#print axioms exists_feasible
#print axioms matrix_representable
end Crown.CertificateGraph
