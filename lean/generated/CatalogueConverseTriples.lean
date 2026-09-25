import Crown.CatalogueCardTransfer
import generated.CatalogueConversePairs

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_obstruction_triple_count :
    Nat.card {M : Finset (Fin 256) //
      (∃ p : Pairing8, MinimalMaskFamily (pairingRows p) M) ∧ M.card = 3} = 2520 := by
  calc
    _ = (catalogueUnion.filter (fun M => M.card = 3)).card :=
      Crown.CatalogueCardTransfer.card_subtype_and_eq_filter catalogueUnion
        (fun M => ∃ p : Pairing8, MinimalMaskFamily (pairingRows p) M)
        (fun M => M.card = 3) (fun M => (catalogueUnion_iff_minimal M).symm)
    _ = 2520 := catalogue_union_triple_count

#print axioms minimal_obstruction_triple_count
end Crown.CertificateData
