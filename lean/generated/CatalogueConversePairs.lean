import Crown.CatalogueCardTransfer
import generated.CatalogueConverseTotal

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_obstruction_pair_count :
    Nat.card {M : Finset (Fin 256) //
      (∃ p : Pairing8, MinimalMaskFamily (pairingRows p) M) ∧ M.card = 2} = 2415 := by
  calc
    _ = (catalogueUnion.filter (fun M => M.card = 2)).card :=
      Crown.CatalogueCardTransfer.card_subtype_and_eq_filter catalogueUnion
        (fun M => ∃ p : Pairing8, MinimalMaskFamily (pairingRows p) M)
        (fun M => M.card = 2) (fun M => (catalogueUnion_iff_minimal M).symm)
    _ = 2415 := catalogue_union_pair_count

#print axioms minimal_obstruction_pair_count
end Crown.CertificateData
