import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0013 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨520+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨520+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0520 M
  · exact minimal_mask_iff0521 M
  · exact minimal_mask_iff0522 M
  · exact minimal_mask_iff0523 M
  · exact minimal_mask_iff0524 M
  · exact minimal_mask_iff0525 M
  · exact minimal_mask_iff0526 M
  · exact minimal_mask_iff0527 M
  · exact minimal_mask_iff0528 M
  · exact minimal_mask_iff0529 M
  · exact minimal_mask_iff0530 M
  · exact minimal_mask_iff0531 M
  · exact minimal_mask_iff0532 M
  · exact minimal_mask_iff0533 M
  · exact minimal_mask_iff0534 M
  · exact minimal_mask_iff0535 M
  · exact minimal_mask_iff0536 M
  · exact minimal_mask_iff0537 M
  · exact minimal_mask_iff0538 M
  · exact minimal_mask_iff0539 M
  · exact minimal_mask_iff0540 M
  · exact minimal_mask_iff0541 M
  · exact minimal_mask_iff0542 M
  · exact minimal_mask_iff0543 M
  · exact minimal_mask_iff0544 M
  · exact minimal_mask_iff0545 M
  · exact minimal_mask_iff0546 M
  · exact minimal_mask_iff0547 M
  · exact minimal_mask_iff0548 M
  · exact minimal_mask_iff0549 M
  · exact minimal_mask_iff0550 M
  · exact minimal_mask_iff0551 M
  · exact minimal_mask_iff0552 M
  · exact minimal_mask_iff0553 M
  · exact minimal_mask_iff0554 M
  · exact minimal_mask_iff0555 M
  · exact minimal_mask_iff0556 M
  · exact minimal_mask_iff0557 M
  · exact minimal_mask_iff0558 M
  · exact minimal_mask_iff0559 M
#print axioms minimal_mask_iff_stored_template_block0013
end Crown.CertificateData
