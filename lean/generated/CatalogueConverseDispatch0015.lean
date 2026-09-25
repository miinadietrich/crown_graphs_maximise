import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0015 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨600+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨600+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0600 M
  · exact minimal_mask_iff0601 M
  · exact minimal_mask_iff0602 M
  · exact minimal_mask_iff0603 M
  · exact minimal_mask_iff0604 M
  · exact minimal_mask_iff0605 M
  · exact minimal_mask_iff0606 M
  · exact minimal_mask_iff0607 M
  · exact minimal_mask_iff0608 M
  · exact minimal_mask_iff0609 M
  · exact minimal_mask_iff0610 M
  · exact minimal_mask_iff0611 M
  · exact minimal_mask_iff0612 M
  · exact minimal_mask_iff0613 M
  · exact minimal_mask_iff0614 M
  · exact minimal_mask_iff0615 M
  · exact minimal_mask_iff0616 M
  · exact minimal_mask_iff0617 M
  · exact minimal_mask_iff0618 M
  · exact minimal_mask_iff0619 M
  · exact minimal_mask_iff0620 M
  · exact minimal_mask_iff0621 M
  · exact minimal_mask_iff0622 M
  · exact minimal_mask_iff0623 M
  · exact minimal_mask_iff0624 M
  · exact minimal_mask_iff0625 M
  · exact minimal_mask_iff0626 M
  · exact minimal_mask_iff0627 M
  · exact minimal_mask_iff0628 M
  · exact minimal_mask_iff0629 M
  · exact minimal_mask_iff0630 M
  · exact minimal_mask_iff0631 M
  · exact minimal_mask_iff0632 M
  · exact minimal_mask_iff0633 M
  · exact minimal_mask_iff0634 M
  · exact minimal_mask_iff0635 M
  · exact minimal_mask_iff0636 M
  · exact minimal_mask_iff0637 M
  · exact minimal_mask_iff0638 M
  · exact minimal_mask_iff0639 M
#print axioms minimal_mask_iff_stored_template_block0015
end Crown.CertificateData
