import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0017 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨680+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨680+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0680 M
  · exact minimal_mask_iff0681 M
  · exact minimal_mask_iff0682 M
  · exact minimal_mask_iff0683 M
  · exact minimal_mask_iff0684 M
  · exact minimal_mask_iff0685 M
  · exact minimal_mask_iff0686 M
  · exact minimal_mask_iff0687 M
  · exact minimal_mask_iff0688 M
  · exact minimal_mask_iff0689 M
  · exact minimal_mask_iff0690 M
  · exact minimal_mask_iff0691 M
  · exact minimal_mask_iff0692 M
  · exact minimal_mask_iff0693 M
  · exact minimal_mask_iff0694 M
  · exact minimal_mask_iff0695 M
  · exact minimal_mask_iff0696 M
  · exact minimal_mask_iff0697 M
  · exact minimal_mask_iff0698 M
  · exact minimal_mask_iff0699 M
  · exact minimal_mask_iff0700 M
  · exact minimal_mask_iff0701 M
  · exact minimal_mask_iff0702 M
  · exact minimal_mask_iff0703 M
  · exact minimal_mask_iff0704 M
  · exact minimal_mask_iff0705 M
  · exact minimal_mask_iff0706 M
  · exact minimal_mask_iff0707 M
  · exact minimal_mask_iff0708 M
  · exact minimal_mask_iff0709 M
  · exact minimal_mask_iff0710 M
  · exact minimal_mask_iff0711 M
  · exact minimal_mask_iff0712 M
  · exact minimal_mask_iff0713 M
  · exact minimal_mask_iff0714 M
  · exact minimal_mask_iff0715 M
  · exact minimal_mask_iff0716 M
  · exact minimal_mask_iff0717 M
  · exact minimal_mask_iff0718 M
  · exact minimal_mask_iff0719 M
#print axioms minimal_mask_iff_stored_template_block0017
end Crown.CertificateData
