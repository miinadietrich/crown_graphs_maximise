import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0019 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨760+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨760+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0760 M
  · exact minimal_mask_iff0761 M
  · exact minimal_mask_iff0762 M
  · exact minimal_mask_iff0763 M
  · exact minimal_mask_iff0764 M
  · exact minimal_mask_iff0765 M
  · exact minimal_mask_iff0766 M
  · exact minimal_mask_iff0767 M
  · exact minimal_mask_iff0768 M
  · exact minimal_mask_iff0769 M
  · exact minimal_mask_iff0770 M
  · exact minimal_mask_iff0771 M
  · exact minimal_mask_iff0772 M
  · exact minimal_mask_iff0773 M
  · exact minimal_mask_iff0774 M
  · exact minimal_mask_iff0775 M
  · exact minimal_mask_iff0776 M
  · exact minimal_mask_iff0777 M
  · exact minimal_mask_iff0778 M
  · exact minimal_mask_iff0779 M
  · exact minimal_mask_iff0780 M
  · exact minimal_mask_iff0781 M
  · exact minimal_mask_iff0782 M
  · exact minimal_mask_iff0783 M
  · exact minimal_mask_iff0784 M
  · exact minimal_mask_iff0785 M
  · exact minimal_mask_iff0786 M
  · exact minimal_mask_iff0787 M
  · exact minimal_mask_iff0788 M
  · exact minimal_mask_iff0789 M
  · exact minimal_mask_iff0790 M
  · exact minimal_mask_iff0791 M
  · exact minimal_mask_iff0792 M
  · exact minimal_mask_iff0793 M
  · exact minimal_mask_iff0794 M
  · exact minimal_mask_iff0795 M
  · exact minimal_mask_iff0796 M
  · exact minimal_mask_iff0797 M
  · exact minimal_mask_iff0798 M
  · exact minimal_mask_iff0799 M
#print axioms minimal_mask_iff_stored_template_block0019
end Crown.CertificateData
