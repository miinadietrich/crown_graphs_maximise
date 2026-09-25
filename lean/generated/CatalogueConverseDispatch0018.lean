import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0018 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨720+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨720+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0720 M
  · exact minimal_mask_iff0721 M
  · exact minimal_mask_iff0722 M
  · exact minimal_mask_iff0723 M
  · exact minimal_mask_iff0724 M
  · exact minimal_mask_iff0725 M
  · exact minimal_mask_iff0726 M
  · exact minimal_mask_iff0727 M
  · exact minimal_mask_iff0728 M
  · exact minimal_mask_iff0729 M
  · exact minimal_mask_iff0730 M
  · exact minimal_mask_iff0731 M
  · exact minimal_mask_iff0732 M
  · exact minimal_mask_iff0733 M
  · exact minimal_mask_iff0734 M
  · exact minimal_mask_iff0735 M
  · exact minimal_mask_iff0736 M
  · exact minimal_mask_iff0737 M
  · exact minimal_mask_iff0738 M
  · exact minimal_mask_iff0739 M
  · exact minimal_mask_iff0740 M
  · exact minimal_mask_iff0741 M
  · exact minimal_mask_iff0742 M
  · exact minimal_mask_iff0743 M
  · exact minimal_mask_iff0744 M
  · exact minimal_mask_iff0745 M
  · exact minimal_mask_iff0746 M
  · exact minimal_mask_iff0747 M
  · exact minimal_mask_iff0748 M
  · exact minimal_mask_iff0749 M
  · exact minimal_mask_iff0750 M
  · exact minimal_mask_iff0751 M
  · exact minimal_mask_iff0752 M
  · exact minimal_mask_iff0753 M
  · exact minimal_mask_iff0754 M
  · exact minimal_mask_iff0755 M
  · exact minimal_mask_iff0756 M
  · exact minimal_mask_iff0757 M
  · exact minimal_mask_iff0758 M
  · exact minimal_mask_iff0759 M
#print axioms minimal_mask_iff_stored_template_block0018
end Crown.CertificateData
