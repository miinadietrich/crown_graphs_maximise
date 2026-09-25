import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0016 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨640+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨640+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0640 M
  · exact minimal_mask_iff0641 M
  · exact minimal_mask_iff0642 M
  · exact minimal_mask_iff0643 M
  · exact minimal_mask_iff0644 M
  · exact minimal_mask_iff0645 M
  · exact minimal_mask_iff0646 M
  · exact minimal_mask_iff0647 M
  · exact minimal_mask_iff0648 M
  · exact minimal_mask_iff0649 M
  · exact minimal_mask_iff0650 M
  · exact minimal_mask_iff0651 M
  · exact minimal_mask_iff0652 M
  · exact minimal_mask_iff0653 M
  · exact minimal_mask_iff0654 M
  · exact minimal_mask_iff0655 M
  · exact minimal_mask_iff0656 M
  · exact minimal_mask_iff0657 M
  · exact minimal_mask_iff0658 M
  · exact minimal_mask_iff0659 M
  · exact minimal_mask_iff0660 M
  · exact minimal_mask_iff0661 M
  · exact minimal_mask_iff0662 M
  · exact minimal_mask_iff0663 M
  · exact minimal_mask_iff0664 M
  · exact minimal_mask_iff0665 M
  · exact minimal_mask_iff0666 M
  · exact minimal_mask_iff0667 M
  · exact minimal_mask_iff0668 M
  · exact minimal_mask_iff0669 M
  · exact minimal_mask_iff0670 M
  · exact minimal_mask_iff0671 M
  · exact minimal_mask_iff0672 M
  · exact minimal_mask_iff0673 M
  · exact minimal_mask_iff0674 M
  · exact minimal_mask_iff0675 M
  · exact minimal_mask_iff0676 M
  · exact minimal_mask_iff0677 M
  · exact minimal_mask_iff0678 M
  · exact minimal_mask_iff0679 M
#print axioms minimal_mask_iff_stored_template_block0016
end Crown.CertificateData
