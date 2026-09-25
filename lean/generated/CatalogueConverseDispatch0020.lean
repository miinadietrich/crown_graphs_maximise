import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0020 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨800+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨800+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0800 M
  · exact minimal_mask_iff0801 M
  · exact minimal_mask_iff0802 M
  · exact minimal_mask_iff0803 M
  · exact minimal_mask_iff0804 M
  · exact minimal_mask_iff0805 M
  · exact minimal_mask_iff0806 M
  · exact minimal_mask_iff0807 M
  · exact minimal_mask_iff0808 M
  · exact minimal_mask_iff0809 M
  · exact minimal_mask_iff0810 M
  · exact minimal_mask_iff0811 M
  · exact minimal_mask_iff0812 M
  · exact minimal_mask_iff0813 M
  · exact minimal_mask_iff0814 M
  · exact minimal_mask_iff0815 M
  · exact minimal_mask_iff0816 M
  · exact minimal_mask_iff0817 M
  · exact minimal_mask_iff0818 M
  · exact minimal_mask_iff0819 M
  · exact minimal_mask_iff0820 M
  · exact minimal_mask_iff0821 M
  · exact minimal_mask_iff0822 M
  · exact minimal_mask_iff0823 M
  · exact minimal_mask_iff0824 M
  · exact minimal_mask_iff0825 M
  · exact minimal_mask_iff0826 M
  · exact minimal_mask_iff0827 M
  · exact minimal_mask_iff0828 M
  · exact minimal_mask_iff0829 M
  · exact minimal_mask_iff0830 M
  · exact minimal_mask_iff0831 M
  · exact minimal_mask_iff0832 M
  · exact minimal_mask_iff0833 M
  · exact minimal_mask_iff0834 M
  · exact minimal_mask_iff0835 M
  · exact minimal_mask_iff0836 M
  · exact minimal_mask_iff0837 M
  · exact minimal_mask_iff0838 M
  · exact minimal_mask_iff0839 M
#print axioms minimal_mask_iff_stored_template_block0020
end Crown.CertificateData
