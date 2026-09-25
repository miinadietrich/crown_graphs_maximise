import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0001 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨40+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨40+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0040 M
  · exact minimal_mask_iff0041 M
  · exact minimal_mask_iff0042 M
  · exact minimal_mask_iff0043 M
  · exact minimal_mask_iff0044 M
  · exact minimal_mask_iff0045 M
  · exact minimal_mask_iff0046 M
  · exact minimal_mask_iff0047 M
  · exact minimal_mask_iff0048 M
  · exact minimal_mask_iff0049 M
  · exact minimal_mask_iff0050 M
  · exact minimal_mask_iff0051 M
  · exact minimal_mask_iff0052 M
  · exact minimal_mask_iff0053 M
  · exact minimal_mask_iff0054 M
  · exact minimal_mask_iff0055 M
  · exact minimal_mask_iff0056 M
  · exact minimal_mask_iff0057 M
  · exact minimal_mask_iff0058 M
  · exact minimal_mask_iff0059 M
  · exact minimal_mask_iff0060 M
  · exact minimal_mask_iff0061 M
  · exact minimal_mask_iff0062 M
  · exact minimal_mask_iff0063 M
  · exact minimal_mask_iff0064 M
  · exact minimal_mask_iff0065 M
  · exact minimal_mask_iff0066 M
  · exact minimal_mask_iff0067 M
  · exact minimal_mask_iff0068 M
  · exact minimal_mask_iff0069 M
  · exact minimal_mask_iff0070 M
  · exact minimal_mask_iff0071 M
  · exact minimal_mask_iff0072 M
  · exact minimal_mask_iff0073 M
  · exact minimal_mask_iff0074 M
  · exact minimal_mask_iff0075 M
  · exact minimal_mask_iff0076 M
  · exact minimal_mask_iff0077 M
  · exact minimal_mask_iff0078 M
  · exact minimal_mask_iff0079 M
#print axioms minimal_mask_iff_stored_template_block0001
end Crown.CertificateData
