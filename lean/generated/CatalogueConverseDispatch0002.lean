import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0002 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨80+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨80+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0080 M
  · exact minimal_mask_iff0081 M
  · exact minimal_mask_iff0082 M
  · exact minimal_mask_iff0083 M
  · exact minimal_mask_iff0084 M
  · exact minimal_mask_iff0085 M
  · exact minimal_mask_iff0086 M
  · exact minimal_mask_iff0087 M
  · exact minimal_mask_iff0088 M
  · exact minimal_mask_iff0089 M
  · exact minimal_mask_iff0090 M
  · exact minimal_mask_iff0091 M
  · exact minimal_mask_iff0092 M
  · exact minimal_mask_iff0093 M
  · exact minimal_mask_iff0094 M
  · exact minimal_mask_iff0095 M
  · exact minimal_mask_iff0096 M
  · exact minimal_mask_iff0097 M
  · exact minimal_mask_iff0098 M
  · exact minimal_mask_iff0099 M
  · exact minimal_mask_iff0100 M
  · exact minimal_mask_iff0101 M
  · exact minimal_mask_iff0102 M
  · exact minimal_mask_iff0103 M
  · exact minimal_mask_iff0104 M
  · exact minimal_mask_iff0105 M
  · exact minimal_mask_iff0106 M
  · exact minimal_mask_iff0107 M
  · exact minimal_mask_iff0108 M
  · exact minimal_mask_iff0109 M
  · exact minimal_mask_iff0110 M
  · exact minimal_mask_iff0111 M
  · exact minimal_mask_iff0112 M
  · exact minimal_mask_iff0113 M
  · exact minimal_mask_iff0114 M
  · exact minimal_mask_iff0115 M
  · exact minimal_mask_iff0116 M
  · exact minimal_mask_iff0117 M
  · exact minimal_mask_iff0118 M
  · exact minimal_mask_iff0119 M
#print axioms minimal_mask_iff_stored_template_block0002
end Crown.CertificateData
