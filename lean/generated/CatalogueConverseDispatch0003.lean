import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0003 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨120+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨120+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0120 M
  · exact minimal_mask_iff0121 M
  · exact minimal_mask_iff0122 M
  · exact minimal_mask_iff0123 M
  · exact minimal_mask_iff0124 M
  · exact minimal_mask_iff0125 M
  · exact minimal_mask_iff0126 M
  · exact minimal_mask_iff0127 M
  · exact minimal_mask_iff0128 M
  · exact minimal_mask_iff0129 M
  · exact minimal_mask_iff0130 M
  · exact minimal_mask_iff0131 M
  · exact minimal_mask_iff0132 M
  · exact minimal_mask_iff0133 M
  · exact minimal_mask_iff0134 M
  · exact minimal_mask_iff0135 M
  · exact minimal_mask_iff0136 M
  · exact minimal_mask_iff0137 M
  · exact minimal_mask_iff0138 M
  · exact minimal_mask_iff0139 M
  · exact minimal_mask_iff0140 M
  · exact minimal_mask_iff0141 M
  · exact minimal_mask_iff0142 M
  · exact minimal_mask_iff0143 M
  · exact minimal_mask_iff0144 M
  · exact minimal_mask_iff0145 M
  · exact minimal_mask_iff0146 M
  · exact minimal_mask_iff0147 M
  · exact minimal_mask_iff0148 M
  · exact minimal_mask_iff0149 M
  · exact minimal_mask_iff0150 M
  · exact minimal_mask_iff0151 M
  · exact minimal_mask_iff0152 M
  · exact minimal_mask_iff0153 M
  · exact minimal_mask_iff0154 M
  · exact minimal_mask_iff0155 M
  · exact minimal_mask_iff0156 M
  · exact minimal_mask_iff0157 M
  · exact minimal_mask_iff0158 M
  · exact minimal_mask_iff0159 M
#print axioms minimal_mask_iff_stored_template_block0003
end Crown.CertificateData
