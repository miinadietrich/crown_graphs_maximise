import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0004 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨160+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨160+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0160 M
  · exact minimal_mask_iff0161 M
  · exact minimal_mask_iff0162 M
  · exact minimal_mask_iff0163 M
  · exact minimal_mask_iff0164 M
  · exact minimal_mask_iff0165 M
  · exact minimal_mask_iff0166 M
  · exact minimal_mask_iff0167 M
  · exact minimal_mask_iff0168 M
  · exact minimal_mask_iff0169 M
  · exact minimal_mask_iff0170 M
  · exact minimal_mask_iff0171 M
  · exact minimal_mask_iff0172 M
  · exact minimal_mask_iff0173 M
  · exact minimal_mask_iff0174 M
  · exact minimal_mask_iff0175 M
  · exact minimal_mask_iff0176 M
  · exact minimal_mask_iff0177 M
  · exact minimal_mask_iff0178 M
  · exact minimal_mask_iff0179 M
  · exact minimal_mask_iff0180 M
  · exact minimal_mask_iff0181 M
  · exact minimal_mask_iff0182 M
  · exact minimal_mask_iff0183 M
  · exact minimal_mask_iff0184 M
  · exact minimal_mask_iff0185 M
  · exact minimal_mask_iff0186 M
  · exact minimal_mask_iff0187 M
  · exact minimal_mask_iff0188 M
  · exact minimal_mask_iff0189 M
  · exact minimal_mask_iff0190 M
  · exact minimal_mask_iff0191 M
  · exact minimal_mask_iff0192 M
  · exact minimal_mask_iff0193 M
  · exact minimal_mask_iff0194 M
  · exact minimal_mask_iff0195 M
  · exact minimal_mask_iff0196 M
  · exact minimal_mask_iff0197 M
  · exact minimal_mask_iff0198 M
  · exact minimal_mask_iff0199 M
#print axioms minimal_mask_iff_stored_template_block0004
end Crown.CertificateData
