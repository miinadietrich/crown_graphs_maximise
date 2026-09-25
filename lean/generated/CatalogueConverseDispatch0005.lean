import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0005 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨200+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨200+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0200 M
  · exact minimal_mask_iff0201 M
  · exact minimal_mask_iff0202 M
  · exact minimal_mask_iff0203 M
  · exact minimal_mask_iff0204 M
  · exact minimal_mask_iff0205 M
  · exact minimal_mask_iff0206 M
  · exact minimal_mask_iff0207 M
  · exact minimal_mask_iff0208 M
  · exact minimal_mask_iff0209 M
  · exact minimal_mask_iff0210 M
  · exact minimal_mask_iff0211 M
  · exact minimal_mask_iff0212 M
  · exact minimal_mask_iff0213 M
  · exact minimal_mask_iff0214 M
  · exact minimal_mask_iff0215 M
  · exact minimal_mask_iff0216 M
  · exact minimal_mask_iff0217 M
  · exact minimal_mask_iff0218 M
  · exact minimal_mask_iff0219 M
  · exact minimal_mask_iff0220 M
  · exact minimal_mask_iff0221 M
  · exact minimal_mask_iff0222 M
  · exact minimal_mask_iff0223 M
  · exact minimal_mask_iff0224 M
  · exact minimal_mask_iff0225 M
  · exact minimal_mask_iff0226 M
  · exact minimal_mask_iff0227 M
  · exact minimal_mask_iff0228 M
  · exact minimal_mask_iff0229 M
  · exact minimal_mask_iff0230 M
  · exact minimal_mask_iff0231 M
  · exact minimal_mask_iff0232 M
  · exact minimal_mask_iff0233 M
  · exact minimal_mask_iff0234 M
  · exact minimal_mask_iff0235 M
  · exact minimal_mask_iff0236 M
  · exact minimal_mask_iff0237 M
  · exact minimal_mask_iff0238 M
  · exact minimal_mask_iff0239 M
#print axioms minimal_mask_iff_stored_template_block0005
end Crown.CertificateData
