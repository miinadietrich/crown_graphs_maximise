import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0007 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨280+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨280+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0280 M
  · exact minimal_mask_iff0281 M
  · exact minimal_mask_iff0282 M
  · exact minimal_mask_iff0283 M
  · exact minimal_mask_iff0284 M
  · exact minimal_mask_iff0285 M
  · exact minimal_mask_iff0286 M
  · exact minimal_mask_iff0287 M
  · exact minimal_mask_iff0288 M
  · exact minimal_mask_iff0289 M
  · exact minimal_mask_iff0290 M
  · exact minimal_mask_iff0291 M
  · exact minimal_mask_iff0292 M
  · exact minimal_mask_iff0293 M
  · exact minimal_mask_iff0294 M
  · exact minimal_mask_iff0295 M
  · exact minimal_mask_iff0296 M
  · exact minimal_mask_iff0297 M
  · exact minimal_mask_iff0298 M
  · exact minimal_mask_iff0299 M
  · exact minimal_mask_iff0300 M
  · exact minimal_mask_iff0301 M
  · exact minimal_mask_iff0302 M
  · exact minimal_mask_iff0303 M
  · exact minimal_mask_iff0304 M
  · exact minimal_mask_iff0305 M
  · exact minimal_mask_iff0306 M
  · exact minimal_mask_iff0307 M
  · exact minimal_mask_iff0308 M
  · exact minimal_mask_iff0309 M
  · exact minimal_mask_iff0310 M
  · exact minimal_mask_iff0311 M
  · exact minimal_mask_iff0312 M
  · exact minimal_mask_iff0313 M
  · exact minimal_mask_iff0314 M
  · exact minimal_mask_iff0315 M
  · exact minimal_mask_iff0316 M
  · exact minimal_mask_iff0317 M
  · exact minimal_mask_iff0318 M
  · exact minimal_mask_iff0319 M
#print axioms minimal_mask_iff_stored_template_block0007
end Crown.CertificateData
