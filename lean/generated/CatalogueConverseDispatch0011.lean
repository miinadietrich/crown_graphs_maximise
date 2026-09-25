import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0011 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨440+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨440+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0440 M
  · exact minimal_mask_iff0441 M
  · exact minimal_mask_iff0442 M
  · exact minimal_mask_iff0443 M
  · exact minimal_mask_iff0444 M
  · exact minimal_mask_iff0445 M
  · exact minimal_mask_iff0446 M
  · exact minimal_mask_iff0447 M
  · exact minimal_mask_iff0448 M
  · exact minimal_mask_iff0449 M
  · exact minimal_mask_iff0450 M
  · exact minimal_mask_iff0451 M
  · exact minimal_mask_iff0452 M
  · exact minimal_mask_iff0453 M
  · exact minimal_mask_iff0454 M
  · exact minimal_mask_iff0455 M
  · exact minimal_mask_iff0456 M
  · exact minimal_mask_iff0457 M
  · exact minimal_mask_iff0458 M
  · exact minimal_mask_iff0459 M
  · exact minimal_mask_iff0460 M
  · exact minimal_mask_iff0461 M
  · exact minimal_mask_iff0462 M
  · exact minimal_mask_iff0463 M
  · exact minimal_mask_iff0464 M
  · exact minimal_mask_iff0465 M
  · exact minimal_mask_iff0466 M
  · exact minimal_mask_iff0467 M
  · exact minimal_mask_iff0468 M
  · exact minimal_mask_iff0469 M
  · exact minimal_mask_iff0470 M
  · exact minimal_mask_iff0471 M
  · exact minimal_mask_iff0472 M
  · exact minimal_mask_iff0473 M
  · exact minimal_mask_iff0474 M
  · exact minimal_mask_iff0475 M
  · exact minimal_mask_iff0476 M
  · exact minimal_mask_iff0477 M
  · exact minimal_mask_iff0478 M
  · exact minimal_mask_iff0479 M
#print axioms minimal_mask_iff_stored_template_block0011
end Crown.CertificateData
