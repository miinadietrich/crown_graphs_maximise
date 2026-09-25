import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0012 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨480+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨480+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0480 M
  · exact minimal_mask_iff0481 M
  · exact minimal_mask_iff0482 M
  · exact minimal_mask_iff0483 M
  · exact minimal_mask_iff0484 M
  · exact minimal_mask_iff0485 M
  · exact minimal_mask_iff0486 M
  · exact minimal_mask_iff0487 M
  · exact minimal_mask_iff0488 M
  · exact minimal_mask_iff0489 M
  · exact minimal_mask_iff0490 M
  · exact minimal_mask_iff0491 M
  · exact minimal_mask_iff0492 M
  · exact minimal_mask_iff0493 M
  · exact minimal_mask_iff0494 M
  · exact minimal_mask_iff0495 M
  · exact minimal_mask_iff0496 M
  · exact minimal_mask_iff0497 M
  · exact minimal_mask_iff0498 M
  · exact minimal_mask_iff0499 M
  · exact minimal_mask_iff0500 M
  · exact minimal_mask_iff0501 M
  · exact minimal_mask_iff0502 M
  · exact minimal_mask_iff0503 M
  · exact minimal_mask_iff0504 M
  · exact minimal_mask_iff0505 M
  · exact minimal_mask_iff0506 M
  · exact minimal_mask_iff0507 M
  · exact minimal_mask_iff0508 M
  · exact minimal_mask_iff0509 M
  · exact minimal_mask_iff0510 M
  · exact minimal_mask_iff0511 M
  · exact minimal_mask_iff0512 M
  · exact minimal_mask_iff0513 M
  · exact minimal_mask_iff0514 M
  · exact minimal_mask_iff0515 M
  · exact minimal_mask_iff0516 M
  · exact minimal_mask_iff0517 M
  · exact minimal_mask_iff0518 M
  · exact minimal_mask_iff0519 M
#print axioms minimal_mask_iff_stored_template_block0012
end Crown.CertificateData
