import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0010 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨400+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨400+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0400 M
  · exact minimal_mask_iff0401 M
  · exact minimal_mask_iff0402 M
  · exact minimal_mask_iff0403 M
  · exact minimal_mask_iff0404 M
  · exact minimal_mask_iff0405 M
  · exact minimal_mask_iff0406 M
  · exact minimal_mask_iff0407 M
  · exact minimal_mask_iff0408 M
  · exact minimal_mask_iff0409 M
  · exact minimal_mask_iff0410 M
  · exact minimal_mask_iff0411 M
  · exact minimal_mask_iff0412 M
  · exact minimal_mask_iff0413 M
  · exact minimal_mask_iff0414 M
  · exact minimal_mask_iff0415 M
  · exact minimal_mask_iff0416 M
  · exact minimal_mask_iff0417 M
  · exact minimal_mask_iff0418 M
  · exact minimal_mask_iff0419 M
  · exact minimal_mask_iff0420 M
  · exact minimal_mask_iff0421 M
  · exact minimal_mask_iff0422 M
  · exact minimal_mask_iff0423 M
  · exact minimal_mask_iff0424 M
  · exact minimal_mask_iff0425 M
  · exact minimal_mask_iff0426 M
  · exact minimal_mask_iff0427 M
  · exact minimal_mask_iff0428 M
  · exact minimal_mask_iff0429 M
  · exact minimal_mask_iff0430 M
  · exact minimal_mask_iff0431 M
  · exact minimal_mask_iff0432 M
  · exact minimal_mask_iff0433 M
  · exact minimal_mask_iff0434 M
  · exact minimal_mask_iff0435 M
  · exact minimal_mask_iff0436 M
  · exact minimal_mask_iff0437 M
  · exact minimal_mask_iff0438 M
  · exact minimal_mask_iff0439 M
#print axioms minimal_mask_iff_stored_template_block0010
end Crown.CertificateData
