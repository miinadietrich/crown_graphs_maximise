import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0009 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨360+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨360+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0360 M
  · exact minimal_mask_iff0361 M
  · exact minimal_mask_iff0362 M
  · exact minimal_mask_iff0363 M
  · exact minimal_mask_iff0364 M
  · exact minimal_mask_iff0365 M
  · exact minimal_mask_iff0366 M
  · exact minimal_mask_iff0367 M
  · exact minimal_mask_iff0368 M
  · exact minimal_mask_iff0369 M
  · exact minimal_mask_iff0370 M
  · exact minimal_mask_iff0371 M
  · exact minimal_mask_iff0372 M
  · exact minimal_mask_iff0373 M
  · exact minimal_mask_iff0374 M
  · exact minimal_mask_iff0375 M
  · exact minimal_mask_iff0376 M
  · exact minimal_mask_iff0377 M
  · exact minimal_mask_iff0378 M
  · exact minimal_mask_iff0379 M
  · exact minimal_mask_iff0380 M
  · exact minimal_mask_iff0381 M
  · exact minimal_mask_iff0382 M
  · exact minimal_mask_iff0383 M
  · exact minimal_mask_iff0384 M
  · exact minimal_mask_iff0385 M
  · exact minimal_mask_iff0386 M
  · exact minimal_mask_iff0387 M
  · exact minimal_mask_iff0388 M
  · exact minimal_mask_iff0389 M
  · exact minimal_mask_iff0390 M
  · exact minimal_mask_iff0391 M
  · exact minimal_mask_iff0392 M
  · exact minimal_mask_iff0393 M
  · exact minimal_mask_iff0394 M
  · exact minimal_mask_iff0395 M
  · exact minimal_mask_iff0396 M
  · exact minimal_mask_iff0397 M
  · exact minimal_mask_iff0398 M
  · exact minimal_mask_iff0399 M
#print axioms minimal_mask_iff_stored_template_block0009
end Crown.CertificateData
