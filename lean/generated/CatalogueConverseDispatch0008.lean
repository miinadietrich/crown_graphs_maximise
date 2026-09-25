import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0008 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨320+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨320+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0320 M
  · exact minimal_mask_iff0321 M
  · exact minimal_mask_iff0322 M
  · exact minimal_mask_iff0323 M
  · exact minimal_mask_iff0324 M
  · exact minimal_mask_iff0325 M
  · exact minimal_mask_iff0326 M
  · exact minimal_mask_iff0327 M
  · exact minimal_mask_iff0328 M
  · exact minimal_mask_iff0329 M
  · exact minimal_mask_iff0330 M
  · exact minimal_mask_iff0331 M
  · exact minimal_mask_iff0332 M
  · exact minimal_mask_iff0333 M
  · exact minimal_mask_iff0334 M
  · exact minimal_mask_iff0335 M
  · exact minimal_mask_iff0336 M
  · exact minimal_mask_iff0337 M
  · exact minimal_mask_iff0338 M
  · exact minimal_mask_iff0339 M
  · exact minimal_mask_iff0340 M
  · exact minimal_mask_iff0341 M
  · exact minimal_mask_iff0342 M
  · exact minimal_mask_iff0343 M
  · exact minimal_mask_iff0344 M
  · exact minimal_mask_iff0345 M
  · exact minimal_mask_iff0346 M
  · exact minimal_mask_iff0347 M
  · exact minimal_mask_iff0348 M
  · exact minimal_mask_iff0349 M
  · exact minimal_mask_iff0350 M
  · exact minimal_mask_iff0351 M
  · exact minimal_mask_iff0352 M
  · exact minimal_mask_iff0353 M
  · exact minimal_mask_iff0354 M
  · exact minimal_mask_iff0355 M
  · exact minimal_mask_iff0356 M
  · exact minimal_mask_iff0357 M
  · exact minimal_mask_iff0358 M
  · exact minimal_mask_iff0359 M
#print axioms minimal_mask_iff_stored_template_block0008
end Crown.CertificateData
