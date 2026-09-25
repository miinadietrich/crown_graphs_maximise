import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0014 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨560+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨560+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0560 M
  · exact minimal_mask_iff0561 M
  · exact minimal_mask_iff0562 M
  · exact minimal_mask_iff0563 M
  · exact minimal_mask_iff0564 M
  · exact minimal_mask_iff0565 M
  · exact minimal_mask_iff0566 M
  · exact minimal_mask_iff0567 M
  · exact minimal_mask_iff0568 M
  · exact minimal_mask_iff0569 M
  · exact minimal_mask_iff0570 M
  · exact minimal_mask_iff0571 M
  · exact minimal_mask_iff0572 M
  · exact minimal_mask_iff0573 M
  · exact minimal_mask_iff0574 M
  · exact minimal_mask_iff0575 M
  · exact minimal_mask_iff0576 M
  · exact minimal_mask_iff0577 M
  · exact minimal_mask_iff0578 M
  · exact minimal_mask_iff0579 M
  · exact minimal_mask_iff0580 M
  · exact minimal_mask_iff0581 M
  · exact minimal_mask_iff0582 M
  · exact minimal_mask_iff0583 M
  · exact minimal_mask_iff0584 M
  · exact minimal_mask_iff0585 M
  · exact minimal_mask_iff0586 M
  · exact minimal_mask_iff0587 M
  · exact minimal_mask_iff0588 M
  · exact minimal_mask_iff0589 M
  · exact minimal_mask_iff0590 M
  · exact minimal_mask_iff0591 M
  · exact minimal_mask_iff0592 M
  · exact minimal_mask_iff0593 M
  · exact minimal_mask_iff0594 M
  · exact minimal_mask_iff0595 M
  · exact minimal_mask_iff0596 M
  · exact minimal_mask_iff0597 M
  · exact minimal_mask_iff0598 M
  · exact minimal_mask_iff0599 M
#print axioms minimal_mask_iff_stored_template_block0014
end Crown.CertificateData
