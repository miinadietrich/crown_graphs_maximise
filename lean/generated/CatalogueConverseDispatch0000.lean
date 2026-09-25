import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0000 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨0+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨0+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0000 M
  · exact minimal_mask_iff0001 M
  · exact minimal_mask_iff0002 M
  · exact minimal_mask_iff0003 M
  · exact minimal_mask_iff0004 M
  · exact minimal_mask_iff0005 M
  · exact minimal_mask_iff0006 M
  · exact minimal_mask_iff0007 M
  · exact minimal_mask_iff0008 M
  · exact minimal_mask_iff0009 M
  · exact minimal_mask_iff0010 M
  · exact minimal_mask_iff0011 M
  · exact minimal_mask_iff0012 M
  · exact minimal_mask_iff0013 M
  · exact minimal_mask_iff0014 M
  · exact minimal_mask_iff0015 M
  · exact minimal_mask_iff0016 M
  · exact minimal_mask_iff0017 M
  · exact minimal_mask_iff0018 M
  · exact minimal_mask_iff0019 M
  · exact minimal_mask_iff0020 M
  · exact minimal_mask_iff0021 M
  · exact minimal_mask_iff0022 M
  · exact minimal_mask_iff0023 M
  · exact minimal_mask_iff0024 M
  · exact minimal_mask_iff0025 M
  · exact minimal_mask_iff0026 M
  · exact minimal_mask_iff0027 M
  · exact minimal_mask_iff0028 M
  · exact minimal_mask_iff0029 M
  · exact minimal_mask_iff0030 M
  · exact minimal_mask_iff0031 M
  · exact minimal_mask_iff0032 M
  · exact minimal_mask_iff0033 M
  · exact minimal_mask_iff0034 M
  · exact minimal_mask_iff0035 M
  · exact minimal_mask_iff0036 M
  · exact minimal_mask_iff0037 M
  · exact minimal_mask_iff0038 M
  · exact minimal_mask_iff0039 M
#print axioms minimal_mask_iff_stored_template_block0000
end Crown.CertificateData
