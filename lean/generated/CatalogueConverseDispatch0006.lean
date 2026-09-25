import generated.CatalogueConverseBatch0021
import generated.PairingStored4

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

theorem minimal_mask_iff_stored_template_block0006 (r : Fin 40) (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows (pairings (⟨240+r.val,by have hr := r.isLt; omega⟩ : Fin 840))) M ↔
      ∃ c ∈ templates (⟨240+r.val,by have hr := r.isLt; omega⟩ : Fin 840), (cores c).toFinset = M := by
  fin_cases r
  · exact minimal_mask_iff0240 M
  · exact minimal_mask_iff0241 M
  · exact minimal_mask_iff0242 M
  · exact minimal_mask_iff0243 M
  · exact minimal_mask_iff0244 M
  · exact minimal_mask_iff0245 M
  · exact minimal_mask_iff0246 M
  · exact minimal_mask_iff0247 M
  · exact minimal_mask_iff0248 M
  · exact minimal_mask_iff0249 M
  · exact minimal_mask_iff0250 M
  · exact minimal_mask_iff0251 M
  · exact minimal_mask_iff0252 M
  · exact minimal_mask_iff0253 M
  · exact minimal_mask_iff0254 M
  · exact minimal_mask_iff0255 M
  · exact minimal_mask_iff0256 M
  · exact minimal_mask_iff0257 M
  · exact minimal_mask_iff0258 M
  · exact minimal_mask_iff0259 M
  · exact minimal_mask_iff0260 M
  · exact minimal_mask_iff0261 M
  · exact minimal_mask_iff0262 M
  · exact minimal_mask_iff0263 M
  · exact minimal_mask_iff0264 M
  · exact minimal_mask_iff0265 M
  · exact minimal_mask_iff0266 M
  · exact minimal_mask_iff0267 M
  · exact minimal_mask_iff0268 M
  · exact minimal_mask_iff0269 M
  · exact minimal_mask_iff0270 M
  · exact minimal_mask_iff0271 M
  · exact minimal_mask_iff0272 M
  · exact minimal_mask_iff0273 M
  · exact minimal_mask_iff0274 M
  · exact minimal_mask_iff0275 M
  · exact minimal_mask_iff0276 M
  · exact minimal_mask_iff0277 M
  · exact minimal_mask_iff0278 M
  · exact minimal_mask_iff0279 M
#print axioms minimal_mask_iff_stored_template_block0006
end Crown.CertificateData
