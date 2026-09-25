import generated.CatalogueBatch0007
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0006

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0240 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0240) M ↔
      ∃ c ∈ template0240, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0240) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0240))
    cores template0240 witness0240 coverage0240
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0240) (maskBits m)) cores template0240 witness0240
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0240))
      coverage0240 catalogue_core_nodup coverageSize0240) (by rfl) M

theorem minimal_mask_iff0241 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0241) M ↔
      ∃ c ∈ template0241, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0241) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0241))
    cores template0241 witness0241 coverage0241
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0241) (maskBits m)) cores template0241 witness0241
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0241))
      coverage0241 catalogue_core_nodup coverageSize0241) (by rfl) M

theorem minimal_mask_iff0242 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0242) M ↔
      ∃ c ∈ template0242, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0242) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0242))
    cores template0242 witness0242 coverage0242
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0242) (maskBits m)) cores template0242 witness0242
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0242))
      coverage0242 catalogue_core_nodup coverageSize0242) (by rfl) M

theorem minimal_mask_iff0243 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0243) M ↔
      ∃ c ∈ template0243, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0243) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0243))
    cores template0243 witness0243 coverage0243
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0243) (maskBits m)) cores template0243 witness0243
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0243))
      coverage0243 catalogue_core_nodup coverageSize0243) (by rfl) M

theorem minimal_mask_iff0244 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0244) M ↔
      ∃ c ∈ template0244, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0244) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0244))
    cores template0244 witness0244 coverage0244
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0244) (maskBits m)) cores template0244 witness0244
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0244))
      coverage0244 catalogue_core_nodup coverageSize0244) (by rfl) M

theorem minimal_mask_iff0245 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0245) M ↔
      ∃ c ∈ template0245, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0245) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0245))
    cores template0245 witness0245 coverage0245
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0245) (maskBits m)) cores template0245 witness0245
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0245))
      coverage0245 catalogue_core_nodup coverageSize0245) (by rfl) M

theorem minimal_mask_iff0246 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0246) M ↔
      ∃ c ∈ template0246, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0246) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0246))
    cores template0246 witness0246 coverage0246
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0246) (maskBits m)) cores template0246 witness0246
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0246))
      coverage0246 catalogue_core_nodup coverageSize0246) (by rfl) M

theorem minimal_mask_iff0247 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0247) M ↔
      ∃ c ∈ template0247, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0247) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0247))
    cores template0247 witness0247 coverage0247
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0247) (maskBits m)) cores template0247 witness0247
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0247))
      coverage0247 catalogue_core_nodup coverageSize0247) (by rfl) M

theorem minimal_mask_iff0248 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0248) M ↔
      ∃ c ∈ template0248, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0248) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0248))
    cores template0248 witness0248 coverage0248
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0248) (maskBits m)) cores template0248 witness0248
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0248))
      coverage0248 catalogue_core_nodup coverageSize0248) (by rfl) M

theorem minimal_mask_iff0249 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0249) M ↔
      ∃ c ∈ template0249, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0249) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0249))
    cores template0249 witness0249 coverage0249
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0249) (maskBits m)) cores template0249 witness0249
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0249))
      coverage0249 catalogue_core_nodup coverageSize0249) (by rfl) M

theorem minimal_mask_iff0250 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0250) M ↔
      ∃ c ∈ template0250, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0250) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0250))
    cores template0250 witness0250 coverage0250
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0250) (maskBits m)) cores template0250 witness0250
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0250))
      coverage0250 catalogue_core_nodup coverageSize0250) (by rfl) M

theorem minimal_mask_iff0251 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0251) M ↔
      ∃ c ∈ template0251, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0251) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0251))
    cores template0251 witness0251 coverage0251
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0251) (maskBits m)) cores template0251 witness0251
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0251))
      coverage0251 catalogue_core_nodup coverageSize0251) (by rfl) M

theorem minimal_mask_iff0252 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0252) M ↔
      ∃ c ∈ template0252, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0252) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0252))
    cores template0252 witness0252 coverage0252
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0252) (maskBits m)) cores template0252 witness0252
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0252))
      coverage0252 catalogue_core_nodup coverageSize0252) (by rfl) M

theorem minimal_mask_iff0253 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0253) M ↔
      ∃ c ∈ template0253, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0253) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0253))
    cores template0253 witness0253 coverage0253
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0253) (maskBits m)) cores template0253 witness0253
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0253))
      coverage0253 catalogue_core_nodup coverageSize0253) (by rfl) M

theorem minimal_mask_iff0254 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0254) M ↔
      ∃ c ∈ template0254, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0254) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0254))
    cores template0254 witness0254 coverage0254
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0254) (maskBits m)) cores template0254 witness0254
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0254))
      coverage0254 catalogue_core_nodup coverageSize0254) (by rfl) M

theorem minimal_mask_iff0255 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0255) M ↔
      ∃ c ∈ template0255, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0255) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0255))
    cores template0255 witness0255 coverage0255
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0255) (maskBits m)) cores template0255 witness0255
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0255))
      coverage0255 catalogue_core_nodup coverageSize0255) (by rfl) M

theorem minimal_mask_iff0256 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0256) M ↔
      ∃ c ∈ template0256, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0256) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0256))
    cores template0256 witness0256 coverage0256
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0256) (maskBits m)) cores template0256 witness0256
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0256))
      coverage0256 catalogue_core_nodup coverageSize0256) (by rfl) M

theorem minimal_mask_iff0257 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0257) M ↔
      ∃ c ∈ template0257, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0257) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0257))
    cores template0257 witness0257 coverage0257
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0257) (maskBits m)) cores template0257 witness0257
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0257))
      coverage0257 catalogue_core_nodup coverageSize0257) (by rfl) M

theorem minimal_mask_iff0258 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0258) M ↔
      ∃ c ∈ template0258, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0258) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0258))
    cores template0258 witness0258 coverage0258
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0258) (maskBits m)) cores template0258 witness0258
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0258))
      coverage0258 catalogue_core_nodup coverageSize0258) (by rfl) M

theorem minimal_mask_iff0259 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0259) M ↔
      ∃ c ∈ template0259, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0259) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0259))
    cores template0259 witness0259 coverage0259
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0259) (maskBits m)) cores template0259 witness0259
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0259))
      coverage0259 catalogue_core_nodup coverageSize0259) (by rfl) M

theorem minimal_mask_iff0260 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0260) M ↔
      ∃ c ∈ template0260, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0260) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0260))
    cores template0260 witness0260 coverage0260
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0260) (maskBits m)) cores template0260 witness0260
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0260))
      coverage0260 catalogue_core_nodup coverageSize0260) (by rfl) M

theorem minimal_mask_iff0261 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0261) M ↔
      ∃ c ∈ template0261, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0261) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0261))
    cores template0261 witness0261 coverage0261
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0261) (maskBits m)) cores template0261 witness0261
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0261))
      coverage0261 catalogue_core_nodup coverageSize0261) (by rfl) M

theorem minimal_mask_iff0262 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0262) M ↔
      ∃ c ∈ template0262, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0262) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0262))
    cores template0262 witness0262 coverage0262
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0262) (maskBits m)) cores template0262 witness0262
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0262))
      coverage0262 catalogue_core_nodup coverageSize0262) (by rfl) M

theorem minimal_mask_iff0263 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0263) M ↔
      ∃ c ∈ template0263, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0263) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0263))
    cores template0263 witness0263 coverage0263
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0263) (maskBits m)) cores template0263 witness0263
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0263))
      coverage0263 catalogue_core_nodup coverageSize0263) (by rfl) M

theorem minimal_mask_iff0264 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0264) M ↔
      ∃ c ∈ template0264, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0264) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0264))
    cores template0264 witness0264 coverage0264
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0264) (maskBits m)) cores template0264 witness0264
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0264))
      coverage0264 catalogue_core_nodup coverageSize0264) (by rfl) M

theorem minimal_mask_iff0265 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0265) M ↔
      ∃ c ∈ template0265, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0265) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0265))
    cores template0265 witness0265 coverage0265
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0265) (maskBits m)) cores template0265 witness0265
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0265))
      coverage0265 catalogue_core_nodup coverageSize0265) (by rfl) M

theorem minimal_mask_iff0266 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0266) M ↔
      ∃ c ∈ template0266, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0266) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0266))
    cores template0266 witness0266 coverage0266
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0266) (maskBits m)) cores template0266 witness0266
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0266))
      coverage0266 catalogue_core_nodup coverageSize0266) (by rfl) M

theorem minimal_mask_iff0267 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0267) M ↔
      ∃ c ∈ template0267, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0267) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0267))
    cores template0267 witness0267 coverage0267
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0267) (maskBits m)) cores template0267 witness0267
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0267))
      coverage0267 catalogue_core_nodup coverageSize0267) (by rfl) M

theorem minimal_mask_iff0268 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0268) M ↔
      ∃ c ∈ template0268, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0268) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0268))
    cores template0268 witness0268 coverage0268
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0268) (maskBits m)) cores template0268 witness0268
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0268))
      coverage0268 catalogue_core_nodup coverageSize0268) (by rfl) M

theorem minimal_mask_iff0269 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0269) M ↔
      ∃ c ∈ template0269, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0269) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0269))
    cores template0269 witness0269 coverage0269
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0269) (maskBits m)) cores template0269 witness0269
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0269))
      coverage0269 catalogue_core_nodup coverageSize0269) (by rfl) M

theorem minimal_mask_iff0270 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0270) M ↔
      ∃ c ∈ template0270, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0270) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0270))
    cores template0270 witness0270 coverage0270
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0270) (maskBits m)) cores template0270 witness0270
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0270))
      coverage0270 catalogue_core_nodup coverageSize0270) (by rfl) M

theorem minimal_mask_iff0271 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0271) M ↔
      ∃ c ∈ template0271, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0271) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0271))
    cores template0271 witness0271 coverage0271
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0271) (maskBits m)) cores template0271 witness0271
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0271))
      coverage0271 catalogue_core_nodup coverageSize0271) (by rfl) M

theorem minimal_mask_iff0272 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0272) M ↔
      ∃ c ∈ template0272, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0272) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0272))
    cores template0272 witness0272 coverage0272
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0272) (maskBits m)) cores template0272 witness0272
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0272))
      coverage0272 catalogue_core_nodup coverageSize0272) (by rfl) M

theorem minimal_mask_iff0273 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0273) M ↔
      ∃ c ∈ template0273, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0273) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0273))
    cores template0273 witness0273 coverage0273
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0273) (maskBits m)) cores template0273 witness0273
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0273))
      coverage0273 catalogue_core_nodup coverageSize0273) (by rfl) M

theorem minimal_mask_iff0274 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0274) M ↔
      ∃ c ∈ template0274, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0274) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0274))
    cores template0274 witness0274 coverage0274
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0274) (maskBits m)) cores template0274 witness0274
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0274))
      coverage0274 catalogue_core_nodup coverageSize0274) (by rfl) M

theorem minimal_mask_iff0275 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0275) M ↔
      ∃ c ∈ template0275, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0275) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0275))
    cores template0275 witness0275 coverage0275
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0275) (maskBits m)) cores template0275 witness0275
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0275))
      coverage0275 catalogue_core_nodup coverageSize0275) (by rfl) M

theorem minimal_mask_iff0276 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0276) M ↔
      ∃ c ∈ template0276, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0276) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0276))
    cores template0276 witness0276 coverage0276
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0276) (maskBits m)) cores template0276 witness0276
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0276))
      coverage0276 catalogue_core_nodup coverageSize0276) (by rfl) M

theorem minimal_mask_iff0277 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0277) M ↔
      ∃ c ∈ template0277, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0277) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0277))
    cores template0277 witness0277 coverage0277
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0277) (maskBits m)) cores template0277 witness0277
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0277))
      coverage0277 catalogue_core_nodup coverageSize0277) (by rfl) M

theorem minimal_mask_iff0278 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0278) M ↔
      ∃ c ∈ template0278, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0278) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0278))
    cores template0278 witness0278 coverage0278
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0278) (maskBits m)) cores template0278 witness0278
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0278))
      coverage0278 catalogue_core_nodup coverageSize0278) (by rfl) M

theorem minimal_mask_iff0279 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0279) M ↔
      ∃ c ∈ template0279, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0279) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0279))
    cores template0279 witness0279 coverage0279
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0279) (maskBits m)) cores template0279 witness0279
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0279))
      coverage0279 catalogue_core_nodup coverageSize0279) (by rfl) M

#print axioms minimal_mask_iff0240
#print axioms minimal_mask_iff0279
end Crown.CertificateData
