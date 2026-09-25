import generated.CatalogueBatch0008
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0007

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0280 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0280) M ↔
      ∃ c ∈ template0280, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0280) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0280))
    cores template0280 witness0280 coverage0280
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0280) (maskBits m)) cores template0280 witness0280
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0280))
      coverage0280 catalogue_core_nodup coverageSize0280) (by rfl) M

theorem minimal_mask_iff0281 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0281) M ↔
      ∃ c ∈ template0281, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0281) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0281))
    cores template0281 witness0281 coverage0281
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0281) (maskBits m)) cores template0281 witness0281
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0281))
      coverage0281 catalogue_core_nodup coverageSize0281) (by rfl) M

theorem minimal_mask_iff0282 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0282) M ↔
      ∃ c ∈ template0282, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0282) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0282))
    cores template0282 witness0282 coverage0282
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0282) (maskBits m)) cores template0282 witness0282
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0282))
      coverage0282 catalogue_core_nodup coverageSize0282) (by rfl) M

theorem minimal_mask_iff0283 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0283) M ↔
      ∃ c ∈ template0283, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0283) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0283))
    cores template0283 witness0283 coverage0283
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0283) (maskBits m)) cores template0283 witness0283
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0283))
      coverage0283 catalogue_core_nodup coverageSize0283) (by rfl) M

theorem minimal_mask_iff0284 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0284) M ↔
      ∃ c ∈ template0284, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0284) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0284))
    cores template0284 witness0284 coverage0284
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0284) (maskBits m)) cores template0284 witness0284
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0284))
      coverage0284 catalogue_core_nodup coverageSize0284) (by rfl) M

theorem minimal_mask_iff0285 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0285) M ↔
      ∃ c ∈ template0285, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0285) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0285))
    cores template0285 witness0285 coverage0285
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0285) (maskBits m)) cores template0285 witness0285
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0285))
      coverage0285 catalogue_core_nodup coverageSize0285) (by rfl) M

theorem minimal_mask_iff0286 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0286) M ↔
      ∃ c ∈ template0286, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0286) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0286))
    cores template0286 witness0286 coverage0286
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0286) (maskBits m)) cores template0286 witness0286
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0286))
      coverage0286 catalogue_core_nodup coverageSize0286) (by rfl) M

theorem minimal_mask_iff0287 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0287) M ↔
      ∃ c ∈ template0287, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0287) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0287))
    cores template0287 witness0287 coverage0287
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0287) (maskBits m)) cores template0287 witness0287
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0287))
      coverage0287 catalogue_core_nodup coverageSize0287) (by rfl) M

theorem minimal_mask_iff0288 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0288) M ↔
      ∃ c ∈ template0288, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0288) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0288))
    cores template0288 witness0288 coverage0288
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0288) (maskBits m)) cores template0288 witness0288
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0288))
      coverage0288 catalogue_core_nodup coverageSize0288) (by rfl) M

theorem minimal_mask_iff0289 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0289) M ↔
      ∃ c ∈ template0289, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0289) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0289))
    cores template0289 witness0289 coverage0289
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0289) (maskBits m)) cores template0289 witness0289
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0289))
      coverage0289 catalogue_core_nodup coverageSize0289) (by rfl) M

theorem minimal_mask_iff0290 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0290) M ↔
      ∃ c ∈ template0290, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0290) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0290))
    cores template0290 witness0290 coverage0290
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0290) (maskBits m)) cores template0290 witness0290
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0290))
      coverage0290 catalogue_core_nodup coverageSize0290) (by rfl) M

theorem minimal_mask_iff0291 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0291) M ↔
      ∃ c ∈ template0291, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0291) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0291))
    cores template0291 witness0291 coverage0291
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0291) (maskBits m)) cores template0291 witness0291
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0291))
      coverage0291 catalogue_core_nodup coverageSize0291) (by rfl) M

theorem minimal_mask_iff0292 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0292) M ↔
      ∃ c ∈ template0292, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0292) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0292))
    cores template0292 witness0292 coverage0292
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0292) (maskBits m)) cores template0292 witness0292
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0292))
      coverage0292 catalogue_core_nodup coverageSize0292) (by rfl) M

theorem minimal_mask_iff0293 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0293) M ↔
      ∃ c ∈ template0293, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0293) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0293))
    cores template0293 witness0293 coverage0293
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0293) (maskBits m)) cores template0293 witness0293
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0293))
      coverage0293 catalogue_core_nodup coverageSize0293) (by rfl) M

theorem minimal_mask_iff0294 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0294) M ↔
      ∃ c ∈ template0294, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0294) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0294))
    cores template0294 witness0294 coverage0294
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0294) (maskBits m)) cores template0294 witness0294
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0294))
      coverage0294 catalogue_core_nodup coverageSize0294) (by rfl) M

theorem minimal_mask_iff0295 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0295) M ↔
      ∃ c ∈ template0295, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0295) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0295))
    cores template0295 witness0295 coverage0295
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0295) (maskBits m)) cores template0295 witness0295
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0295))
      coverage0295 catalogue_core_nodup coverageSize0295) (by rfl) M

theorem minimal_mask_iff0296 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0296) M ↔
      ∃ c ∈ template0296, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0296) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0296))
    cores template0296 witness0296 coverage0296
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0296) (maskBits m)) cores template0296 witness0296
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0296))
      coverage0296 catalogue_core_nodup coverageSize0296) (by rfl) M

theorem minimal_mask_iff0297 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0297) M ↔
      ∃ c ∈ template0297, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0297) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0297))
    cores template0297 witness0297 coverage0297
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0297) (maskBits m)) cores template0297 witness0297
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0297))
      coverage0297 catalogue_core_nodup coverageSize0297) (by rfl) M

theorem minimal_mask_iff0298 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0298) M ↔
      ∃ c ∈ template0298, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0298) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0298))
    cores template0298 witness0298 coverage0298
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0298) (maskBits m)) cores template0298 witness0298
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0298))
      coverage0298 catalogue_core_nodup coverageSize0298) (by rfl) M

theorem minimal_mask_iff0299 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0299) M ↔
      ∃ c ∈ template0299, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0299) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0299))
    cores template0299 witness0299 coverage0299
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0299) (maskBits m)) cores template0299 witness0299
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0299))
      coverage0299 catalogue_core_nodup coverageSize0299) (by rfl) M

theorem minimal_mask_iff0300 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0300) M ↔
      ∃ c ∈ template0300, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0300) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0300))
    cores template0300 witness0300 coverage0300
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0300) (maskBits m)) cores template0300 witness0300
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0300))
      coverage0300 catalogue_core_nodup coverageSize0300) (by rfl) M

theorem minimal_mask_iff0301 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0301) M ↔
      ∃ c ∈ template0301, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0301) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0301))
    cores template0301 witness0301 coverage0301
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0301) (maskBits m)) cores template0301 witness0301
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0301))
      coverage0301 catalogue_core_nodup coverageSize0301) (by rfl) M

theorem minimal_mask_iff0302 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0302) M ↔
      ∃ c ∈ template0302, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0302) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0302))
    cores template0302 witness0302 coverage0302
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0302) (maskBits m)) cores template0302 witness0302
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0302))
      coverage0302 catalogue_core_nodup coverageSize0302) (by rfl) M

theorem minimal_mask_iff0303 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0303) M ↔
      ∃ c ∈ template0303, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0303) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0303))
    cores template0303 witness0303 coverage0303
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0303) (maskBits m)) cores template0303 witness0303
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0303))
      coverage0303 catalogue_core_nodup coverageSize0303) (by rfl) M

theorem minimal_mask_iff0304 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0304) M ↔
      ∃ c ∈ template0304, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0304) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0304))
    cores template0304 witness0304 coverage0304
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0304) (maskBits m)) cores template0304 witness0304
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0304))
      coverage0304 catalogue_core_nodup coverageSize0304) (by rfl) M

theorem minimal_mask_iff0305 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0305) M ↔
      ∃ c ∈ template0305, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0305) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0305))
    cores template0305 witness0305 coverage0305
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0305) (maskBits m)) cores template0305 witness0305
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0305))
      coverage0305 catalogue_core_nodup coverageSize0305) (by rfl) M

theorem minimal_mask_iff0306 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0306) M ↔
      ∃ c ∈ template0306, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0306) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0306))
    cores template0306 witness0306 coverage0306
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0306) (maskBits m)) cores template0306 witness0306
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0306))
      coverage0306 catalogue_core_nodup coverageSize0306) (by rfl) M

theorem minimal_mask_iff0307 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0307) M ↔
      ∃ c ∈ template0307, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0307) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0307))
    cores template0307 witness0307 coverage0307
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0307) (maskBits m)) cores template0307 witness0307
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0307))
      coverage0307 catalogue_core_nodup coverageSize0307) (by rfl) M

theorem minimal_mask_iff0308 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0308) M ↔
      ∃ c ∈ template0308, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0308) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0308))
    cores template0308 witness0308 coverage0308
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0308) (maskBits m)) cores template0308 witness0308
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0308))
      coverage0308 catalogue_core_nodup coverageSize0308) (by rfl) M

theorem minimal_mask_iff0309 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0309) M ↔
      ∃ c ∈ template0309, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0309) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0309))
    cores template0309 witness0309 coverage0309
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0309) (maskBits m)) cores template0309 witness0309
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0309))
      coverage0309 catalogue_core_nodup coverageSize0309) (by rfl) M

theorem minimal_mask_iff0310 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0310) M ↔
      ∃ c ∈ template0310, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0310) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0310))
    cores template0310 witness0310 coverage0310
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0310) (maskBits m)) cores template0310 witness0310
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0310))
      coverage0310 catalogue_core_nodup coverageSize0310) (by rfl) M

theorem minimal_mask_iff0311 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0311) M ↔
      ∃ c ∈ template0311, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0311) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0311))
    cores template0311 witness0311 coverage0311
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0311) (maskBits m)) cores template0311 witness0311
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0311))
      coverage0311 catalogue_core_nodup coverageSize0311) (by rfl) M

theorem minimal_mask_iff0312 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0312) M ↔
      ∃ c ∈ template0312, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0312) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0312))
    cores template0312 witness0312 coverage0312
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0312) (maskBits m)) cores template0312 witness0312
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0312))
      coverage0312 catalogue_core_nodup coverageSize0312) (by rfl) M

theorem minimal_mask_iff0313 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0313) M ↔
      ∃ c ∈ template0313, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0313) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0313))
    cores template0313 witness0313 coverage0313
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0313) (maskBits m)) cores template0313 witness0313
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0313))
      coverage0313 catalogue_core_nodup coverageSize0313) (by rfl) M

theorem minimal_mask_iff0314 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0314) M ↔
      ∃ c ∈ template0314, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0314) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0314))
    cores template0314 witness0314 coverage0314
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0314) (maskBits m)) cores template0314 witness0314
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0314))
      coverage0314 catalogue_core_nodup coverageSize0314) (by rfl) M

theorem minimal_mask_iff0315 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0315) M ↔
      ∃ c ∈ template0315, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0315) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0315))
    cores template0315 witness0315 coverage0315
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0315) (maskBits m)) cores template0315 witness0315
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0315))
      coverage0315 catalogue_core_nodup coverageSize0315) (by rfl) M

theorem minimal_mask_iff0316 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0316) M ↔
      ∃ c ∈ template0316, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0316) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0316))
    cores template0316 witness0316 coverage0316
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0316) (maskBits m)) cores template0316 witness0316
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0316))
      coverage0316 catalogue_core_nodup coverageSize0316) (by rfl) M

theorem minimal_mask_iff0317 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0317) M ↔
      ∃ c ∈ template0317, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0317) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0317))
    cores template0317 witness0317 coverage0317
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0317) (maskBits m)) cores template0317 witness0317
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0317))
      coverage0317 catalogue_core_nodup coverageSize0317) (by rfl) M

theorem minimal_mask_iff0318 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0318) M ↔
      ∃ c ∈ template0318, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0318) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0318))
    cores template0318 witness0318 coverage0318
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0318) (maskBits m)) cores template0318 witness0318
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0318))
      coverage0318 catalogue_core_nodup coverageSize0318) (by rfl) M

theorem minimal_mask_iff0319 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0319) M ↔
      ∃ c ∈ template0319, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0319) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0319))
    cores template0319 witness0319 coverage0319
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0319) (maskBits m)) cores template0319 witness0319
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0319))
      coverage0319 catalogue_core_nodup coverageSize0319) (by rfl) M

#print axioms minimal_mask_iff0280
#print axioms minimal_mask_iff0319
end Crown.CertificateData
