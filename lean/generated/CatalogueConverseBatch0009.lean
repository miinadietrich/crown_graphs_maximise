import generated.CatalogueBatch0009
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0008

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0320 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0320) M ↔
      ∃ c ∈ template0320, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0320) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0320))
    cores template0320 witness0320 coverage0320
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0320) (maskBits m)) cores template0320 witness0320
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0320))
      coverage0320 catalogue_core_nodup coverageSize0320) (by rfl) M

theorem minimal_mask_iff0321 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0321) M ↔
      ∃ c ∈ template0321, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0321) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0321))
    cores template0321 witness0321 coverage0321
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0321) (maskBits m)) cores template0321 witness0321
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0321))
      coverage0321 catalogue_core_nodup coverageSize0321) (by rfl) M

theorem minimal_mask_iff0322 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0322) M ↔
      ∃ c ∈ template0322, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0322) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0322))
    cores template0322 witness0322 coverage0322
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0322) (maskBits m)) cores template0322 witness0322
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0322))
      coverage0322 catalogue_core_nodup coverageSize0322) (by rfl) M

theorem minimal_mask_iff0323 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0323) M ↔
      ∃ c ∈ template0323, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0323) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0323))
    cores template0323 witness0323 coverage0323
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0323) (maskBits m)) cores template0323 witness0323
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0323))
      coverage0323 catalogue_core_nodup coverageSize0323) (by rfl) M

theorem minimal_mask_iff0324 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0324) M ↔
      ∃ c ∈ template0324, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0324) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0324))
    cores template0324 witness0324 coverage0324
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0324) (maskBits m)) cores template0324 witness0324
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0324))
      coverage0324 catalogue_core_nodup coverageSize0324) (by rfl) M

theorem minimal_mask_iff0325 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0325) M ↔
      ∃ c ∈ template0325, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0325) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0325))
    cores template0325 witness0325 coverage0325
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0325) (maskBits m)) cores template0325 witness0325
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0325))
      coverage0325 catalogue_core_nodup coverageSize0325) (by rfl) M

theorem minimal_mask_iff0326 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0326) M ↔
      ∃ c ∈ template0326, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0326) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0326))
    cores template0326 witness0326 coverage0326
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0326) (maskBits m)) cores template0326 witness0326
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0326))
      coverage0326 catalogue_core_nodup coverageSize0326) (by rfl) M

theorem minimal_mask_iff0327 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0327) M ↔
      ∃ c ∈ template0327, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0327) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0327))
    cores template0327 witness0327 coverage0327
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0327) (maskBits m)) cores template0327 witness0327
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0327))
      coverage0327 catalogue_core_nodup coverageSize0327) (by rfl) M

theorem minimal_mask_iff0328 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0328) M ↔
      ∃ c ∈ template0328, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0328) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0328))
    cores template0328 witness0328 coverage0328
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0328) (maskBits m)) cores template0328 witness0328
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0328))
      coverage0328 catalogue_core_nodup coverageSize0328) (by rfl) M

theorem minimal_mask_iff0329 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0329) M ↔
      ∃ c ∈ template0329, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0329) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0329))
    cores template0329 witness0329 coverage0329
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0329) (maskBits m)) cores template0329 witness0329
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0329))
      coverage0329 catalogue_core_nodup coverageSize0329) (by rfl) M

theorem minimal_mask_iff0330 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0330) M ↔
      ∃ c ∈ template0330, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0330) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0330))
    cores template0330 witness0330 coverage0330
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0330) (maskBits m)) cores template0330 witness0330
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0330))
      coverage0330 catalogue_core_nodup coverageSize0330) (by rfl) M

theorem minimal_mask_iff0331 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0331) M ↔
      ∃ c ∈ template0331, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0331) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0331))
    cores template0331 witness0331 coverage0331
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0331) (maskBits m)) cores template0331 witness0331
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0331))
      coverage0331 catalogue_core_nodup coverageSize0331) (by rfl) M

theorem minimal_mask_iff0332 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0332) M ↔
      ∃ c ∈ template0332, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0332) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0332))
    cores template0332 witness0332 coverage0332
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0332) (maskBits m)) cores template0332 witness0332
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0332))
      coverage0332 catalogue_core_nodup coverageSize0332) (by rfl) M

theorem minimal_mask_iff0333 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0333) M ↔
      ∃ c ∈ template0333, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0333) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0333))
    cores template0333 witness0333 coverage0333
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0333) (maskBits m)) cores template0333 witness0333
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0333))
      coverage0333 catalogue_core_nodup coverageSize0333) (by rfl) M

theorem minimal_mask_iff0334 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0334) M ↔
      ∃ c ∈ template0334, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0334) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0334))
    cores template0334 witness0334 coverage0334
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0334) (maskBits m)) cores template0334 witness0334
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0334))
      coverage0334 catalogue_core_nodup coverageSize0334) (by rfl) M

theorem minimal_mask_iff0335 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0335) M ↔
      ∃ c ∈ template0335, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0335) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0335))
    cores template0335 witness0335 coverage0335
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0335) (maskBits m)) cores template0335 witness0335
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0335))
      coverage0335 catalogue_core_nodup coverageSize0335) (by rfl) M

theorem minimal_mask_iff0336 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0336) M ↔
      ∃ c ∈ template0336, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0336) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0336))
    cores template0336 witness0336 coverage0336
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0336) (maskBits m)) cores template0336 witness0336
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0336))
      coverage0336 catalogue_core_nodup coverageSize0336) (by rfl) M

theorem minimal_mask_iff0337 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0337) M ↔
      ∃ c ∈ template0337, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0337) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0337))
    cores template0337 witness0337 coverage0337
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0337) (maskBits m)) cores template0337 witness0337
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0337))
      coverage0337 catalogue_core_nodup coverageSize0337) (by rfl) M

theorem minimal_mask_iff0338 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0338) M ↔
      ∃ c ∈ template0338, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0338) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0338))
    cores template0338 witness0338 coverage0338
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0338) (maskBits m)) cores template0338 witness0338
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0338))
      coverage0338 catalogue_core_nodup coverageSize0338) (by rfl) M

theorem minimal_mask_iff0339 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0339) M ↔
      ∃ c ∈ template0339, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0339) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0339))
    cores template0339 witness0339 coverage0339
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0339) (maskBits m)) cores template0339 witness0339
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0339))
      coverage0339 catalogue_core_nodup coverageSize0339) (by rfl) M

theorem minimal_mask_iff0340 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0340) M ↔
      ∃ c ∈ template0340, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0340) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0340))
    cores template0340 witness0340 coverage0340
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0340) (maskBits m)) cores template0340 witness0340
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0340))
      coverage0340 catalogue_core_nodup coverageSize0340) (by rfl) M

theorem minimal_mask_iff0341 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0341) M ↔
      ∃ c ∈ template0341, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0341) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0341))
    cores template0341 witness0341 coverage0341
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0341) (maskBits m)) cores template0341 witness0341
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0341))
      coverage0341 catalogue_core_nodup coverageSize0341) (by rfl) M

theorem minimal_mask_iff0342 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0342) M ↔
      ∃ c ∈ template0342, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0342) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0342))
    cores template0342 witness0342 coverage0342
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0342) (maskBits m)) cores template0342 witness0342
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0342))
      coverage0342 catalogue_core_nodup coverageSize0342) (by rfl) M

theorem minimal_mask_iff0343 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0343) M ↔
      ∃ c ∈ template0343, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0343) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0343))
    cores template0343 witness0343 coverage0343
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0343) (maskBits m)) cores template0343 witness0343
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0343))
      coverage0343 catalogue_core_nodup coverageSize0343) (by rfl) M

theorem minimal_mask_iff0344 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0344) M ↔
      ∃ c ∈ template0344, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0344) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0344))
    cores template0344 witness0344 coverage0344
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0344) (maskBits m)) cores template0344 witness0344
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0344))
      coverage0344 catalogue_core_nodup coverageSize0344) (by rfl) M

theorem minimal_mask_iff0345 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0345) M ↔
      ∃ c ∈ template0345, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0345) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0345))
    cores template0345 witness0345 coverage0345
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0345) (maskBits m)) cores template0345 witness0345
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0345))
      coverage0345 catalogue_core_nodup coverageSize0345) (by rfl) M

theorem minimal_mask_iff0346 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0346) M ↔
      ∃ c ∈ template0346, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0346) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0346))
    cores template0346 witness0346 coverage0346
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0346) (maskBits m)) cores template0346 witness0346
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0346))
      coverage0346 catalogue_core_nodup coverageSize0346) (by rfl) M

theorem minimal_mask_iff0347 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0347) M ↔
      ∃ c ∈ template0347, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0347) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0347))
    cores template0347 witness0347 coverage0347
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0347) (maskBits m)) cores template0347 witness0347
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0347))
      coverage0347 catalogue_core_nodup coverageSize0347) (by rfl) M

theorem minimal_mask_iff0348 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0348) M ↔
      ∃ c ∈ template0348, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0348) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0348))
    cores template0348 witness0348 coverage0348
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0348) (maskBits m)) cores template0348 witness0348
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0348))
      coverage0348 catalogue_core_nodup coverageSize0348) (by rfl) M

theorem minimal_mask_iff0349 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0349) M ↔
      ∃ c ∈ template0349, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0349) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0349))
    cores template0349 witness0349 coverage0349
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0349) (maskBits m)) cores template0349 witness0349
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0349))
      coverage0349 catalogue_core_nodup coverageSize0349) (by rfl) M

theorem minimal_mask_iff0350 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0350) M ↔
      ∃ c ∈ template0350, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0350) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0350))
    cores template0350 witness0350 coverage0350
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0350) (maskBits m)) cores template0350 witness0350
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0350))
      coverage0350 catalogue_core_nodup coverageSize0350) (by rfl) M

theorem minimal_mask_iff0351 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0351) M ↔
      ∃ c ∈ template0351, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0351) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0351))
    cores template0351 witness0351 coverage0351
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0351) (maskBits m)) cores template0351 witness0351
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0351))
      coverage0351 catalogue_core_nodup coverageSize0351) (by rfl) M

theorem minimal_mask_iff0352 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0352) M ↔
      ∃ c ∈ template0352, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0352) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0352))
    cores template0352 witness0352 coverage0352
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0352) (maskBits m)) cores template0352 witness0352
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0352))
      coverage0352 catalogue_core_nodup coverageSize0352) (by rfl) M

theorem minimal_mask_iff0353 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0353) M ↔
      ∃ c ∈ template0353, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0353) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0353))
    cores template0353 witness0353 coverage0353
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0353) (maskBits m)) cores template0353 witness0353
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0353))
      coverage0353 catalogue_core_nodup coverageSize0353) (by rfl) M

theorem minimal_mask_iff0354 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0354) M ↔
      ∃ c ∈ template0354, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0354) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0354))
    cores template0354 witness0354 coverage0354
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0354) (maskBits m)) cores template0354 witness0354
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0354))
      coverage0354 catalogue_core_nodup coverageSize0354) (by rfl) M

theorem minimal_mask_iff0355 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0355) M ↔
      ∃ c ∈ template0355, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0355) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0355))
    cores template0355 witness0355 coverage0355
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0355) (maskBits m)) cores template0355 witness0355
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0355))
      coverage0355 catalogue_core_nodup coverageSize0355) (by rfl) M

theorem minimal_mask_iff0356 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0356) M ↔
      ∃ c ∈ template0356, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0356) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0356))
    cores template0356 witness0356 coverage0356
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0356) (maskBits m)) cores template0356 witness0356
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0356))
      coverage0356 catalogue_core_nodup coverageSize0356) (by rfl) M

theorem minimal_mask_iff0357 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0357) M ↔
      ∃ c ∈ template0357, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0357) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0357))
    cores template0357 witness0357 coverage0357
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0357) (maskBits m)) cores template0357 witness0357
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0357))
      coverage0357 catalogue_core_nodup coverageSize0357) (by rfl) M

theorem minimal_mask_iff0358 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0358) M ↔
      ∃ c ∈ template0358, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0358) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0358))
    cores template0358 witness0358 coverage0358
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0358) (maskBits m)) cores template0358 witness0358
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0358))
      coverage0358 catalogue_core_nodup coverageSize0358) (by rfl) M

theorem minimal_mask_iff0359 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0359) M ↔
      ∃ c ∈ template0359, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0359) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0359))
    cores template0359 witness0359 coverage0359
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0359) (maskBits m)) cores template0359 witness0359
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0359))
      coverage0359 catalogue_core_nodup coverageSize0359) (by rfl) M

#print axioms minimal_mask_iff0320
#print axioms minimal_mask_iff0359
end Crown.CertificateData
