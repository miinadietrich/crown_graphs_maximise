import generated.CatalogueBatch0011
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0010

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0400 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0400) M ↔
      ∃ c ∈ template0400, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0400) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0400))
    cores template0400 witness0400 coverage0400
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0400) (maskBits m)) cores template0400 witness0400
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0400))
      coverage0400 catalogue_core_nodup coverageSize0400) (by rfl) M

theorem minimal_mask_iff0401 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0401) M ↔
      ∃ c ∈ template0401, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0401) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0401))
    cores template0401 witness0401 coverage0401
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0401) (maskBits m)) cores template0401 witness0401
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0401))
      coverage0401 catalogue_core_nodup coverageSize0401) (by rfl) M

theorem minimal_mask_iff0402 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0402) M ↔
      ∃ c ∈ template0402, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0402) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0402))
    cores template0402 witness0402 coverage0402
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0402) (maskBits m)) cores template0402 witness0402
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0402))
      coverage0402 catalogue_core_nodup coverageSize0402) (by rfl) M

theorem minimal_mask_iff0403 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0403) M ↔
      ∃ c ∈ template0403, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0403) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0403))
    cores template0403 witness0403 coverage0403
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0403) (maskBits m)) cores template0403 witness0403
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0403))
      coverage0403 catalogue_core_nodup coverageSize0403) (by rfl) M

theorem minimal_mask_iff0404 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0404) M ↔
      ∃ c ∈ template0404, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0404) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0404))
    cores template0404 witness0404 coverage0404
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0404) (maskBits m)) cores template0404 witness0404
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0404))
      coverage0404 catalogue_core_nodup coverageSize0404) (by rfl) M

theorem minimal_mask_iff0405 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0405) M ↔
      ∃ c ∈ template0405, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0405) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0405))
    cores template0405 witness0405 coverage0405
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0405) (maskBits m)) cores template0405 witness0405
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0405))
      coverage0405 catalogue_core_nodup coverageSize0405) (by rfl) M

theorem minimal_mask_iff0406 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0406) M ↔
      ∃ c ∈ template0406, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0406) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0406))
    cores template0406 witness0406 coverage0406
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0406) (maskBits m)) cores template0406 witness0406
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0406))
      coverage0406 catalogue_core_nodup coverageSize0406) (by rfl) M

theorem minimal_mask_iff0407 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0407) M ↔
      ∃ c ∈ template0407, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0407) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0407))
    cores template0407 witness0407 coverage0407
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0407) (maskBits m)) cores template0407 witness0407
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0407))
      coverage0407 catalogue_core_nodup coverageSize0407) (by rfl) M

theorem minimal_mask_iff0408 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0408) M ↔
      ∃ c ∈ template0408, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0408) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0408))
    cores template0408 witness0408 coverage0408
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0408) (maskBits m)) cores template0408 witness0408
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0408))
      coverage0408 catalogue_core_nodup coverageSize0408) (by rfl) M

theorem minimal_mask_iff0409 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0409) M ↔
      ∃ c ∈ template0409, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0409) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0409))
    cores template0409 witness0409 coverage0409
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0409) (maskBits m)) cores template0409 witness0409
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0409))
      coverage0409 catalogue_core_nodup coverageSize0409) (by rfl) M

theorem minimal_mask_iff0410 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0410) M ↔
      ∃ c ∈ template0410, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0410) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0410))
    cores template0410 witness0410 coverage0410
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0410) (maskBits m)) cores template0410 witness0410
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0410))
      coverage0410 catalogue_core_nodup coverageSize0410) (by rfl) M

theorem minimal_mask_iff0411 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0411) M ↔
      ∃ c ∈ template0411, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0411) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0411))
    cores template0411 witness0411 coverage0411
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0411) (maskBits m)) cores template0411 witness0411
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0411))
      coverage0411 catalogue_core_nodup coverageSize0411) (by rfl) M

theorem minimal_mask_iff0412 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0412) M ↔
      ∃ c ∈ template0412, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0412) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0412))
    cores template0412 witness0412 coverage0412
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0412) (maskBits m)) cores template0412 witness0412
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0412))
      coverage0412 catalogue_core_nodup coverageSize0412) (by rfl) M

theorem minimal_mask_iff0413 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0413) M ↔
      ∃ c ∈ template0413, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0413) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0413))
    cores template0413 witness0413 coverage0413
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0413) (maskBits m)) cores template0413 witness0413
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0413))
      coverage0413 catalogue_core_nodup coverageSize0413) (by rfl) M

theorem minimal_mask_iff0414 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0414) M ↔
      ∃ c ∈ template0414, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0414) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0414))
    cores template0414 witness0414 coverage0414
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0414) (maskBits m)) cores template0414 witness0414
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0414))
      coverage0414 catalogue_core_nodup coverageSize0414) (by rfl) M

theorem minimal_mask_iff0415 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0415) M ↔
      ∃ c ∈ template0415, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0415) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0415))
    cores template0415 witness0415 coverage0415
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0415) (maskBits m)) cores template0415 witness0415
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0415))
      coverage0415 catalogue_core_nodup coverageSize0415) (by rfl) M

theorem minimal_mask_iff0416 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0416) M ↔
      ∃ c ∈ template0416, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0416) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0416))
    cores template0416 witness0416 coverage0416
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0416) (maskBits m)) cores template0416 witness0416
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0416))
      coverage0416 catalogue_core_nodup coverageSize0416) (by rfl) M

theorem minimal_mask_iff0417 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0417) M ↔
      ∃ c ∈ template0417, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0417) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0417))
    cores template0417 witness0417 coverage0417
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0417) (maskBits m)) cores template0417 witness0417
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0417))
      coverage0417 catalogue_core_nodup coverageSize0417) (by rfl) M

theorem minimal_mask_iff0418 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0418) M ↔
      ∃ c ∈ template0418, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0418) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0418))
    cores template0418 witness0418 coverage0418
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0418) (maskBits m)) cores template0418 witness0418
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0418))
      coverage0418 catalogue_core_nodup coverageSize0418) (by rfl) M

theorem minimal_mask_iff0419 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0419) M ↔
      ∃ c ∈ template0419, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0419) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0419))
    cores template0419 witness0419 coverage0419
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0419) (maskBits m)) cores template0419 witness0419
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0419))
      coverage0419 catalogue_core_nodup coverageSize0419) (by rfl) M

theorem minimal_mask_iff0420 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0420) M ↔
      ∃ c ∈ template0420, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0420) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0420))
    cores template0420 witness0420 coverage0420
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0420) (maskBits m)) cores template0420 witness0420
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0420))
      coverage0420 catalogue_core_nodup coverageSize0420) (by rfl) M

theorem minimal_mask_iff0421 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0421) M ↔
      ∃ c ∈ template0421, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0421) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0421))
    cores template0421 witness0421 coverage0421
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0421) (maskBits m)) cores template0421 witness0421
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0421))
      coverage0421 catalogue_core_nodup coverageSize0421) (by rfl) M

theorem minimal_mask_iff0422 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0422) M ↔
      ∃ c ∈ template0422, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0422) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0422))
    cores template0422 witness0422 coverage0422
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0422) (maskBits m)) cores template0422 witness0422
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0422))
      coverage0422 catalogue_core_nodup coverageSize0422) (by rfl) M

theorem minimal_mask_iff0423 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0423) M ↔
      ∃ c ∈ template0423, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0423) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0423))
    cores template0423 witness0423 coverage0423
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0423) (maskBits m)) cores template0423 witness0423
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0423))
      coverage0423 catalogue_core_nodup coverageSize0423) (by rfl) M

theorem minimal_mask_iff0424 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0424) M ↔
      ∃ c ∈ template0424, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0424) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0424))
    cores template0424 witness0424 coverage0424
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0424) (maskBits m)) cores template0424 witness0424
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0424))
      coverage0424 catalogue_core_nodup coverageSize0424) (by rfl) M

theorem minimal_mask_iff0425 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0425) M ↔
      ∃ c ∈ template0425, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0425) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0425))
    cores template0425 witness0425 coverage0425
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0425) (maskBits m)) cores template0425 witness0425
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0425))
      coverage0425 catalogue_core_nodup coverageSize0425) (by rfl) M

theorem minimal_mask_iff0426 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0426) M ↔
      ∃ c ∈ template0426, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0426) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0426))
    cores template0426 witness0426 coverage0426
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0426) (maskBits m)) cores template0426 witness0426
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0426))
      coverage0426 catalogue_core_nodup coverageSize0426) (by rfl) M

theorem minimal_mask_iff0427 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0427) M ↔
      ∃ c ∈ template0427, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0427) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0427))
    cores template0427 witness0427 coverage0427
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0427) (maskBits m)) cores template0427 witness0427
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0427))
      coverage0427 catalogue_core_nodup coverageSize0427) (by rfl) M

theorem minimal_mask_iff0428 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0428) M ↔
      ∃ c ∈ template0428, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0428) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0428))
    cores template0428 witness0428 coverage0428
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0428) (maskBits m)) cores template0428 witness0428
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0428))
      coverage0428 catalogue_core_nodup coverageSize0428) (by rfl) M

theorem minimal_mask_iff0429 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0429) M ↔
      ∃ c ∈ template0429, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0429) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0429))
    cores template0429 witness0429 coverage0429
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0429) (maskBits m)) cores template0429 witness0429
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0429))
      coverage0429 catalogue_core_nodup coverageSize0429) (by rfl) M

theorem minimal_mask_iff0430 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0430) M ↔
      ∃ c ∈ template0430, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0430) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0430))
    cores template0430 witness0430 coverage0430
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0430) (maskBits m)) cores template0430 witness0430
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0430))
      coverage0430 catalogue_core_nodup coverageSize0430) (by rfl) M

theorem minimal_mask_iff0431 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0431) M ↔
      ∃ c ∈ template0431, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0431) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0431))
    cores template0431 witness0431 coverage0431
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0431) (maskBits m)) cores template0431 witness0431
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0431))
      coverage0431 catalogue_core_nodup coverageSize0431) (by rfl) M

theorem minimal_mask_iff0432 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0432) M ↔
      ∃ c ∈ template0432, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0432) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0432))
    cores template0432 witness0432 coverage0432
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0432) (maskBits m)) cores template0432 witness0432
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0432))
      coverage0432 catalogue_core_nodup coverageSize0432) (by rfl) M

theorem minimal_mask_iff0433 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0433) M ↔
      ∃ c ∈ template0433, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0433) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0433))
    cores template0433 witness0433 coverage0433
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0433) (maskBits m)) cores template0433 witness0433
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0433))
      coverage0433 catalogue_core_nodup coverageSize0433) (by rfl) M

theorem minimal_mask_iff0434 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0434) M ↔
      ∃ c ∈ template0434, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0434) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0434))
    cores template0434 witness0434 coverage0434
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0434) (maskBits m)) cores template0434 witness0434
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0434))
      coverage0434 catalogue_core_nodup coverageSize0434) (by rfl) M

theorem minimal_mask_iff0435 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0435) M ↔
      ∃ c ∈ template0435, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0435) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0435))
    cores template0435 witness0435 coverage0435
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0435) (maskBits m)) cores template0435 witness0435
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0435))
      coverage0435 catalogue_core_nodup coverageSize0435) (by rfl) M

theorem minimal_mask_iff0436 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0436) M ↔
      ∃ c ∈ template0436, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0436) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0436))
    cores template0436 witness0436 coverage0436
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0436) (maskBits m)) cores template0436 witness0436
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0436))
      coverage0436 catalogue_core_nodup coverageSize0436) (by rfl) M

theorem minimal_mask_iff0437 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0437) M ↔
      ∃ c ∈ template0437, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0437) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0437))
    cores template0437 witness0437 coverage0437
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0437) (maskBits m)) cores template0437 witness0437
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0437))
      coverage0437 catalogue_core_nodup coverageSize0437) (by rfl) M

theorem minimal_mask_iff0438 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0438) M ↔
      ∃ c ∈ template0438, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0438) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0438))
    cores template0438 witness0438 coverage0438
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0438) (maskBits m)) cores template0438 witness0438
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0438))
      coverage0438 catalogue_core_nodup coverageSize0438) (by rfl) M

theorem minimal_mask_iff0439 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0439) M ↔
      ∃ c ∈ template0439, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0439) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0439))
    cores template0439 witness0439 coverage0439
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0439) (maskBits m)) cores template0439 witness0439
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0439))
      coverage0439 catalogue_core_nodup coverageSize0439) (by rfl) M

#print axioms minimal_mask_iff0400
#print axioms minimal_mask_iff0439
end Crown.CertificateData
