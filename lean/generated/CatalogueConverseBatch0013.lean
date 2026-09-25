import generated.CatalogueBatch0013
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0012

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0480 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0480) M ↔
      ∃ c ∈ template0480, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0480) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0480))
    cores template0480 witness0480 coverage0480
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0480) (maskBits m)) cores template0480 witness0480
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0480))
      coverage0480 catalogue_core_nodup coverageSize0480) (by rfl) M

theorem minimal_mask_iff0481 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0481) M ↔
      ∃ c ∈ template0481, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0481) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0481))
    cores template0481 witness0481 coverage0481
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0481) (maskBits m)) cores template0481 witness0481
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0481))
      coverage0481 catalogue_core_nodup coverageSize0481) (by rfl) M

theorem minimal_mask_iff0482 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0482) M ↔
      ∃ c ∈ template0482, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0482) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0482))
    cores template0482 witness0482 coverage0482
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0482) (maskBits m)) cores template0482 witness0482
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0482))
      coverage0482 catalogue_core_nodup coverageSize0482) (by rfl) M

theorem minimal_mask_iff0483 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0483) M ↔
      ∃ c ∈ template0483, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0483) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0483))
    cores template0483 witness0483 coverage0483
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0483) (maskBits m)) cores template0483 witness0483
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0483))
      coverage0483 catalogue_core_nodup coverageSize0483) (by rfl) M

theorem minimal_mask_iff0484 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0484) M ↔
      ∃ c ∈ template0484, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0484) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0484))
    cores template0484 witness0484 coverage0484
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0484) (maskBits m)) cores template0484 witness0484
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0484))
      coverage0484 catalogue_core_nodup coverageSize0484) (by rfl) M

theorem minimal_mask_iff0485 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0485) M ↔
      ∃ c ∈ template0485, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0485) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0485))
    cores template0485 witness0485 coverage0485
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0485) (maskBits m)) cores template0485 witness0485
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0485))
      coverage0485 catalogue_core_nodup coverageSize0485) (by rfl) M

theorem minimal_mask_iff0486 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0486) M ↔
      ∃ c ∈ template0486, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0486) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0486))
    cores template0486 witness0486 coverage0486
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0486) (maskBits m)) cores template0486 witness0486
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0486))
      coverage0486 catalogue_core_nodup coverageSize0486) (by rfl) M

theorem minimal_mask_iff0487 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0487) M ↔
      ∃ c ∈ template0487, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0487) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0487))
    cores template0487 witness0487 coverage0487
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0487) (maskBits m)) cores template0487 witness0487
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0487))
      coverage0487 catalogue_core_nodup coverageSize0487) (by rfl) M

theorem minimal_mask_iff0488 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0488) M ↔
      ∃ c ∈ template0488, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0488) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0488))
    cores template0488 witness0488 coverage0488
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0488) (maskBits m)) cores template0488 witness0488
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0488))
      coverage0488 catalogue_core_nodup coverageSize0488) (by rfl) M

theorem minimal_mask_iff0489 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0489) M ↔
      ∃ c ∈ template0489, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0489) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0489))
    cores template0489 witness0489 coverage0489
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0489) (maskBits m)) cores template0489 witness0489
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0489))
      coverage0489 catalogue_core_nodup coverageSize0489) (by rfl) M

theorem minimal_mask_iff0490 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0490) M ↔
      ∃ c ∈ template0490, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0490) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0490))
    cores template0490 witness0490 coverage0490
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0490) (maskBits m)) cores template0490 witness0490
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0490))
      coverage0490 catalogue_core_nodup coverageSize0490) (by rfl) M

theorem minimal_mask_iff0491 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0491) M ↔
      ∃ c ∈ template0491, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0491) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0491))
    cores template0491 witness0491 coverage0491
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0491) (maskBits m)) cores template0491 witness0491
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0491))
      coverage0491 catalogue_core_nodup coverageSize0491) (by rfl) M

theorem minimal_mask_iff0492 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0492) M ↔
      ∃ c ∈ template0492, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0492) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0492))
    cores template0492 witness0492 coverage0492
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0492) (maskBits m)) cores template0492 witness0492
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0492))
      coverage0492 catalogue_core_nodup coverageSize0492) (by rfl) M

theorem minimal_mask_iff0493 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0493) M ↔
      ∃ c ∈ template0493, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0493) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0493))
    cores template0493 witness0493 coverage0493
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0493) (maskBits m)) cores template0493 witness0493
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0493))
      coverage0493 catalogue_core_nodup coverageSize0493) (by rfl) M

theorem minimal_mask_iff0494 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0494) M ↔
      ∃ c ∈ template0494, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0494) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0494))
    cores template0494 witness0494 coverage0494
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0494) (maskBits m)) cores template0494 witness0494
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0494))
      coverage0494 catalogue_core_nodup coverageSize0494) (by rfl) M

theorem minimal_mask_iff0495 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0495) M ↔
      ∃ c ∈ template0495, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0495) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0495))
    cores template0495 witness0495 coverage0495
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0495) (maskBits m)) cores template0495 witness0495
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0495))
      coverage0495 catalogue_core_nodup coverageSize0495) (by rfl) M

theorem minimal_mask_iff0496 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0496) M ↔
      ∃ c ∈ template0496, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0496) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0496))
    cores template0496 witness0496 coverage0496
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0496) (maskBits m)) cores template0496 witness0496
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0496))
      coverage0496 catalogue_core_nodup coverageSize0496) (by rfl) M

theorem minimal_mask_iff0497 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0497) M ↔
      ∃ c ∈ template0497, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0497) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0497))
    cores template0497 witness0497 coverage0497
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0497) (maskBits m)) cores template0497 witness0497
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0497))
      coverage0497 catalogue_core_nodup coverageSize0497) (by rfl) M

theorem minimal_mask_iff0498 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0498) M ↔
      ∃ c ∈ template0498, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0498) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0498))
    cores template0498 witness0498 coverage0498
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0498) (maskBits m)) cores template0498 witness0498
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0498))
      coverage0498 catalogue_core_nodup coverageSize0498) (by rfl) M

theorem minimal_mask_iff0499 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0499) M ↔
      ∃ c ∈ template0499, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0499) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0499))
    cores template0499 witness0499 coverage0499
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0499) (maskBits m)) cores template0499 witness0499
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0499))
      coverage0499 catalogue_core_nodup coverageSize0499) (by rfl) M

theorem minimal_mask_iff0500 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0500) M ↔
      ∃ c ∈ template0500, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0500) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0500))
    cores template0500 witness0500 coverage0500
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0500) (maskBits m)) cores template0500 witness0500
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0500))
      coverage0500 catalogue_core_nodup coverageSize0500) (by rfl) M

theorem minimal_mask_iff0501 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0501) M ↔
      ∃ c ∈ template0501, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0501) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0501))
    cores template0501 witness0501 coverage0501
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0501) (maskBits m)) cores template0501 witness0501
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0501))
      coverage0501 catalogue_core_nodup coverageSize0501) (by rfl) M

theorem minimal_mask_iff0502 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0502) M ↔
      ∃ c ∈ template0502, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0502) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0502))
    cores template0502 witness0502 coverage0502
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0502) (maskBits m)) cores template0502 witness0502
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0502))
      coverage0502 catalogue_core_nodup coverageSize0502) (by rfl) M

theorem minimal_mask_iff0503 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0503) M ↔
      ∃ c ∈ template0503, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0503) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0503))
    cores template0503 witness0503 coverage0503
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0503) (maskBits m)) cores template0503 witness0503
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0503))
      coverage0503 catalogue_core_nodup coverageSize0503) (by rfl) M

theorem minimal_mask_iff0504 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0504) M ↔
      ∃ c ∈ template0504, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0504) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0504))
    cores template0504 witness0504 coverage0504
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0504) (maskBits m)) cores template0504 witness0504
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0504))
      coverage0504 catalogue_core_nodup coverageSize0504) (by rfl) M

theorem minimal_mask_iff0505 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0505) M ↔
      ∃ c ∈ template0505, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0505) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0505))
    cores template0505 witness0505 coverage0505
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0505) (maskBits m)) cores template0505 witness0505
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0505))
      coverage0505 catalogue_core_nodup coverageSize0505) (by rfl) M

theorem minimal_mask_iff0506 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0506) M ↔
      ∃ c ∈ template0506, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0506) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0506))
    cores template0506 witness0506 coverage0506
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0506) (maskBits m)) cores template0506 witness0506
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0506))
      coverage0506 catalogue_core_nodup coverageSize0506) (by rfl) M

theorem minimal_mask_iff0507 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0507) M ↔
      ∃ c ∈ template0507, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0507) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0507))
    cores template0507 witness0507 coverage0507
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0507) (maskBits m)) cores template0507 witness0507
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0507))
      coverage0507 catalogue_core_nodup coverageSize0507) (by rfl) M

theorem minimal_mask_iff0508 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0508) M ↔
      ∃ c ∈ template0508, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0508) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0508))
    cores template0508 witness0508 coverage0508
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0508) (maskBits m)) cores template0508 witness0508
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0508))
      coverage0508 catalogue_core_nodup coverageSize0508) (by rfl) M

theorem minimal_mask_iff0509 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0509) M ↔
      ∃ c ∈ template0509, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0509) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0509))
    cores template0509 witness0509 coverage0509
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0509) (maskBits m)) cores template0509 witness0509
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0509))
      coverage0509 catalogue_core_nodup coverageSize0509) (by rfl) M

theorem minimal_mask_iff0510 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0510) M ↔
      ∃ c ∈ template0510, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0510) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0510))
    cores template0510 witness0510 coverage0510
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0510) (maskBits m)) cores template0510 witness0510
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0510))
      coverage0510 catalogue_core_nodup coverageSize0510) (by rfl) M

theorem minimal_mask_iff0511 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0511) M ↔
      ∃ c ∈ template0511, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0511) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0511))
    cores template0511 witness0511 coverage0511
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0511) (maskBits m)) cores template0511 witness0511
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0511))
      coverage0511 catalogue_core_nodup coverageSize0511) (by rfl) M

theorem minimal_mask_iff0512 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0512) M ↔
      ∃ c ∈ template0512, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0512) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0512))
    cores template0512 witness0512 coverage0512
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0512) (maskBits m)) cores template0512 witness0512
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0512))
      coverage0512 catalogue_core_nodup coverageSize0512) (by rfl) M

theorem minimal_mask_iff0513 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0513) M ↔
      ∃ c ∈ template0513, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0513) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0513))
    cores template0513 witness0513 coverage0513
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0513) (maskBits m)) cores template0513 witness0513
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0513))
      coverage0513 catalogue_core_nodup coverageSize0513) (by rfl) M

theorem minimal_mask_iff0514 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0514) M ↔
      ∃ c ∈ template0514, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0514) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0514))
    cores template0514 witness0514 coverage0514
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0514) (maskBits m)) cores template0514 witness0514
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0514))
      coverage0514 catalogue_core_nodup coverageSize0514) (by rfl) M

theorem minimal_mask_iff0515 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0515) M ↔
      ∃ c ∈ template0515, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0515) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0515))
    cores template0515 witness0515 coverage0515
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0515) (maskBits m)) cores template0515 witness0515
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0515))
      coverage0515 catalogue_core_nodup coverageSize0515) (by rfl) M

theorem minimal_mask_iff0516 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0516) M ↔
      ∃ c ∈ template0516, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0516) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0516))
    cores template0516 witness0516 coverage0516
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0516) (maskBits m)) cores template0516 witness0516
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0516))
      coverage0516 catalogue_core_nodup coverageSize0516) (by rfl) M

theorem minimal_mask_iff0517 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0517) M ↔
      ∃ c ∈ template0517, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0517) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0517))
    cores template0517 witness0517 coverage0517
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0517) (maskBits m)) cores template0517 witness0517
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0517))
      coverage0517 catalogue_core_nodup coverageSize0517) (by rfl) M

theorem minimal_mask_iff0518 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0518) M ↔
      ∃ c ∈ template0518, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0518) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0518))
    cores template0518 witness0518 coverage0518
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0518) (maskBits m)) cores template0518 witness0518
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0518))
      coverage0518 catalogue_core_nodup coverageSize0518) (by rfl) M

theorem minimal_mask_iff0519 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0519) M ↔
      ∃ c ∈ template0519, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0519) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0519))
    cores template0519 witness0519 coverage0519
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0519) (maskBits m)) cores template0519 witness0519
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0519))
      coverage0519 catalogue_core_nodup coverageSize0519) (by rfl) M

#print axioms minimal_mask_iff0480
#print axioms minimal_mask_iff0519
end Crown.CertificateData
