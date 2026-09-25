import generated.CatalogueBatch0012
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0011

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0440 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0440) M ↔
      ∃ c ∈ template0440, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0440) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0440))
    cores template0440 witness0440 coverage0440
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0440) (maskBits m)) cores template0440 witness0440
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0440))
      coverage0440 catalogue_core_nodup coverageSize0440) (by rfl) M

theorem minimal_mask_iff0441 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0441) M ↔
      ∃ c ∈ template0441, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0441) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0441))
    cores template0441 witness0441 coverage0441
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0441) (maskBits m)) cores template0441 witness0441
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0441))
      coverage0441 catalogue_core_nodup coverageSize0441) (by rfl) M

theorem minimal_mask_iff0442 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0442) M ↔
      ∃ c ∈ template0442, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0442) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0442))
    cores template0442 witness0442 coverage0442
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0442) (maskBits m)) cores template0442 witness0442
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0442))
      coverage0442 catalogue_core_nodup coverageSize0442) (by rfl) M

theorem minimal_mask_iff0443 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0443) M ↔
      ∃ c ∈ template0443, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0443) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0443))
    cores template0443 witness0443 coverage0443
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0443) (maskBits m)) cores template0443 witness0443
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0443))
      coverage0443 catalogue_core_nodup coverageSize0443) (by rfl) M

theorem minimal_mask_iff0444 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0444) M ↔
      ∃ c ∈ template0444, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0444) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0444))
    cores template0444 witness0444 coverage0444
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0444) (maskBits m)) cores template0444 witness0444
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0444))
      coverage0444 catalogue_core_nodup coverageSize0444) (by rfl) M

theorem minimal_mask_iff0445 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0445) M ↔
      ∃ c ∈ template0445, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0445) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0445))
    cores template0445 witness0445 coverage0445
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0445) (maskBits m)) cores template0445 witness0445
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0445))
      coverage0445 catalogue_core_nodup coverageSize0445) (by rfl) M

theorem minimal_mask_iff0446 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0446) M ↔
      ∃ c ∈ template0446, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0446) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0446))
    cores template0446 witness0446 coverage0446
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0446) (maskBits m)) cores template0446 witness0446
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0446))
      coverage0446 catalogue_core_nodup coverageSize0446) (by rfl) M

theorem minimal_mask_iff0447 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0447) M ↔
      ∃ c ∈ template0447, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0447) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0447))
    cores template0447 witness0447 coverage0447
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0447) (maskBits m)) cores template0447 witness0447
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0447))
      coverage0447 catalogue_core_nodup coverageSize0447) (by rfl) M

theorem minimal_mask_iff0448 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0448) M ↔
      ∃ c ∈ template0448, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0448) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0448))
    cores template0448 witness0448 coverage0448
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0448) (maskBits m)) cores template0448 witness0448
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0448))
      coverage0448 catalogue_core_nodup coverageSize0448) (by rfl) M

theorem minimal_mask_iff0449 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0449) M ↔
      ∃ c ∈ template0449, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0449) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0449))
    cores template0449 witness0449 coverage0449
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0449) (maskBits m)) cores template0449 witness0449
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0449))
      coverage0449 catalogue_core_nodup coverageSize0449) (by rfl) M

theorem minimal_mask_iff0450 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0450) M ↔
      ∃ c ∈ template0450, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0450) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0450))
    cores template0450 witness0450 coverage0450
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0450) (maskBits m)) cores template0450 witness0450
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0450))
      coverage0450 catalogue_core_nodup coverageSize0450) (by rfl) M

theorem minimal_mask_iff0451 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0451) M ↔
      ∃ c ∈ template0451, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0451) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0451))
    cores template0451 witness0451 coverage0451
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0451) (maskBits m)) cores template0451 witness0451
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0451))
      coverage0451 catalogue_core_nodup coverageSize0451) (by rfl) M

theorem minimal_mask_iff0452 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0452) M ↔
      ∃ c ∈ template0452, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0452) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0452))
    cores template0452 witness0452 coverage0452
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0452) (maskBits m)) cores template0452 witness0452
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0452))
      coverage0452 catalogue_core_nodup coverageSize0452) (by rfl) M

theorem minimal_mask_iff0453 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0453) M ↔
      ∃ c ∈ template0453, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0453) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0453))
    cores template0453 witness0453 coverage0453
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0453) (maskBits m)) cores template0453 witness0453
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0453))
      coverage0453 catalogue_core_nodup coverageSize0453) (by rfl) M

theorem minimal_mask_iff0454 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0454) M ↔
      ∃ c ∈ template0454, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0454) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0454))
    cores template0454 witness0454 coverage0454
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0454) (maskBits m)) cores template0454 witness0454
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0454))
      coverage0454 catalogue_core_nodup coverageSize0454) (by rfl) M

theorem minimal_mask_iff0455 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0455) M ↔
      ∃ c ∈ template0455, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0455) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0455))
    cores template0455 witness0455 coverage0455
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0455) (maskBits m)) cores template0455 witness0455
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0455))
      coverage0455 catalogue_core_nodup coverageSize0455) (by rfl) M

theorem minimal_mask_iff0456 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0456) M ↔
      ∃ c ∈ template0456, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0456) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0456))
    cores template0456 witness0456 coverage0456
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0456) (maskBits m)) cores template0456 witness0456
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0456))
      coverage0456 catalogue_core_nodup coverageSize0456) (by rfl) M

theorem minimal_mask_iff0457 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0457) M ↔
      ∃ c ∈ template0457, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0457) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0457))
    cores template0457 witness0457 coverage0457
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0457) (maskBits m)) cores template0457 witness0457
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0457))
      coverage0457 catalogue_core_nodup coverageSize0457) (by rfl) M

theorem minimal_mask_iff0458 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0458) M ↔
      ∃ c ∈ template0458, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0458) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0458))
    cores template0458 witness0458 coverage0458
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0458) (maskBits m)) cores template0458 witness0458
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0458))
      coverage0458 catalogue_core_nodup coverageSize0458) (by rfl) M

theorem minimal_mask_iff0459 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0459) M ↔
      ∃ c ∈ template0459, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0459) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0459))
    cores template0459 witness0459 coverage0459
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0459) (maskBits m)) cores template0459 witness0459
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0459))
      coverage0459 catalogue_core_nodup coverageSize0459) (by rfl) M

theorem minimal_mask_iff0460 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0460) M ↔
      ∃ c ∈ template0460, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0460) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0460))
    cores template0460 witness0460 coverage0460
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0460) (maskBits m)) cores template0460 witness0460
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0460))
      coverage0460 catalogue_core_nodup coverageSize0460) (by rfl) M

theorem minimal_mask_iff0461 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0461) M ↔
      ∃ c ∈ template0461, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0461) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0461))
    cores template0461 witness0461 coverage0461
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0461) (maskBits m)) cores template0461 witness0461
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0461))
      coverage0461 catalogue_core_nodup coverageSize0461) (by rfl) M

theorem minimal_mask_iff0462 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0462) M ↔
      ∃ c ∈ template0462, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0462) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0462))
    cores template0462 witness0462 coverage0462
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0462) (maskBits m)) cores template0462 witness0462
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0462))
      coverage0462 catalogue_core_nodup coverageSize0462) (by rfl) M

theorem minimal_mask_iff0463 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0463) M ↔
      ∃ c ∈ template0463, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0463) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0463))
    cores template0463 witness0463 coverage0463
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0463) (maskBits m)) cores template0463 witness0463
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0463))
      coverage0463 catalogue_core_nodup coverageSize0463) (by rfl) M

theorem minimal_mask_iff0464 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0464) M ↔
      ∃ c ∈ template0464, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0464) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0464))
    cores template0464 witness0464 coverage0464
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0464) (maskBits m)) cores template0464 witness0464
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0464))
      coverage0464 catalogue_core_nodup coverageSize0464) (by rfl) M

theorem minimal_mask_iff0465 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0465) M ↔
      ∃ c ∈ template0465, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0465) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0465))
    cores template0465 witness0465 coverage0465
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0465) (maskBits m)) cores template0465 witness0465
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0465))
      coverage0465 catalogue_core_nodup coverageSize0465) (by rfl) M

theorem minimal_mask_iff0466 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0466) M ↔
      ∃ c ∈ template0466, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0466) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0466))
    cores template0466 witness0466 coverage0466
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0466) (maskBits m)) cores template0466 witness0466
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0466))
      coverage0466 catalogue_core_nodup coverageSize0466) (by rfl) M

theorem minimal_mask_iff0467 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0467) M ↔
      ∃ c ∈ template0467, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0467) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0467))
    cores template0467 witness0467 coverage0467
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0467) (maskBits m)) cores template0467 witness0467
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0467))
      coverage0467 catalogue_core_nodup coverageSize0467) (by rfl) M

theorem minimal_mask_iff0468 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0468) M ↔
      ∃ c ∈ template0468, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0468) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0468))
    cores template0468 witness0468 coverage0468
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0468) (maskBits m)) cores template0468 witness0468
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0468))
      coverage0468 catalogue_core_nodup coverageSize0468) (by rfl) M

theorem minimal_mask_iff0469 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0469) M ↔
      ∃ c ∈ template0469, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0469) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0469))
    cores template0469 witness0469 coverage0469
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0469) (maskBits m)) cores template0469 witness0469
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0469))
      coverage0469 catalogue_core_nodup coverageSize0469) (by rfl) M

theorem minimal_mask_iff0470 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0470) M ↔
      ∃ c ∈ template0470, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0470) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0470))
    cores template0470 witness0470 coverage0470
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0470) (maskBits m)) cores template0470 witness0470
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0470))
      coverage0470 catalogue_core_nodup coverageSize0470) (by rfl) M

theorem minimal_mask_iff0471 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0471) M ↔
      ∃ c ∈ template0471, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0471) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0471))
    cores template0471 witness0471 coverage0471
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0471) (maskBits m)) cores template0471 witness0471
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0471))
      coverage0471 catalogue_core_nodup coverageSize0471) (by rfl) M

theorem minimal_mask_iff0472 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0472) M ↔
      ∃ c ∈ template0472, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0472) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0472))
    cores template0472 witness0472 coverage0472
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0472) (maskBits m)) cores template0472 witness0472
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0472))
      coverage0472 catalogue_core_nodup coverageSize0472) (by rfl) M

theorem minimal_mask_iff0473 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0473) M ↔
      ∃ c ∈ template0473, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0473) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0473))
    cores template0473 witness0473 coverage0473
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0473) (maskBits m)) cores template0473 witness0473
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0473))
      coverage0473 catalogue_core_nodup coverageSize0473) (by rfl) M

theorem minimal_mask_iff0474 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0474) M ↔
      ∃ c ∈ template0474, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0474) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0474))
    cores template0474 witness0474 coverage0474
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0474) (maskBits m)) cores template0474 witness0474
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0474))
      coverage0474 catalogue_core_nodup coverageSize0474) (by rfl) M

theorem minimal_mask_iff0475 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0475) M ↔
      ∃ c ∈ template0475, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0475) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0475))
    cores template0475 witness0475 coverage0475
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0475) (maskBits m)) cores template0475 witness0475
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0475))
      coverage0475 catalogue_core_nodup coverageSize0475) (by rfl) M

theorem minimal_mask_iff0476 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0476) M ↔
      ∃ c ∈ template0476, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0476) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0476))
    cores template0476 witness0476 coverage0476
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0476) (maskBits m)) cores template0476 witness0476
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0476))
      coverage0476 catalogue_core_nodup coverageSize0476) (by rfl) M

theorem minimal_mask_iff0477 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0477) M ↔
      ∃ c ∈ template0477, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0477) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0477))
    cores template0477 witness0477 coverage0477
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0477) (maskBits m)) cores template0477 witness0477
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0477))
      coverage0477 catalogue_core_nodup coverageSize0477) (by rfl) M

theorem minimal_mask_iff0478 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0478) M ↔
      ∃ c ∈ template0478, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0478) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0478))
    cores template0478 witness0478 coverage0478
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0478) (maskBits m)) cores template0478 witness0478
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0478))
      coverage0478 catalogue_core_nodup coverageSize0478) (by rfl) M

theorem minimal_mask_iff0479 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0479) M ↔
      ∃ c ∈ template0479, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0479) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0479))
    cores template0479 witness0479 coverage0479
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0479) (maskBits m)) cores template0479 witness0479
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0479))
      coverage0479 catalogue_core_nodup coverageSize0479) (by rfl) M

#print axioms minimal_mask_iff0440
#print axioms minimal_mask_iff0479
end Crown.CertificateData
