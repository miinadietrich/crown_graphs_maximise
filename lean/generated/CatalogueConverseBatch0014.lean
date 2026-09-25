import generated.CatalogueBatch0014
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0013

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0520 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0520) M ↔
      ∃ c ∈ template0520, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0520) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0520))
    cores template0520 witness0520 coverage0520
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0520) (maskBits m)) cores template0520 witness0520
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0520))
      coverage0520 catalogue_core_nodup coverageSize0520) (by rfl) M

theorem minimal_mask_iff0521 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0521) M ↔
      ∃ c ∈ template0521, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0521) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0521))
    cores template0521 witness0521 coverage0521
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0521) (maskBits m)) cores template0521 witness0521
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0521))
      coverage0521 catalogue_core_nodup coverageSize0521) (by rfl) M

theorem minimal_mask_iff0522 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0522) M ↔
      ∃ c ∈ template0522, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0522) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0522))
    cores template0522 witness0522 coverage0522
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0522) (maskBits m)) cores template0522 witness0522
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0522))
      coverage0522 catalogue_core_nodup coverageSize0522) (by rfl) M

theorem minimal_mask_iff0523 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0523) M ↔
      ∃ c ∈ template0523, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0523) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0523))
    cores template0523 witness0523 coverage0523
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0523) (maskBits m)) cores template0523 witness0523
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0523))
      coverage0523 catalogue_core_nodup coverageSize0523) (by rfl) M

theorem minimal_mask_iff0524 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0524) M ↔
      ∃ c ∈ template0524, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0524) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0524))
    cores template0524 witness0524 coverage0524
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0524) (maskBits m)) cores template0524 witness0524
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0524))
      coverage0524 catalogue_core_nodup coverageSize0524) (by rfl) M

theorem minimal_mask_iff0525 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0525) M ↔
      ∃ c ∈ template0525, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0525) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0525))
    cores template0525 witness0525 coverage0525
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0525) (maskBits m)) cores template0525 witness0525
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0525))
      coverage0525 catalogue_core_nodup coverageSize0525) (by rfl) M

theorem minimal_mask_iff0526 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0526) M ↔
      ∃ c ∈ template0526, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0526) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0526))
    cores template0526 witness0526 coverage0526
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0526) (maskBits m)) cores template0526 witness0526
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0526))
      coverage0526 catalogue_core_nodup coverageSize0526) (by rfl) M

theorem minimal_mask_iff0527 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0527) M ↔
      ∃ c ∈ template0527, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0527) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0527))
    cores template0527 witness0527 coverage0527
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0527) (maskBits m)) cores template0527 witness0527
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0527))
      coverage0527 catalogue_core_nodup coverageSize0527) (by rfl) M

theorem minimal_mask_iff0528 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0528) M ↔
      ∃ c ∈ template0528, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0528) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0528))
    cores template0528 witness0528 coverage0528
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0528) (maskBits m)) cores template0528 witness0528
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0528))
      coverage0528 catalogue_core_nodup coverageSize0528) (by rfl) M

theorem minimal_mask_iff0529 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0529) M ↔
      ∃ c ∈ template0529, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0529) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0529))
    cores template0529 witness0529 coverage0529
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0529) (maskBits m)) cores template0529 witness0529
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0529))
      coverage0529 catalogue_core_nodup coverageSize0529) (by rfl) M

theorem minimal_mask_iff0530 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0530) M ↔
      ∃ c ∈ template0530, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0530) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0530))
    cores template0530 witness0530 coverage0530
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0530) (maskBits m)) cores template0530 witness0530
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0530))
      coverage0530 catalogue_core_nodup coverageSize0530) (by rfl) M

theorem minimal_mask_iff0531 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0531) M ↔
      ∃ c ∈ template0531, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0531) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0531))
    cores template0531 witness0531 coverage0531
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0531) (maskBits m)) cores template0531 witness0531
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0531))
      coverage0531 catalogue_core_nodup coverageSize0531) (by rfl) M

theorem minimal_mask_iff0532 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0532) M ↔
      ∃ c ∈ template0532, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0532) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0532))
    cores template0532 witness0532 coverage0532
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0532) (maskBits m)) cores template0532 witness0532
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0532))
      coverage0532 catalogue_core_nodup coverageSize0532) (by rfl) M

theorem minimal_mask_iff0533 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0533) M ↔
      ∃ c ∈ template0533, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0533) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0533))
    cores template0533 witness0533 coverage0533
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0533) (maskBits m)) cores template0533 witness0533
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0533))
      coverage0533 catalogue_core_nodup coverageSize0533) (by rfl) M

theorem minimal_mask_iff0534 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0534) M ↔
      ∃ c ∈ template0534, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0534) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0534))
    cores template0534 witness0534 coverage0534
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0534) (maskBits m)) cores template0534 witness0534
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0534))
      coverage0534 catalogue_core_nodup coverageSize0534) (by rfl) M

theorem minimal_mask_iff0535 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0535) M ↔
      ∃ c ∈ template0535, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0535) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0535))
    cores template0535 witness0535 coverage0535
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0535) (maskBits m)) cores template0535 witness0535
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0535))
      coverage0535 catalogue_core_nodup coverageSize0535) (by rfl) M

theorem minimal_mask_iff0536 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0536) M ↔
      ∃ c ∈ template0536, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0536) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0536))
    cores template0536 witness0536 coverage0536
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0536) (maskBits m)) cores template0536 witness0536
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0536))
      coverage0536 catalogue_core_nodup coverageSize0536) (by rfl) M

theorem minimal_mask_iff0537 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0537) M ↔
      ∃ c ∈ template0537, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0537) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0537))
    cores template0537 witness0537 coverage0537
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0537) (maskBits m)) cores template0537 witness0537
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0537))
      coverage0537 catalogue_core_nodup coverageSize0537) (by rfl) M

theorem minimal_mask_iff0538 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0538) M ↔
      ∃ c ∈ template0538, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0538) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0538))
    cores template0538 witness0538 coverage0538
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0538) (maskBits m)) cores template0538 witness0538
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0538))
      coverage0538 catalogue_core_nodup coverageSize0538) (by rfl) M

theorem minimal_mask_iff0539 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0539) M ↔
      ∃ c ∈ template0539, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0539) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0539))
    cores template0539 witness0539 coverage0539
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0539) (maskBits m)) cores template0539 witness0539
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0539))
      coverage0539 catalogue_core_nodup coverageSize0539) (by rfl) M

theorem minimal_mask_iff0540 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0540) M ↔
      ∃ c ∈ template0540, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0540) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0540))
    cores template0540 witness0540 coverage0540
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0540) (maskBits m)) cores template0540 witness0540
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0540))
      coverage0540 catalogue_core_nodup coverageSize0540) (by rfl) M

theorem minimal_mask_iff0541 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0541) M ↔
      ∃ c ∈ template0541, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0541) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0541))
    cores template0541 witness0541 coverage0541
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0541) (maskBits m)) cores template0541 witness0541
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0541))
      coverage0541 catalogue_core_nodup coverageSize0541) (by rfl) M

theorem minimal_mask_iff0542 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0542) M ↔
      ∃ c ∈ template0542, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0542) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0542))
    cores template0542 witness0542 coverage0542
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0542) (maskBits m)) cores template0542 witness0542
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0542))
      coverage0542 catalogue_core_nodup coverageSize0542) (by rfl) M

theorem minimal_mask_iff0543 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0543) M ↔
      ∃ c ∈ template0543, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0543) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0543))
    cores template0543 witness0543 coverage0543
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0543) (maskBits m)) cores template0543 witness0543
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0543))
      coverage0543 catalogue_core_nodup coverageSize0543) (by rfl) M

theorem minimal_mask_iff0544 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0544) M ↔
      ∃ c ∈ template0544, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0544) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0544))
    cores template0544 witness0544 coverage0544
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0544) (maskBits m)) cores template0544 witness0544
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0544))
      coverage0544 catalogue_core_nodup coverageSize0544) (by rfl) M

theorem minimal_mask_iff0545 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0545) M ↔
      ∃ c ∈ template0545, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0545) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0545))
    cores template0545 witness0545 coverage0545
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0545) (maskBits m)) cores template0545 witness0545
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0545))
      coverage0545 catalogue_core_nodup coverageSize0545) (by rfl) M

theorem minimal_mask_iff0546 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0546) M ↔
      ∃ c ∈ template0546, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0546) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0546))
    cores template0546 witness0546 coverage0546
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0546) (maskBits m)) cores template0546 witness0546
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0546))
      coverage0546 catalogue_core_nodup coverageSize0546) (by rfl) M

theorem minimal_mask_iff0547 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0547) M ↔
      ∃ c ∈ template0547, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0547) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0547))
    cores template0547 witness0547 coverage0547
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0547) (maskBits m)) cores template0547 witness0547
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0547))
      coverage0547 catalogue_core_nodup coverageSize0547) (by rfl) M

theorem minimal_mask_iff0548 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0548) M ↔
      ∃ c ∈ template0548, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0548) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0548))
    cores template0548 witness0548 coverage0548
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0548) (maskBits m)) cores template0548 witness0548
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0548))
      coverage0548 catalogue_core_nodup coverageSize0548) (by rfl) M

theorem minimal_mask_iff0549 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0549) M ↔
      ∃ c ∈ template0549, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0549) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0549))
    cores template0549 witness0549 coverage0549
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0549) (maskBits m)) cores template0549 witness0549
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0549))
      coverage0549 catalogue_core_nodup coverageSize0549) (by rfl) M

theorem minimal_mask_iff0550 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0550) M ↔
      ∃ c ∈ template0550, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0550) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0550))
    cores template0550 witness0550 coverage0550
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0550) (maskBits m)) cores template0550 witness0550
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0550))
      coverage0550 catalogue_core_nodup coverageSize0550) (by rfl) M

theorem minimal_mask_iff0551 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0551) M ↔
      ∃ c ∈ template0551, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0551) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0551))
    cores template0551 witness0551 coverage0551
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0551) (maskBits m)) cores template0551 witness0551
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0551))
      coverage0551 catalogue_core_nodup coverageSize0551) (by rfl) M

theorem minimal_mask_iff0552 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0552) M ↔
      ∃ c ∈ template0552, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0552) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0552))
    cores template0552 witness0552 coverage0552
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0552) (maskBits m)) cores template0552 witness0552
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0552))
      coverage0552 catalogue_core_nodup coverageSize0552) (by rfl) M

theorem minimal_mask_iff0553 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0553) M ↔
      ∃ c ∈ template0553, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0553) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0553))
    cores template0553 witness0553 coverage0553
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0553) (maskBits m)) cores template0553 witness0553
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0553))
      coverage0553 catalogue_core_nodup coverageSize0553) (by rfl) M

theorem minimal_mask_iff0554 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0554) M ↔
      ∃ c ∈ template0554, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0554) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0554))
    cores template0554 witness0554 coverage0554
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0554) (maskBits m)) cores template0554 witness0554
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0554))
      coverage0554 catalogue_core_nodup coverageSize0554) (by rfl) M

theorem minimal_mask_iff0555 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0555) M ↔
      ∃ c ∈ template0555, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0555) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0555))
    cores template0555 witness0555 coverage0555
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0555) (maskBits m)) cores template0555 witness0555
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0555))
      coverage0555 catalogue_core_nodup coverageSize0555) (by rfl) M

theorem minimal_mask_iff0556 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0556) M ↔
      ∃ c ∈ template0556, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0556) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0556))
    cores template0556 witness0556 coverage0556
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0556) (maskBits m)) cores template0556 witness0556
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0556))
      coverage0556 catalogue_core_nodup coverageSize0556) (by rfl) M

theorem minimal_mask_iff0557 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0557) M ↔
      ∃ c ∈ template0557, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0557) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0557))
    cores template0557 witness0557 coverage0557
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0557) (maskBits m)) cores template0557 witness0557
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0557))
      coverage0557 catalogue_core_nodup coverageSize0557) (by rfl) M

theorem minimal_mask_iff0558 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0558) M ↔
      ∃ c ∈ template0558, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0558) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0558))
    cores template0558 witness0558 coverage0558
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0558) (maskBits m)) cores template0558 witness0558
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0558))
      coverage0558 catalogue_core_nodup coverageSize0558) (by rfl) M

theorem minimal_mask_iff0559 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0559) M ↔
      ∃ c ∈ template0559, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0559) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0559))
    cores template0559 witness0559 coverage0559
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0559) (maskBits m)) cores template0559 witness0559
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0559))
      coverage0559 catalogue_core_nodup coverageSize0559) (by rfl) M

#print axioms minimal_mask_iff0520
#print axioms minimal_mask_iff0559
end Crown.CertificateData
