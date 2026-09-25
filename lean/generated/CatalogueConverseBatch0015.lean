import generated.CatalogueBatch0015
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0014

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0560 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0560) M ↔
      ∃ c ∈ template0560, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0560) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0560))
    cores template0560 witness0560 coverage0560
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0560) (maskBits m)) cores template0560 witness0560
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0560))
      coverage0560 catalogue_core_nodup coverageSize0560) (by rfl) M

theorem minimal_mask_iff0561 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0561) M ↔
      ∃ c ∈ template0561, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0561) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0561))
    cores template0561 witness0561 coverage0561
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0561) (maskBits m)) cores template0561 witness0561
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0561))
      coverage0561 catalogue_core_nodup coverageSize0561) (by rfl) M

theorem minimal_mask_iff0562 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0562) M ↔
      ∃ c ∈ template0562, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0562) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0562))
    cores template0562 witness0562 coverage0562
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0562) (maskBits m)) cores template0562 witness0562
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0562))
      coverage0562 catalogue_core_nodup coverageSize0562) (by rfl) M

theorem minimal_mask_iff0563 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0563) M ↔
      ∃ c ∈ template0563, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0563) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0563))
    cores template0563 witness0563 coverage0563
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0563) (maskBits m)) cores template0563 witness0563
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0563))
      coverage0563 catalogue_core_nodup coverageSize0563) (by rfl) M

theorem minimal_mask_iff0564 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0564) M ↔
      ∃ c ∈ template0564, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0564) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0564))
    cores template0564 witness0564 coverage0564
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0564) (maskBits m)) cores template0564 witness0564
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0564))
      coverage0564 catalogue_core_nodup coverageSize0564) (by rfl) M

theorem minimal_mask_iff0565 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0565) M ↔
      ∃ c ∈ template0565, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0565) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0565))
    cores template0565 witness0565 coverage0565
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0565) (maskBits m)) cores template0565 witness0565
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0565))
      coverage0565 catalogue_core_nodup coverageSize0565) (by rfl) M

theorem minimal_mask_iff0566 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0566) M ↔
      ∃ c ∈ template0566, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0566) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0566))
    cores template0566 witness0566 coverage0566
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0566) (maskBits m)) cores template0566 witness0566
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0566))
      coverage0566 catalogue_core_nodup coverageSize0566) (by rfl) M

theorem minimal_mask_iff0567 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0567) M ↔
      ∃ c ∈ template0567, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0567) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0567))
    cores template0567 witness0567 coverage0567
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0567) (maskBits m)) cores template0567 witness0567
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0567))
      coverage0567 catalogue_core_nodup coverageSize0567) (by rfl) M

theorem minimal_mask_iff0568 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0568) M ↔
      ∃ c ∈ template0568, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0568) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0568))
    cores template0568 witness0568 coverage0568
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0568) (maskBits m)) cores template0568 witness0568
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0568))
      coverage0568 catalogue_core_nodup coverageSize0568) (by rfl) M

theorem minimal_mask_iff0569 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0569) M ↔
      ∃ c ∈ template0569, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0569) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0569))
    cores template0569 witness0569 coverage0569
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0569) (maskBits m)) cores template0569 witness0569
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0569))
      coverage0569 catalogue_core_nodup coverageSize0569) (by rfl) M

theorem minimal_mask_iff0570 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0570) M ↔
      ∃ c ∈ template0570, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0570) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0570))
    cores template0570 witness0570 coverage0570
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0570) (maskBits m)) cores template0570 witness0570
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0570))
      coverage0570 catalogue_core_nodup coverageSize0570) (by rfl) M

theorem minimal_mask_iff0571 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0571) M ↔
      ∃ c ∈ template0571, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0571) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0571))
    cores template0571 witness0571 coverage0571
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0571) (maskBits m)) cores template0571 witness0571
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0571))
      coverage0571 catalogue_core_nodup coverageSize0571) (by rfl) M

theorem minimal_mask_iff0572 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0572) M ↔
      ∃ c ∈ template0572, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0572) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0572))
    cores template0572 witness0572 coverage0572
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0572) (maskBits m)) cores template0572 witness0572
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0572))
      coverage0572 catalogue_core_nodup coverageSize0572) (by rfl) M

theorem minimal_mask_iff0573 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0573) M ↔
      ∃ c ∈ template0573, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0573) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0573))
    cores template0573 witness0573 coverage0573
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0573) (maskBits m)) cores template0573 witness0573
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0573))
      coverage0573 catalogue_core_nodup coverageSize0573) (by rfl) M

theorem minimal_mask_iff0574 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0574) M ↔
      ∃ c ∈ template0574, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0574) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0574))
    cores template0574 witness0574 coverage0574
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0574) (maskBits m)) cores template0574 witness0574
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0574))
      coverage0574 catalogue_core_nodup coverageSize0574) (by rfl) M

theorem minimal_mask_iff0575 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0575) M ↔
      ∃ c ∈ template0575, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0575) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0575))
    cores template0575 witness0575 coverage0575
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0575) (maskBits m)) cores template0575 witness0575
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0575))
      coverage0575 catalogue_core_nodup coverageSize0575) (by rfl) M

theorem minimal_mask_iff0576 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0576) M ↔
      ∃ c ∈ template0576, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0576) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0576))
    cores template0576 witness0576 coverage0576
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0576) (maskBits m)) cores template0576 witness0576
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0576))
      coverage0576 catalogue_core_nodup coverageSize0576) (by rfl) M

theorem minimal_mask_iff0577 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0577) M ↔
      ∃ c ∈ template0577, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0577) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0577))
    cores template0577 witness0577 coverage0577
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0577) (maskBits m)) cores template0577 witness0577
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0577))
      coverage0577 catalogue_core_nodup coverageSize0577) (by rfl) M

theorem minimal_mask_iff0578 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0578) M ↔
      ∃ c ∈ template0578, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0578) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0578))
    cores template0578 witness0578 coverage0578
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0578) (maskBits m)) cores template0578 witness0578
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0578))
      coverage0578 catalogue_core_nodup coverageSize0578) (by rfl) M

theorem minimal_mask_iff0579 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0579) M ↔
      ∃ c ∈ template0579, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0579) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0579))
    cores template0579 witness0579 coverage0579
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0579) (maskBits m)) cores template0579 witness0579
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0579))
      coverage0579 catalogue_core_nodup coverageSize0579) (by rfl) M

theorem minimal_mask_iff0580 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0580) M ↔
      ∃ c ∈ template0580, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0580) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0580))
    cores template0580 witness0580 coverage0580
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0580) (maskBits m)) cores template0580 witness0580
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0580))
      coverage0580 catalogue_core_nodup coverageSize0580) (by rfl) M

theorem minimal_mask_iff0581 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0581) M ↔
      ∃ c ∈ template0581, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0581) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0581))
    cores template0581 witness0581 coverage0581
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0581) (maskBits m)) cores template0581 witness0581
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0581))
      coverage0581 catalogue_core_nodup coverageSize0581) (by rfl) M

theorem minimal_mask_iff0582 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0582) M ↔
      ∃ c ∈ template0582, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0582) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0582))
    cores template0582 witness0582 coverage0582
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0582) (maskBits m)) cores template0582 witness0582
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0582))
      coverage0582 catalogue_core_nodup coverageSize0582) (by rfl) M

theorem minimal_mask_iff0583 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0583) M ↔
      ∃ c ∈ template0583, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0583) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0583))
    cores template0583 witness0583 coverage0583
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0583) (maskBits m)) cores template0583 witness0583
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0583))
      coverage0583 catalogue_core_nodup coverageSize0583) (by rfl) M

theorem minimal_mask_iff0584 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0584) M ↔
      ∃ c ∈ template0584, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0584) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0584))
    cores template0584 witness0584 coverage0584
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0584) (maskBits m)) cores template0584 witness0584
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0584))
      coverage0584 catalogue_core_nodup coverageSize0584) (by rfl) M

theorem minimal_mask_iff0585 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0585) M ↔
      ∃ c ∈ template0585, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0585) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0585))
    cores template0585 witness0585 coverage0585
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0585) (maskBits m)) cores template0585 witness0585
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0585))
      coverage0585 catalogue_core_nodup coverageSize0585) (by rfl) M

theorem minimal_mask_iff0586 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0586) M ↔
      ∃ c ∈ template0586, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0586) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0586))
    cores template0586 witness0586 coverage0586
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0586) (maskBits m)) cores template0586 witness0586
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0586))
      coverage0586 catalogue_core_nodup coverageSize0586) (by rfl) M

theorem minimal_mask_iff0587 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0587) M ↔
      ∃ c ∈ template0587, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0587) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0587))
    cores template0587 witness0587 coverage0587
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0587) (maskBits m)) cores template0587 witness0587
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0587))
      coverage0587 catalogue_core_nodup coverageSize0587) (by rfl) M

theorem minimal_mask_iff0588 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0588) M ↔
      ∃ c ∈ template0588, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0588) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0588))
    cores template0588 witness0588 coverage0588
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0588) (maskBits m)) cores template0588 witness0588
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0588))
      coverage0588 catalogue_core_nodup coverageSize0588) (by rfl) M

theorem minimal_mask_iff0589 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0589) M ↔
      ∃ c ∈ template0589, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0589) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0589))
    cores template0589 witness0589 coverage0589
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0589) (maskBits m)) cores template0589 witness0589
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0589))
      coverage0589 catalogue_core_nodup coverageSize0589) (by rfl) M

theorem minimal_mask_iff0590 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0590) M ↔
      ∃ c ∈ template0590, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0590) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0590))
    cores template0590 witness0590 coverage0590
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0590) (maskBits m)) cores template0590 witness0590
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0590))
      coverage0590 catalogue_core_nodup coverageSize0590) (by rfl) M

theorem minimal_mask_iff0591 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0591) M ↔
      ∃ c ∈ template0591, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0591) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0591))
    cores template0591 witness0591 coverage0591
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0591) (maskBits m)) cores template0591 witness0591
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0591))
      coverage0591 catalogue_core_nodup coverageSize0591) (by rfl) M

theorem minimal_mask_iff0592 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0592) M ↔
      ∃ c ∈ template0592, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0592) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0592))
    cores template0592 witness0592 coverage0592
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0592) (maskBits m)) cores template0592 witness0592
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0592))
      coverage0592 catalogue_core_nodup coverageSize0592) (by rfl) M

theorem minimal_mask_iff0593 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0593) M ↔
      ∃ c ∈ template0593, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0593) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0593))
    cores template0593 witness0593 coverage0593
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0593) (maskBits m)) cores template0593 witness0593
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0593))
      coverage0593 catalogue_core_nodup coverageSize0593) (by rfl) M

theorem minimal_mask_iff0594 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0594) M ↔
      ∃ c ∈ template0594, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0594) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0594))
    cores template0594 witness0594 coverage0594
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0594) (maskBits m)) cores template0594 witness0594
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0594))
      coverage0594 catalogue_core_nodup coverageSize0594) (by rfl) M

theorem minimal_mask_iff0595 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0595) M ↔
      ∃ c ∈ template0595, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0595) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0595))
    cores template0595 witness0595 coverage0595
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0595) (maskBits m)) cores template0595 witness0595
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0595))
      coverage0595 catalogue_core_nodup coverageSize0595) (by rfl) M

theorem minimal_mask_iff0596 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0596) M ↔
      ∃ c ∈ template0596, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0596) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0596))
    cores template0596 witness0596 coverage0596
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0596) (maskBits m)) cores template0596 witness0596
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0596))
      coverage0596 catalogue_core_nodup coverageSize0596) (by rfl) M

theorem minimal_mask_iff0597 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0597) M ↔
      ∃ c ∈ template0597, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0597) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0597))
    cores template0597 witness0597 coverage0597
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0597) (maskBits m)) cores template0597 witness0597
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0597))
      coverage0597 catalogue_core_nodup coverageSize0597) (by rfl) M

theorem minimal_mask_iff0598 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0598) M ↔
      ∃ c ∈ template0598, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0598) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0598))
    cores template0598 witness0598 coverage0598
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0598) (maskBits m)) cores template0598 witness0598
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0598))
      coverage0598 catalogue_core_nodup coverageSize0598) (by rfl) M

theorem minimal_mask_iff0599 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0599) M ↔
      ∃ c ∈ template0599, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0599) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0599))
    cores template0599 witness0599 coverage0599
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0599) (maskBits m)) cores template0599 witness0599
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0599))
      coverage0599 catalogue_core_nodup coverageSize0599) (by rfl) M

#print axioms minimal_mask_iff0560
#print axioms minimal_mask_iff0599
end Crown.CertificateData
