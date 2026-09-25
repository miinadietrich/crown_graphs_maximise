import generated.CatalogueBatch0016
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0015

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0600 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0600) M ↔
      ∃ c ∈ template0600, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0600) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0600))
    cores template0600 witness0600 coverage0600
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0600) (maskBits m)) cores template0600 witness0600
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0600))
      coverage0600 catalogue_core_nodup coverageSize0600) (by rfl) M

theorem minimal_mask_iff0601 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0601) M ↔
      ∃ c ∈ template0601, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0601) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0601))
    cores template0601 witness0601 coverage0601
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0601) (maskBits m)) cores template0601 witness0601
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0601))
      coverage0601 catalogue_core_nodup coverageSize0601) (by rfl) M

theorem minimal_mask_iff0602 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0602) M ↔
      ∃ c ∈ template0602, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0602) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0602))
    cores template0602 witness0602 coverage0602
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0602) (maskBits m)) cores template0602 witness0602
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0602))
      coverage0602 catalogue_core_nodup coverageSize0602) (by rfl) M

theorem minimal_mask_iff0603 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0603) M ↔
      ∃ c ∈ template0603, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0603) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0603))
    cores template0603 witness0603 coverage0603
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0603) (maskBits m)) cores template0603 witness0603
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0603))
      coverage0603 catalogue_core_nodup coverageSize0603) (by rfl) M

theorem minimal_mask_iff0604 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0604) M ↔
      ∃ c ∈ template0604, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0604) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0604))
    cores template0604 witness0604 coverage0604
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0604) (maskBits m)) cores template0604 witness0604
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0604))
      coverage0604 catalogue_core_nodup coverageSize0604) (by rfl) M

theorem minimal_mask_iff0605 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0605) M ↔
      ∃ c ∈ template0605, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0605) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0605))
    cores template0605 witness0605 coverage0605
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0605) (maskBits m)) cores template0605 witness0605
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0605))
      coverage0605 catalogue_core_nodup coverageSize0605) (by rfl) M

theorem minimal_mask_iff0606 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0606) M ↔
      ∃ c ∈ template0606, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0606) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0606))
    cores template0606 witness0606 coverage0606
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0606) (maskBits m)) cores template0606 witness0606
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0606))
      coverage0606 catalogue_core_nodup coverageSize0606) (by rfl) M

theorem minimal_mask_iff0607 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0607) M ↔
      ∃ c ∈ template0607, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0607) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0607))
    cores template0607 witness0607 coverage0607
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0607) (maskBits m)) cores template0607 witness0607
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0607))
      coverage0607 catalogue_core_nodup coverageSize0607) (by rfl) M

theorem minimal_mask_iff0608 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0608) M ↔
      ∃ c ∈ template0608, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0608) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0608))
    cores template0608 witness0608 coverage0608
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0608) (maskBits m)) cores template0608 witness0608
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0608))
      coverage0608 catalogue_core_nodup coverageSize0608) (by rfl) M

theorem minimal_mask_iff0609 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0609) M ↔
      ∃ c ∈ template0609, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0609) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0609))
    cores template0609 witness0609 coverage0609
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0609) (maskBits m)) cores template0609 witness0609
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0609))
      coverage0609 catalogue_core_nodup coverageSize0609) (by rfl) M

theorem minimal_mask_iff0610 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0610) M ↔
      ∃ c ∈ template0610, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0610) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0610))
    cores template0610 witness0610 coverage0610
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0610) (maskBits m)) cores template0610 witness0610
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0610))
      coverage0610 catalogue_core_nodup coverageSize0610) (by rfl) M

theorem minimal_mask_iff0611 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0611) M ↔
      ∃ c ∈ template0611, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0611) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0611))
    cores template0611 witness0611 coverage0611
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0611) (maskBits m)) cores template0611 witness0611
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0611))
      coverage0611 catalogue_core_nodup coverageSize0611) (by rfl) M

theorem minimal_mask_iff0612 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0612) M ↔
      ∃ c ∈ template0612, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0612) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0612))
    cores template0612 witness0612 coverage0612
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0612) (maskBits m)) cores template0612 witness0612
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0612))
      coverage0612 catalogue_core_nodup coverageSize0612) (by rfl) M

theorem minimal_mask_iff0613 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0613) M ↔
      ∃ c ∈ template0613, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0613) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0613))
    cores template0613 witness0613 coverage0613
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0613) (maskBits m)) cores template0613 witness0613
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0613))
      coverage0613 catalogue_core_nodup coverageSize0613) (by rfl) M

theorem minimal_mask_iff0614 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0614) M ↔
      ∃ c ∈ template0614, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0614) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0614))
    cores template0614 witness0614 coverage0614
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0614) (maskBits m)) cores template0614 witness0614
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0614))
      coverage0614 catalogue_core_nodup coverageSize0614) (by rfl) M

theorem minimal_mask_iff0615 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0615) M ↔
      ∃ c ∈ template0615, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0615) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0615))
    cores template0615 witness0615 coverage0615
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0615) (maskBits m)) cores template0615 witness0615
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0615))
      coverage0615 catalogue_core_nodup coverageSize0615) (by rfl) M

theorem minimal_mask_iff0616 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0616) M ↔
      ∃ c ∈ template0616, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0616) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0616))
    cores template0616 witness0616 coverage0616
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0616) (maskBits m)) cores template0616 witness0616
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0616))
      coverage0616 catalogue_core_nodup coverageSize0616) (by rfl) M

theorem minimal_mask_iff0617 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0617) M ↔
      ∃ c ∈ template0617, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0617) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0617))
    cores template0617 witness0617 coverage0617
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0617) (maskBits m)) cores template0617 witness0617
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0617))
      coverage0617 catalogue_core_nodup coverageSize0617) (by rfl) M

theorem minimal_mask_iff0618 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0618) M ↔
      ∃ c ∈ template0618, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0618) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0618))
    cores template0618 witness0618 coverage0618
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0618) (maskBits m)) cores template0618 witness0618
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0618))
      coverage0618 catalogue_core_nodup coverageSize0618) (by rfl) M

theorem minimal_mask_iff0619 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0619) M ↔
      ∃ c ∈ template0619, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0619) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0619))
    cores template0619 witness0619 coverage0619
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0619) (maskBits m)) cores template0619 witness0619
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0619))
      coverage0619 catalogue_core_nodup coverageSize0619) (by rfl) M

theorem minimal_mask_iff0620 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0620) M ↔
      ∃ c ∈ template0620, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0620) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0620))
    cores template0620 witness0620 coverage0620
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0620) (maskBits m)) cores template0620 witness0620
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0620))
      coverage0620 catalogue_core_nodup coverageSize0620) (by rfl) M

theorem minimal_mask_iff0621 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0621) M ↔
      ∃ c ∈ template0621, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0621) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0621))
    cores template0621 witness0621 coverage0621
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0621) (maskBits m)) cores template0621 witness0621
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0621))
      coverage0621 catalogue_core_nodup coverageSize0621) (by rfl) M

theorem minimal_mask_iff0622 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0622) M ↔
      ∃ c ∈ template0622, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0622) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0622))
    cores template0622 witness0622 coverage0622
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0622) (maskBits m)) cores template0622 witness0622
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0622))
      coverage0622 catalogue_core_nodup coverageSize0622) (by rfl) M

theorem minimal_mask_iff0623 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0623) M ↔
      ∃ c ∈ template0623, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0623) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0623))
    cores template0623 witness0623 coverage0623
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0623) (maskBits m)) cores template0623 witness0623
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0623))
      coverage0623 catalogue_core_nodup coverageSize0623) (by rfl) M

theorem minimal_mask_iff0624 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0624) M ↔
      ∃ c ∈ template0624, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0624) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0624))
    cores template0624 witness0624 coverage0624
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0624) (maskBits m)) cores template0624 witness0624
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0624))
      coverage0624 catalogue_core_nodup coverageSize0624) (by rfl) M

theorem minimal_mask_iff0625 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0625) M ↔
      ∃ c ∈ template0625, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0625) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0625))
    cores template0625 witness0625 coverage0625
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0625) (maskBits m)) cores template0625 witness0625
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0625))
      coverage0625 catalogue_core_nodup coverageSize0625) (by rfl) M

theorem minimal_mask_iff0626 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0626) M ↔
      ∃ c ∈ template0626, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0626) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0626))
    cores template0626 witness0626 coverage0626
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0626) (maskBits m)) cores template0626 witness0626
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0626))
      coverage0626 catalogue_core_nodup coverageSize0626) (by rfl) M

theorem minimal_mask_iff0627 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0627) M ↔
      ∃ c ∈ template0627, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0627) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0627))
    cores template0627 witness0627 coverage0627
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0627) (maskBits m)) cores template0627 witness0627
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0627))
      coverage0627 catalogue_core_nodup coverageSize0627) (by rfl) M

theorem minimal_mask_iff0628 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0628) M ↔
      ∃ c ∈ template0628, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0628) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0628))
    cores template0628 witness0628 coverage0628
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0628) (maskBits m)) cores template0628 witness0628
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0628))
      coverage0628 catalogue_core_nodup coverageSize0628) (by rfl) M

theorem minimal_mask_iff0629 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0629) M ↔
      ∃ c ∈ template0629, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0629) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0629))
    cores template0629 witness0629 coverage0629
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0629) (maskBits m)) cores template0629 witness0629
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0629))
      coverage0629 catalogue_core_nodup coverageSize0629) (by rfl) M

theorem minimal_mask_iff0630 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0630) M ↔
      ∃ c ∈ template0630, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0630) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0630))
    cores template0630 witness0630 coverage0630
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0630) (maskBits m)) cores template0630 witness0630
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0630))
      coverage0630 catalogue_core_nodup coverageSize0630) (by rfl) M

theorem minimal_mask_iff0631 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0631) M ↔
      ∃ c ∈ template0631, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0631) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0631))
    cores template0631 witness0631 coverage0631
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0631) (maskBits m)) cores template0631 witness0631
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0631))
      coverage0631 catalogue_core_nodup coverageSize0631) (by rfl) M

theorem minimal_mask_iff0632 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0632) M ↔
      ∃ c ∈ template0632, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0632) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0632))
    cores template0632 witness0632 coverage0632
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0632) (maskBits m)) cores template0632 witness0632
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0632))
      coverage0632 catalogue_core_nodup coverageSize0632) (by rfl) M

theorem minimal_mask_iff0633 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0633) M ↔
      ∃ c ∈ template0633, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0633) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0633))
    cores template0633 witness0633 coverage0633
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0633) (maskBits m)) cores template0633 witness0633
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0633))
      coverage0633 catalogue_core_nodup coverageSize0633) (by rfl) M

theorem minimal_mask_iff0634 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0634) M ↔
      ∃ c ∈ template0634, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0634) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0634))
    cores template0634 witness0634 coverage0634
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0634) (maskBits m)) cores template0634 witness0634
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0634))
      coverage0634 catalogue_core_nodup coverageSize0634) (by rfl) M

theorem minimal_mask_iff0635 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0635) M ↔
      ∃ c ∈ template0635, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0635) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0635))
    cores template0635 witness0635 coverage0635
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0635) (maskBits m)) cores template0635 witness0635
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0635))
      coverage0635 catalogue_core_nodup coverageSize0635) (by rfl) M

theorem minimal_mask_iff0636 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0636) M ↔
      ∃ c ∈ template0636, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0636) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0636))
    cores template0636 witness0636 coverage0636
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0636) (maskBits m)) cores template0636 witness0636
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0636))
      coverage0636 catalogue_core_nodup coverageSize0636) (by rfl) M

theorem minimal_mask_iff0637 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0637) M ↔
      ∃ c ∈ template0637, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0637) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0637))
    cores template0637 witness0637 coverage0637
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0637) (maskBits m)) cores template0637 witness0637
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0637))
      coverage0637 catalogue_core_nodup coverageSize0637) (by rfl) M

theorem minimal_mask_iff0638 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0638) M ↔
      ∃ c ∈ template0638, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0638) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0638))
    cores template0638 witness0638 coverage0638
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0638) (maskBits m)) cores template0638 witness0638
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0638))
      coverage0638 catalogue_core_nodup coverageSize0638) (by rfl) M

theorem minimal_mask_iff0639 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0639) M ↔
      ∃ c ∈ template0639, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0639) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0639))
    cores template0639 witness0639 coverage0639
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0639) (maskBits m)) cores template0639 witness0639
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0639))
      coverage0639 catalogue_core_nodup coverageSize0639) (by rfl) M

#print axioms minimal_mask_iff0600
#print axioms minimal_mask_iff0639
end Crown.CertificateData
