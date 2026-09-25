import generated.CatalogueBatch0017
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0016

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0640 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0640) M ↔
      ∃ c ∈ template0640, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0640) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0640))
    cores template0640 witness0640 coverage0640
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0640) (maskBits m)) cores template0640 witness0640
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0640))
      coverage0640 catalogue_core_nodup coverageSize0640) (by rfl) M

theorem minimal_mask_iff0641 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0641) M ↔
      ∃ c ∈ template0641, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0641) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0641))
    cores template0641 witness0641 coverage0641
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0641) (maskBits m)) cores template0641 witness0641
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0641))
      coverage0641 catalogue_core_nodup coverageSize0641) (by rfl) M

theorem minimal_mask_iff0642 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0642) M ↔
      ∃ c ∈ template0642, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0642) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0642))
    cores template0642 witness0642 coverage0642
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0642) (maskBits m)) cores template0642 witness0642
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0642))
      coverage0642 catalogue_core_nodup coverageSize0642) (by rfl) M

theorem minimal_mask_iff0643 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0643) M ↔
      ∃ c ∈ template0643, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0643) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0643))
    cores template0643 witness0643 coverage0643
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0643) (maskBits m)) cores template0643 witness0643
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0643))
      coverage0643 catalogue_core_nodup coverageSize0643) (by rfl) M

theorem minimal_mask_iff0644 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0644) M ↔
      ∃ c ∈ template0644, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0644) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0644))
    cores template0644 witness0644 coverage0644
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0644) (maskBits m)) cores template0644 witness0644
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0644))
      coverage0644 catalogue_core_nodup coverageSize0644) (by rfl) M

theorem minimal_mask_iff0645 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0645) M ↔
      ∃ c ∈ template0645, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0645) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0645))
    cores template0645 witness0645 coverage0645
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0645) (maskBits m)) cores template0645 witness0645
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0645))
      coverage0645 catalogue_core_nodup coverageSize0645) (by rfl) M

theorem minimal_mask_iff0646 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0646) M ↔
      ∃ c ∈ template0646, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0646) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0646))
    cores template0646 witness0646 coverage0646
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0646) (maskBits m)) cores template0646 witness0646
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0646))
      coverage0646 catalogue_core_nodup coverageSize0646) (by rfl) M

theorem minimal_mask_iff0647 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0647) M ↔
      ∃ c ∈ template0647, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0647) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0647))
    cores template0647 witness0647 coverage0647
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0647) (maskBits m)) cores template0647 witness0647
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0647))
      coverage0647 catalogue_core_nodup coverageSize0647) (by rfl) M

theorem minimal_mask_iff0648 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0648) M ↔
      ∃ c ∈ template0648, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0648) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0648))
    cores template0648 witness0648 coverage0648
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0648) (maskBits m)) cores template0648 witness0648
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0648))
      coverage0648 catalogue_core_nodup coverageSize0648) (by rfl) M

theorem minimal_mask_iff0649 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0649) M ↔
      ∃ c ∈ template0649, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0649) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0649))
    cores template0649 witness0649 coverage0649
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0649) (maskBits m)) cores template0649 witness0649
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0649))
      coverage0649 catalogue_core_nodup coverageSize0649) (by rfl) M

theorem minimal_mask_iff0650 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0650) M ↔
      ∃ c ∈ template0650, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0650) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0650))
    cores template0650 witness0650 coverage0650
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0650) (maskBits m)) cores template0650 witness0650
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0650))
      coverage0650 catalogue_core_nodup coverageSize0650) (by rfl) M

theorem minimal_mask_iff0651 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0651) M ↔
      ∃ c ∈ template0651, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0651) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0651))
    cores template0651 witness0651 coverage0651
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0651) (maskBits m)) cores template0651 witness0651
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0651))
      coverage0651 catalogue_core_nodup coverageSize0651) (by rfl) M

theorem minimal_mask_iff0652 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0652) M ↔
      ∃ c ∈ template0652, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0652) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0652))
    cores template0652 witness0652 coverage0652
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0652) (maskBits m)) cores template0652 witness0652
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0652))
      coverage0652 catalogue_core_nodup coverageSize0652) (by rfl) M

theorem minimal_mask_iff0653 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0653) M ↔
      ∃ c ∈ template0653, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0653) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0653))
    cores template0653 witness0653 coverage0653
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0653) (maskBits m)) cores template0653 witness0653
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0653))
      coverage0653 catalogue_core_nodup coverageSize0653) (by rfl) M

theorem minimal_mask_iff0654 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0654) M ↔
      ∃ c ∈ template0654, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0654) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0654))
    cores template0654 witness0654 coverage0654
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0654) (maskBits m)) cores template0654 witness0654
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0654))
      coverage0654 catalogue_core_nodup coverageSize0654) (by rfl) M

theorem minimal_mask_iff0655 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0655) M ↔
      ∃ c ∈ template0655, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0655) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0655))
    cores template0655 witness0655 coverage0655
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0655) (maskBits m)) cores template0655 witness0655
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0655))
      coverage0655 catalogue_core_nodup coverageSize0655) (by rfl) M

theorem minimal_mask_iff0656 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0656) M ↔
      ∃ c ∈ template0656, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0656) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0656))
    cores template0656 witness0656 coverage0656
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0656) (maskBits m)) cores template0656 witness0656
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0656))
      coverage0656 catalogue_core_nodup coverageSize0656) (by rfl) M

theorem minimal_mask_iff0657 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0657) M ↔
      ∃ c ∈ template0657, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0657) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0657))
    cores template0657 witness0657 coverage0657
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0657) (maskBits m)) cores template0657 witness0657
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0657))
      coverage0657 catalogue_core_nodup coverageSize0657) (by rfl) M

theorem minimal_mask_iff0658 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0658) M ↔
      ∃ c ∈ template0658, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0658) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0658))
    cores template0658 witness0658 coverage0658
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0658) (maskBits m)) cores template0658 witness0658
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0658))
      coverage0658 catalogue_core_nodup coverageSize0658) (by rfl) M

theorem minimal_mask_iff0659 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0659) M ↔
      ∃ c ∈ template0659, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0659) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0659))
    cores template0659 witness0659 coverage0659
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0659) (maskBits m)) cores template0659 witness0659
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0659))
      coverage0659 catalogue_core_nodup coverageSize0659) (by rfl) M

theorem minimal_mask_iff0660 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0660) M ↔
      ∃ c ∈ template0660, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0660) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0660))
    cores template0660 witness0660 coverage0660
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0660) (maskBits m)) cores template0660 witness0660
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0660))
      coverage0660 catalogue_core_nodup coverageSize0660) (by rfl) M

theorem minimal_mask_iff0661 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0661) M ↔
      ∃ c ∈ template0661, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0661) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0661))
    cores template0661 witness0661 coverage0661
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0661) (maskBits m)) cores template0661 witness0661
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0661))
      coverage0661 catalogue_core_nodup coverageSize0661) (by rfl) M

theorem minimal_mask_iff0662 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0662) M ↔
      ∃ c ∈ template0662, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0662) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0662))
    cores template0662 witness0662 coverage0662
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0662) (maskBits m)) cores template0662 witness0662
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0662))
      coverage0662 catalogue_core_nodup coverageSize0662) (by rfl) M

theorem minimal_mask_iff0663 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0663) M ↔
      ∃ c ∈ template0663, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0663) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0663))
    cores template0663 witness0663 coverage0663
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0663) (maskBits m)) cores template0663 witness0663
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0663))
      coverage0663 catalogue_core_nodup coverageSize0663) (by rfl) M

theorem minimal_mask_iff0664 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0664) M ↔
      ∃ c ∈ template0664, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0664) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0664))
    cores template0664 witness0664 coverage0664
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0664) (maskBits m)) cores template0664 witness0664
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0664))
      coverage0664 catalogue_core_nodup coverageSize0664) (by rfl) M

theorem minimal_mask_iff0665 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0665) M ↔
      ∃ c ∈ template0665, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0665) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0665))
    cores template0665 witness0665 coverage0665
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0665) (maskBits m)) cores template0665 witness0665
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0665))
      coverage0665 catalogue_core_nodup coverageSize0665) (by rfl) M

theorem minimal_mask_iff0666 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0666) M ↔
      ∃ c ∈ template0666, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0666) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0666))
    cores template0666 witness0666 coverage0666
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0666) (maskBits m)) cores template0666 witness0666
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0666))
      coverage0666 catalogue_core_nodup coverageSize0666) (by rfl) M

theorem minimal_mask_iff0667 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0667) M ↔
      ∃ c ∈ template0667, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0667) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0667))
    cores template0667 witness0667 coverage0667
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0667) (maskBits m)) cores template0667 witness0667
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0667))
      coverage0667 catalogue_core_nodup coverageSize0667) (by rfl) M

theorem minimal_mask_iff0668 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0668) M ↔
      ∃ c ∈ template0668, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0668) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0668))
    cores template0668 witness0668 coverage0668
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0668) (maskBits m)) cores template0668 witness0668
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0668))
      coverage0668 catalogue_core_nodup coverageSize0668) (by rfl) M

theorem minimal_mask_iff0669 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0669) M ↔
      ∃ c ∈ template0669, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0669) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0669))
    cores template0669 witness0669 coverage0669
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0669) (maskBits m)) cores template0669 witness0669
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0669))
      coverage0669 catalogue_core_nodup coverageSize0669) (by rfl) M

theorem minimal_mask_iff0670 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0670) M ↔
      ∃ c ∈ template0670, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0670) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0670))
    cores template0670 witness0670 coverage0670
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0670) (maskBits m)) cores template0670 witness0670
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0670))
      coverage0670 catalogue_core_nodup coverageSize0670) (by rfl) M

theorem minimal_mask_iff0671 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0671) M ↔
      ∃ c ∈ template0671, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0671) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0671))
    cores template0671 witness0671 coverage0671
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0671) (maskBits m)) cores template0671 witness0671
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0671))
      coverage0671 catalogue_core_nodup coverageSize0671) (by rfl) M

theorem minimal_mask_iff0672 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0672) M ↔
      ∃ c ∈ template0672, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0672) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0672))
    cores template0672 witness0672 coverage0672
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0672) (maskBits m)) cores template0672 witness0672
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0672))
      coverage0672 catalogue_core_nodup coverageSize0672) (by rfl) M

theorem minimal_mask_iff0673 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0673) M ↔
      ∃ c ∈ template0673, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0673) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0673))
    cores template0673 witness0673 coverage0673
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0673) (maskBits m)) cores template0673 witness0673
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0673))
      coverage0673 catalogue_core_nodup coverageSize0673) (by rfl) M

theorem minimal_mask_iff0674 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0674) M ↔
      ∃ c ∈ template0674, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0674) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0674))
    cores template0674 witness0674 coverage0674
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0674) (maskBits m)) cores template0674 witness0674
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0674))
      coverage0674 catalogue_core_nodup coverageSize0674) (by rfl) M

theorem minimal_mask_iff0675 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0675) M ↔
      ∃ c ∈ template0675, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0675) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0675))
    cores template0675 witness0675 coverage0675
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0675) (maskBits m)) cores template0675 witness0675
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0675))
      coverage0675 catalogue_core_nodup coverageSize0675) (by rfl) M

theorem minimal_mask_iff0676 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0676) M ↔
      ∃ c ∈ template0676, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0676) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0676))
    cores template0676 witness0676 coverage0676
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0676) (maskBits m)) cores template0676 witness0676
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0676))
      coverage0676 catalogue_core_nodup coverageSize0676) (by rfl) M

theorem minimal_mask_iff0677 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0677) M ↔
      ∃ c ∈ template0677, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0677) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0677))
    cores template0677 witness0677 coverage0677
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0677) (maskBits m)) cores template0677 witness0677
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0677))
      coverage0677 catalogue_core_nodup coverageSize0677) (by rfl) M

theorem minimal_mask_iff0678 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0678) M ↔
      ∃ c ∈ template0678, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0678) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0678))
    cores template0678 witness0678 coverage0678
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0678) (maskBits m)) cores template0678 witness0678
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0678))
      coverage0678 catalogue_core_nodup coverageSize0678) (by rfl) M

theorem minimal_mask_iff0679 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0679) M ↔
      ∃ c ∈ template0679, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0679) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0679))
    cores template0679 witness0679 coverage0679
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0679) (maskBits m)) cores template0679 witness0679
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0679))
      coverage0679 catalogue_core_nodup coverageSize0679) (by rfl) M

#print axioms minimal_mask_iff0640
#print axioms minimal_mask_iff0679
end Crown.CertificateData
