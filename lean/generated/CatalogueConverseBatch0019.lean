import generated.CatalogueBatch0019
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0018

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0720 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0720) M ↔
      ∃ c ∈ template0720, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0720) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0720))
    cores template0720 witness0720 coverage0720
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0720) (maskBits m)) cores template0720 witness0720
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0720))
      coverage0720 catalogue_core_nodup coverageSize0720) (by rfl) M

theorem minimal_mask_iff0721 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0721) M ↔
      ∃ c ∈ template0721, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0721) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0721))
    cores template0721 witness0721 coverage0721
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0721) (maskBits m)) cores template0721 witness0721
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0721))
      coverage0721 catalogue_core_nodup coverageSize0721) (by rfl) M

theorem minimal_mask_iff0722 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0722) M ↔
      ∃ c ∈ template0722, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0722) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0722))
    cores template0722 witness0722 coverage0722
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0722) (maskBits m)) cores template0722 witness0722
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0722))
      coverage0722 catalogue_core_nodup coverageSize0722) (by rfl) M

theorem minimal_mask_iff0723 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0723) M ↔
      ∃ c ∈ template0723, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0723) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0723))
    cores template0723 witness0723 coverage0723
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0723) (maskBits m)) cores template0723 witness0723
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0723))
      coverage0723 catalogue_core_nodup coverageSize0723) (by rfl) M

theorem minimal_mask_iff0724 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0724) M ↔
      ∃ c ∈ template0724, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0724) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0724))
    cores template0724 witness0724 coverage0724
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0724) (maskBits m)) cores template0724 witness0724
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0724))
      coverage0724 catalogue_core_nodup coverageSize0724) (by rfl) M

theorem minimal_mask_iff0725 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0725) M ↔
      ∃ c ∈ template0725, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0725) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0725))
    cores template0725 witness0725 coverage0725
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0725) (maskBits m)) cores template0725 witness0725
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0725))
      coverage0725 catalogue_core_nodup coverageSize0725) (by rfl) M

theorem minimal_mask_iff0726 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0726) M ↔
      ∃ c ∈ template0726, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0726) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0726))
    cores template0726 witness0726 coverage0726
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0726) (maskBits m)) cores template0726 witness0726
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0726))
      coverage0726 catalogue_core_nodup coverageSize0726) (by rfl) M

theorem minimal_mask_iff0727 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0727) M ↔
      ∃ c ∈ template0727, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0727) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0727))
    cores template0727 witness0727 coverage0727
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0727) (maskBits m)) cores template0727 witness0727
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0727))
      coverage0727 catalogue_core_nodup coverageSize0727) (by rfl) M

theorem minimal_mask_iff0728 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0728) M ↔
      ∃ c ∈ template0728, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0728) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0728))
    cores template0728 witness0728 coverage0728
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0728) (maskBits m)) cores template0728 witness0728
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0728))
      coverage0728 catalogue_core_nodup coverageSize0728) (by rfl) M

theorem minimal_mask_iff0729 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0729) M ↔
      ∃ c ∈ template0729, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0729) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0729))
    cores template0729 witness0729 coverage0729
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0729) (maskBits m)) cores template0729 witness0729
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0729))
      coverage0729 catalogue_core_nodup coverageSize0729) (by rfl) M

theorem minimal_mask_iff0730 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0730) M ↔
      ∃ c ∈ template0730, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0730) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0730))
    cores template0730 witness0730 coverage0730
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0730) (maskBits m)) cores template0730 witness0730
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0730))
      coverage0730 catalogue_core_nodup coverageSize0730) (by rfl) M

theorem minimal_mask_iff0731 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0731) M ↔
      ∃ c ∈ template0731, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0731) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0731))
    cores template0731 witness0731 coverage0731
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0731) (maskBits m)) cores template0731 witness0731
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0731))
      coverage0731 catalogue_core_nodup coverageSize0731) (by rfl) M

theorem minimal_mask_iff0732 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0732) M ↔
      ∃ c ∈ template0732, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0732) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0732))
    cores template0732 witness0732 coverage0732
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0732) (maskBits m)) cores template0732 witness0732
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0732))
      coverage0732 catalogue_core_nodup coverageSize0732) (by rfl) M

theorem minimal_mask_iff0733 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0733) M ↔
      ∃ c ∈ template0733, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0733) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0733))
    cores template0733 witness0733 coverage0733
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0733) (maskBits m)) cores template0733 witness0733
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0733))
      coverage0733 catalogue_core_nodup coverageSize0733) (by rfl) M

theorem minimal_mask_iff0734 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0734) M ↔
      ∃ c ∈ template0734, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0734) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0734))
    cores template0734 witness0734 coverage0734
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0734) (maskBits m)) cores template0734 witness0734
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0734))
      coverage0734 catalogue_core_nodup coverageSize0734) (by rfl) M

theorem minimal_mask_iff0735 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0735) M ↔
      ∃ c ∈ template0735, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0735) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0735))
    cores template0735 witness0735 coverage0735
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0735) (maskBits m)) cores template0735 witness0735
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0735))
      coverage0735 catalogue_core_nodup coverageSize0735) (by rfl) M

theorem minimal_mask_iff0736 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0736) M ↔
      ∃ c ∈ template0736, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0736) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0736))
    cores template0736 witness0736 coverage0736
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0736) (maskBits m)) cores template0736 witness0736
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0736))
      coverage0736 catalogue_core_nodup coverageSize0736) (by rfl) M

theorem minimal_mask_iff0737 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0737) M ↔
      ∃ c ∈ template0737, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0737) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0737))
    cores template0737 witness0737 coverage0737
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0737) (maskBits m)) cores template0737 witness0737
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0737))
      coverage0737 catalogue_core_nodup coverageSize0737) (by rfl) M

theorem minimal_mask_iff0738 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0738) M ↔
      ∃ c ∈ template0738, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0738) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0738))
    cores template0738 witness0738 coverage0738
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0738) (maskBits m)) cores template0738 witness0738
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0738))
      coverage0738 catalogue_core_nodup coverageSize0738) (by rfl) M

theorem minimal_mask_iff0739 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0739) M ↔
      ∃ c ∈ template0739, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0739) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0739))
    cores template0739 witness0739 coverage0739
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0739) (maskBits m)) cores template0739 witness0739
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0739))
      coverage0739 catalogue_core_nodup coverageSize0739) (by rfl) M

theorem minimal_mask_iff0740 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0740) M ↔
      ∃ c ∈ template0740, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0740) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0740))
    cores template0740 witness0740 coverage0740
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0740) (maskBits m)) cores template0740 witness0740
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0740))
      coverage0740 catalogue_core_nodup coverageSize0740) (by rfl) M

theorem minimal_mask_iff0741 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0741) M ↔
      ∃ c ∈ template0741, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0741) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0741))
    cores template0741 witness0741 coverage0741
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0741) (maskBits m)) cores template0741 witness0741
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0741))
      coverage0741 catalogue_core_nodup coverageSize0741) (by rfl) M

theorem minimal_mask_iff0742 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0742) M ↔
      ∃ c ∈ template0742, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0742) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0742))
    cores template0742 witness0742 coverage0742
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0742) (maskBits m)) cores template0742 witness0742
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0742))
      coverage0742 catalogue_core_nodup coverageSize0742) (by rfl) M

theorem minimal_mask_iff0743 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0743) M ↔
      ∃ c ∈ template0743, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0743) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0743))
    cores template0743 witness0743 coverage0743
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0743) (maskBits m)) cores template0743 witness0743
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0743))
      coverage0743 catalogue_core_nodup coverageSize0743) (by rfl) M

theorem minimal_mask_iff0744 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0744) M ↔
      ∃ c ∈ template0744, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0744) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0744))
    cores template0744 witness0744 coverage0744
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0744) (maskBits m)) cores template0744 witness0744
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0744))
      coverage0744 catalogue_core_nodup coverageSize0744) (by rfl) M

theorem minimal_mask_iff0745 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0745) M ↔
      ∃ c ∈ template0745, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0745) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0745))
    cores template0745 witness0745 coverage0745
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0745) (maskBits m)) cores template0745 witness0745
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0745))
      coverage0745 catalogue_core_nodup coverageSize0745) (by rfl) M

theorem minimal_mask_iff0746 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0746) M ↔
      ∃ c ∈ template0746, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0746) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0746))
    cores template0746 witness0746 coverage0746
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0746) (maskBits m)) cores template0746 witness0746
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0746))
      coverage0746 catalogue_core_nodup coverageSize0746) (by rfl) M

theorem minimal_mask_iff0747 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0747) M ↔
      ∃ c ∈ template0747, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0747) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0747))
    cores template0747 witness0747 coverage0747
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0747) (maskBits m)) cores template0747 witness0747
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0747))
      coverage0747 catalogue_core_nodup coverageSize0747) (by rfl) M

theorem minimal_mask_iff0748 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0748) M ↔
      ∃ c ∈ template0748, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0748) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0748))
    cores template0748 witness0748 coverage0748
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0748) (maskBits m)) cores template0748 witness0748
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0748))
      coverage0748 catalogue_core_nodup coverageSize0748) (by rfl) M

theorem minimal_mask_iff0749 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0749) M ↔
      ∃ c ∈ template0749, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0749) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0749))
    cores template0749 witness0749 coverage0749
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0749) (maskBits m)) cores template0749 witness0749
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0749))
      coverage0749 catalogue_core_nodup coverageSize0749) (by rfl) M

theorem minimal_mask_iff0750 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0750) M ↔
      ∃ c ∈ template0750, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0750) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0750))
    cores template0750 witness0750 coverage0750
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0750) (maskBits m)) cores template0750 witness0750
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0750))
      coverage0750 catalogue_core_nodup coverageSize0750) (by rfl) M

theorem minimal_mask_iff0751 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0751) M ↔
      ∃ c ∈ template0751, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0751) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0751))
    cores template0751 witness0751 coverage0751
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0751) (maskBits m)) cores template0751 witness0751
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0751))
      coverage0751 catalogue_core_nodup coverageSize0751) (by rfl) M

theorem minimal_mask_iff0752 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0752) M ↔
      ∃ c ∈ template0752, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0752) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0752))
    cores template0752 witness0752 coverage0752
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0752) (maskBits m)) cores template0752 witness0752
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0752))
      coverage0752 catalogue_core_nodup coverageSize0752) (by rfl) M

theorem minimal_mask_iff0753 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0753) M ↔
      ∃ c ∈ template0753, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0753) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0753))
    cores template0753 witness0753 coverage0753
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0753) (maskBits m)) cores template0753 witness0753
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0753))
      coverage0753 catalogue_core_nodup coverageSize0753) (by rfl) M

theorem minimal_mask_iff0754 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0754) M ↔
      ∃ c ∈ template0754, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0754) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0754))
    cores template0754 witness0754 coverage0754
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0754) (maskBits m)) cores template0754 witness0754
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0754))
      coverage0754 catalogue_core_nodup coverageSize0754) (by rfl) M

theorem minimal_mask_iff0755 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0755) M ↔
      ∃ c ∈ template0755, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0755) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0755))
    cores template0755 witness0755 coverage0755
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0755) (maskBits m)) cores template0755 witness0755
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0755))
      coverage0755 catalogue_core_nodup coverageSize0755) (by rfl) M

theorem minimal_mask_iff0756 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0756) M ↔
      ∃ c ∈ template0756, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0756) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0756))
    cores template0756 witness0756 coverage0756
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0756) (maskBits m)) cores template0756 witness0756
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0756))
      coverage0756 catalogue_core_nodup coverageSize0756) (by rfl) M

theorem minimal_mask_iff0757 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0757) M ↔
      ∃ c ∈ template0757, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0757) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0757))
    cores template0757 witness0757 coverage0757
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0757) (maskBits m)) cores template0757 witness0757
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0757))
      coverage0757 catalogue_core_nodup coverageSize0757) (by rfl) M

theorem minimal_mask_iff0758 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0758) M ↔
      ∃ c ∈ template0758, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0758) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0758))
    cores template0758 witness0758 coverage0758
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0758) (maskBits m)) cores template0758 witness0758
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0758))
      coverage0758 catalogue_core_nodup coverageSize0758) (by rfl) M

theorem minimal_mask_iff0759 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0759) M ↔
      ∃ c ∈ template0759, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0759) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0759))
    cores template0759 witness0759 coverage0759
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0759) (maskBits m)) cores template0759 witness0759
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0759))
      coverage0759 catalogue_core_nodup coverageSize0759) (by rfl) M

#print axioms minimal_mask_iff0720
#print axioms minimal_mask_iff0759
end Crown.CertificateData
