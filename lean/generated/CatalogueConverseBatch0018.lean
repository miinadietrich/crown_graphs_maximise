import generated.CatalogueBatch0018
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0017

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0680 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0680) M ↔
      ∃ c ∈ template0680, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0680) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0680))
    cores template0680 witness0680 coverage0680
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0680) (maskBits m)) cores template0680 witness0680
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0680))
      coverage0680 catalogue_core_nodup coverageSize0680) (by rfl) M

theorem minimal_mask_iff0681 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0681) M ↔
      ∃ c ∈ template0681, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0681) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0681))
    cores template0681 witness0681 coverage0681
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0681) (maskBits m)) cores template0681 witness0681
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0681))
      coverage0681 catalogue_core_nodup coverageSize0681) (by rfl) M

theorem minimal_mask_iff0682 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0682) M ↔
      ∃ c ∈ template0682, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0682) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0682))
    cores template0682 witness0682 coverage0682
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0682) (maskBits m)) cores template0682 witness0682
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0682))
      coverage0682 catalogue_core_nodup coverageSize0682) (by rfl) M

theorem minimal_mask_iff0683 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0683) M ↔
      ∃ c ∈ template0683, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0683) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0683))
    cores template0683 witness0683 coverage0683
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0683) (maskBits m)) cores template0683 witness0683
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0683))
      coverage0683 catalogue_core_nodup coverageSize0683) (by rfl) M

theorem minimal_mask_iff0684 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0684) M ↔
      ∃ c ∈ template0684, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0684) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0684))
    cores template0684 witness0684 coverage0684
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0684) (maskBits m)) cores template0684 witness0684
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0684))
      coverage0684 catalogue_core_nodup coverageSize0684) (by rfl) M

theorem minimal_mask_iff0685 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0685) M ↔
      ∃ c ∈ template0685, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0685) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0685))
    cores template0685 witness0685 coverage0685
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0685) (maskBits m)) cores template0685 witness0685
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0685))
      coverage0685 catalogue_core_nodup coverageSize0685) (by rfl) M

theorem minimal_mask_iff0686 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0686) M ↔
      ∃ c ∈ template0686, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0686) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0686))
    cores template0686 witness0686 coverage0686
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0686) (maskBits m)) cores template0686 witness0686
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0686))
      coverage0686 catalogue_core_nodup coverageSize0686) (by rfl) M

theorem minimal_mask_iff0687 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0687) M ↔
      ∃ c ∈ template0687, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0687) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0687))
    cores template0687 witness0687 coverage0687
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0687) (maskBits m)) cores template0687 witness0687
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0687))
      coverage0687 catalogue_core_nodup coverageSize0687) (by rfl) M

theorem minimal_mask_iff0688 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0688) M ↔
      ∃ c ∈ template0688, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0688) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0688))
    cores template0688 witness0688 coverage0688
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0688) (maskBits m)) cores template0688 witness0688
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0688))
      coverage0688 catalogue_core_nodup coverageSize0688) (by rfl) M

theorem minimal_mask_iff0689 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0689) M ↔
      ∃ c ∈ template0689, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0689) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0689))
    cores template0689 witness0689 coverage0689
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0689) (maskBits m)) cores template0689 witness0689
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0689))
      coverage0689 catalogue_core_nodup coverageSize0689) (by rfl) M

theorem minimal_mask_iff0690 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0690) M ↔
      ∃ c ∈ template0690, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0690) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0690))
    cores template0690 witness0690 coverage0690
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0690) (maskBits m)) cores template0690 witness0690
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0690))
      coverage0690 catalogue_core_nodup coverageSize0690) (by rfl) M

theorem minimal_mask_iff0691 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0691) M ↔
      ∃ c ∈ template0691, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0691) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0691))
    cores template0691 witness0691 coverage0691
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0691) (maskBits m)) cores template0691 witness0691
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0691))
      coverage0691 catalogue_core_nodup coverageSize0691) (by rfl) M

theorem minimal_mask_iff0692 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0692) M ↔
      ∃ c ∈ template0692, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0692) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0692))
    cores template0692 witness0692 coverage0692
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0692) (maskBits m)) cores template0692 witness0692
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0692))
      coverage0692 catalogue_core_nodup coverageSize0692) (by rfl) M

theorem minimal_mask_iff0693 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0693) M ↔
      ∃ c ∈ template0693, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0693) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0693))
    cores template0693 witness0693 coverage0693
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0693) (maskBits m)) cores template0693 witness0693
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0693))
      coverage0693 catalogue_core_nodup coverageSize0693) (by rfl) M

theorem minimal_mask_iff0694 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0694) M ↔
      ∃ c ∈ template0694, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0694) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0694))
    cores template0694 witness0694 coverage0694
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0694) (maskBits m)) cores template0694 witness0694
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0694))
      coverage0694 catalogue_core_nodup coverageSize0694) (by rfl) M

theorem minimal_mask_iff0695 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0695) M ↔
      ∃ c ∈ template0695, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0695) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0695))
    cores template0695 witness0695 coverage0695
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0695) (maskBits m)) cores template0695 witness0695
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0695))
      coverage0695 catalogue_core_nodup coverageSize0695) (by rfl) M

theorem minimal_mask_iff0696 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0696) M ↔
      ∃ c ∈ template0696, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0696) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0696))
    cores template0696 witness0696 coverage0696
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0696) (maskBits m)) cores template0696 witness0696
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0696))
      coverage0696 catalogue_core_nodup coverageSize0696) (by rfl) M

theorem minimal_mask_iff0697 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0697) M ↔
      ∃ c ∈ template0697, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0697) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0697))
    cores template0697 witness0697 coverage0697
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0697) (maskBits m)) cores template0697 witness0697
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0697))
      coverage0697 catalogue_core_nodup coverageSize0697) (by rfl) M

theorem minimal_mask_iff0698 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0698) M ↔
      ∃ c ∈ template0698, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0698) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0698))
    cores template0698 witness0698 coverage0698
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0698) (maskBits m)) cores template0698 witness0698
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0698))
      coverage0698 catalogue_core_nodup coverageSize0698) (by rfl) M

theorem minimal_mask_iff0699 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0699) M ↔
      ∃ c ∈ template0699, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0699) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0699))
    cores template0699 witness0699 coverage0699
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0699) (maskBits m)) cores template0699 witness0699
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0699))
      coverage0699 catalogue_core_nodup coverageSize0699) (by rfl) M

theorem minimal_mask_iff0700 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0700) M ↔
      ∃ c ∈ template0700, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0700) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0700))
    cores template0700 witness0700 coverage0700
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0700) (maskBits m)) cores template0700 witness0700
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0700))
      coverage0700 catalogue_core_nodup coverageSize0700) (by rfl) M

theorem minimal_mask_iff0701 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0701) M ↔
      ∃ c ∈ template0701, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0701) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0701))
    cores template0701 witness0701 coverage0701
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0701) (maskBits m)) cores template0701 witness0701
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0701))
      coverage0701 catalogue_core_nodup coverageSize0701) (by rfl) M

theorem minimal_mask_iff0702 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0702) M ↔
      ∃ c ∈ template0702, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0702) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0702))
    cores template0702 witness0702 coverage0702
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0702) (maskBits m)) cores template0702 witness0702
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0702))
      coverage0702 catalogue_core_nodup coverageSize0702) (by rfl) M

theorem minimal_mask_iff0703 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0703) M ↔
      ∃ c ∈ template0703, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0703) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0703))
    cores template0703 witness0703 coverage0703
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0703) (maskBits m)) cores template0703 witness0703
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0703))
      coverage0703 catalogue_core_nodup coverageSize0703) (by rfl) M

theorem minimal_mask_iff0704 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0704) M ↔
      ∃ c ∈ template0704, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0704) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0704))
    cores template0704 witness0704 coverage0704
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0704) (maskBits m)) cores template0704 witness0704
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0704))
      coverage0704 catalogue_core_nodup coverageSize0704) (by rfl) M

theorem minimal_mask_iff0705 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0705) M ↔
      ∃ c ∈ template0705, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0705) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0705))
    cores template0705 witness0705 coverage0705
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0705) (maskBits m)) cores template0705 witness0705
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0705))
      coverage0705 catalogue_core_nodup coverageSize0705) (by rfl) M

theorem minimal_mask_iff0706 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0706) M ↔
      ∃ c ∈ template0706, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0706) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0706))
    cores template0706 witness0706 coverage0706
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0706) (maskBits m)) cores template0706 witness0706
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0706))
      coverage0706 catalogue_core_nodup coverageSize0706) (by rfl) M

theorem minimal_mask_iff0707 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0707) M ↔
      ∃ c ∈ template0707, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0707) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0707))
    cores template0707 witness0707 coverage0707
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0707) (maskBits m)) cores template0707 witness0707
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0707))
      coverage0707 catalogue_core_nodup coverageSize0707) (by rfl) M

theorem minimal_mask_iff0708 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0708) M ↔
      ∃ c ∈ template0708, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0708) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0708))
    cores template0708 witness0708 coverage0708
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0708) (maskBits m)) cores template0708 witness0708
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0708))
      coverage0708 catalogue_core_nodup coverageSize0708) (by rfl) M

theorem minimal_mask_iff0709 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0709) M ↔
      ∃ c ∈ template0709, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0709) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0709))
    cores template0709 witness0709 coverage0709
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0709) (maskBits m)) cores template0709 witness0709
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0709))
      coverage0709 catalogue_core_nodup coverageSize0709) (by rfl) M

theorem minimal_mask_iff0710 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0710) M ↔
      ∃ c ∈ template0710, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0710) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0710))
    cores template0710 witness0710 coverage0710
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0710) (maskBits m)) cores template0710 witness0710
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0710))
      coverage0710 catalogue_core_nodup coverageSize0710) (by rfl) M

theorem minimal_mask_iff0711 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0711) M ↔
      ∃ c ∈ template0711, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0711) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0711))
    cores template0711 witness0711 coverage0711
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0711) (maskBits m)) cores template0711 witness0711
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0711))
      coverage0711 catalogue_core_nodup coverageSize0711) (by rfl) M

theorem minimal_mask_iff0712 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0712) M ↔
      ∃ c ∈ template0712, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0712) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0712))
    cores template0712 witness0712 coverage0712
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0712) (maskBits m)) cores template0712 witness0712
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0712))
      coverage0712 catalogue_core_nodup coverageSize0712) (by rfl) M

theorem minimal_mask_iff0713 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0713) M ↔
      ∃ c ∈ template0713, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0713) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0713))
    cores template0713 witness0713 coverage0713
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0713) (maskBits m)) cores template0713 witness0713
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0713))
      coverage0713 catalogue_core_nodup coverageSize0713) (by rfl) M

theorem minimal_mask_iff0714 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0714) M ↔
      ∃ c ∈ template0714, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0714) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0714))
    cores template0714 witness0714 coverage0714
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0714) (maskBits m)) cores template0714 witness0714
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0714))
      coverage0714 catalogue_core_nodup coverageSize0714) (by rfl) M

theorem minimal_mask_iff0715 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0715) M ↔
      ∃ c ∈ template0715, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0715) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0715))
    cores template0715 witness0715 coverage0715
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0715) (maskBits m)) cores template0715 witness0715
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0715))
      coverage0715 catalogue_core_nodup coverageSize0715) (by rfl) M

theorem minimal_mask_iff0716 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0716) M ↔
      ∃ c ∈ template0716, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0716) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0716))
    cores template0716 witness0716 coverage0716
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0716) (maskBits m)) cores template0716 witness0716
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0716))
      coverage0716 catalogue_core_nodup coverageSize0716) (by rfl) M

theorem minimal_mask_iff0717 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0717) M ↔
      ∃ c ∈ template0717, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0717) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0717))
    cores template0717 witness0717 coverage0717
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0717) (maskBits m)) cores template0717 witness0717
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0717))
      coverage0717 catalogue_core_nodup coverageSize0717) (by rfl) M

theorem minimal_mask_iff0718 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0718) M ↔
      ∃ c ∈ template0718, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0718) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0718))
    cores template0718 witness0718 coverage0718
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0718) (maskBits m)) cores template0718 witness0718
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0718))
      coverage0718 catalogue_core_nodup coverageSize0718) (by rfl) M

theorem minimal_mask_iff0719 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0719) M ↔
      ∃ c ∈ template0719, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0719) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0719))
    cores template0719 witness0719 coverage0719
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0719) (maskBits m)) cores template0719 witness0719
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0719))
      coverage0719 catalogue_core_nodup coverageSize0719) (by rfl) M

#print axioms minimal_mask_iff0680
#print axioms minimal_mask_iff0719
end Crown.CertificateData
