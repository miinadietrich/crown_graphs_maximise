import generated.CatalogueBatch0020
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0019

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0760 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0760) M ↔
      ∃ c ∈ template0760, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0760) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0760))
    cores template0760 witness0760 coverage0760
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0760) (maskBits m)) cores template0760 witness0760
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0760))
      coverage0760 catalogue_core_nodup coverageSize0760) (by rfl) M

theorem minimal_mask_iff0761 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0761) M ↔
      ∃ c ∈ template0761, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0761) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0761))
    cores template0761 witness0761 coverage0761
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0761) (maskBits m)) cores template0761 witness0761
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0761))
      coverage0761 catalogue_core_nodup coverageSize0761) (by rfl) M

theorem minimal_mask_iff0762 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0762) M ↔
      ∃ c ∈ template0762, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0762) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0762))
    cores template0762 witness0762 coverage0762
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0762) (maskBits m)) cores template0762 witness0762
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0762))
      coverage0762 catalogue_core_nodup coverageSize0762) (by rfl) M

theorem minimal_mask_iff0763 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0763) M ↔
      ∃ c ∈ template0763, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0763) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0763))
    cores template0763 witness0763 coverage0763
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0763) (maskBits m)) cores template0763 witness0763
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0763))
      coverage0763 catalogue_core_nodup coverageSize0763) (by rfl) M

theorem minimal_mask_iff0764 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0764) M ↔
      ∃ c ∈ template0764, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0764) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0764))
    cores template0764 witness0764 coverage0764
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0764) (maskBits m)) cores template0764 witness0764
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0764))
      coverage0764 catalogue_core_nodup coverageSize0764) (by rfl) M

theorem minimal_mask_iff0765 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0765) M ↔
      ∃ c ∈ template0765, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0765) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0765))
    cores template0765 witness0765 coverage0765
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0765) (maskBits m)) cores template0765 witness0765
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0765))
      coverage0765 catalogue_core_nodup coverageSize0765) (by rfl) M

theorem minimal_mask_iff0766 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0766) M ↔
      ∃ c ∈ template0766, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0766) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0766))
    cores template0766 witness0766 coverage0766
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0766) (maskBits m)) cores template0766 witness0766
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0766))
      coverage0766 catalogue_core_nodup coverageSize0766) (by rfl) M

theorem minimal_mask_iff0767 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0767) M ↔
      ∃ c ∈ template0767, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0767) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0767))
    cores template0767 witness0767 coverage0767
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0767) (maskBits m)) cores template0767 witness0767
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0767))
      coverage0767 catalogue_core_nodup coverageSize0767) (by rfl) M

theorem minimal_mask_iff0768 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0768) M ↔
      ∃ c ∈ template0768, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0768) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0768))
    cores template0768 witness0768 coverage0768
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0768) (maskBits m)) cores template0768 witness0768
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0768))
      coverage0768 catalogue_core_nodup coverageSize0768) (by rfl) M

theorem minimal_mask_iff0769 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0769) M ↔
      ∃ c ∈ template0769, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0769) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0769))
    cores template0769 witness0769 coverage0769
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0769) (maskBits m)) cores template0769 witness0769
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0769))
      coverage0769 catalogue_core_nodup coverageSize0769) (by rfl) M

theorem minimal_mask_iff0770 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0770) M ↔
      ∃ c ∈ template0770, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0770) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0770))
    cores template0770 witness0770 coverage0770
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0770) (maskBits m)) cores template0770 witness0770
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0770))
      coverage0770 catalogue_core_nodup coverageSize0770) (by rfl) M

theorem minimal_mask_iff0771 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0771) M ↔
      ∃ c ∈ template0771, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0771) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0771))
    cores template0771 witness0771 coverage0771
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0771) (maskBits m)) cores template0771 witness0771
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0771))
      coverage0771 catalogue_core_nodup coverageSize0771) (by rfl) M

theorem minimal_mask_iff0772 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0772) M ↔
      ∃ c ∈ template0772, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0772) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0772))
    cores template0772 witness0772 coverage0772
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0772) (maskBits m)) cores template0772 witness0772
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0772))
      coverage0772 catalogue_core_nodup coverageSize0772) (by rfl) M

theorem minimal_mask_iff0773 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0773) M ↔
      ∃ c ∈ template0773, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0773) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0773))
    cores template0773 witness0773 coverage0773
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0773) (maskBits m)) cores template0773 witness0773
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0773))
      coverage0773 catalogue_core_nodup coverageSize0773) (by rfl) M

theorem minimal_mask_iff0774 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0774) M ↔
      ∃ c ∈ template0774, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0774) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0774))
    cores template0774 witness0774 coverage0774
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0774) (maskBits m)) cores template0774 witness0774
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0774))
      coverage0774 catalogue_core_nodup coverageSize0774) (by rfl) M

theorem minimal_mask_iff0775 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0775) M ↔
      ∃ c ∈ template0775, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0775) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0775))
    cores template0775 witness0775 coverage0775
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0775) (maskBits m)) cores template0775 witness0775
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0775))
      coverage0775 catalogue_core_nodup coverageSize0775) (by rfl) M

theorem minimal_mask_iff0776 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0776) M ↔
      ∃ c ∈ template0776, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0776) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0776))
    cores template0776 witness0776 coverage0776
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0776) (maskBits m)) cores template0776 witness0776
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0776))
      coverage0776 catalogue_core_nodup coverageSize0776) (by rfl) M

theorem minimal_mask_iff0777 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0777) M ↔
      ∃ c ∈ template0777, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0777) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0777))
    cores template0777 witness0777 coverage0777
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0777) (maskBits m)) cores template0777 witness0777
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0777))
      coverage0777 catalogue_core_nodup coverageSize0777) (by rfl) M

theorem minimal_mask_iff0778 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0778) M ↔
      ∃ c ∈ template0778, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0778) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0778))
    cores template0778 witness0778 coverage0778
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0778) (maskBits m)) cores template0778 witness0778
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0778))
      coverage0778 catalogue_core_nodup coverageSize0778) (by rfl) M

theorem minimal_mask_iff0779 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0779) M ↔
      ∃ c ∈ template0779, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0779) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0779))
    cores template0779 witness0779 coverage0779
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0779) (maskBits m)) cores template0779 witness0779
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0779))
      coverage0779 catalogue_core_nodup coverageSize0779) (by rfl) M

theorem minimal_mask_iff0780 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0780) M ↔
      ∃ c ∈ template0780, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0780) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0780))
    cores template0780 witness0780 coverage0780
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0780) (maskBits m)) cores template0780 witness0780
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0780))
      coverage0780 catalogue_core_nodup coverageSize0780) (by rfl) M

theorem minimal_mask_iff0781 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0781) M ↔
      ∃ c ∈ template0781, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0781) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0781))
    cores template0781 witness0781 coverage0781
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0781) (maskBits m)) cores template0781 witness0781
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0781))
      coverage0781 catalogue_core_nodup coverageSize0781) (by rfl) M

theorem minimal_mask_iff0782 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0782) M ↔
      ∃ c ∈ template0782, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0782) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0782))
    cores template0782 witness0782 coverage0782
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0782) (maskBits m)) cores template0782 witness0782
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0782))
      coverage0782 catalogue_core_nodup coverageSize0782) (by rfl) M

theorem minimal_mask_iff0783 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0783) M ↔
      ∃ c ∈ template0783, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0783) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0783))
    cores template0783 witness0783 coverage0783
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0783) (maskBits m)) cores template0783 witness0783
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0783))
      coverage0783 catalogue_core_nodup coverageSize0783) (by rfl) M

theorem minimal_mask_iff0784 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0784) M ↔
      ∃ c ∈ template0784, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0784) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0784))
    cores template0784 witness0784 coverage0784
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0784) (maskBits m)) cores template0784 witness0784
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0784))
      coverage0784 catalogue_core_nodup coverageSize0784) (by rfl) M

theorem minimal_mask_iff0785 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0785) M ↔
      ∃ c ∈ template0785, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0785) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0785))
    cores template0785 witness0785 coverage0785
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0785) (maskBits m)) cores template0785 witness0785
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0785))
      coverage0785 catalogue_core_nodup coverageSize0785) (by rfl) M

theorem minimal_mask_iff0786 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0786) M ↔
      ∃ c ∈ template0786, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0786) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0786))
    cores template0786 witness0786 coverage0786
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0786) (maskBits m)) cores template0786 witness0786
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0786))
      coverage0786 catalogue_core_nodup coverageSize0786) (by rfl) M

theorem minimal_mask_iff0787 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0787) M ↔
      ∃ c ∈ template0787, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0787) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0787))
    cores template0787 witness0787 coverage0787
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0787) (maskBits m)) cores template0787 witness0787
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0787))
      coverage0787 catalogue_core_nodup coverageSize0787) (by rfl) M

theorem minimal_mask_iff0788 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0788) M ↔
      ∃ c ∈ template0788, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0788) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0788))
    cores template0788 witness0788 coverage0788
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0788) (maskBits m)) cores template0788 witness0788
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0788))
      coverage0788 catalogue_core_nodup coverageSize0788) (by rfl) M

theorem minimal_mask_iff0789 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0789) M ↔
      ∃ c ∈ template0789, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0789) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0789))
    cores template0789 witness0789 coverage0789
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0789) (maskBits m)) cores template0789 witness0789
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0789))
      coverage0789 catalogue_core_nodup coverageSize0789) (by rfl) M

theorem minimal_mask_iff0790 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0790) M ↔
      ∃ c ∈ template0790, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0790) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0790))
    cores template0790 witness0790 coverage0790
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0790) (maskBits m)) cores template0790 witness0790
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0790))
      coverage0790 catalogue_core_nodup coverageSize0790) (by rfl) M

theorem minimal_mask_iff0791 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0791) M ↔
      ∃ c ∈ template0791, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0791) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0791))
    cores template0791 witness0791 coverage0791
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0791) (maskBits m)) cores template0791 witness0791
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0791))
      coverage0791 catalogue_core_nodup coverageSize0791) (by rfl) M

theorem minimal_mask_iff0792 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0792) M ↔
      ∃ c ∈ template0792, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0792) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0792))
    cores template0792 witness0792 coverage0792
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0792) (maskBits m)) cores template0792 witness0792
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0792))
      coverage0792 catalogue_core_nodup coverageSize0792) (by rfl) M

theorem minimal_mask_iff0793 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0793) M ↔
      ∃ c ∈ template0793, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0793) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0793))
    cores template0793 witness0793 coverage0793
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0793) (maskBits m)) cores template0793 witness0793
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0793))
      coverage0793 catalogue_core_nodup coverageSize0793) (by rfl) M

theorem minimal_mask_iff0794 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0794) M ↔
      ∃ c ∈ template0794, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0794) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0794))
    cores template0794 witness0794 coverage0794
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0794) (maskBits m)) cores template0794 witness0794
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0794))
      coverage0794 catalogue_core_nodup coverageSize0794) (by rfl) M

theorem minimal_mask_iff0795 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0795) M ↔
      ∃ c ∈ template0795, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0795) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0795))
    cores template0795 witness0795 coverage0795
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0795) (maskBits m)) cores template0795 witness0795
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0795))
      coverage0795 catalogue_core_nodup coverageSize0795) (by rfl) M

theorem minimal_mask_iff0796 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0796) M ↔
      ∃ c ∈ template0796, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0796) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0796))
    cores template0796 witness0796 coverage0796
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0796) (maskBits m)) cores template0796 witness0796
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0796))
      coverage0796 catalogue_core_nodup coverageSize0796) (by rfl) M

theorem minimal_mask_iff0797 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0797) M ↔
      ∃ c ∈ template0797, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0797) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0797))
    cores template0797 witness0797 coverage0797
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0797) (maskBits m)) cores template0797 witness0797
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0797))
      coverage0797 catalogue_core_nodup coverageSize0797) (by rfl) M

theorem minimal_mask_iff0798 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0798) M ↔
      ∃ c ∈ template0798, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0798) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0798))
    cores template0798 witness0798 coverage0798
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0798) (maskBits m)) cores template0798 witness0798
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0798))
      coverage0798 catalogue_core_nodup coverageSize0798) (by rfl) M

theorem minimal_mask_iff0799 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0799) M ↔
      ∃ c ∈ template0799, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0799) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0799))
    cores template0799 witness0799 coverage0799
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0799) (maskBits m)) cores template0799 witness0799
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0799))
      coverage0799 catalogue_core_nodup coverageSize0799) (by rfl) M

#print axioms minimal_mask_iff0760
#print axioms minimal_mask_iff0799
end Crown.CertificateData
