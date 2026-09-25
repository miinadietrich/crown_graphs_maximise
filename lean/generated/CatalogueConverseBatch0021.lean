import generated.CatalogueBatch0021
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0020

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0800 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0800) M ↔
      ∃ c ∈ template0800, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0800) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0800))
    cores template0800 witness0800 coverage0800
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0800) (maskBits m)) cores template0800 witness0800
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0800))
      coverage0800 catalogue_core_nodup coverageSize0800) (by rfl) M

theorem minimal_mask_iff0801 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0801) M ↔
      ∃ c ∈ template0801, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0801) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0801))
    cores template0801 witness0801 coverage0801
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0801) (maskBits m)) cores template0801 witness0801
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0801))
      coverage0801 catalogue_core_nodup coverageSize0801) (by rfl) M

theorem minimal_mask_iff0802 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0802) M ↔
      ∃ c ∈ template0802, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0802) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0802))
    cores template0802 witness0802 coverage0802
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0802) (maskBits m)) cores template0802 witness0802
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0802))
      coverage0802 catalogue_core_nodup coverageSize0802) (by rfl) M

theorem minimal_mask_iff0803 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0803) M ↔
      ∃ c ∈ template0803, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0803) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0803))
    cores template0803 witness0803 coverage0803
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0803) (maskBits m)) cores template0803 witness0803
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0803))
      coverage0803 catalogue_core_nodup coverageSize0803) (by rfl) M

theorem minimal_mask_iff0804 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0804) M ↔
      ∃ c ∈ template0804, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0804) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0804))
    cores template0804 witness0804 coverage0804
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0804) (maskBits m)) cores template0804 witness0804
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0804))
      coverage0804 catalogue_core_nodup coverageSize0804) (by rfl) M

theorem minimal_mask_iff0805 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0805) M ↔
      ∃ c ∈ template0805, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0805) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0805))
    cores template0805 witness0805 coverage0805
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0805) (maskBits m)) cores template0805 witness0805
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0805))
      coverage0805 catalogue_core_nodup coverageSize0805) (by rfl) M

theorem minimal_mask_iff0806 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0806) M ↔
      ∃ c ∈ template0806, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0806) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0806))
    cores template0806 witness0806 coverage0806
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0806) (maskBits m)) cores template0806 witness0806
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0806))
      coverage0806 catalogue_core_nodup coverageSize0806) (by rfl) M

theorem minimal_mask_iff0807 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0807) M ↔
      ∃ c ∈ template0807, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0807) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0807))
    cores template0807 witness0807 coverage0807
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0807) (maskBits m)) cores template0807 witness0807
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0807))
      coverage0807 catalogue_core_nodup coverageSize0807) (by rfl) M

theorem minimal_mask_iff0808 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0808) M ↔
      ∃ c ∈ template0808, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0808) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0808))
    cores template0808 witness0808 coverage0808
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0808) (maskBits m)) cores template0808 witness0808
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0808))
      coverage0808 catalogue_core_nodup coverageSize0808) (by rfl) M

theorem minimal_mask_iff0809 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0809) M ↔
      ∃ c ∈ template0809, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0809) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0809))
    cores template0809 witness0809 coverage0809
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0809) (maskBits m)) cores template0809 witness0809
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0809))
      coverage0809 catalogue_core_nodup coverageSize0809) (by rfl) M

theorem minimal_mask_iff0810 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0810) M ↔
      ∃ c ∈ template0810, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0810) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0810))
    cores template0810 witness0810 coverage0810
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0810) (maskBits m)) cores template0810 witness0810
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0810))
      coverage0810 catalogue_core_nodup coverageSize0810) (by rfl) M

theorem minimal_mask_iff0811 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0811) M ↔
      ∃ c ∈ template0811, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0811) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0811))
    cores template0811 witness0811 coverage0811
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0811) (maskBits m)) cores template0811 witness0811
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0811))
      coverage0811 catalogue_core_nodup coverageSize0811) (by rfl) M

theorem minimal_mask_iff0812 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0812) M ↔
      ∃ c ∈ template0812, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0812) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0812))
    cores template0812 witness0812 coverage0812
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0812) (maskBits m)) cores template0812 witness0812
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0812))
      coverage0812 catalogue_core_nodup coverageSize0812) (by rfl) M

theorem minimal_mask_iff0813 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0813) M ↔
      ∃ c ∈ template0813, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0813) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0813))
    cores template0813 witness0813 coverage0813
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0813) (maskBits m)) cores template0813 witness0813
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0813))
      coverage0813 catalogue_core_nodup coverageSize0813) (by rfl) M

theorem minimal_mask_iff0814 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0814) M ↔
      ∃ c ∈ template0814, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0814) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0814))
    cores template0814 witness0814 coverage0814
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0814) (maskBits m)) cores template0814 witness0814
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0814))
      coverage0814 catalogue_core_nodup coverageSize0814) (by rfl) M

theorem minimal_mask_iff0815 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0815) M ↔
      ∃ c ∈ template0815, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0815) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0815))
    cores template0815 witness0815 coverage0815
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0815) (maskBits m)) cores template0815 witness0815
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0815))
      coverage0815 catalogue_core_nodup coverageSize0815) (by rfl) M

theorem minimal_mask_iff0816 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0816) M ↔
      ∃ c ∈ template0816, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0816) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0816))
    cores template0816 witness0816 coverage0816
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0816) (maskBits m)) cores template0816 witness0816
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0816))
      coverage0816 catalogue_core_nodup coverageSize0816) (by rfl) M

theorem minimal_mask_iff0817 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0817) M ↔
      ∃ c ∈ template0817, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0817) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0817))
    cores template0817 witness0817 coverage0817
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0817) (maskBits m)) cores template0817 witness0817
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0817))
      coverage0817 catalogue_core_nodup coverageSize0817) (by rfl) M

theorem minimal_mask_iff0818 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0818) M ↔
      ∃ c ∈ template0818, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0818) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0818))
    cores template0818 witness0818 coverage0818
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0818) (maskBits m)) cores template0818 witness0818
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0818))
      coverage0818 catalogue_core_nodup coverageSize0818) (by rfl) M

theorem minimal_mask_iff0819 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0819) M ↔
      ∃ c ∈ template0819, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0819) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0819))
    cores template0819 witness0819 coverage0819
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0819) (maskBits m)) cores template0819 witness0819
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0819))
      coverage0819 catalogue_core_nodup coverageSize0819) (by rfl) M

theorem minimal_mask_iff0820 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0820) M ↔
      ∃ c ∈ template0820, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0820) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0820))
    cores template0820 witness0820 coverage0820
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0820) (maskBits m)) cores template0820 witness0820
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0820))
      coverage0820 catalogue_core_nodup coverageSize0820) (by rfl) M

theorem minimal_mask_iff0821 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0821) M ↔
      ∃ c ∈ template0821, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0821) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0821))
    cores template0821 witness0821 coverage0821
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0821) (maskBits m)) cores template0821 witness0821
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0821))
      coverage0821 catalogue_core_nodup coverageSize0821) (by rfl) M

theorem minimal_mask_iff0822 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0822) M ↔
      ∃ c ∈ template0822, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0822) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0822))
    cores template0822 witness0822 coverage0822
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0822) (maskBits m)) cores template0822 witness0822
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0822))
      coverage0822 catalogue_core_nodup coverageSize0822) (by rfl) M

theorem minimal_mask_iff0823 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0823) M ↔
      ∃ c ∈ template0823, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0823) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0823))
    cores template0823 witness0823 coverage0823
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0823) (maskBits m)) cores template0823 witness0823
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0823))
      coverage0823 catalogue_core_nodup coverageSize0823) (by rfl) M

theorem minimal_mask_iff0824 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0824) M ↔
      ∃ c ∈ template0824, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0824) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0824))
    cores template0824 witness0824 coverage0824
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0824) (maskBits m)) cores template0824 witness0824
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0824))
      coverage0824 catalogue_core_nodup coverageSize0824) (by rfl) M

theorem minimal_mask_iff0825 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0825) M ↔
      ∃ c ∈ template0825, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0825) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0825))
    cores template0825 witness0825 coverage0825
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0825) (maskBits m)) cores template0825 witness0825
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0825))
      coverage0825 catalogue_core_nodup coverageSize0825) (by rfl) M

theorem minimal_mask_iff0826 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0826) M ↔
      ∃ c ∈ template0826, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0826) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0826))
    cores template0826 witness0826 coverage0826
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0826) (maskBits m)) cores template0826 witness0826
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0826))
      coverage0826 catalogue_core_nodup coverageSize0826) (by rfl) M

theorem minimal_mask_iff0827 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0827) M ↔
      ∃ c ∈ template0827, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0827) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0827))
    cores template0827 witness0827 coverage0827
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0827) (maskBits m)) cores template0827 witness0827
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0827))
      coverage0827 catalogue_core_nodup coverageSize0827) (by rfl) M

theorem minimal_mask_iff0828 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0828) M ↔
      ∃ c ∈ template0828, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0828) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0828))
    cores template0828 witness0828 coverage0828
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0828) (maskBits m)) cores template0828 witness0828
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0828))
      coverage0828 catalogue_core_nodup coverageSize0828) (by rfl) M

theorem minimal_mask_iff0829 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0829) M ↔
      ∃ c ∈ template0829, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0829) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0829))
    cores template0829 witness0829 coverage0829
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0829) (maskBits m)) cores template0829 witness0829
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0829))
      coverage0829 catalogue_core_nodup coverageSize0829) (by rfl) M

theorem minimal_mask_iff0830 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0830) M ↔
      ∃ c ∈ template0830, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0830) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0830))
    cores template0830 witness0830 coverage0830
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0830) (maskBits m)) cores template0830 witness0830
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0830))
      coverage0830 catalogue_core_nodup coverageSize0830) (by rfl) M

theorem minimal_mask_iff0831 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0831) M ↔
      ∃ c ∈ template0831, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0831) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0831))
    cores template0831 witness0831 coverage0831
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0831) (maskBits m)) cores template0831 witness0831
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0831))
      coverage0831 catalogue_core_nodup coverageSize0831) (by rfl) M

theorem minimal_mask_iff0832 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0832) M ↔
      ∃ c ∈ template0832, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0832) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0832))
    cores template0832 witness0832 coverage0832
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0832) (maskBits m)) cores template0832 witness0832
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0832))
      coverage0832 catalogue_core_nodup coverageSize0832) (by rfl) M

theorem minimal_mask_iff0833 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0833) M ↔
      ∃ c ∈ template0833, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0833) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0833))
    cores template0833 witness0833 coverage0833
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0833) (maskBits m)) cores template0833 witness0833
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0833))
      coverage0833 catalogue_core_nodup coverageSize0833) (by rfl) M

theorem minimal_mask_iff0834 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0834) M ↔
      ∃ c ∈ template0834, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0834) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0834))
    cores template0834 witness0834 coverage0834
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0834) (maskBits m)) cores template0834 witness0834
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0834))
      coverage0834 catalogue_core_nodup coverageSize0834) (by rfl) M

theorem minimal_mask_iff0835 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0835) M ↔
      ∃ c ∈ template0835, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0835) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0835))
    cores template0835 witness0835 coverage0835
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0835) (maskBits m)) cores template0835 witness0835
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0835))
      coverage0835 catalogue_core_nodup coverageSize0835) (by rfl) M

theorem minimal_mask_iff0836 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0836) M ↔
      ∃ c ∈ template0836, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0836) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0836))
    cores template0836 witness0836 coverage0836
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0836) (maskBits m)) cores template0836 witness0836
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0836))
      coverage0836 catalogue_core_nodup coverageSize0836) (by rfl) M

theorem minimal_mask_iff0837 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0837) M ↔
      ∃ c ∈ template0837, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0837) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0837))
    cores template0837 witness0837 coverage0837
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0837) (maskBits m)) cores template0837 witness0837
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0837))
      coverage0837 catalogue_core_nodup coverageSize0837) (by rfl) M

theorem minimal_mask_iff0838 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0838) M ↔
      ∃ c ∈ template0838, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0838) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0838))
    cores template0838 witness0838 coverage0838
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0838) (maskBits m)) cores template0838 witness0838
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0838))
      coverage0838 catalogue_core_nodup coverageSize0838) (by rfl) M

theorem minimal_mask_iff0839 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0839) M ↔
      ∃ c ∈ template0839, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0839) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0839))
    cores template0839 witness0839 coverage0839
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0839) (maskBits m)) cores template0839 witness0839
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0839))
      coverage0839 catalogue_core_nodup coverageSize0839) (by rfl) M

#print axioms minimal_mask_iff0800
#print axioms minimal_mask_iff0839
end Crown.CertificateData
