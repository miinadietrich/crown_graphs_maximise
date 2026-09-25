import generated.CatalogueBatch0002
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0001

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0040 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0040) M ↔
      ∃ c ∈ template0040, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0040) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0040))
    cores template0040 witness0040 coverage0040
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0040) (maskBits m)) cores template0040 witness0040
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0040))
      coverage0040 catalogue_core_nodup coverageSize0040) (by rfl) M

theorem minimal_mask_iff0041 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0041) M ↔
      ∃ c ∈ template0041, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0041) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0041))
    cores template0041 witness0041 coverage0041
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0041) (maskBits m)) cores template0041 witness0041
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0041))
      coverage0041 catalogue_core_nodup coverageSize0041) (by rfl) M

theorem minimal_mask_iff0042 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0042) M ↔
      ∃ c ∈ template0042, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0042) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0042))
    cores template0042 witness0042 coverage0042
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0042) (maskBits m)) cores template0042 witness0042
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0042))
      coverage0042 catalogue_core_nodup coverageSize0042) (by rfl) M

theorem minimal_mask_iff0043 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0043) M ↔
      ∃ c ∈ template0043, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0043) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0043))
    cores template0043 witness0043 coverage0043
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0043) (maskBits m)) cores template0043 witness0043
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0043))
      coverage0043 catalogue_core_nodup coverageSize0043) (by rfl) M

theorem minimal_mask_iff0044 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0044) M ↔
      ∃ c ∈ template0044, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0044) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0044))
    cores template0044 witness0044 coverage0044
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0044) (maskBits m)) cores template0044 witness0044
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0044))
      coverage0044 catalogue_core_nodup coverageSize0044) (by rfl) M

theorem minimal_mask_iff0045 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0045) M ↔
      ∃ c ∈ template0045, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0045) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0045))
    cores template0045 witness0045 coverage0045
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0045) (maskBits m)) cores template0045 witness0045
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0045))
      coverage0045 catalogue_core_nodup coverageSize0045) (by rfl) M

theorem minimal_mask_iff0046 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0046) M ↔
      ∃ c ∈ template0046, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0046) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0046))
    cores template0046 witness0046 coverage0046
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0046) (maskBits m)) cores template0046 witness0046
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0046))
      coverage0046 catalogue_core_nodup coverageSize0046) (by rfl) M

theorem minimal_mask_iff0047 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0047) M ↔
      ∃ c ∈ template0047, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0047) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0047))
    cores template0047 witness0047 coverage0047
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0047) (maskBits m)) cores template0047 witness0047
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0047))
      coverage0047 catalogue_core_nodup coverageSize0047) (by rfl) M

theorem minimal_mask_iff0048 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0048) M ↔
      ∃ c ∈ template0048, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0048) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0048))
    cores template0048 witness0048 coverage0048
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0048) (maskBits m)) cores template0048 witness0048
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0048))
      coverage0048 catalogue_core_nodup coverageSize0048) (by rfl) M

theorem minimal_mask_iff0049 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0049) M ↔
      ∃ c ∈ template0049, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0049) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0049))
    cores template0049 witness0049 coverage0049
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0049) (maskBits m)) cores template0049 witness0049
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0049))
      coverage0049 catalogue_core_nodup coverageSize0049) (by rfl) M

theorem minimal_mask_iff0050 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0050) M ↔
      ∃ c ∈ template0050, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0050) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0050))
    cores template0050 witness0050 coverage0050
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0050) (maskBits m)) cores template0050 witness0050
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0050))
      coverage0050 catalogue_core_nodup coverageSize0050) (by rfl) M

theorem minimal_mask_iff0051 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0051) M ↔
      ∃ c ∈ template0051, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0051) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0051))
    cores template0051 witness0051 coverage0051
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0051) (maskBits m)) cores template0051 witness0051
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0051))
      coverage0051 catalogue_core_nodup coverageSize0051) (by rfl) M

theorem minimal_mask_iff0052 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0052) M ↔
      ∃ c ∈ template0052, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0052) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0052))
    cores template0052 witness0052 coverage0052
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0052) (maskBits m)) cores template0052 witness0052
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0052))
      coverage0052 catalogue_core_nodup coverageSize0052) (by rfl) M

theorem minimal_mask_iff0053 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0053) M ↔
      ∃ c ∈ template0053, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0053) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0053))
    cores template0053 witness0053 coverage0053
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0053) (maskBits m)) cores template0053 witness0053
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0053))
      coverage0053 catalogue_core_nodup coverageSize0053) (by rfl) M

theorem minimal_mask_iff0054 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0054) M ↔
      ∃ c ∈ template0054, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0054) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0054))
    cores template0054 witness0054 coverage0054
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0054) (maskBits m)) cores template0054 witness0054
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0054))
      coverage0054 catalogue_core_nodup coverageSize0054) (by rfl) M

theorem minimal_mask_iff0055 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0055) M ↔
      ∃ c ∈ template0055, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0055) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0055))
    cores template0055 witness0055 coverage0055
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0055) (maskBits m)) cores template0055 witness0055
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0055))
      coverage0055 catalogue_core_nodup coverageSize0055) (by rfl) M

theorem minimal_mask_iff0056 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0056) M ↔
      ∃ c ∈ template0056, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0056) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0056))
    cores template0056 witness0056 coverage0056
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0056) (maskBits m)) cores template0056 witness0056
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0056))
      coverage0056 catalogue_core_nodup coverageSize0056) (by rfl) M

theorem minimal_mask_iff0057 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0057) M ↔
      ∃ c ∈ template0057, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0057) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0057))
    cores template0057 witness0057 coverage0057
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0057) (maskBits m)) cores template0057 witness0057
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0057))
      coverage0057 catalogue_core_nodup coverageSize0057) (by rfl) M

theorem minimal_mask_iff0058 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0058) M ↔
      ∃ c ∈ template0058, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0058) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0058))
    cores template0058 witness0058 coverage0058
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0058) (maskBits m)) cores template0058 witness0058
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0058))
      coverage0058 catalogue_core_nodup coverageSize0058) (by rfl) M

theorem minimal_mask_iff0059 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0059) M ↔
      ∃ c ∈ template0059, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0059) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0059))
    cores template0059 witness0059 coverage0059
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0059) (maskBits m)) cores template0059 witness0059
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0059))
      coverage0059 catalogue_core_nodup coverageSize0059) (by rfl) M

theorem minimal_mask_iff0060 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0060) M ↔
      ∃ c ∈ template0060, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0060) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0060))
    cores template0060 witness0060 coverage0060
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0060) (maskBits m)) cores template0060 witness0060
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0060))
      coverage0060 catalogue_core_nodup coverageSize0060) (by rfl) M

theorem minimal_mask_iff0061 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0061) M ↔
      ∃ c ∈ template0061, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0061) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0061))
    cores template0061 witness0061 coverage0061
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0061) (maskBits m)) cores template0061 witness0061
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0061))
      coverage0061 catalogue_core_nodup coverageSize0061) (by rfl) M

theorem minimal_mask_iff0062 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0062) M ↔
      ∃ c ∈ template0062, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0062) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0062))
    cores template0062 witness0062 coverage0062
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0062) (maskBits m)) cores template0062 witness0062
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0062))
      coverage0062 catalogue_core_nodup coverageSize0062) (by rfl) M

theorem minimal_mask_iff0063 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0063) M ↔
      ∃ c ∈ template0063, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0063) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0063))
    cores template0063 witness0063 coverage0063
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0063) (maskBits m)) cores template0063 witness0063
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0063))
      coverage0063 catalogue_core_nodup coverageSize0063) (by rfl) M

theorem minimal_mask_iff0064 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0064) M ↔
      ∃ c ∈ template0064, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0064) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0064))
    cores template0064 witness0064 coverage0064
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0064) (maskBits m)) cores template0064 witness0064
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0064))
      coverage0064 catalogue_core_nodup coverageSize0064) (by rfl) M

theorem minimal_mask_iff0065 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0065) M ↔
      ∃ c ∈ template0065, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0065) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0065))
    cores template0065 witness0065 coverage0065
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0065) (maskBits m)) cores template0065 witness0065
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0065))
      coverage0065 catalogue_core_nodup coverageSize0065) (by rfl) M

theorem minimal_mask_iff0066 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0066) M ↔
      ∃ c ∈ template0066, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0066) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0066))
    cores template0066 witness0066 coverage0066
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0066) (maskBits m)) cores template0066 witness0066
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0066))
      coverage0066 catalogue_core_nodup coverageSize0066) (by rfl) M

theorem minimal_mask_iff0067 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0067) M ↔
      ∃ c ∈ template0067, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0067) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0067))
    cores template0067 witness0067 coverage0067
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0067) (maskBits m)) cores template0067 witness0067
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0067))
      coverage0067 catalogue_core_nodup coverageSize0067) (by rfl) M

theorem minimal_mask_iff0068 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0068) M ↔
      ∃ c ∈ template0068, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0068) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0068))
    cores template0068 witness0068 coverage0068
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0068) (maskBits m)) cores template0068 witness0068
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0068))
      coverage0068 catalogue_core_nodup coverageSize0068) (by rfl) M

theorem minimal_mask_iff0069 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0069) M ↔
      ∃ c ∈ template0069, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0069) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0069))
    cores template0069 witness0069 coverage0069
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0069) (maskBits m)) cores template0069 witness0069
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0069))
      coverage0069 catalogue_core_nodup coverageSize0069) (by rfl) M

theorem minimal_mask_iff0070 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0070) M ↔
      ∃ c ∈ template0070, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0070) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0070))
    cores template0070 witness0070 coverage0070
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0070) (maskBits m)) cores template0070 witness0070
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0070))
      coverage0070 catalogue_core_nodup coverageSize0070) (by rfl) M

theorem minimal_mask_iff0071 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0071) M ↔
      ∃ c ∈ template0071, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0071) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0071))
    cores template0071 witness0071 coverage0071
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0071) (maskBits m)) cores template0071 witness0071
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0071))
      coverage0071 catalogue_core_nodup coverageSize0071) (by rfl) M

theorem minimal_mask_iff0072 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0072) M ↔
      ∃ c ∈ template0072, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0072) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0072))
    cores template0072 witness0072 coverage0072
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0072) (maskBits m)) cores template0072 witness0072
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0072))
      coverage0072 catalogue_core_nodup coverageSize0072) (by rfl) M

theorem minimal_mask_iff0073 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0073) M ↔
      ∃ c ∈ template0073, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0073) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0073))
    cores template0073 witness0073 coverage0073
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0073) (maskBits m)) cores template0073 witness0073
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0073))
      coverage0073 catalogue_core_nodup coverageSize0073) (by rfl) M

theorem minimal_mask_iff0074 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0074) M ↔
      ∃ c ∈ template0074, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0074) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0074))
    cores template0074 witness0074 coverage0074
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0074) (maskBits m)) cores template0074 witness0074
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0074))
      coverage0074 catalogue_core_nodup coverageSize0074) (by rfl) M

theorem minimal_mask_iff0075 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0075) M ↔
      ∃ c ∈ template0075, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0075) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0075))
    cores template0075 witness0075 coverage0075
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0075) (maskBits m)) cores template0075 witness0075
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0075))
      coverage0075 catalogue_core_nodup coverageSize0075) (by rfl) M

theorem minimal_mask_iff0076 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0076) M ↔
      ∃ c ∈ template0076, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0076) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0076))
    cores template0076 witness0076 coverage0076
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0076) (maskBits m)) cores template0076 witness0076
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0076))
      coverage0076 catalogue_core_nodup coverageSize0076) (by rfl) M

theorem minimal_mask_iff0077 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0077) M ↔
      ∃ c ∈ template0077, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0077) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0077))
    cores template0077 witness0077 coverage0077
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0077) (maskBits m)) cores template0077 witness0077
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0077))
      coverage0077 catalogue_core_nodup coverageSize0077) (by rfl) M

theorem minimal_mask_iff0078 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0078) M ↔
      ∃ c ∈ template0078, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0078) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0078))
    cores template0078 witness0078 coverage0078
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0078) (maskBits m)) cores template0078 witness0078
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0078))
      coverage0078 catalogue_core_nodup coverageSize0078) (by rfl) M

theorem minimal_mask_iff0079 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0079) M ↔
      ∃ c ∈ template0079, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0079) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0079))
    cores template0079 witness0079 coverage0079
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0079) (maskBits m)) cores template0079 witness0079
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0079))
      coverage0079 catalogue_core_nodup coverageSize0079) (by rfl) M

#print axioms minimal_mask_iff0040
#print axioms minimal_mask_iff0079
end Crown.CertificateData
