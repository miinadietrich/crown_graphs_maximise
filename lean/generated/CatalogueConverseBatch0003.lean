import generated.CatalogueBatch0003
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0002

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0080 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0080) M ↔
      ∃ c ∈ template0080, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0080) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0080))
    cores template0080 witness0080 coverage0080
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0080) (maskBits m)) cores template0080 witness0080
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0080))
      coverage0080 catalogue_core_nodup coverageSize0080) (by rfl) M

theorem minimal_mask_iff0081 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0081) M ↔
      ∃ c ∈ template0081, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0081) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0081))
    cores template0081 witness0081 coverage0081
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0081) (maskBits m)) cores template0081 witness0081
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0081))
      coverage0081 catalogue_core_nodup coverageSize0081) (by rfl) M

theorem minimal_mask_iff0082 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0082) M ↔
      ∃ c ∈ template0082, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0082) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0082))
    cores template0082 witness0082 coverage0082
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0082) (maskBits m)) cores template0082 witness0082
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0082))
      coverage0082 catalogue_core_nodup coverageSize0082) (by rfl) M

theorem minimal_mask_iff0083 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0083) M ↔
      ∃ c ∈ template0083, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0083) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0083))
    cores template0083 witness0083 coverage0083
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0083) (maskBits m)) cores template0083 witness0083
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0083))
      coverage0083 catalogue_core_nodup coverageSize0083) (by rfl) M

theorem minimal_mask_iff0084 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0084) M ↔
      ∃ c ∈ template0084, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0084) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0084))
    cores template0084 witness0084 coverage0084
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0084) (maskBits m)) cores template0084 witness0084
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0084))
      coverage0084 catalogue_core_nodup coverageSize0084) (by rfl) M

theorem minimal_mask_iff0085 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0085) M ↔
      ∃ c ∈ template0085, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0085) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0085))
    cores template0085 witness0085 coverage0085
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0085) (maskBits m)) cores template0085 witness0085
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0085))
      coverage0085 catalogue_core_nodup coverageSize0085) (by rfl) M

theorem minimal_mask_iff0086 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0086) M ↔
      ∃ c ∈ template0086, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0086) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0086))
    cores template0086 witness0086 coverage0086
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0086) (maskBits m)) cores template0086 witness0086
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0086))
      coverage0086 catalogue_core_nodup coverageSize0086) (by rfl) M

theorem minimal_mask_iff0087 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0087) M ↔
      ∃ c ∈ template0087, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0087) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0087))
    cores template0087 witness0087 coverage0087
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0087) (maskBits m)) cores template0087 witness0087
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0087))
      coverage0087 catalogue_core_nodup coverageSize0087) (by rfl) M

theorem minimal_mask_iff0088 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0088) M ↔
      ∃ c ∈ template0088, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0088) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0088))
    cores template0088 witness0088 coverage0088
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0088) (maskBits m)) cores template0088 witness0088
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0088))
      coverage0088 catalogue_core_nodup coverageSize0088) (by rfl) M

theorem minimal_mask_iff0089 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0089) M ↔
      ∃ c ∈ template0089, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0089) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0089))
    cores template0089 witness0089 coverage0089
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0089) (maskBits m)) cores template0089 witness0089
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0089))
      coverage0089 catalogue_core_nodup coverageSize0089) (by rfl) M

theorem minimal_mask_iff0090 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0090) M ↔
      ∃ c ∈ template0090, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0090) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0090))
    cores template0090 witness0090 coverage0090
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0090) (maskBits m)) cores template0090 witness0090
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0090))
      coverage0090 catalogue_core_nodup coverageSize0090) (by rfl) M

theorem minimal_mask_iff0091 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0091) M ↔
      ∃ c ∈ template0091, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0091) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0091))
    cores template0091 witness0091 coverage0091
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0091) (maskBits m)) cores template0091 witness0091
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0091))
      coverage0091 catalogue_core_nodup coverageSize0091) (by rfl) M

theorem minimal_mask_iff0092 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0092) M ↔
      ∃ c ∈ template0092, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0092) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0092))
    cores template0092 witness0092 coverage0092
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0092) (maskBits m)) cores template0092 witness0092
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0092))
      coverage0092 catalogue_core_nodup coverageSize0092) (by rfl) M

theorem minimal_mask_iff0093 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0093) M ↔
      ∃ c ∈ template0093, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0093) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0093))
    cores template0093 witness0093 coverage0093
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0093) (maskBits m)) cores template0093 witness0093
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0093))
      coverage0093 catalogue_core_nodup coverageSize0093) (by rfl) M

theorem minimal_mask_iff0094 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0094) M ↔
      ∃ c ∈ template0094, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0094) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0094))
    cores template0094 witness0094 coverage0094
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0094) (maskBits m)) cores template0094 witness0094
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0094))
      coverage0094 catalogue_core_nodup coverageSize0094) (by rfl) M

theorem minimal_mask_iff0095 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0095) M ↔
      ∃ c ∈ template0095, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0095) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0095))
    cores template0095 witness0095 coverage0095
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0095) (maskBits m)) cores template0095 witness0095
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0095))
      coverage0095 catalogue_core_nodup coverageSize0095) (by rfl) M

theorem minimal_mask_iff0096 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0096) M ↔
      ∃ c ∈ template0096, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0096) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0096))
    cores template0096 witness0096 coverage0096
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0096) (maskBits m)) cores template0096 witness0096
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0096))
      coverage0096 catalogue_core_nodup coverageSize0096) (by rfl) M

theorem minimal_mask_iff0097 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0097) M ↔
      ∃ c ∈ template0097, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0097) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0097))
    cores template0097 witness0097 coverage0097
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0097) (maskBits m)) cores template0097 witness0097
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0097))
      coverage0097 catalogue_core_nodup coverageSize0097) (by rfl) M

theorem minimal_mask_iff0098 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0098) M ↔
      ∃ c ∈ template0098, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0098) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0098))
    cores template0098 witness0098 coverage0098
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0098) (maskBits m)) cores template0098 witness0098
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0098))
      coverage0098 catalogue_core_nodup coverageSize0098) (by rfl) M

theorem minimal_mask_iff0099 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0099) M ↔
      ∃ c ∈ template0099, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0099) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0099))
    cores template0099 witness0099 coverage0099
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0099) (maskBits m)) cores template0099 witness0099
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0099))
      coverage0099 catalogue_core_nodup coverageSize0099) (by rfl) M

theorem minimal_mask_iff0100 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0100) M ↔
      ∃ c ∈ template0100, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0100) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0100))
    cores template0100 witness0100 coverage0100
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0100) (maskBits m)) cores template0100 witness0100
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0100))
      coverage0100 catalogue_core_nodup coverageSize0100) (by rfl) M

theorem minimal_mask_iff0101 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0101) M ↔
      ∃ c ∈ template0101, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0101) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0101))
    cores template0101 witness0101 coverage0101
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0101) (maskBits m)) cores template0101 witness0101
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0101))
      coverage0101 catalogue_core_nodup coverageSize0101) (by rfl) M

theorem minimal_mask_iff0102 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0102) M ↔
      ∃ c ∈ template0102, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0102) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0102))
    cores template0102 witness0102 coverage0102
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0102) (maskBits m)) cores template0102 witness0102
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0102))
      coverage0102 catalogue_core_nodup coverageSize0102) (by rfl) M

theorem minimal_mask_iff0103 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0103) M ↔
      ∃ c ∈ template0103, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0103) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0103))
    cores template0103 witness0103 coverage0103
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0103) (maskBits m)) cores template0103 witness0103
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0103))
      coverage0103 catalogue_core_nodup coverageSize0103) (by rfl) M

theorem minimal_mask_iff0104 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0104) M ↔
      ∃ c ∈ template0104, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0104) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0104))
    cores template0104 witness0104 coverage0104
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0104) (maskBits m)) cores template0104 witness0104
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0104))
      coverage0104 catalogue_core_nodup coverageSize0104) (by rfl) M

theorem minimal_mask_iff0105 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0105) M ↔
      ∃ c ∈ template0105, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0105) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0105))
    cores template0105 witness0105 coverage0105
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0105) (maskBits m)) cores template0105 witness0105
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0105))
      coverage0105 catalogue_core_nodup coverageSize0105) (by rfl) M

theorem minimal_mask_iff0106 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0106) M ↔
      ∃ c ∈ template0106, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0106) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0106))
    cores template0106 witness0106 coverage0106
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0106) (maskBits m)) cores template0106 witness0106
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0106))
      coverage0106 catalogue_core_nodup coverageSize0106) (by rfl) M

theorem minimal_mask_iff0107 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0107) M ↔
      ∃ c ∈ template0107, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0107) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0107))
    cores template0107 witness0107 coverage0107
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0107) (maskBits m)) cores template0107 witness0107
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0107))
      coverage0107 catalogue_core_nodup coverageSize0107) (by rfl) M

theorem minimal_mask_iff0108 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0108) M ↔
      ∃ c ∈ template0108, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0108) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0108))
    cores template0108 witness0108 coverage0108
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0108) (maskBits m)) cores template0108 witness0108
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0108))
      coverage0108 catalogue_core_nodup coverageSize0108) (by rfl) M

theorem minimal_mask_iff0109 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0109) M ↔
      ∃ c ∈ template0109, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0109) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0109))
    cores template0109 witness0109 coverage0109
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0109) (maskBits m)) cores template0109 witness0109
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0109))
      coverage0109 catalogue_core_nodup coverageSize0109) (by rfl) M

theorem minimal_mask_iff0110 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0110) M ↔
      ∃ c ∈ template0110, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0110) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0110))
    cores template0110 witness0110 coverage0110
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0110) (maskBits m)) cores template0110 witness0110
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0110))
      coverage0110 catalogue_core_nodup coverageSize0110) (by rfl) M

theorem minimal_mask_iff0111 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0111) M ↔
      ∃ c ∈ template0111, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0111) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0111))
    cores template0111 witness0111 coverage0111
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0111) (maskBits m)) cores template0111 witness0111
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0111))
      coverage0111 catalogue_core_nodup coverageSize0111) (by rfl) M

theorem minimal_mask_iff0112 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0112) M ↔
      ∃ c ∈ template0112, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0112) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0112))
    cores template0112 witness0112 coverage0112
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0112) (maskBits m)) cores template0112 witness0112
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0112))
      coverage0112 catalogue_core_nodup coverageSize0112) (by rfl) M

theorem minimal_mask_iff0113 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0113) M ↔
      ∃ c ∈ template0113, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0113) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0113))
    cores template0113 witness0113 coverage0113
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0113) (maskBits m)) cores template0113 witness0113
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0113))
      coverage0113 catalogue_core_nodup coverageSize0113) (by rfl) M

theorem minimal_mask_iff0114 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0114) M ↔
      ∃ c ∈ template0114, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0114) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0114))
    cores template0114 witness0114 coverage0114
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0114) (maskBits m)) cores template0114 witness0114
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0114))
      coverage0114 catalogue_core_nodup coverageSize0114) (by rfl) M

theorem minimal_mask_iff0115 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0115) M ↔
      ∃ c ∈ template0115, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0115) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0115))
    cores template0115 witness0115 coverage0115
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0115) (maskBits m)) cores template0115 witness0115
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0115))
      coverage0115 catalogue_core_nodup coverageSize0115) (by rfl) M

theorem minimal_mask_iff0116 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0116) M ↔
      ∃ c ∈ template0116, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0116) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0116))
    cores template0116 witness0116 coverage0116
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0116) (maskBits m)) cores template0116 witness0116
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0116))
      coverage0116 catalogue_core_nodup coverageSize0116) (by rfl) M

theorem minimal_mask_iff0117 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0117) M ↔
      ∃ c ∈ template0117, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0117) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0117))
    cores template0117 witness0117 coverage0117
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0117) (maskBits m)) cores template0117 witness0117
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0117))
      coverage0117 catalogue_core_nodup coverageSize0117) (by rfl) M

theorem minimal_mask_iff0118 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0118) M ↔
      ∃ c ∈ template0118, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0118) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0118))
    cores template0118 witness0118 coverage0118
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0118) (maskBits m)) cores template0118 witness0118
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0118))
      coverage0118 catalogue_core_nodup coverageSize0118) (by rfl) M

theorem minimal_mask_iff0119 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0119) M ↔
      ∃ c ∈ template0119, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0119) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0119))
    cores template0119 witness0119 coverage0119
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0119) (maskBits m)) cores template0119 witness0119
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0119))
      coverage0119 catalogue_core_nodup coverageSize0119) (by rfl) M

#print axioms minimal_mask_iff0080
#print axioms minimal_mask_iff0119
end Crown.CertificateData
