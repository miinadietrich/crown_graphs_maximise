import generated.CatalogueBatch0004
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0003

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0120 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0120) M ↔
      ∃ c ∈ template0120, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0120) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0120))
    cores template0120 witness0120 coverage0120
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0120) (maskBits m)) cores template0120 witness0120
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0120))
      coverage0120 catalogue_core_nodup coverageSize0120) (by rfl) M

theorem minimal_mask_iff0121 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0121) M ↔
      ∃ c ∈ template0121, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0121) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0121))
    cores template0121 witness0121 coverage0121
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0121) (maskBits m)) cores template0121 witness0121
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0121))
      coverage0121 catalogue_core_nodup coverageSize0121) (by rfl) M

theorem minimal_mask_iff0122 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0122) M ↔
      ∃ c ∈ template0122, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0122) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0122))
    cores template0122 witness0122 coverage0122
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0122) (maskBits m)) cores template0122 witness0122
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0122))
      coverage0122 catalogue_core_nodup coverageSize0122) (by rfl) M

theorem minimal_mask_iff0123 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0123) M ↔
      ∃ c ∈ template0123, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0123) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0123))
    cores template0123 witness0123 coverage0123
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0123) (maskBits m)) cores template0123 witness0123
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0123))
      coverage0123 catalogue_core_nodup coverageSize0123) (by rfl) M

theorem minimal_mask_iff0124 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0124) M ↔
      ∃ c ∈ template0124, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0124) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0124))
    cores template0124 witness0124 coverage0124
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0124) (maskBits m)) cores template0124 witness0124
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0124))
      coverage0124 catalogue_core_nodup coverageSize0124) (by rfl) M

theorem minimal_mask_iff0125 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0125) M ↔
      ∃ c ∈ template0125, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0125) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0125))
    cores template0125 witness0125 coverage0125
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0125) (maskBits m)) cores template0125 witness0125
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0125))
      coverage0125 catalogue_core_nodup coverageSize0125) (by rfl) M

theorem minimal_mask_iff0126 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0126) M ↔
      ∃ c ∈ template0126, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0126) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0126))
    cores template0126 witness0126 coverage0126
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0126) (maskBits m)) cores template0126 witness0126
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0126))
      coverage0126 catalogue_core_nodup coverageSize0126) (by rfl) M

theorem minimal_mask_iff0127 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0127) M ↔
      ∃ c ∈ template0127, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0127) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0127))
    cores template0127 witness0127 coverage0127
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0127) (maskBits m)) cores template0127 witness0127
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0127))
      coverage0127 catalogue_core_nodup coverageSize0127) (by rfl) M

theorem minimal_mask_iff0128 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0128) M ↔
      ∃ c ∈ template0128, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0128) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0128))
    cores template0128 witness0128 coverage0128
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0128) (maskBits m)) cores template0128 witness0128
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0128))
      coverage0128 catalogue_core_nodup coverageSize0128) (by rfl) M

theorem minimal_mask_iff0129 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0129) M ↔
      ∃ c ∈ template0129, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0129) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0129))
    cores template0129 witness0129 coverage0129
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0129) (maskBits m)) cores template0129 witness0129
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0129))
      coverage0129 catalogue_core_nodup coverageSize0129) (by rfl) M

theorem minimal_mask_iff0130 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0130) M ↔
      ∃ c ∈ template0130, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0130) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0130))
    cores template0130 witness0130 coverage0130
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0130) (maskBits m)) cores template0130 witness0130
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0130))
      coverage0130 catalogue_core_nodup coverageSize0130) (by rfl) M

theorem minimal_mask_iff0131 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0131) M ↔
      ∃ c ∈ template0131, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0131) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0131))
    cores template0131 witness0131 coverage0131
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0131) (maskBits m)) cores template0131 witness0131
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0131))
      coverage0131 catalogue_core_nodup coverageSize0131) (by rfl) M

theorem minimal_mask_iff0132 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0132) M ↔
      ∃ c ∈ template0132, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0132) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0132))
    cores template0132 witness0132 coverage0132
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0132) (maskBits m)) cores template0132 witness0132
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0132))
      coverage0132 catalogue_core_nodup coverageSize0132) (by rfl) M

theorem minimal_mask_iff0133 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0133) M ↔
      ∃ c ∈ template0133, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0133) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0133))
    cores template0133 witness0133 coverage0133
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0133) (maskBits m)) cores template0133 witness0133
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0133))
      coverage0133 catalogue_core_nodup coverageSize0133) (by rfl) M

theorem minimal_mask_iff0134 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0134) M ↔
      ∃ c ∈ template0134, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0134) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0134))
    cores template0134 witness0134 coverage0134
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0134) (maskBits m)) cores template0134 witness0134
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0134))
      coverage0134 catalogue_core_nodup coverageSize0134) (by rfl) M

theorem minimal_mask_iff0135 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0135) M ↔
      ∃ c ∈ template0135, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0135) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0135))
    cores template0135 witness0135 coverage0135
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0135) (maskBits m)) cores template0135 witness0135
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0135))
      coverage0135 catalogue_core_nodup coverageSize0135) (by rfl) M

theorem minimal_mask_iff0136 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0136) M ↔
      ∃ c ∈ template0136, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0136) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0136))
    cores template0136 witness0136 coverage0136
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0136) (maskBits m)) cores template0136 witness0136
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0136))
      coverage0136 catalogue_core_nodup coverageSize0136) (by rfl) M

theorem minimal_mask_iff0137 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0137) M ↔
      ∃ c ∈ template0137, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0137) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0137))
    cores template0137 witness0137 coverage0137
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0137) (maskBits m)) cores template0137 witness0137
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0137))
      coverage0137 catalogue_core_nodup coverageSize0137) (by rfl) M

theorem minimal_mask_iff0138 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0138) M ↔
      ∃ c ∈ template0138, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0138) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0138))
    cores template0138 witness0138 coverage0138
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0138) (maskBits m)) cores template0138 witness0138
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0138))
      coverage0138 catalogue_core_nodup coverageSize0138) (by rfl) M

theorem minimal_mask_iff0139 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0139) M ↔
      ∃ c ∈ template0139, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0139) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0139))
    cores template0139 witness0139 coverage0139
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0139) (maskBits m)) cores template0139 witness0139
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0139))
      coverage0139 catalogue_core_nodup coverageSize0139) (by rfl) M

theorem minimal_mask_iff0140 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0140) M ↔
      ∃ c ∈ template0140, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0140) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0140))
    cores template0140 witness0140 coverage0140
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0140) (maskBits m)) cores template0140 witness0140
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0140))
      coverage0140 catalogue_core_nodup coverageSize0140) (by rfl) M

theorem minimal_mask_iff0141 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0141) M ↔
      ∃ c ∈ template0141, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0141) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0141))
    cores template0141 witness0141 coverage0141
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0141) (maskBits m)) cores template0141 witness0141
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0141))
      coverage0141 catalogue_core_nodup coverageSize0141) (by rfl) M

theorem minimal_mask_iff0142 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0142) M ↔
      ∃ c ∈ template0142, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0142) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0142))
    cores template0142 witness0142 coverage0142
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0142) (maskBits m)) cores template0142 witness0142
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0142))
      coverage0142 catalogue_core_nodup coverageSize0142) (by rfl) M

theorem minimal_mask_iff0143 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0143) M ↔
      ∃ c ∈ template0143, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0143) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0143))
    cores template0143 witness0143 coverage0143
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0143) (maskBits m)) cores template0143 witness0143
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0143))
      coverage0143 catalogue_core_nodup coverageSize0143) (by rfl) M

theorem minimal_mask_iff0144 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0144) M ↔
      ∃ c ∈ template0144, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0144) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0144))
    cores template0144 witness0144 coverage0144
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0144) (maskBits m)) cores template0144 witness0144
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0144))
      coverage0144 catalogue_core_nodup coverageSize0144) (by rfl) M

theorem minimal_mask_iff0145 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0145) M ↔
      ∃ c ∈ template0145, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0145) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0145))
    cores template0145 witness0145 coverage0145
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0145) (maskBits m)) cores template0145 witness0145
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0145))
      coverage0145 catalogue_core_nodup coverageSize0145) (by rfl) M

theorem minimal_mask_iff0146 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0146) M ↔
      ∃ c ∈ template0146, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0146) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0146))
    cores template0146 witness0146 coverage0146
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0146) (maskBits m)) cores template0146 witness0146
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0146))
      coverage0146 catalogue_core_nodup coverageSize0146) (by rfl) M

theorem minimal_mask_iff0147 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0147) M ↔
      ∃ c ∈ template0147, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0147) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0147))
    cores template0147 witness0147 coverage0147
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0147) (maskBits m)) cores template0147 witness0147
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0147))
      coverage0147 catalogue_core_nodup coverageSize0147) (by rfl) M

theorem minimal_mask_iff0148 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0148) M ↔
      ∃ c ∈ template0148, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0148) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0148))
    cores template0148 witness0148 coverage0148
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0148) (maskBits m)) cores template0148 witness0148
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0148))
      coverage0148 catalogue_core_nodup coverageSize0148) (by rfl) M

theorem minimal_mask_iff0149 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0149) M ↔
      ∃ c ∈ template0149, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0149) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0149))
    cores template0149 witness0149 coverage0149
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0149) (maskBits m)) cores template0149 witness0149
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0149))
      coverage0149 catalogue_core_nodup coverageSize0149) (by rfl) M

theorem minimal_mask_iff0150 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0150) M ↔
      ∃ c ∈ template0150, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0150) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0150))
    cores template0150 witness0150 coverage0150
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0150) (maskBits m)) cores template0150 witness0150
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0150))
      coverage0150 catalogue_core_nodup coverageSize0150) (by rfl) M

theorem minimal_mask_iff0151 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0151) M ↔
      ∃ c ∈ template0151, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0151) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0151))
    cores template0151 witness0151 coverage0151
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0151) (maskBits m)) cores template0151 witness0151
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0151))
      coverage0151 catalogue_core_nodup coverageSize0151) (by rfl) M

theorem minimal_mask_iff0152 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0152) M ↔
      ∃ c ∈ template0152, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0152) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0152))
    cores template0152 witness0152 coverage0152
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0152) (maskBits m)) cores template0152 witness0152
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0152))
      coverage0152 catalogue_core_nodup coverageSize0152) (by rfl) M

theorem minimal_mask_iff0153 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0153) M ↔
      ∃ c ∈ template0153, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0153) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0153))
    cores template0153 witness0153 coverage0153
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0153) (maskBits m)) cores template0153 witness0153
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0153))
      coverage0153 catalogue_core_nodup coverageSize0153) (by rfl) M

theorem minimal_mask_iff0154 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0154) M ↔
      ∃ c ∈ template0154, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0154) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0154))
    cores template0154 witness0154 coverage0154
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0154) (maskBits m)) cores template0154 witness0154
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0154))
      coverage0154 catalogue_core_nodup coverageSize0154) (by rfl) M

theorem minimal_mask_iff0155 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0155) M ↔
      ∃ c ∈ template0155, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0155) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0155))
    cores template0155 witness0155 coverage0155
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0155) (maskBits m)) cores template0155 witness0155
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0155))
      coverage0155 catalogue_core_nodup coverageSize0155) (by rfl) M

theorem minimal_mask_iff0156 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0156) M ↔
      ∃ c ∈ template0156, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0156) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0156))
    cores template0156 witness0156 coverage0156
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0156) (maskBits m)) cores template0156 witness0156
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0156))
      coverage0156 catalogue_core_nodup coverageSize0156) (by rfl) M

theorem minimal_mask_iff0157 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0157) M ↔
      ∃ c ∈ template0157, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0157) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0157))
    cores template0157 witness0157 coverage0157
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0157) (maskBits m)) cores template0157 witness0157
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0157))
      coverage0157 catalogue_core_nodup coverageSize0157) (by rfl) M

theorem minimal_mask_iff0158 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0158) M ↔
      ∃ c ∈ template0158, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0158) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0158))
    cores template0158 witness0158 coverage0158
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0158) (maskBits m)) cores template0158 witness0158
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0158))
      coverage0158 catalogue_core_nodup coverageSize0158) (by rfl) M

theorem minimal_mask_iff0159 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0159) M ↔
      ∃ c ∈ template0159, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0159) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0159))
    cores template0159 witness0159 coverage0159
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0159) (maskBits m)) cores template0159 witness0159
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0159))
      coverage0159 catalogue_core_nodup coverageSize0159) (by rfl) M

#print axioms minimal_mask_iff0120
#print axioms minimal_mask_iff0159
end Crown.CertificateData
