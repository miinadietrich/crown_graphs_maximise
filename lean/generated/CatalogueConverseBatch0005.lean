import generated.CatalogueBatch0005
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0004

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0160 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0160) M ↔
      ∃ c ∈ template0160, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0160) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0160))
    cores template0160 witness0160 coverage0160
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0160) (maskBits m)) cores template0160 witness0160
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0160))
      coverage0160 catalogue_core_nodup coverageSize0160) (by rfl) M

theorem minimal_mask_iff0161 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0161) M ↔
      ∃ c ∈ template0161, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0161) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0161))
    cores template0161 witness0161 coverage0161
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0161) (maskBits m)) cores template0161 witness0161
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0161))
      coverage0161 catalogue_core_nodup coverageSize0161) (by rfl) M

theorem minimal_mask_iff0162 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0162) M ↔
      ∃ c ∈ template0162, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0162) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0162))
    cores template0162 witness0162 coverage0162
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0162) (maskBits m)) cores template0162 witness0162
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0162))
      coverage0162 catalogue_core_nodup coverageSize0162) (by rfl) M

theorem minimal_mask_iff0163 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0163) M ↔
      ∃ c ∈ template0163, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0163) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0163))
    cores template0163 witness0163 coverage0163
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0163) (maskBits m)) cores template0163 witness0163
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0163))
      coverage0163 catalogue_core_nodup coverageSize0163) (by rfl) M

theorem minimal_mask_iff0164 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0164) M ↔
      ∃ c ∈ template0164, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0164) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0164))
    cores template0164 witness0164 coverage0164
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0164) (maskBits m)) cores template0164 witness0164
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0164))
      coverage0164 catalogue_core_nodup coverageSize0164) (by rfl) M

theorem minimal_mask_iff0165 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0165) M ↔
      ∃ c ∈ template0165, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0165) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0165))
    cores template0165 witness0165 coverage0165
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0165) (maskBits m)) cores template0165 witness0165
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0165))
      coverage0165 catalogue_core_nodup coverageSize0165) (by rfl) M

theorem minimal_mask_iff0166 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0166) M ↔
      ∃ c ∈ template0166, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0166) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0166))
    cores template0166 witness0166 coverage0166
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0166) (maskBits m)) cores template0166 witness0166
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0166))
      coverage0166 catalogue_core_nodup coverageSize0166) (by rfl) M

theorem minimal_mask_iff0167 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0167) M ↔
      ∃ c ∈ template0167, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0167) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0167))
    cores template0167 witness0167 coverage0167
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0167) (maskBits m)) cores template0167 witness0167
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0167))
      coverage0167 catalogue_core_nodup coverageSize0167) (by rfl) M

theorem minimal_mask_iff0168 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0168) M ↔
      ∃ c ∈ template0168, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0168) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0168))
    cores template0168 witness0168 coverage0168
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0168) (maskBits m)) cores template0168 witness0168
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0168))
      coverage0168 catalogue_core_nodup coverageSize0168) (by rfl) M

theorem minimal_mask_iff0169 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0169) M ↔
      ∃ c ∈ template0169, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0169) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0169))
    cores template0169 witness0169 coverage0169
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0169) (maskBits m)) cores template0169 witness0169
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0169))
      coverage0169 catalogue_core_nodup coverageSize0169) (by rfl) M

theorem minimal_mask_iff0170 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0170) M ↔
      ∃ c ∈ template0170, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0170) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0170))
    cores template0170 witness0170 coverage0170
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0170) (maskBits m)) cores template0170 witness0170
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0170))
      coverage0170 catalogue_core_nodup coverageSize0170) (by rfl) M

theorem minimal_mask_iff0171 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0171) M ↔
      ∃ c ∈ template0171, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0171) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0171))
    cores template0171 witness0171 coverage0171
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0171) (maskBits m)) cores template0171 witness0171
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0171))
      coverage0171 catalogue_core_nodup coverageSize0171) (by rfl) M

theorem minimal_mask_iff0172 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0172) M ↔
      ∃ c ∈ template0172, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0172) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0172))
    cores template0172 witness0172 coverage0172
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0172) (maskBits m)) cores template0172 witness0172
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0172))
      coverage0172 catalogue_core_nodup coverageSize0172) (by rfl) M

theorem minimal_mask_iff0173 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0173) M ↔
      ∃ c ∈ template0173, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0173) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0173))
    cores template0173 witness0173 coverage0173
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0173) (maskBits m)) cores template0173 witness0173
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0173))
      coverage0173 catalogue_core_nodup coverageSize0173) (by rfl) M

theorem minimal_mask_iff0174 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0174) M ↔
      ∃ c ∈ template0174, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0174) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0174))
    cores template0174 witness0174 coverage0174
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0174) (maskBits m)) cores template0174 witness0174
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0174))
      coverage0174 catalogue_core_nodup coverageSize0174) (by rfl) M

theorem minimal_mask_iff0175 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0175) M ↔
      ∃ c ∈ template0175, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0175) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0175))
    cores template0175 witness0175 coverage0175
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0175) (maskBits m)) cores template0175 witness0175
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0175))
      coverage0175 catalogue_core_nodup coverageSize0175) (by rfl) M

theorem minimal_mask_iff0176 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0176) M ↔
      ∃ c ∈ template0176, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0176) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0176))
    cores template0176 witness0176 coverage0176
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0176) (maskBits m)) cores template0176 witness0176
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0176))
      coverage0176 catalogue_core_nodup coverageSize0176) (by rfl) M

theorem minimal_mask_iff0177 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0177) M ↔
      ∃ c ∈ template0177, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0177) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0177))
    cores template0177 witness0177 coverage0177
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0177) (maskBits m)) cores template0177 witness0177
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0177))
      coverage0177 catalogue_core_nodup coverageSize0177) (by rfl) M

theorem minimal_mask_iff0178 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0178) M ↔
      ∃ c ∈ template0178, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0178) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0178))
    cores template0178 witness0178 coverage0178
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0178) (maskBits m)) cores template0178 witness0178
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0178))
      coverage0178 catalogue_core_nodup coverageSize0178) (by rfl) M

theorem minimal_mask_iff0179 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0179) M ↔
      ∃ c ∈ template0179, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0179) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0179))
    cores template0179 witness0179 coverage0179
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0179) (maskBits m)) cores template0179 witness0179
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0179))
      coverage0179 catalogue_core_nodup coverageSize0179) (by rfl) M

theorem minimal_mask_iff0180 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0180) M ↔
      ∃ c ∈ template0180, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0180) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0180))
    cores template0180 witness0180 coverage0180
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0180) (maskBits m)) cores template0180 witness0180
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0180))
      coverage0180 catalogue_core_nodup coverageSize0180) (by rfl) M

theorem minimal_mask_iff0181 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0181) M ↔
      ∃ c ∈ template0181, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0181) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0181))
    cores template0181 witness0181 coverage0181
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0181) (maskBits m)) cores template0181 witness0181
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0181))
      coverage0181 catalogue_core_nodup coverageSize0181) (by rfl) M

theorem minimal_mask_iff0182 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0182) M ↔
      ∃ c ∈ template0182, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0182) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0182))
    cores template0182 witness0182 coverage0182
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0182) (maskBits m)) cores template0182 witness0182
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0182))
      coverage0182 catalogue_core_nodup coverageSize0182) (by rfl) M

theorem minimal_mask_iff0183 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0183) M ↔
      ∃ c ∈ template0183, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0183) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0183))
    cores template0183 witness0183 coverage0183
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0183) (maskBits m)) cores template0183 witness0183
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0183))
      coverage0183 catalogue_core_nodup coverageSize0183) (by rfl) M

theorem minimal_mask_iff0184 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0184) M ↔
      ∃ c ∈ template0184, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0184) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0184))
    cores template0184 witness0184 coverage0184
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0184) (maskBits m)) cores template0184 witness0184
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0184))
      coverage0184 catalogue_core_nodup coverageSize0184) (by rfl) M

theorem minimal_mask_iff0185 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0185) M ↔
      ∃ c ∈ template0185, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0185) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0185))
    cores template0185 witness0185 coverage0185
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0185) (maskBits m)) cores template0185 witness0185
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0185))
      coverage0185 catalogue_core_nodup coverageSize0185) (by rfl) M

theorem minimal_mask_iff0186 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0186) M ↔
      ∃ c ∈ template0186, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0186) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0186))
    cores template0186 witness0186 coverage0186
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0186) (maskBits m)) cores template0186 witness0186
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0186))
      coverage0186 catalogue_core_nodup coverageSize0186) (by rfl) M

theorem minimal_mask_iff0187 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0187) M ↔
      ∃ c ∈ template0187, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0187) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0187))
    cores template0187 witness0187 coverage0187
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0187) (maskBits m)) cores template0187 witness0187
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0187))
      coverage0187 catalogue_core_nodup coverageSize0187) (by rfl) M

theorem minimal_mask_iff0188 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0188) M ↔
      ∃ c ∈ template0188, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0188) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0188))
    cores template0188 witness0188 coverage0188
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0188) (maskBits m)) cores template0188 witness0188
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0188))
      coverage0188 catalogue_core_nodup coverageSize0188) (by rfl) M

theorem minimal_mask_iff0189 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0189) M ↔
      ∃ c ∈ template0189, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0189) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0189))
    cores template0189 witness0189 coverage0189
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0189) (maskBits m)) cores template0189 witness0189
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0189))
      coverage0189 catalogue_core_nodup coverageSize0189) (by rfl) M

theorem minimal_mask_iff0190 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0190) M ↔
      ∃ c ∈ template0190, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0190) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0190))
    cores template0190 witness0190 coverage0190
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0190) (maskBits m)) cores template0190 witness0190
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0190))
      coverage0190 catalogue_core_nodup coverageSize0190) (by rfl) M

theorem minimal_mask_iff0191 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0191) M ↔
      ∃ c ∈ template0191, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0191) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0191))
    cores template0191 witness0191 coverage0191
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0191) (maskBits m)) cores template0191 witness0191
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0191))
      coverage0191 catalogue_core_nodup coverageSize0191) (by rfl) M

theorem minimal_mask_iff0192 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0192) M ↔
      ∃ c ∈ template0192, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0192) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0192))
    cores template0192 witness0192 coverage0192
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0192) (maskBits m)) cores template0192 witness0192
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0192))
      coverage0192 catalogue_core_nodup coverageSize0192) (by rfl) M

theorem minimal_mask_iff0193 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0193) M ↔
      ∃ c ∈ template0193, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0193) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0193))
    cores template0193 witness0193 coverage0193
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0193) (maskBits m)) cores template0193 witness0193
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0193))
      coverage0193 catalogue_core_nodup coverageSize0193) (by rfl) M

theorem minimal_mask_iff0194 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0194) M ↔
      ∃ c ∈ template0194, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0194) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0194))
    cores template0194 witness0194 coverage0194
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0194) (maskBits m)) cores template0194 witness0194
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0194))
      coverage0194 catalogue_core_nodup coverageSize0194) (by rfl) M

theorem minimal_mask_iff0195 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0195) M ↔
      ∃ c ∈ template0195, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0195) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0195))
    cores template0195 witness0195 coverage0195
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0195) (maskBits m)) cores template0195 witness0195
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0195))
      coverage0195 catalogue_core_nodup coverageSize0195) (by rfl) M

theorem minimal_mask_iff0196 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0196) M ↔
      ∃ c ∈ template0196, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0196) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0196))
    cores template0196 witness0196 coverage0196
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0196) (maskBits m)) cores template0196 witness0196
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0196))
      coverage0196 catalogue_core_nodup coverageSize0196) (by rfl) M

theorem minimal_mask_iff0197 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0197) M ↔
      ∃ c ∈ template0197, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0197) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0197))
    cores template0197 witness0197 coverage0197
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0197) (maskBits m)) cores template0197 witness0197
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0197))
      coverage0197 catalogue_core_nodup coverageSize0197) (by rfl) M

theorem minimal_mask_iff0198 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0198) M ↔
      ∃ c ∈ template0198, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0198) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0198))
    cores template0198 witness0198 coverage0198
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0198) (maskBits m)) cores template0198 witness0198
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0198))
      coverage0198 catalogue_core_nodup coverageSize0198) (by rfl) M

theorem minimal_mask_iff0199 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0199) M ↔
      ∃ c ∈ template0199, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0199) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0199))
    cores template0199 witness0199 coverage0199
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0199) (maskBits m)) cores template0199 witness0199
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0199))
      coverage0199 catalogue_core_nodup coverageSize0199) (by rfl) M

#print axioms minimal_mask_iff0160
#print axioms minimal_mask_iff0199
end Crown.CertificateData
