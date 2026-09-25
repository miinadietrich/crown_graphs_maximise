import generated.CatalogueBatch0006
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0005

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0200 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0200) M ↔
      ∃ c ∈ template0200, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0200) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0200))
    cores template0200 witness0200 coverage0200
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0200) (maskBits m)) cores template0200 witness0200
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0200))
      coverage0200 catalogue_core_nodup coverageSize0200) (by rfl) M

theorem minimal_mask_iff0201 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0201) M ↔
      ∃ c ∈ template0201, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0201) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0201))
    cores template0201 witness0201 coverage0201
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0201) (maskBits m)) cores template0201 witness0201
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0201))
      coverage0201 catalogue_core_nodup coverageSize0201) (by rfl) M

theorem minimal_mask_iff0202 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0202) M ↔
      ∃ c ∈ template0202, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0202) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0202))
    cores template0202 witness0202 coverage0202
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0202) (maskBits m)) cores template0202 witness0202
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0202))
      coverage0202 catalogue_core_nodup coverageSize0202) (by rfl) M

theorem minimal_mask_iff0203 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0203) M ↔
      ∃ c ∈ template0203, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0203) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0203))
    cores template0203 witness0203 coverage0203
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0203) (maskBits m)) cores template0203 witness0203
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0203))
      coverage0203 catalogue_core_nodup coverageSize0203) (by rfl) M

theorem minimal_mask_iff0204 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0204) M ↔
      ∃ c ∈ template0204, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0204) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0204))
    cores template0204 witness0204 coverage0204
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0204) (maskBits m)) cores template0204 witness0204
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0204))
      coverage0204 catalogue_core_nodup coverageSize0204) (by rfl) M

theorem minimal_mask_iff0205 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0205) M ↔
      ∃ c ∈ template0205, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0205) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0205))
    cores template0205 witness0205 coverage0205
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0205) (maskBits m)) cores template0205 witness0205
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0205))
      coverage0205 catalogue_core_nodup coverageSize0205) (by rfl) M

theorem minimal_mask_iff0206 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0206) M ↔
      ∃ c ∈ template0206, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0206) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0206))
    cores template0206 witness0206 coverage0206
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0206) (maskBits m)) cores template0206 witness0206
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0206))
      coverage0206 catalogue_core_nodup coverageSize0206) (by rfl) M

theorem minimal_mask_iff0207 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0207) M ↔
      ∃ c ∈ template0207, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0207) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0207))
    cores template0207 witness0207 coverage0207
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0207) (maskBits m)) cores template0207 witness0207
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0207))
      coverage0207 catalogue_core_nodup coverageSize0207) (by rfl) M

theorem minimal_mask_iff0208 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0208) M ↔
      ∃ c ∈ template0208, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0208) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0208))
    cores template0208 witness0208 coverage0208
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0208) (maskBits m)) cores template0208 witness0208
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0208))
      coverage0208 catalogue_core_nodup coverageSize0208) (by rfl) M

theorem minimal_mask_iff0209 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0209) M ↔
      ∃ c ∈ template0209, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0209) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0209))
    cores template0209 witness0209 coverage0209
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0209) (maskBits m)) cores template0209 witness0209
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0209))
      coverage0209 catalogue_core_nodup coverageSize0209) (by rfl) M

theorem minimal_mask_iff0210 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0210) M ↔
      ∃ c ∈ template0210, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0210) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0210))
    cores template0210 witness0210 coverage0210
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0210) (maskBits m)) cores template0210 witness0210
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0210))
      coverage0210 catalogue_core_nodup coverageSize0210) (by rfl) M

theorem minimal_mask_iff0211 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0211) M ↔
      ∃ c ∈ template0211, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0211) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0211))
    cores template0211 witness0211 coverage0211
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0211) (maskBits m)) cores template0211 witness0211
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0211))
      coverage0211 catalogue_core_nodup coverageSize0211) (by rfl) M

theorem minimal_mask_iff0212 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0212) M ↔
      ∃ c ∈ template0212, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0212) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0212))
    cores template0212 witness0212 coverage0212
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0212) (maskBits m)) cores template0212 witness0212
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0212))
      coverage0212 catalogue_core_nodup coverageSize0212) (by rfl) M

theorem minimal_mask_iff0213 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0213) M ↔
      ∃ c ∈ template0213, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0213) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0213))
    cores template0213 witness0213 coverage0213
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0213) (maskBits m)) cores template0213 witness0213
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0213))
      coverage0213 catalogue_core_nodup coverageSize0213) (by rfl) M

theorem minimal_mask_iff0214 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0214) M ↔
      ∃ c ∈ template0214, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0214) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0214))
    cores template0214 witness0214 coverage0214
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0214) (maskBits m)) cores template0214 witness0214
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0214))
      coverage0214 catalogue_core_nodup coverageSize0214) (by rfl) M

theorem minimal_mask_iff0215 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0215) M ↔
      ∃ c ∈ template0215, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0215) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0215))
    cores template0215 witness0215 coverage0215
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0215) (maskBits m)) cores template0215 witness0215
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0215))
      coverage0215 catalogue_core_nodup coverageSize0215) (by rfl) M

theorem minimal_mask_iff0216 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0216) M ↔
      ∃ c ∈ template0216, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0216) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0216))
    cores template0216 witness0216 coverage0216
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0216) (maskBits m)) cores template0216 witness0216
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0216))
      coverage0216 catalogue_core_nodup coverageSize0216) (by rfl) M

theorem minimal_mask_iff0217 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0217) M ↔
      ∃ c ∈ template0217, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0217) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0217))
    cores template0217 witness0217 coverage0217
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0217) (maskBits m)) cores template0217 witness0217
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0217))
      coverage0217 catalogue_core_nodup coverageSize0217) (by rfl) M

theorem minimal_mask_iff0218 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0218) M ↔
      ∃ c ∈ template0218, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0218) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0218))
    cores template0218 witness0218 coverage0218
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0218) (maskBits m)) cores template0218 witness0218
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0218))
      coverage0218 catalogue_core_nodup coverageSize0218) (by rfl) M

theorem minimal_mask_iff0219 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0219) M ↔
      ∃ c ∈ template0219, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0219) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0219))
    cores template0219 witness0219 coverage0219
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0219) (maskBits m)) cores template0219 witness0219
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0219))
      coverage0219 catalogue_core_nodup coverageSize0219) (by rfl) M

theorem minimal_mask_iff0220 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0220) M ↔
      ∃ c ∈ template0220, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0220) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0220))
    cores template0220 witness0220 coverage0220
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0220) (maskBits m)) cores template0220 witness0220
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0220))
      coverage0220 catalogue_core_nodup coverageSize0220) (by rfl) M

theorem minimal_mask_iff0221 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0221) M ↔
      ∃ c ∈ template0221, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0221) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0221))
    cores template0221 witness0221 coverage0221
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0221) (maskBits m)) cores template0221 witness0221
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0221))
      coverage0221 catalogue_core_nodup coverageSize0221) (by rfl) M

theorem minimal_mask_iff0222 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0222) M ↔
      ∃ c ∈ template0222, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0222) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0222))
    cores template0222 witness0222 coverage0222
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0222) (maskBits m)) cores template0222 witness0222
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0222))
      coverage0222 catalogue_core_nodup coverageSize0222) (by rfl) M

theorem minimal_mask_iff0223 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0223) M ↔
      ∃ c ∈ template0223, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0223) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0223))
    cores template0223 witness0223 coverage0223
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0223) (maskBits m)) cores template0223 witness0223
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0223))
      coverage0223 catalogue_core_nodup coverageSize0223) (by rfl) M

theorem minimal_mask_iff0224 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0224) M ↔
      ∃ c ∈ template0224, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0224) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0224))
    cores template0224 witness0224 coverage0224
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0224) (maskBits m)) cores template0224 witness0224
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0224))
      coverage0224 catalogue_core_nodup coverageSize0224) (by rfl) M

theorem minimal_mask_iff0225 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0225) M ↔
      ∃ c ∈ template0225, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0225) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0225))
    cores template0225 witness0225 coverage0225
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0225) (maskBits m)) cores template0225 witness0225
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0225))
      coverage0225 catalogue_core_nodup coverageSize0225) (by rfl) M

theorem minimal_mask_iff0226 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0226) M ↔
      ∃ c ∈ template0226, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0226) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0226))
    cores template0226 witness0226 coverage0226
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0226) (maskBits m)) cores template0226 witness0226
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0226))
      coverage0226 catalogue_core_nodup coverageSize0226) (by rfl) M

theorem minimal_mask_iff0227 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0227) M ↔
      ∃ c ∈ template0227, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0227) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0227))
    cores template0227 witness0227 coverage0227
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0227) (maskBits m)) cores template0227 witness0227
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0227))
      coverage0227 catalogue_core_nodup coverageSize0227) (by rfl) M

theorem minimal_mask_iff0228 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0228) M ↔
      ∃ c ∈ template0228, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0228) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0228))
    cores template0228 witness0228 coverage0228
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0228) (maskBits m)) cores template0228 witness0228
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0228))
      coverage0228 catalogue_core_nodup coverageSize0228) (by rfl) M

theorem minimal_mask_iff0229 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0229) M ↔
      ∃ c ∈ template0229, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0229) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0229))
    cores template0229 witness0229 coverage0229
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0229) (maskBits m)) cores template0229 witness0229
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0229))
      coverage0229 catalogue_core_nodup coverageSize0229) (by rfl) M

theorem minimal_mask_iff0230 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0230) M ↔
      ∃ c ∈ template0230, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0230) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0230))
    cores template0230 witness0230 coverage0230
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0230) (maskBits m)) cores template0230 witness0230
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0230))
      coverage0230 catalogue_core_nodup coverageSize0230) (by rfl) M

theorem minimal_mask_iff0231 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0231) M ↔
      ∃ c ∈ template0231, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0231) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0231))
    cores template0231 witness0231 coverage0231
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0231) (maskBits m)) cores template0231 witness0231
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0231))
      coverage0231 catalogue_core_nodup coverageSize0231) (by rfl) M

theorem minimal_mask_iff0232 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0232) M ↔
      ∃ c ∈ template0232, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0232) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0232))
    cores template0232 witness0232 coverage0232
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0232) (maskBits m)) cores template0232 witness0232
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0232))
      coverage0232 catalogue_core_nodup coverageSize0232) (by rfl) M

theorem minimal_mask_iff0233 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0233) M ↔
      ∃ c ∈ template0233, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0233) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0233))
    cores template0233 witness0233 coverage0233
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0233) (maskBits m)) cores template0233 witness0233
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0233))
      coverage0233 catalogue_core_nodup coverageSize0233) (by rfl) M

theorem minimal_mask_iff0234 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0234) M ↔
      ∃ c ∈ template0234, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0234) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0234))
    cores template0234 witness0234 coverage0234
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0234) (maskBits m)) cores template0234 witness0234
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0234))
      coverage0234 catalogue_core_nodup coverageSize0234) (by rfl) M

theorem minimal_mask_iff0235 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0235) M ↔
      ∃ c ∈ template0235, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0235) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0235))
    cores template0235 witness0235 coverage0235
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0235) (maskBits m)) cores template0235 witness0235
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0235))
      coverage0235 catalogue_core_nodup coverageSize0235) (by rfl) M

theorem minimal_mask_iff0236 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0236) M ↔
      ∃ c ∈ template0236, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0236) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0236))
    cores template0236 witness0236 coverage0236
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0236) (maskBits m)) cores template0236 witness0236
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0236))
      coverage0236 catalogue_core_nodup coverageSize0236) (by rfl) M

theorem minimal_mask_iff0237 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0237) M ↔
      ∃ c ∈ template0237, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0237) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0237))
    cores template0237 witness0237 coverage0237
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0237) (maskBits m)) cores template0237 witness0237
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0237))
      coverage0237 catalogue_core_nodup coverageSize0237) (by rfl) M

theorem minimal_mask_iff0238 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0238) M ↔
      ∃ c ∈ template0238, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0238) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0238))
    cores template0238 witness0238 coverage0238
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0238) (maskBits m)) cores template0238 witness0238
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0238))
      coverage0238 catalogue_core_nodup coverageSize0238) (by rfl) M

theorem minimal_mask_iff0239 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0239) M ↔
      ∃ c ∈ template0239, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0239) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0239))
    cores template0239 witness0239 coverage0239
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0239) (maskBits m)) cores template0239 witness0239
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0239))
      coverage0239 catalogue_core_nodup coverageSize0239) (by rfl) M

#print axioms minimal_mask_iff0200
#print axioms minimal_mask_iff0239
end Crown.CertificateData
