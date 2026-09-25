import generated.CatalogueBatch0001
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0000 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0000) M ↔
      ∃ c ∈ template0000, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0000) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0000))
    cores template0000 witness0000 coverage0000
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0000) (maskBits m)) cores template0000 witness0000
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0000))
      coverage0000 catalogue_core_nodup coverageSize0000) (by rfl) M

theorem minimal_mask_iff0001 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0001) M ↔
      ∃ c ∈ template0001, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0001) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0001))
    cores template0001 witness0001 coverage0001
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0001) (maskBits m)) cores template0001 witness0001
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0001))
      coverage0001 catalogue_core_nodup coverageSize0001) (by rfl) M

theorem minimal_mask_iff0002 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0002) M ↔
      ∃ c ∈ template0002, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0002) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0002))
    cores template0002 witness0002 coverage0002
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0002) (maskBits m)) cores template0002 witness0002
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0002))
      coverage0002 catalogue_core_nodup coverageSize0002) (by rfl) M

theorem minimal_mask_iff0003 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0003) M ↔
      ∃ c ∈ template0003, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0003) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0003))
    cores template0003 witness0003 coverage0003
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0003) (maskBits m)) cores template0003 witness0003
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0003))
      coverage0003 catalogue_core_nodup coverageSize0003) (by rfl) M

theorem minimal_mask_iff0004 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0004) M ↔
      ∃ c ∈ template0004, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0004) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0004))
    cores template0004 witness0004 coverage0004
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0004) (maskBits m)) cores template0004 witness0004
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0004))
      coverage0004 catalogue_core_nodup coverageSize0004) (by rfl) M

theorem minimal_mask_iff0005 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0005) M ↔
      ∃ c ∈ template0005, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0005) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0005))
    cores template0005 witness0005 coverage0005
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0005) (maskBits m)) cores template0005 witness0005
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0005))
      coverage0005 catalogue_core_nodup coverageSize0005) (by rfl) M

theorem minimal_mask_iff0006 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0006) M ↔
      ∃ c ∈ template0006, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0006) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0006))
    cores template0006 witness0006 coverage0006
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0006) (maskBits m)) cores template0006 witness0006
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0006))
      coverage0006 catalogue_core_nodup coverageSize0006) (by rfl) M

theorem minimal_mask_iff0007 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0007) M ↔
      ∃ c ∈ template0007, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0007) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0007))
    cores template0007 witness0007 coverage0007
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0007) (maskBits m)) cores template0007 witness0007
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0007))
      coverage0007 catalogue_core_nodup coverageSize0007) (by rfl) M

theorem minimal_mask_iff0008 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0008) M ↔
      ∃ c ∈ template0008, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0008) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0008))
    cores template0008 witness0008 coverage0008
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0008) (maskBits m)) cores template0008 witness0008
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0008))
      coverage0008 catalogue_core_nodup coverageSize0008) (by rfl) M

theorem minimal_mask_iff0009 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0009) M ↔
      ∃ c ∈ template0009, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0009) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0009))
    cores template0009 witness0009 coverage0009
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0009) (maskBits m)) cores template0009 witness0009
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0009))
      coverage0009 catalogue_core_nodup coverageSize0009) (by rfl) M

theorem minimal_mask_iff0010 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0010) M ↔
      ∃ c ∈ template0010, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0010) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0010))
    cores template0010 witness0010 coverage0010
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0010) (maskBits m)) cores template0010 witness0010
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0010))
      coverage0010 catalogue_core_nodup coverageSize0010) (by rfl) M

theorem minimal_mask_iff0011 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0011) M ↔
      ∃ c ∈ template0011, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0011) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0011))
    cores template0011 witness0011 coverage0011
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0011) (maskBits m)) cores template0011 witness0011
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0011))
      coverage0011 catalogue_core_nodup coverageSize0011) (by rfl) M

theorem minimal_mask_iff0012 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0012) M ↔
      ∃ c ∈ template0012, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0012) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0012))
    cores template0012 witness0012 coverage0012
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0012) (maskBits m)) cores template0012 witness0012
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0012))
      coverage0012 catalogue_core_nodup coverageSize0012) (by rfl) M

theorem minimal_mask_iff0013 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0013) M ↔
      ∃ c ∈ template0013, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0013) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0013))
    cores template0013 witness0013 coverage0013
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0013) (maskBits m)) cores template0013 witness0013
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0013))
      coverage0013 catalogue_core_nodup coverageSize0013) (by rfl) M

theorem minimal_mask_iff0014 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0014) M ↔
      ∃ c ∈ template0014, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0014) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0014))
    cores template0014 witness0014 coverage0014
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0014) (maskBits m)) cores template0014 witness0014
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0014))
      coverage0014 catalogue_core_nodup coverageSize0014) (by rfl) M

theorem minimal_mask_iff0015 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0015) M ↔
      ∃ c ∈ template0015, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0015) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0015))
    cores template0015 witness0015 coverage0015
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0015) (maskBits m)) cores template0015 witness0015
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0015))
      coverage0015 catalogue_core_nodup coverageSize0015) (by rfl) M

theorem minimal_mask_iff0016 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0016) M ↔
      ∃ c ∈ template0016, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0016) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0016))
    cores template0016 witness0016 coverage0016
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0016) (maskBits m)) cores template0016 witness0016
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0016))
      coverage0016 catalogue_core_nodup coverageSize0016) (by rfl) M

theorem minimal_mask_iff0017 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0017) M ↔
      ∃ c ∈ template0017, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0017) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0017))
    cores template0017 witness0017 coverage0017
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0017) (maskBits m)) cores template0017 witness0017
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0017))
      coverage0017 catalogue_core_nodup coverageSize0017) (by rfl) M

theorem minimal_mask_iff0018 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0018) M ↔
      ∃ c ∈ template0018, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0018) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0018))
    cores template0018 witness0018 coverage0018
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0018) (maskBits m)) cores template0018 witness0018
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0018))
      coverage0018 catalogue_core_nodup coverageSize0018) (by rfl) M

theorem minimal_mask_iff0019 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0019) M ↔
      ∃ c ∈ template0019, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0019) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0019))
    cores template0019 witness0019 coverage0019
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0019) (maskBits m)) cores template0019 witness0019
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0019))
      coverage0019 catalogue_core_nodup coverageSize0019) (by rfl) M

theorem minimal_mask_iff0020 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0020) M ↔
      ∃ c ∈ template0020, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0020) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0020))
    cores template0020 witness0020 coverage0020
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0020) (maskBits m)) cores template0020 witness0020
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0020))
      coverage0020 catalogue_core_nodup coverageSize0020) (by rfl) M

theorem minimal_mask_iff0021 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0021) M ↔
      ∃ c ∈ template0021, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0021) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0021))
    cores template0021 witness0021 coverage0021
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0021) (maskBits m)) cores template0021 witness0021
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0021))
      coverage0021 catalogue_core_nodup coverageSize0021) (by rfl) M

theorem minimal_mask_iff0022 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0022) M ↔
      ∃ c ∈ template0022, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0022) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0022))
    cores template0022 witness0022 coverage0022
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0022) (maskBits m)) cores template0022 witness0022
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0022))
      coverage0022 catalogue_core_nodup coverageSize0022) (by rfl) M

theorem minimal_mask_iff0023 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0023) M ↔
      ∃ c ∈ template0023, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0023) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0023))
    cores template0023 witness0023 coverage0023
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0023) (maskBits m)) cores template0023 witness0023
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0023))
      coverage0023 catalogue_core_nodup coverageSize0023) (by rfl) M

theorem minimal_mask_iff0024 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0024) M ↔
      ∃ c ∈ template0024, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0024) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0024))
    cores template0024 witness0024 coverage0024
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0024) (maskBits m)) cores template0024 witness0024
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0024))
      coverage0024 catalogue_core_nodup coverageSize0024) (by rfl) M

theorem minimal_mask_iff0025 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0025) M ↔
      ∃ c ∈ template0025, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0025) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0025))
    cores template0025 witness0025 coverage0025
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0025) (maskBits m)) cores template0025 witness0025
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0025))
      coverage0025 catalogue_core_nodup coverageSize0025) (by rfl) M

theorem minimal_mask_iff0026 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0026) M ↔
      ∃ c ∈ template0026, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0026) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0026))
    cores template0026 witness0026 coverage0026
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0026) (maskBits m)) cores template0026 witness0026
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0026))
      coverage0026 catalogue_core_nodup coverageSize0026) (by rfl) M

theorem minimal_mask_iff0027 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0027) M ↔
      ∃ c ∈ template0027, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0027) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0027))
    cores template0027 witness0027 coverage0027
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0027) (maskBits m)) cores template0027 witness0027
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0027))
      coverage0027 catalogue_core_nodup coverageSize0027) (by rfl) M

theorem minimal_mask_iff0028 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0028) M ↔
      ∃ c ∈ template0028, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0028) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0028))
    cores template0028 witness0028 coverage0028
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0028) (maskBits m)) cores template0028 witness0028
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0028))
      coverage0028 catalogue_core_nodup coverageSize0028) (by rfl) M

theorem minimal_mask_iff0029 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0029) M ↔
      ∃ c ∈ template0029, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0029) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0029))
    cores template0029 witness0029 coverage0029
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0029) (maskBits m)) cores template0029 witness0029
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0029))
      coverage0029 catalogue_core_nodup coverageSize0029) (by rfl) M

theorem minimal_mask_iff0030 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0030) M ↔
      ∃ c ∈ template0030, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0030) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0030))
    cores template0030 witness0030 coverage0030
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0030) (maskBits m)) cores template0030 witness0030
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0030))
      coverage0030 catalogue_core_nodup coverageSize0030) (by rfl) M

theorem minimal_mask_iff0031 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0031) M ↔
      ∃ c ∈ template0031, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0031) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0031))
    cores template0031 witness0031 coverage0031
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0031) (maskBits m)) cores template0031 witness0031
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0031))
      coverage0031 catalogue_core_nodup coverageSize0031) (by rfl) M

theorem minimal_mask_iff0032 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0032) M ↔
      ∃ c ∈ template0032, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0032) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0032))
    cores template0032 witness0032 coverage0032
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0032) (maskBits m)) cores template0032 witness0032
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0032))
      coverage0032 catalogue_core_nodup coverageSize0032) (by rfl) M

theorem minimal_mask_iff0033 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0033) M ↔
      ∃ c ∈ template0033, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0033) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0033))
    cores template0033 witness0033 coverage0033
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0033) (maskBits m)) cores template0033 witness0033
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0033))
      coverage0033 catalogue_core_nodup coverageSize0033) (by rfl) M

theorem minimal_mask_iff0034 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0034) M ↔
      ∃ c ∈ template0034, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0034) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0034))
    cores template0034 witness0034 coverage0034
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0034) (maskBits m)) cores template0034 witness0034
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0034))
      coverage0034 catalogue_core_nodup coverageSize0034) (by rfl) M

theorem minimal_mask_iff0035 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0035) M ↔
      ∃ c ∈ template0035, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0035) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0035))
    cores template0035 witness0035 coverage0035
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0035) (maskBits m)) cores template0035 witness0035
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0035))
      coverage0035 catalogue_core_nodup coverageSize0035) (by rfl) M

theorem minimal_mask_iff0036 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0036) M ↔
      ∃ c ∈ template0036, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0036) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0036))
    cores template0036 witness0036 coverage0036
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0036) (maskBits m)) cores template0036 witness0036
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0036))
      coverage0036 catalogue_core_nodup coverageSize0036) (by rfl) M

theorem minimal_mask_iff0037 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0037) M ↔
      ∃ c ∈ template0037, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0037) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0037))
    cores template0037 witness0037 coverage0037
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0037) (maskBits m)) cores template0037 witness0037
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0037))
      coverage0037 catalogue_core_nodup coverageSize0037) (by rfl) M

theorem minimal_mask_iff0038 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0038) M ↔
      ∃ c ∈ template0038, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0038) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0038))
    cores template0038 witness0038 coverage0038
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0038) (maskBits m)) cores template0038 witness0038
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0038))
      coverage0038 catalogue_core_nodup coverageSize0038) (by rfl) M

theorem minimal_mask_iff0039 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0039) M ↔
      ∃ c ∈ template0039, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0039) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0039))
    cores template0039 witness0039 coverage0039
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0039) (maskBits m)) cores template0039 witness0039
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0039))
      coverage0039 catalogue_core_nodup coverageSize0039) (by rfl) M

#print axioms minimal_mask_iff0000
#print axioms minimal_mask_iff0039
end Crown.CertificateData
