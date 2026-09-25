import generated.CatalogueBatch0010
import generated.CatalogueStatistics
import Crown.CertificateCatalogueReversal
import generated.CatalogueConverseBatch0009

namespace Crown.CertificateData
open Crown.CertificateSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem minimal_mask_iff0360 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0360) M ↔
      ∃ c ∈ template0360, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0360) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0360))
    cores template0360 witness0360 coverage0360
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0360) (maskBits m)) cores template0360 witness0360
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0360))
      coverage0360 catalogue_core_nodup coverageSize0360) (by rfl) M

theorem minimal_mask_iff0361 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0361) M ↔
      ∃ c ∈ template0361, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0361) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0361))
    cores template0361 witness0361 coverage0361
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0361) (maskBits m)) cores template0361 witness0361
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0361))
      coverage0361 catalogue_core_nodup coverageSize0361) (by rfl) M

theorem minimal_mask_iff0362 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0362) M ↔
      ∃ c ∈ template0362, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0362) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0362))
    cores template0362 witness0362 coverage0362
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0362) (maskBits m)) cores template0362 witness0362
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0362))
      coverage0362 catalogue_core_nodup coverageSize0362) (by rfl) M

theorem minimal_mask_iff0363 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0363) M ↔
      ∃ c ∈ template0363, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0363) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0363))
    cores template0363 witness0363 coverage0363
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0363) (maskBits m)) cores template0363 witness0363
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0363))
      coverage0363 catalogue_core_nodup coverageSize0363) (by rfl) M

theorem minimal_mask_iff0364 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0364) M ↔
      ∃ c ∈ template0364, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0364) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0364))
    cores template0364 witness0364 coverage0364
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0364) (maskBits m)) cores template0364 witness0364
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0364))
      coverage0364 catalogue_core_nodup coverageSize0364) (by rfl) M

theorem minimal_mask_iff0365 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0365) M ↔
      ∃ c ∈ template0365, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0365) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0365))
    cores template0365 witness0365 coverage0365
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0365) (maskBits m)) cores template0365 witness0365
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0365))
      coverage0365 catalogue_core_nodup coverageSize0365) (by rfl) M

theorem minimal_mask_iff0366 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0366) M ↔
      ∃ c ∈ template0366, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0366) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0366))
    cores template0366 witness0366 coverage0366
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0366) (maskBits m)) cores template0366 witness0366
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0366))
      coverage0366 catalogue_core_nodup coverageSize0366) (by rfl) M

theorem minimal_mask_iff0367 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0367) M ↔
      ∃ c ∈ template0367, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0367) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0367))
    cores template0367 witness0367 coverage0367
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0367) (maskBits m)) cores template0367 witness0367
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0367))
      coverage0367 catalogue_core_nodup coverageSize0367) (by rfl) M

theorem minimal_mask_iff0368 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0368) M ↔
      ∃ c ∈ template0368, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0368) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0368))
    cores template0368 witness0368 coverage0368
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0368) (maskBits m)) cores template0368 witness0368
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0368))
      coverage0368 catalogue_core_nodup coverageSize0368) (by rfl) M

theorem minimal_mask_iff0369 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0369) M ↔
      ∃ c ∈ template0369, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0369) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0369))
    cores template0369 witness0369 coverage0369
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0369) (maskBits m)) cores template0369 witness0369
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0369))
      coverage0369 catalogue_core_nodup coverageSize0369) (by rfl) M

theorem minimal_mask_iff0370 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0370) M ↔
      ∃ c ∈ template0370, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0370) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0370))
    cores template0370 witness0370 coverage0370
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0370) (maskBits m)) cores template0370 witness0370
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0370))
      coverage0370 catalogue_core_nodup coverageSize0370) (by rfl) M

theorem minimal_mask_iff0371 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0371) M ↔
      ∃ c ∈ template0371, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0371) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0371))
    cores template0371 witness0371 coverage0371
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0371) (maskBits m)) cores template0371 witness0371
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0371))
      coverage0371 catalogue_core_nodup coverageSize0371) (by rfl) M

theorem minimal_mask_iff0372 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0372) M ↔
      ∃ c ∈ template0372, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0372) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0372))
    cores template0372 witness0372 coverage0372
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0372) (maskBits m)) cores template0372 witness0372
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0372))
      coverage0372 catalogue_core_nodup coverageSize0372) (by rfl) M

theorem minimal_mask_iff0373 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0373) M ↔
      ∃ c ∈ template0373, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0373) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0373))
    cores template0373 witness0373 coverage0373
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0373) (maskBits m)) cores template0373 witness0373
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0373))
      coverage0373 catalogue_core_nodup coverageSize0373) (by rfl) M

theorem minimal_mask_iff0374 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0374) M ↔
      ∃ c ∈ template0374, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0374) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0374))
    cores template0374 witness0374 coverage0374
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0374) (maskBits m)) cores template0374 witness0374
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0374))
      coverage0374 catalogue_core_nodup coverageSize0374) (by rfl) M

theorem minimal_mask_iff0375 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0375) M ↔
      ∃ c ∈ template0375, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0375) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0375))
    cores template0375 witness0375 coverage0375
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0375) (maskBits m)) cores template0375 witness0375
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0375))
      coverage0375 catalogue_core_nodup coverageSize0375) (by rfl) M

theorem minimal_mask_iff0376 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0376) M ↔
      ∃ c ∈ template0376, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0376) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0376))
    cores template0376 witness0376 coverage0376
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0376) (maskBits m)) cores template0376 witness0376
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0376))
      coverage0376 catalogue_core_nodup coverageSize0376) (by rfl) M

theorem minimal_mask_iff0377 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0377) M ↔
      ∃ c ∈ template0377, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0377) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0377))
    cores template0377 witness0377 coverage0377
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0377) (maskBits m)) cores template0377 witness0377
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0377))
      coverage0377 catalogue_core_nodup coverageSize0377) (by rfl) M

theorem minimal_mask_iff0378 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0378) M ↔
      ∃ c ∈ template0378, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0378) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0378))
    cores template0378 witness0378 coverage0378
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0378) (maskBits m)) cores template0378 witness0378
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0378))
      coverage0378 catalogue_core_nodup coverageSize0378) (by rfl) M

theorem minimal_mask_iff0379 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0379) M ↔
      ∃ c ∈ template0379, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0379) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0379))
    cores template0379 witness0379 coverage0379
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0379) (maskBits m)) cores template0379 witness0379
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0379))
      coverage0379 catalogue_core_nodup coverageSize0379) (by rfl) M

theorem minimal_mask_iff0380 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0380) M ↔
      ∃ c ∈ template0380, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0380) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0380))
    cores template0380 witness0380 coverage0380
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0380) (maskBits m)) cores template0380 witness0380
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0380))
      coverage0380 catalogue_core_nodup coverageSize0380) (by rfl) M

theorem minimal_mask_iff0381 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0381) M ↔
      ∃ c ∈ template0381, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0381) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0381))
    cores template0381 witness0381 coverage0381
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0381) (maskBits m)) cores template0381 witness0381
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0381))
      coverage0381 catalogue_core_nodup coverageSize0381) (by rfl) M

theorem minimal_mask_iff0382 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0382) M ↔
      ∃ c ∈ template0382, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0382) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0382))
    cores template0382 witness0382 coverage0382
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0382) (maskBits m)) cores template0382 witness0382
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0382))
      coverage0382 catalogue_core_nodup coverageSize0382) (by rfl) M

theorem minimal_mask_iff0383 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0383) M ↔
      ∃ c ∈ template0383, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0383) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0383))
    cores template0383 witness0383 coverage0383
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0383) (maskBits m)) cores template0383 witness0383
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0383))
      coverage0383 catalogue_core_nodup coverageSize0383) (by rfl) M

theorem minimal_mask_iff0384 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0384) M ↔
      ∃ c ∈ template0384, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0384) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0384))
    cores template0384 witness0384 coverage0384
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0384) (maskBits m)) cores template0384 witness0384
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0384))
      coverage0384 catalogue_core_nodup coverageSize0384) (by rfl) M

theorem minimal_mask_iff0385 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0385) M ↔
      ∃ c ∈ template0385, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0385) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0385))
    cores template0385 witness0385 coverage0385
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0385) (maskBits m)) cores template0385 witness0385
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0385))
      coverage0385 catalogue_core_nodup coverageSize0385) (by rfl) M

theorem minimal_mask_iff0386 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0386) M ↔
      ∃ c ∈ template0386, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0386) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0386))
    cores template0386 witness0386 coverage0386
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0386) (maskBits m)) cores template0386 witness0386
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0386))
      coverage0386 catalogue_core_nodup coverageSize0386) (by rfl) M

theorem minimal_mask_iff0387 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0387) M ↔
      ∃ c ∈ template0387, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0387) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0387))
    cores template0387 witness0387 coverage0387
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0387) (maskBits m)) cores template0387 witness0387
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0387))
      coverage0387 catalogue_core_nodup coverageSize0387) (by rfl) M

theorem minimal_mask_iff0388 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0388) M ↔
      ∃ c ∈ template0388, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0388) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0388))
    cores template0388 witness0388 coverage0388
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0388) (maskBits m)) cores template0388 witness0388
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0388))
      coverage0388 catalogue_core_nodup coverageSize0388) (by rfl) M

theorem minimal_mask_iff0389 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0389) M ↔
      ∃ c ∈ template0389, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0389) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0389))
    cores template0389 witness0389 coverage0389
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0389) (maskBits m)) cores template0389 witness0389
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0389))
      coverage0389 catalogue_core_nodup coverageSize0389) (by rfl) M

theorem minimal_mask_iff0390 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0390) M ↔
      ∃ c ∈ template0390, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0390) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0390))
    cores template0390 witness0390 coverage0390
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0390) (maskBits m)) cores template0390 witness0390
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0390))
      coverage0390 catalogue_core_nodup coverageSize0390) (by rfl) M

theorem minimal_mask_iff0391 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0391) M ↔
      ∃ c ∈ template0391, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0391) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0391))
    cores template0391 witness0391 coverage0391
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0391) (maskBits m)) cores template0391 witness0391
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0391))
      coverage0391 catalogue_core_nodup coverageSize0391) (by rfl) M

theorem minimal_mask_iff0392 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0392) M ↔
      ∃ c ∈ template0392, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0392) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0392))
    cores template0392 witness0392 coverage0392
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0392) (maskBits m)) cores template0392 witness0392
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0392))
      coverage0392 catalogue_core_nodup coverageSize0392) (by rfl) M

theorem minimal_mask_iff0393 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0393) M ↔
      ∃ c ∈ template0393, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0393) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0393))
    cores template0393 witness0393 coverage0393
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0393) (maskBits m)) cores template0393 witness0393
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0393))
      coverage0393 catalogue_core_nodup coverageSize0393) (by rfl) M

theorem minimal_mask_iff0394 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0394) M ↔
      ∃ c ∈ template0394, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0394) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0394))
    cores template0394 witness0394 coverage0394
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0394) (maskBits m)) cores template0394 witness0394
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0394))
      coverage0394 catalogue_core_nodup coverageSize0394) (by rfl) M

theorem minimal_mask_iff0395 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0395) M ↔
      ∃ c ∈ template0395, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0395) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0395))
    cores template0395 witness0395 coverage0395
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0395) (maskBits m)) cores template0395 witness0395
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0395))
      coverage0395 catalogue_core_nodup coverageSize0395) (by rfl) M

theorem minimal_mask_iff0396 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0396) M ↔
      ∃ c ∈ template0396, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0396) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0396))
    cores template0396 witness0396 coverage0396
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0396) (maskBits m)) cores template0396 witness0396
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0396))
      coverage0396 catalogue_core_nodup coverageSize0396) (by rfl) M

theorem minimal_mask_iff0397 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0397) M ↔
      ∃ c ∈ template0397, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0397) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0397))
    cores template0397 witness0397 coverage0397
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0397) (maskBits m)) cores template0397 witness0397
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0397))
      coverage0397 catalogue_core_nodup coverageSize0397) (by rfl) M

theorem minimal_mask_iff0398 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0398) M ↔
      ∃ c ∈ template0398, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0398) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0398))
    cores template0398 witness0398 coverage0398
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0398) (maskBits m)) cores template0398 witness0398
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0398))
      coverage0398 catalogue_core_nodup coverageSize0398) (by rfl) M

theorem minimal_mask_iff0399 (M : Finset (Fin 256)) :
    MinimalMaskFamily (pairingRows pairing0399) M ↔
      ∃ c ∈ template0399, (cores c).toFinset = M :=
  minimal_maskSet_iff_template (fun m => rowOfMask (pairsOfEquiv pairing0399) (maskBits m))
    (mask_rank_injective _ (pairsOfEquiv_covers pairing0399))
    cores template0399 witness0399 coverage0399
    (exactCoverage_of_sizes (fun m => rowOfMask (pairsOfEquiv pairing0399) (maskBits m)) cores template0399 witness0399
      (mask_rank_injective _ (pairsOfEquiv_covers pairing0399))
      coverage0399 catalogue_core_nodup coverageSize0399) (by rfl) M

#print axioms minimal_mask_iff0360
#print axioms minimal_mask_iff0399
end Crown.CertificateData
