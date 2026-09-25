import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0011

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0440 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0440 : List (Fin 4935) := templateData0440

noncomputable def witness0440 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 3959) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3227) else (if t 3 = 0 then 3352 else if t 3 = 1 then 3351 else 2501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1611) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1610) else (if t 3 = 0 then 1882 else if t 3 = 1 then 1880 else 1619)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1650 else 878) else if t 2 = 1 then (if t 3 = 0 then 1651 else if t 3 = 1 then 1649 else 1853) else (if t 3 = 0 then 555 else if t 3 = 1 then 1670 else 2174))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1443) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1442) else (if t 3 = 0 then 1723 else if t 3 = 1 then 1721 else 1451)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3161) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4514) else (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4516)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3074 else 3314) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4518) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4507 else 4520))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2073 else 593) else if t 2 = 1 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2072 else 1448) else (if t 3 = 0 then 841 else if t 3 = 1 then 1735 else 1454)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3465 else 3164) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4515) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4499 else 4517)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 3084 else 3316) else if t 2 = 1 then (if t 3 = 0 then 3838 else if t 3 = 1 then 4506 else 4519) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4513 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4470 else (if jt.2.val < 2 then 4490 else 4491)) else (if jt.2.val < 4 then 4487 else (if jt.2.val < 5 then 4489 else 4488))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4575 else (if jt.2.val < 2 then 4585 else 4586)) else (if jt.2.val < 4 then 4582 else (if jt.2.val < 5 then 4584 else 4583)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4576 else (if jt.2.val < 2 then 4580 else 4581)) else (if jt.2.val < 4 then 4577 else (if jt.2.val < 5 then 4579 else 4578))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4467 else (if jt.2.val < 2 then 4509 else 4512)) else (if jt.2.val < 4 then 4508 else (if jt.2.val < 5 then 4511 else 4510)))))

checked_coverage fastCoverage0440 pairing0440 template0440 witness0440

theorem coverage0440 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0440) (maskBits m))
    cores template0440 witness0440 := by
  rw [← coresFast_eq]
  exact fastCoverage0440

theorem coverageSize0440 : ∀ q : Pattern,
    (cores (witness0440 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0440 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0440
#print axioms coverageSize0440

noncomputable def pairing0441 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0441 : List (Fin 4935) := templateData0441

noncomputable def witness0441 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4525) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 3225) else (if t 3 = 0 then 2741 else if t 3 = 1 then 2737 else 3344)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 1597) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 1593) else (if t 3 = 0 then 490 else if t 3 = 1 then 462 else 464)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1075 else 1599) else if t 2 = 1 then (if t 3 = 0 then 1090 else if t 3 = 1 then 1069 else 1071) else (if t 3 = 0 then 2150 else if t 3 = 1 then 467 else 469))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 1429) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 1424) else (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 366)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 3146) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3875) else (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3881)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2950) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3885) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3888 else 3889))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 175 else 2116) else if t 2 = 1 then (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 163) else (if t 3 = 0 then 1502 else if t 3 = 1 then 889 else 891)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2551) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3878) else (if t 3 = 0 then 3919 else if t 3 = 1 then 3882 else 3883)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2555 else 2557) else if t 2 = 1 then (if t 3 = 0 then 4039 else if t 3 = 1 then 3886 else 3887) else (if t 3 = 0 then 4526 else if t 3 = 1 then 3890 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4407 else (if jt.2.val < 2 then 4409 else 4416)) else (if jt.2.val < 4 then 4408 else (if jt.2.val < 5 then 4415 else 4414))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4245 else (if jt.2.val < 2 then 4247 else 4250)) else (if jt.2.val < 4 then 4246 else (if jt.2.val < 5 then 4249 else 4248)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3864 else (if jt.2.val < 2 then 3866 else 3901)) else (if jt.2.val < 4 then 3865 else (if jt.2.val < 5 then 3900 else 3879))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4510 else (if jt.2.val < 2 then 4524 else 4512)) else (if jt.2.val < 4 then 4522 else (if jt.2.val < 5 then 4523 else 4467)))))

checked_coverage fastCoverage0441 pairing0441 template0441 witness0441

theorem coverage0441 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0441) (maskBits m))
    cores template0441 witness0441 := by
  rw [← coresFast_eq]
  exact fastCoverage0441

theorem coverageSize0441 : ∀ q : Pattern,
    (cores (witness0441 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0441 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0441
#print axioms coverageSize0441

noncomputable def pairing0442 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0442 : List (Fin 4935) := templateData0442

noncomputable def witness0442 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3258 else 2798) else if t 2 = 1 then (if t 3 = 0 then 3254 else if t 3 = 1 then 3250 else 2797) else (if t 3 = 0 then 4537 else if t 3 = 1 then 4064 else 3943)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3256 else 88) else if t 2 = 1 then (if t 3 = 0 then 3252 else if t 3 = 1 then 3248 else 86) else (if t 3 = 0 then 1879 else if t 3 = 1 then 1877 else 94)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 144 else 2129) else if t 2 = 1 then (if t 3 = 0 then 143 else if t 3 = 1 then 142 else 898) else (if t 3 = 0 then 1538 else if t 3 = 1 then 158 else 900))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3257 else 775) else if t 2 = 1 then (if t 3 = 0 then 3253 else if t 3 = 1 then 3249 else 773) else (if t 3 = 0 then 1720 else if t 3 = 1 then 1718 else 781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3255 else 3165) else if t 2 = 1 then (if t 3 = 0 then 3251 else if t 3 = 1 then 3247 else 3295) else (if t 3 = 0 then 3269 else if t 3 = 1 then 3267 else 3296)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 3091 else 3500) else if t 2 = 1 then (if t 3 = 0 then 2623 else if t 3 = 1 then 3291 else 3299) else (if t 3 = 0 then 2627 else if t 3 = 1 then 3292 else 3300))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1043 else 1550) else if t 2 = 1 then (if t 3 = 0 then 1040 else if t 3 = 1 then 1039 else 787) else (if t 3 = 0 then 2147 else if t 3 = 1 then 1055 else 791)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 3278 else 3167) else if t 2 = 1 then (if t 3 = 0 then 2837 else if t 3 = 1 then 3276 else 3297) else (if t 3 = 0 then 2841 else if t 3 = 1 then 3279 else 3298)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 3095 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2637 else if t 3 = 1 then 3293 else 3301) else (if t 3 = 0 then 2639 else if t 3 = 1 then 3294 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4368 else (if jt.2.val < 2 then 4378 else 4379)) else (if jt.2.val < 4 then 4375 else (if jt.2.val < 5 then 4377 else 4376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3555 else (if jt.2.val < 2 then 3565 else 3566)) else (if jt.2.val < 4 then 3562 else (if jt.2.val < 5 then 3564 else 3563)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4578 else (if jt.2.val < 2 then 4589 else 4581)) else (if jt.2.val < 4 then 4587 else (if jt.2.val < 5 then 4588 else 4576))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3357 else (if jt.2.val < 2 then 3363 else 3368)) else (if jt.2.val < 4 then 3362 else (if jt.2.val < 5 then 3367 else 3366)))))

checked_coverage fastCoverage0442 pairing0442 template0442 witness0442

theorem coverage0442 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0442) (maskBits m))
    cores template0442 witness0442 := by
  rw [← coresFast_eq]
  exact fastCoverage0442

theorem coverageSize0442 : ∀ q : Pattern,
    (cores (witness0442 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0442 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0442
#print axioms coverageSize0442

noncomputable def pairing0443 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0443 : List (Fin 4935) := templateData0443

noncomputable def witness0443 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2705 else 3312) else if t 2 = 1 then (if t 3 = 0 then 2710 else if t 3 = 1 then 2688 else 3191) else (if t 3 = 0 then 3935 else if t 3 = 1 then 3929 else 4539)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2703 else 73) else if t 2 = 1 then (if t 3 = 0 then 2708 else if t 3 = 1 then 2682 else 43) else (if t 3 = 0 then 489 else if t 3 = 1 then 445 else 1507)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2098 else 75) else if t 2 = 1 then (if t 3 = 0 then 2107 else if t 3 = 1 then 2090 else 48) else (if t 3 = 0 then 1120 else if t 3 = 1 then 450 else 1510))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2704 else 760) else if t 2 = 1 then (if t 3 = 0 then 2709 else if t 3 = 1 then 2685 else 733) else (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 1484)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2695 else 2697) else if t 2 = 1 then (if t 3 = 0 then 2707 else if t 3 = 1 then 2664 else 2668) else (if t 3 = 0 then 2715 else if t 3 = 1 then 2666 else 2669)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2699 else 2701) else if t 2 = 1 then (if t 3 = 0 then 2902 else if t 3 = 1 then 2674 else 2676) else (if t 3 = 0 then 2903 else if t 3 = 1 then 2675 else 2677))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1672 else 1111) else if t 2 = 1 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1657 else 735) else (if t 3 = 0 then 404 else if t 3 = 1 then 351 else 2158)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2878 else 2880) else if t 2 = 1 then (if t 3 = 0 then 2721 else if t 3 = 1 then 2670 else 2672) else (if t 3 = 0 then 2723 else if t 3 = 1 then 2671 else 2673)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3196 else 3934) else if t 2 = 1 then (if t 3 = 0 then 3321 else if t 3 = 1 then 2678 else 2680) else (if t 3 = 0 then 3322 else if t 3 = 1 then 2679 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4344 else (if jt.2.val < 2 then 4346 else 4349)) else (if jt.2.val < 4 then 4345 else (if jt.2.val < 5 then 4348 else 4347))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3615 else (if jt.2.val < 2 then 3617 else 3620)) else (if jt.2.val < 4 then 3616 else (if jt.2.val < 5 then 3619 else 3618)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3879 else (if jt.2.val < 2 then 3932 else 3901)) else (if jt.2.val < 4 then 3931 else (if jt.2.val < 5 then 3933 else 3864))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3366 else (if jt.2.val < 2 then 3380 else 3368)) else (if jt.2.val < 4 then 3378 else (if jt.2.val < 5 then 3379 else 3357)))))

checked_coverage fastCoverage0443 pairing0443 template0443 witness0443

theorem coverage0443 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0443) (maskBits m))
    cores template0443 witness0443 := by
  rw [← coresFast_eq]
  exact fastCoverage0443

theorem coverageSize0443 : ∀ q : Pattern,
    (cores (witness0443 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0443 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0443
#print axioms coverageSize0443

noncomputable def pairing0444 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0444 : List (Fin 4935) := templateData0444

noncomputable def witness0444 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1316 else 1222) else if t 2 = 1 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1314 else 1777) else (if t 3 = 0 then 258 else if t 3 = 1 then 1353 else 2119)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1312 else if t 3 = 1 then 1308 else 1211) else if t 2 = 1 then (if t 3 = 0 then 1310 else if t 3 = 1 then 1306 else 1370) else (if t 3 = 0 then 254 else if t 3 = 1 then 1350 else 1372)) else (if t 2 = 0 then (if t 3 = 0 then 4530 else if t 3 = 1 then 3963 else 3967) else if t 2 = 1 then (if t 3 = 0 then 3234 else if t 3 = 1 then 3232 else 2860) else (if t 3 = 0 then 3342 else if t 3 = 1 then 2545 else 2577))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1315 else 1221) else if t 2 = 1 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1313 else 1776) else (if t 3 = 0 then 257 else if t 3 = 1 then 1352 else 2118)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1311 else if t 3 = 1 then 1307 else 1208) else if t 2 = 1 then (if t 3 = 0 then 1309 else if t 3 = 1 then 1305 else 1362) else (if t 3 = 0 then 253 else if t 3 = 1 then 1349 else 1366)) else (if t 2 = 0 then (if t 3 = 0 then 1329 else if t 3 = 1 then 1327 else 1209) else if t 2 = 1 then (if t 3 = 0 then 1328 else if t 3 = 1 then 1325 else 1363) else (if t 3 = 0 then 260 else if t 3 = 1 then 1354 else 1367))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 451 else 3343) else if t 2 = 1 then (if t 3 = 0 then 49 else if t 3 = 1 then 1341 else 1779) else (if t 3 = 0 then 3942 else if t 3 = 1 then 1358 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2124 else if t 3 = 1 then 447 else 500) else if t 2 = 1 then (if t 3 = 0 then 45 else if t 3 = 1 then 1338 else 1364) else (if t 3 = 0 then 921 else if t 3 = 1 then 1356 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 2126 else if t 3 = 1 then 454 else 501) else if t 2 = 1 then (if t 3 = 0 then 52 else if t 3 = 1 then 1343 else 1365) else (if t 3 = 0 then 923 else if t 3 = 1 then 1360 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4344 else (if jt.2.val < 2 then 4355 else 4349)) else (if jt.2.val < 4 then 4353 else (if jt.2.val < 5 then 4354 else 4347))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4583 else (if jt.2.val < 2 then 4592 else 4586)) else (if jt.2.val < 4 then 4590 else (if jt.2.val < 5 then 4591 else 4575)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1971 else (if jt.2.val < 2 then 1981 else 1982)) else (if jt.2.val < 4 then 1978 else (if jt.2.val < 5 then 1980 else 1979))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1931 else (if jt.2.val < 2 then 1933 else 1937)) else (if jt.2.val < 4 then 1932 else (if jt.2.val < 5 then 1936 else 1935)))))

checked_coverage fastCoverage0444 pairing0444 template0444 witness0444

theorem coverage0444 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0444) (maskBits m))
    cores template0444 witness0444 := by
  rw [← coresFast_eq]
  exact fastCoverage0444

theorem coverageSize0444 : ∀ q : Pattern,
    (cores (witness0444 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0444 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0444
#print axioms coverageSize0444

noncomputable def pairing0445 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0445 : List (Fin 4935) := templateData0445

noncomputable def witness0445 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 995 else 1433) else if t 2 = 1 then (if t 3 = 0 then 1006 else if t 3 = 1 then 991 else 992) else (if t 3 = 0 then 2140 else if t 3 = 1 then 373 else 374)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1004 else if t 3 = 1 then 977 else 1801) else if t 2 = 1 then (if t 3 = 0 then 1000 else if t 3 = 1 then 957 else 960) else (if t 3 = 0 then 304 else if t 3 = 1 then 963 else 964)) else (if t 2 = 0 then (if t 3 = 0 then 3860 else if t 3 = 1 then 4046 else 4532) else if t 2 = 1 then (if t 3 = 0 then 2980 else if t 3 = 1 then 2970 else 3338) else (if t 3 = 0 then 2762 else if t 3 = 1 then 2973 else 3340))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 993 else 1430) else if t 2 = 1 then (if t 3 = 0 then 1005 else if t 3 = 1 then 987 else 989) else (if t 3 = 0 then 2139 else if t 3 = 1 then 367 else 369)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1002 else if t 3 = 1 then 967 else 1795) else if t 2 = 1 then (if t 3 = 0 then 996 else if t 3 = 1 then 939 else 943) else (if t 3 = 0 then 300 else if t 3 = 1 then 949 else 951)) else (if t 2 = 0 then (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 1796) else if t 2 = 1 then (if t 3 = 0 then 997 else if t 3 = 1 then 941 else 944) else (if t 3 = 0 then 301 else if t 3 = 1 then 950 else 952))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 176 else 2758) else if t 2 = 1 then (if t 3 = 0 then 1806 else if t 3 = 1 then 166 else 168) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1494 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 102 else if t 3 = 1 then 971 else 2136) else if t 2 = 1 then (if t 3 = 0 then 96 else if t 3 = 1 then 945 else 947) else (if t 3 = 0 then 1476 else if t 3 = 1 then 953 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 103 else if t 3 = 1 then 972 else 2137) else if t 2 = 1 then (if t 3 = 0 then 97 else if t 3 = 1 then 946 else 948) else (if t 3 = 0 then 1477 else if t 3 = 1 then 954 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4368 else (if jt.2.val < 2 then 4393 else 4379)) else (if jt.2.val < 4 then 4392 else (if jt.2.val < 5 then 4394 else 4376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4248 else (if jt.2.val < 2 then 4258 else 4250)) else (if jt.2.val < 4 then 4257 else (if jt.2.val < 5 then 4259 else 4245)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2130 else (if jt.2.val < 2 then 2132 else 2135)) else (if jt.2.val < 4 then 2131 else (if jt.2.val < 5 then 2134 else 2133))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1935 else (if jt.2.val < 2 then 1943 else 1937)) else (if jt.2.val < 4 then 1941 else (if jt.2.val < 5 then 1942 else 1931)))))

checked_coverage fastCoverage0445 pairing0445 template0445 witness0445

theorem coverage0445 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0445) (maskBits m))
    cores template0445 witness0445 := by
  rw [← coresFast_eq]
  exact fastCoverage0445

theorem coverageSize0445 : ∀ q : Pattern,
    (cores (witness0445 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0445 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0445
#print axioms coverageSize0445

noncomputable def pairing0446 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0446 : List (Fin 4935) := templateData0446

noncomputable def witness0446 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 626 else 2161) else if t 2 = 1 then (if t 3 = 0 then 624 else if t 3 = 1 then 622 else 1144) else (if t 3 = 0 then 1462 else if t 3 = 1 then 646 else 1145)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 620 else if t 3 = 1 then 618 else 694) else if t 2 = 1 then (if t 3 = 0 then 616 else if t 3 = 1 then 614 else 680) else (if t 3 = 0 then 1459 else if t 3 = 1 then 641 else 681)) else (if t 2 = 0 then (if t 3 = 0 then 3320 else if t 3 = 1 then 2768 else 2781) else if t 2 = 1 then (if t 3 = 0 then 3172 else if t 3 = 1 then 2766 else 2778) else (if t 3 = 0 then 4541 else if t 3 = 1 then 3945 else 3951))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 625 else 2160) else if t 2 = 1 then (if t 3 = 0 then 623 else if t 3 = 1 then 621 else 1140) else (if t 3 = 0 then 1461 else if t 3 = 1 then 645 else 1142)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 619 else if t 3 = 1 then 617 else 690) else if t 2 = 1 then (if t 3 = 0 then 615 else if t 3 = 1 then 613 else 672) else (if t 3 = 0 then 1458 else if t 3 = 1 then 640 else 674)) else (if t 2 = 0 then (if t 3 = 0 then 635 else if t 3 = 1 then 634 else 691) else if t 2 = 1 then (if t 3 = 0 then 633 else if t 3 = 1 then 632 else 673) else (if t 3 = 0 then 1463 else if t 3 = 1 then 649 else 675))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 1518 else 4542) else if t 2 = 1 then (if t 3 = 0 then 660 else if t 3 = 1 then 658 else 1824) else (if t 3 = 0 then 2777 else if t 3 = 1 then 668 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1133 else if t 3 = 1 then 1131 else 1524) else if t 2 = 1 then (if t 3 = 0 then 655 else if t 3 = 1 then 653 else 676) else (if t 3 = 0 then 2169 else if t 3 = 1 then 666 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 1136 else if t 3 = 1 then 1135 else 1525) else if t 2 = 1 then (if t 3 = 0 then 663 else if t 3 = 1 then 662 else 677) else (if t 3 = 0 then 2171 else if t 3 = 1 then 670 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4407 else (if jt.2.val < 2 then 4427 else 4416)) else (if jt.2.val < 4 then 4425 else (if jt.2.val < 5 then 4426 else 4414))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3563 else (if jt.2.val < 2 then 3590 else 3566)) else (if jt.2.val < 4 then 3588 else (if jt.2.val < 5 then 3589 else 3555)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1979 else (if jt.2.val < 2 then 2016 else 1982)) else (if jt.2.val < 4 then 2013 else (if jt.2.val < 5 then 2014 else 1971))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2250 else (if jt.2.val < 2 then 2252 else 2255)) else (if jt.2.val < 4 then 2251 else (if jt.2.val < 5 then 2254 else 2253)))))

checked_coverage fastCoverage0446 pairing0446 template0446 witness0446

theorem coverage0446 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0446) (maskBits m))
    cores template0446 witness0446 := by
  rw [← coresFast_eq]
  exact fastCoverage0446

theorem coverageSize0446 : ∀ q : Pattern,
    (cores (witness0446 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0446 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0446
#print axioms coverageSize0446

noncomputable def pairing0447 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0447 : List (Fin 4935) := templateData0447

noncomputable def witness0447 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2219 else 764) else if t 2 = 1 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2213 else 742) else (if t 3 = 0 then 932 else if t 3 = 1 then 358 else 1490)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2207 else 1189) else if t 2 = 1 then (if t 3 = 0 then 2222 else if t 3 = 1 then 2193 else 2196) else (if t 3 = 0 then 298 else if t 3 = 1 then 2195 else 2197)) else (if t 2 = 0 then (if t 3 = 0 then 2654 else if t 3 = 1 then 2939 else 3330) else if t 2 = 1 then (if t 3 = 0 then 2648 else if t 3 = 1 then 3528 else 3530) else (if t 3 = 0 then 3927 else if t 3 = 1 then 4211 else 4546))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2217 else 761) else if t 2 = 1 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2211 else 736) else (if t 3 = 0 then 930 else if t 3 = 1 then 352 else 1487)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2205 else 1183) else if t 2 = 1 then (if t 3 = 0 then 2220 else if t 3 = 1 then 2177 else 2181) else (if t 3 = 0 then 294 else if t 3 = 1 then 2179 else 2183)) else (if t 2 = 0 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2206 else 1184) else if t 2 = 1 then (if t 3 = 0 then 2221 else if t 3 = 1 then 2178 else 2182) else (if t 3 = 0 then 295 else if t 3 = 1 then 2180 else 2184))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1673 else 3966) else if t 2 = 1 then (if t 3 = 0 then 1854 else if t 3 = 1 then 1658 else 738) else (if t 3 = 0 then 3345 else if t 3 = 1 then 354 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1620 else if t 3 = 1 then 1889 else 1185) else if t 2 = 1 then (if t 3 = 0 then 1614 else if t 3 = 1 then 2185 else 2189) else (if t 3 = 0 then 296 else if t 3 = 1 then 2187 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 1621 else if t 3 = 1 then 1890 else 1186) else if t 2 = 1 then (if t 3 = 0 then 1615 else if t 3 = 1 then 2186 else 2190) else (if t 3 = 0 then 297 else if t 3 = 1 then 2188 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4470 else (if jt.2.val < 2 then 4544 else 4491)) else (if jt.2.val < 4 then 4543 else (if jt.2.val < 5 then 4545 else 4488))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3618 else (if jt.2.val < 2 then 3625 else 3620)) else (if jt.2.val < 4 then 3624 else (if jt.2.val < 5 then 3626 else 3615)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2133 else (if jt.2.val < 2 then 2203 else 2135)) else (if jt.2.val < 4 then 2202 else (if jt.2.val < 5 then 2204 else 2130))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2253 else (if jt.2.val < 2 then 2267 else 2255)) else (if jt.2.val < 4 then 2265 else (if jt.2.val < 5 then 2266 else 2250)))))

checked_coverage fastCoverage0447 pairing0447 template0447 witness0447

theorem coverage0447 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0447) (maskBits m))
    cores template0447 witness0447 := by
  rw [← coresFast_eq]
  exact fastCoverage0447

theorem coverageSize0447 : ∀ q : Pattern,
    (cores (witness0447 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0447 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0447
#print axioms coverageSize0447

noncomputable def pairing0448 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0448 : List (Fin 4935) := templateData0448

noncomputable def witness0448 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 4066) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3351) else (if t 3 = 0 then 3228 else if t 3 = 1 then 3227 else 2501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1881) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1880) else (if t 3 = 0 then 1612 else if t 3 = 1 then 1610 else 1619)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1650 else 159) else if t 2 = 1 then (if t 3 = 0 then 1651 else if t 3 = 1 then 1649 else 1670) else (if t 3 = 0 then 1094 else if t 3 = 1 then 1853 else 2174))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1722) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1721) else (if t 3 = 0 then 1444 else if t 3 = 1 then 1442 else 1451)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3270) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4498) else (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4516)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3074 else 3093) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4507) else (if t 3 = 0 then 4038 else if t 3 = 1 then 4518 else 4520))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2073 else 1057) else if t 2 = 1 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2072 else 1735) else (if t 3 = 0 then 197 else if t 3 = 1 then 1448 else 1454)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3465 else 3280) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4499) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4515 else 4517)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 3084 else 3097) else if t 2 = 1 then (if t 3 = 0 then 3838 else if t 3 = 1 then 4506 else 4513) else (if t 3 = 0 then 4040 else if t 3 = 1 then 4519 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4470 else (if jt.2.val < 2 then 4490 else 4491)) else (if jt.2.val < 4 then 4487 else (if jt.2.val < 5 then 4489 else 4488))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4575 else (if jt.2.val < 2 then 4585 else 4586)) else (if jt.2.val < 4 then 4582 else (if jt.2.val < 5 then 4584 else 4583)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4548 else (if jt.2.val < 2 then 4556 else 4559)) else (if jt.2.val < 4 then 4555 else (if jt.2.val < 5 then 4558 else 4557))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4593 else (if jt.2.val < 2 then 4597 else 4598)) else (if jt.2.val < 4 then 4594 else (if jt.2.val < 5 then 4596 else 4595)))))

checked_coverage fastCoverage0448 pairing0448 template0448 witness0448

theorem coverage0448 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0448) (maskBits m))
    cores template0448 witness0448 := by
  rw [← coresFast_eq]
  exact fastCoverage0448

theorem coverageSize0448 : ∀ q : Pattern,
    (cores (witness0448 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0448 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0448
#print axioms coverageSize0448

noncomputable def pairing0449 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0449 : List (Fin 4935) := templateData0449

noncomputable def witness0449 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 4537) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 3350) else (if t 3 = 0 then 2741 else if t 3 = 1 then 2740 else 3207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 1879) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 1878) else (if t 3 = 0 then 490 else if t 3 = 1 then 488 else 496)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 538 else 1538) else if t 2 = 1 then (if t 3 = 0 then 539 else if t 3 = 1 then 537 else 554) else (if t 3 = 0 then 2150 else if t 3 = 1 then 1114 else 1116))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 1720) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 1719) else (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 397)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 3269) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 3993) else (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4020)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2627) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4016) else (if t 3 = 0 then 4191 else if t 3 = 1 then 4023 else 4024))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 820 else 2147) else if t 2 = 1 then (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 839) else (if t 3 = 0 then 1502 else if t 3 = 1 then 403 else 407)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2841) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4003) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4021 else 4022)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2635 else 2639) else if t 2 = 1 then (if t 3 = 0 then 3849 else if t 3 = 1 then 4017 else 4018) else (if t 3 = 0 then 4526 else if t 3 = 1 then 4025 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4431 else (if jt.2.val < 2 then 4441 else 4442)) else (if jt.2.val < 4 then 4438 else (if jt.2.val < 5 then 4440 else 4439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4233 else (if jt.2.val < 2 then 4243 else 4244)) else (if jt.2.val < 4 then 4240 else (if jt.2.val < 5 then 4242 else 4241)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4068 else (if jt.2.val < 2 then 4074 else 4079)) else (if jt.2.val < 4 then 4073 else (if jt.2.val < 5 then 4078 else 4077))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4595 else (if jt.2.val < 2 then 4601 else 4598)) else (if jt.2.val < 4 then 4599 else (if jt.2.val < 5 then 4600 else 4593)))))

checked_coverage fastCoverage0449 pairing0449 template0449 witness0449

theorem coverage0449 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0449) (maskBits m))
    cores template0449 witness0449 := by
  rw [← coresFast_eq]
  exact fastCoverage0449

theorem coverageSize0449 : ∀ q : Pattern,
    (cores (witness0449 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0449 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0449
#print axioms coverageSize0449

noncomputable def pairing0450 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0450 : List (Fin 4935) := templateData0450

noncomputable def witness0450 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3156 else 2798) else if t 2 = 1 then (if t 3 = 0 then 3151 else if t 3 = 1 then 3144 else 2794) else (if t 3 = 0 then 4525 else if t 3 = 1 then 3953 else 4060)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3154 else 88) else if t 2 = 1 then (if t 3 = 0 then 3149 else if t 3 = 1 then 3138 else 60) else (if t 3 = 0 then 1597 else if t 3 = 1 then 1589 else 62)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 874 else 2129) else if t 2 = 1 then (if t 3 = 0 then 859 else if t 3 = 1 then 853 else 65) else (if t 3 = 0 then 1599 else if t 3 = 1 then 855 else 67))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3155 else 775) else if t 2 = 1 then (if t 3 = 0 then 3150 else if t 3 = 1 then 3141 else 748) else (if t 3 = 0 then 1429 else if t 3 = 1 then 1419 else 750)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3153 else 3165) else if t 2 = 1 then (if t 3 = 0 then 3145 else if t 3 = 1 then 3119 else 3126) else (if t 3 = 0 then 3146 else if t 3 = 1 then 3121 else 3127)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 3313 else 3500) else if t 2 = 1 then (if t 3 = 0 then 2949 else if t 3 = 1 then 3130 else 3134) else (if t 3 = 0 then 2950 else if t 3 = 1 then 3131 else 3135))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 586 else 1550) else if t 2 = 1 then (if t 3 = 0 then 571 else if t 3 = 1 then 557 else 1105) else (if t 3 = 0 then 2116 else if t 3 = 1 then 559 else 1107)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 3163 else 3167) else if t 2 = 1 then (if t 3 = 0 then 2550 else if t 3 = 1 then 3123 else 3128) else (if t 3 = 0 then 2551 else if t 3 = 1 then 3124 else 3129)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 3315 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2556 else if t 3 = 1 then 3132 else 3136) else (if t 3 = 0 then 2557 else if t 3 = 1 then 3133 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4326 else (if jt.2.val < 2 then 4328 else 4335)) else (if jt.2.val < 4 then 4327 else (if jt.2.val < 5 then 4334 else 4333))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3567 else (if jt.2.val < 2 then 3569 else 3572)) else (if jt.2.val < 4 then 3568 else (if jt.2.val < 5 then 3571 else 3570)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4557 else (if jt.2.val < 2 then 4565 else 4559)) else (if jt.2.val < 4 then 4563 else (if jt.2.val < 5 then 4564 else 4548))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3110 else (if jt.2.val < 2 then 3112 else 3148)) else (if jt.2.val < 4 then 3111 else (if jt.2.val < 5 then 3147 else 3125)))))

checked_coverage fastCoverage0450 pairing0450 template0450 witness0450

theorem coverage0450 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0450) (maskBits m))
    cores template0450 witness0450 := by
  rw [← coresFast_eq]
  exact fastCoverage0450

theorem coverageSize0450 : ∀ q : Pattern,
    (cores (witness0450 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0450 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0450
#print axioms coverageSize0450

noncomputable def pairing0451 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0451 : List (Fin 4935) := templateData0451

noncomputable def witness0451 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2710 else 3198) else if t 2 = 1 then (if t 3 = 0 then 2705 else if t 3 = 1 then 2688 else 3191) else (if t 3 = 0 then 4036 else if t 3 = 1 then 3929 else 4539)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2708 else 87) else if t 2 = 1 then (if t 3 = 0 then 2703 else if t 3 = 1 then 2682 else 43) else (if t 3 = 0 then 475 else if t 3 = 1 then 445 else 1507)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2107 else 904) else if t 2 = 1 then (if t 3 = 0 then 2098 else if t 3 = 1 then 2090 else 48) else (if t 3 = 0 then 477 else if t 3 = 1 then 450 else 1510))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2709 else 774) else if t 2 = 1 then (if t 3 = 0 then 2704 else if t 3 = 1 then 2685 else 733) else (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 1484)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2707 else 2717) else if t 2 = 1 then (if t 3 = 0 then 2695 else if t 3 = 1 then 2664 else 2668) else (if t 3 = 0 then 2696 else if t 3 = 1 then 2666 else 2669)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2902 else 2904) else if t 2 = 1 then (if t 3 = 0 then 2699 else if t 3 = 1 then 2674 else 2676) else (if t 3 = 0 then 2700 else if t 3 = 1 then 2675 else 2677))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1686 else 788) else if t 2 = 1 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1657 else 735) else (if t 3 = 0 then 895 else if t 3 = 1 then 351 else 2158)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2721 else 2724) else if t 2 = 1 then (if t 3 = 0 then 2878 else if t 3 = 1 then 2670 else 2672) else (if t 3 = 0 then 2879 else if t 3 = 1 then 2671 else 2673)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3321 else 4045) else if t 2 = 1 then (if t 3 = 0 then 3196 else if t 3 = 1 then 2678 else 2680) else (if t 3 = 0 then 3197 else if t 3 = 1 then 2679 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4344 else (if jt.2.val < 2 then 4346 else 4349)) else (if jt.2.val < 4 then 4345 else (if jt.2.val < 5 then 4348 else 4347))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3615 else (if jt.2.val < 2 then 3617 else 3620)) else (if jt.2.val < 4 then 3616 else (if jt.2.val < 5 then 3619 else 3618)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4077 else (if jt.2.val < 2 then 4091 else 4079)) else (if jt.2.val < 4 then 4089 else (if jt.2.val < 5 then 4090 else 4068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3125 else (if jt.2.val < 2 then 3194 else 3148)) else (if jt.2.val < 4 then 3193 else (if jt.2.val < 5 then 3195 else 3110)))))

checked_coverage fastCoverage0451 pairing0451 template0451 witness0451

theorem coverage0451 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0451) (maskBits m))
    cores template0451 witness0451 := by
  rw [← coresFast_eq]
  exact fastCoverage0451

theorem coverageSize0451 : ∀ q : Pattern,
    (cores (witness0451 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0451 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0451
#print axioms coverageSize0451

noncomputable def pairing0452 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0452 : List (Fin 4935) := templateData0452

noncomputable def witness0452 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1316 else 648) else if t 2 = 1 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1314 else 1353) else (if t 3 = 0 then 1012 else if t 3 = 1 then 1777 else 2119)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1312 else if t 3 = 1 then 1308 else 644) else if t 2 = 1 then (if t 3 = 0 then 1310 else if t 3 = 1 then 1306 else 1350) else (if t 3 = 0 then 1001 else if t 3 = 1 then 1370 else 1372)) else (if t 2 = 0 then (if t 3 = 0 then 4530 else if t 3 = 1 then 3963 else 4058) else if t 2 = 1 then (if t 3 = 0 then 3234 else if t 3 = 1 then 3232 else 2545) else (if t 3 = 0 then 3242 else if t 3 = 1 then 2860 else 2577))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1315 else 647) else if t 2 = 1 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1313 else 1352) else (if t 3 = 0 then 1011 else if t 3 = 1 then 1776 else 2118)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1311 else if t 3 = 1 then 1307 else 643) else if t 2 = 1 then (if t 3 = 0 then 1309 else if t 3 = 1 then 1305 else 1349) else (if t 3 = 0 then 998 else if t 3 = 1 then 1362 else 1366)) else (if t 2 = 0 then (if t 3 = 0 then 1329 else if t 3 = 1 then 1327 else 650) else if t 2 = 1 then (if t 3 = 0 then 1328 else if t 3 = 1 then 1325 else 1354) else (if t 3 = 0 then 999 else if t 3 = 1 then 1363 else 1367))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 451 else 3206) else if t 2 = 1 then (if t 3 = 0 then 49 else if t 3 = 1 then 1341 else 1358) else (if t 3 = 0 then 4059 else if t 3 = 1 then 1779 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2124 else if t 3 = 1 then 447 else 1137) else if t 2 = 1 then (if t 3 = 0 then 45 else if t 3 = 1 then 1338 else 1356) else (if t 3 = 0 then 98 else if t 3 = 1 then 1364 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 2126 else if t 3 = 1 then 454 else 1139) else if t 2 = 1 then (if t 3 = 0 then 52 else if t 3 = 1 then 1343 else 1360) else (if t 3 = 0 then 99 else if t 3 = 1 then 1365 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4344 else (if jt.2.val < 2 then 4355 else 4349)) else (if jt.2.val < 4 then 4353 else (if jt.2.val < 5 then 4354 else 4347))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4583 else (if jt.2.val < 2 then 4592 else 4586)) else (if jt.2.val < 4 then 4590 else (if jt.2.val < 5 then 4591 else 4575)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2382 else (if jt.2.val < 2 then 2384 else 2387)) else (if jt.2.val < 4 then 2383 else (if jt.2.val < 5 then 2386 else 2385))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1302 else (if jt.2.val < 2 then 1348 else 1351)) else (if jt.2.val < 4 then 1345 else (if jt.2.val < 5 then 1347 else 1346)))))

checked_coverage fastCoverage0452 pairing0452 template0452 witness0452

theorem coverage0452 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0452) (maskBits m))
    cores template0452 witness0452 := by
  rw [← coresFast_eq]
  exact fastCoverage0452

theorem coverageSize0452 : ∀ q : Pattern,
    (cores (witness0452 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0452 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0452
#print axioms coverageSize0452

noncomputable def pairing0453 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0453 : List (Fin 4935) := templateData0453

noncomputable def witness0453 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 228 else 1462) else if t 2 = 1 then (if t 3 = 0 then 230 else if t 3 = 1 then 226 else 256) else (if t 3 = 0 then 2140 else if t 3 = 1 then 928 else 929)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 224 else if t 3 = 1 then 220 else 1459) else if t 2 = 1 then (if t 3 = 0 then 222 else if t 3 = 1 then 218 else 251) else (if t 3 = 0 then 304 else if t 3 = 1 then 290 else 291)) else (if t 2 = 0 then (if t 3 = 0 then 4044 else if t 3 = 1 then 3923 else 4541) else if t 2 = 1 then (if t 3 = 0 then 2749 else if t 3 = 1 then 2747 else 3209) else (if t 3 = 0 then 2762 else if t 3 = 1 then 2759 else 3215))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 227 else 1461) else if t 2 = 1 then (if t 3 = 0 then 229 else if t 3 = 1 then 225 else 255) else (if t 3 = 0 then 2139 else if t 3 = 1 then 924 else 926)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 223 else if t 3 = 1 then 219 else 1458) else if t 2 = 1 then (if t 3 = 0 then 221 else if t 3 = 1 then 217 else 250) else (if t 3 = 0 then 300 else if t 3 = 1 then 282 else 284)) else (if t 2 = 0 then (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 1463) else if t 2 = 1 then (if t 3 = 0 then 240 else if t 3 = 1 then 237 else 259) else (if t 3 = 0 then 301 else if t 3 = 1 then 283 else 285))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 270 else 2777) else if t 2 = 1 then (if t 3 = 0 then 1470 else if t 3 = 1 then 268 else 278) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1788 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 917 else if t 3 = 1 then 265 else 2169) else if t 2 = 1 then (if t 3 = 0 then 915 else if t 3 = 1 then 263 else 276) else (if t 3 = 0 then 1476 else if t 3 = 1 then 286 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 920 else if t 3 = 1 then 273 else 2171) else if t 2 = 1 then (if t 3 = 0 then 919 else if t 3 = 1 then 272 else 280) else (if t 3 = 0 then 1477 else if t 3 = 1 then 287 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4326 else (if jt.2.val < 2 then 4364 else 4335)) else (if jt.2.val < 4 then 4362 else (if jt.2.val < 5 then 4363 else 4333))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4241 else (if jt.2.val < 2 then 4256 else 4244)) else (if jt.2.val < 4 then 4254 else (if jt.2.val < 5 then 4255 else 4233)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2418 else (if jt.2.val < 2 then 2420 else 2423)) else (if jt.2.val < 4 then 2419 else (if jt.2.val < 5 then 2422 else 2421))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1346 else (if jt.2.val < 2 then 1460 else 1351)) else (if jt.2.val < 4 then 1455 else (if jt.2.val < 5 then 1456 else 1302)))))

checked_coverage fastCoverage0453 pairing0453 template0453 witness0453

theorem coverage0453 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0453) (maskBits m))
    cores template0453 witness0453 := by
  rw [← coresFast_eq]
  exact fastCoverage0453

theorem coverageSize0453 : ∀ q : Pattern,
    (cores (witness0453 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0453 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0453
#print axioms coverageSize0453

noncomputable def pairing0454 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0454 : List (Fin 4935) := templateData0454

noncomputable def witness0454 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1216 else 2161) else if t 2 = 1 then (if t 3 = 0 then 1205 else if t 3 = 1 then 1201 else 757) else (if t 3 = 0 then 1433 else if t 3 = 1 then 1202 else 758)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1214 else if t 3 = 1 then 1210 else 694) else if t 2 = 1 then (if t 3 = 0 then 1187 else if t 3 = 1 then 1167 else 1172) else (if t 3 = 0 then 1801 else if t 3 = 1 then 1169 else 1173)) else (if t 2 = 0 then (if t 3 = 0 then 3106 else if t 3 = 1 then 3003 else 2781) else if t 2 = 1 then (if t 3 = 0 then 3329 else if t 3 = 1 then 2993 else 2996) else (if t 3 = 0 then 4532 else if t 3 = 1 then 4054 else 4056))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1215 else 2160) else if t 2 = 1 then (if t 3 = 0 then 1203 else if t 3 = 1 then 1197 else 751) else (if t 3 = 0 then 1430 else if t 3 = 1 then 1199 else 753)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1212 else if t 3 = 1 then 1206 else 690) else if t 2 = 1 then (if t 3 = 0 then 1179 else if t 3 = 1 then 1151 else 1159) else (if t 3 = 0 then 1795 else if t 3 = 1 then 1153 else 1161)) else (if t 2 = 0 then (if t 3 = 0 then 1213 else if t 3 = 1 then 1207 else 691) else if t 2 = 1 then (if t 3 = 0 then 1180 else if t 3 = 1 then 1152 else 1160) else (if t 3 = 0 then 1796 else if t 3 = 1 then 1154 else 1162))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 1836 else 4542) else if t 2 = 1 then (if t 3 = 0 then 572 else if t 3 = 1 then 562 else 1542) else (if t 3 = 0 then 2758 else if t 3 = 1 then 564 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 504 else if t 3 = 1 then 498 else 1524) else if t 2 = 1 then (if t 3 = 0 then 1181 else if t 3 = 1 then 1155 else 1163) else (if t 3 = 0 then 2136 else if t 3 = 1 then 1157 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 505 else if t 3 = 1 then 499 else 1525) else if t 2 = 1 then (if t 3 = 0 then 1182 else if t 3 = 1 then 1156 else 1164) else (if t 3 = 0 then 2137 else if t 3 = 1 then 1158 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4431 else (if jt.2.val < 2 then 4447 else 4442)) else (if jt.2.val < 4 then 4446 else (if jt.2.val < 5 then 4448 else 4439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3570 else (if jt.2.val < 2 then 3592 else 3572)) else (if jt.2.val < 4 then 3591 else (if jt.2.val < 5 then 3593 else 3567)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2385 else (if jt.2.val < 2 then 2405 else 2387)) else (if jt.2.val < 4 then 2403 else (if jt.2.val < 5 then 2404 else 2382))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2346 else (if jt.2.val < 2 then 2348 else 2351)) else (if jt.2.val < 4 then 2347 else (if jt.2.val < 5 then 2350 else 2349)))))

checked_coverage fastCoverage0454 pairing0454 template0454 witness0454

theorem coverage0454 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0454) (maskBits m))
    cores template0454 witness0454 := by
  rw [← coresFast_eq]
  exact fastCoverage0454

theorem coverageSize0454 : ∀ q : Pattern,
    (cores (witness0454 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0454 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0454
#print axioms coverageSize0454

noncomputable def pairing0455 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0455 : List (Fin 4935) := templateData0455

noncomputable def witness0455 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2228 else 1148) else if t 2 = 1 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2213 else 742) else (if t 3 = 0 then 380 else if t 3 = 1 then 358 else 1490)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2222 else 688) else if t 2 = 1 then (if t 3 = 0 then 2207 else if t 3 = 1 then 2193 else 2196) else (if t 3 = 0 then 979 else if t 3 = 1 then 2195 else 2197)) else (if t 2 = 0 then (if t 3 = 0 then 2654 else if t 3 = 1 then 2648 else 3182) else if t 2 = 1 then (if t 3 = 0 then 2939 else if t 3 = 1 then 3528 else 3530) else (if t 3 = 0 then 4047 else if t 3 = 1 then 4211 else 4546))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2226 else 1146) else if t 2 = 1 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2211 else 736) else (if t 3 = 0 then 377 else if t 3 = 1 then 352 else 1487)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2220 else 684) else if t 2 = 1 then (if t 3 = 0 then 2205 else if t 3 = 1 then 2177 else 2181) else (if t 3 = 0 then 973 else if t 3 = 1 then 2179 else 2183)) else (if t 2 = 0 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2221 else 685) else if t 2 = 1 then (if t 3 = 0 then 2206 else if t 3 = 1 then 2178 else 2182) else (if t 3 = 0 then 974 else if t 3 = 1 then 2180 else 2184))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1854 else 4061) else if t 2 = 1 then (if t 3 = 0 then 1673 else if t 3 = 1 then 1658 else 738) else (if t 3 = 0 then 3240 else if t 3 = 1 then 354 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1620 else if t 3 = 1 then 1614 else 686) else if t 2 = 1 then (if t 3 = 0 then 1889 else if t 3 = 1 then 2185 else 2189) else (if t 3 = 0 then 975 else if t 3 = 1 then 2187 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 1621 else if t 3 = 1 then 1615 else 687) else if t 2 = 1 then (if t 3 = 0 then 1890 else if t 3 = 1 then 2186 else 2190) else (if t 3 = 0 then 976 else if t 3 = 1 then 2188 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4470 else (if jt.2.val < 2 then 4544 else 4491)) else (if jt.2.val < 4 then 4543 else (if jt.2.val < 5 then 4545 else 4488))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3618 else (if jt.2.val < 2 then 3625 else 3620)) else (if jt.2.val < 4 then 3624 else (if jt.2.val < 5 then 3626 else 3615)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2421 else (if jt.2.val < 2 then 2429 else 2423)) else (if jt.2.val < 4 then 2427 else (if jt.2.val < 5 then 2428 else 2418))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2349 else (if jt.2.val < 2 then 2353 else 2351)) else (if jt.2.val < 4 then 2352 else (if jt.2.val < 5 then 2354 else 2346)))))

checked_coverage fastCoverage0455 pairing0455 template0455 witness0455

theorem coverage0455 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0455) (maskBits m))
    cores template0455 witness0455 := by
  rw [← coresFast_eq]
  exact fastCoverage0455

theorem coverageSize0455 : ∀ q : Pattern,
    (cores (witness0455 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0455 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0455
#print axioms coverageSize0455

noncomputable def pairing0456 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0456 : List (Fin 4935) := templateData0456

noncomputable def witness0456 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 3925) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2750) else (if t 3 = 0 then 3352 else if t 3 = 1 then 3350 else 3210)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 538) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 537) else (if t 3 = 0 then 1882 else if t 3 = 1 then 1878 else 554)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 489 else 1120) else if t 2 = 1 then (if t 3 = 0 then 490 else if t 3 = 1 then 488 else 1114) else (if t 3 = 0 then 497 else if t 3 = 1 then 496 else 1116))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 243) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 242) else (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 261)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2614) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4015) else (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4016)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2903) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4023) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4020 else 4024))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 820 else 275) else if t 2 = 1 then (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 274) else (if t 3 = 0 then 841 else if t 3 = 1 then 839 else 281)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2635) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4017) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4003 else 4018)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2723 else 3322) else if t 2 = 1 then (if t 3 = 0 then 3919 else if t 3 = 1 then 4021 else 4025) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4022 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4431 else (if jt.2.val < 2 then 4441 else 4442)) else (if jt.2.val < 4 then 4438 else (if jt.2.val < 5 then 4440 else 4439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4287 else (if jt.2.val < 2 then 4289 else 4292)) else (if jt.2.val < 4 then 4288 else (if jt.2.val < 5 then 4291 else 4290)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4566 else (if jt.2.val < 2 then 4570 else 4571)) else (if jt.2.val < 4 then 4567 else (if jt.2.val < 5 then 4569 else 4568))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4069 else (if jt.2.val < 2 then 4075 else 4076)) else (if jt.2.val < 4 then 4070 else (if jt.2.val < 5 then 4072 else 4071)))))

checked_coverage fastCoverage0456 pairing0456 template0456 witness0456

theorem coverage0456 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0456) (maskBits m))
    cores template0456 witness0456 := by
  rw [← coresFast_eq]
  exact fastCoverage0456

theorem coverageSize0456 : ∀ q : Pattern,
    (cores (witness0456 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0456 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0456
#print axioms coverageSize0456

noncomputable def pairing0457 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0457 : List (Fin 4935) := templateData0457

noncomputable def witness0457 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4044) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2749) else (if t 3 = 0 then 3236 else if t 3 = 1 then 3234 else 3342)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 536) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 535) else (if t 3 = 0 then 1651 else if t 3 = 1 then 1647 else 553)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1084 else 601) else if t 2 = 1 then (if t 3 = 0 then 1090 else if t 3 = 1 then 1078 else 595) else (if t 3 = 0 then 1094 else if t 3 = 1 then 1080 else 597))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 241) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 240) else (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 260)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2613) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3843) else (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3846)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2651) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3856) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3853 else 3857))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 33 else 920) else if t 2 = 1 then (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 919) else (if t 3 = 0 then 54 else if t 3 = 1 then 52 else 923)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2899) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3848) else (if t 3 = 0 then 3838 else if t 3 = 1 then 3837 else 3850)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2503 else 3184) else if t 2 = 1 then (if t 3 = 0 then 4039 else if t 3 = 1 then 3854 else 3858) else (if t 3 = 0 then 4040 else if t 3 = 1 then 3855 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4395 else (if jt.2.val < 2 then 4405 else 4406)) else (if jt.2.val < 4 then 4402 else (if jt.2.val < 5 then 4404 else 4403))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4293 else (if jt.2.val < 2 then 4295 else 4298)) else (if jt.2.val < 4 then 4294 else (if jt.2.val < 5 then 4297 else 4296)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4449 else (if jt.2.val < 2 then 4453 else 4454)) else (if jt.2.val < 4 then 4450 else (if jt.2.val < 5 then 4452 else 4451))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4071 else (if jt.2.val < 2 then 4085 else 4076)) else (if jt.2.val < 4 then 4080 else (if jt.2.val < 5 then 4081 else 4069)))))

checked_coverage fastCoverage0457 pairing0457 template0457 witness0457

theorem coverage0457 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0457) (maskBits m))
    cores template0457 witness0457 := by
  rw [← coresFast_eq]
  exact fastCoverage0457

theorem coverageSize0457 : ∀ q : Pattern,
    (cores (witness0457 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0457 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0457
#print axioms coverageSize0457

noncomputable def pairing0458 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0458 : List (Fin 4935) := templateData0458

noncomputable def witness0458 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3174) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2769) else (if t 3 = 0 then 4066 else if t 3 = 1 then 4064 else 3946)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 143) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 142) else (if t 3 = 0 then 1881 else if t 3 = 1 then 1877 else 158)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 87 else 904) else if t 2 = 1 then (if t 3 = 0 then 88 else if t 3 = 1 then 86 else 898) else (if t 3 = 0 then 95 else if t 3 = 1 then 94 else 900))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 637) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 636) else (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 651)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2623) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3291) else (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3292)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2717 else 2904) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3295 else 3299) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3296 else 3300))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1040 else 665) else if t 2 = 1 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 664) else (if t 3 = 0 then 1057 else if t 3 = 1 then 1055 else 671)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2637) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3276 else 3293) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3279 else 3294)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2724 else 4045) else if t 2 = 1 then (if t 3 = 0 then 3167 else if t 3 = 1 then 3297 else 3301) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3298 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4368 else (if jt.2.val < 2 then 4378 else 4379)) else (if jt.2.val < 4 then 4375 else (if jt.2.val < 5 then 4377 else 4376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3636 else (if jt.2.val < 2 then 3638 else 3641)) else (if jt.2.val < 4 then 3637 else (if jt.2.val < 5 then 3640 else 3639)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4568 else (if jt.2.val < 2 then 4574 else 4571)) else (if jt.2.val < 4 then 4572 else (if jt.2.val < 5 then 4573 else 4566))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3358 else (if jt.2.val < 2 then 3364 else 3365)) else (if jt.2.val < 4 then 3359 else (if jt.2.val < 5 then 3361 else 3360)))))

checked_coverage fastCoverage0458 pairing0458 template0458 witness0458

theorem coverage0458 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0458) (maskBits m))
    cores template0458 witness0458 := by
  rw [← coresFast_eq]
  exact fastCoverage0458

theorem coverageSize0458 : ∀ q : Pattern,
    (cores (witness0458 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0458 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0458
#print axioms coverageSize0458

noncomputable def pairing0459 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0459 : List (Fin 4935) := templateData0459

noncomputable def witness0459 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3320) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 2768) else (if t 3 = 0 then 3965 else if t 3 = 1 then 3963 else 4058)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 141) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 140) else (if t 3 = 0 then 1650 else if t 3 = 1 then 1646 else 157)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 868 else 205) else if t 2 = 1 then (if t 3 = 0 then 874 else if t 3 = 1 then 862 else 199) else (if t 3 = 0 then 878 else if t 3 = 1 then 864 else 201))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 635) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 634) else (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 650)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2622) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3089) else (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3092)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2956 else 2652) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3098 else 3102) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3099 else 3103))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 439 else 1136) else if t 2 = 1 then (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 1135) else (if t 3 = 0 then 456 else if t 3 = 1 then 454 else 1139)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2900) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3080 else 3094) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3083 else 3096)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2504 else 3928) else if t 2 = 1 then (if t 3 = 0 then 3315 else if t 3 = 1 then 3100 else 3104) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3101 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4314 else (if jt.2.val < 2 then 4324 else 4325)) else (if jt.2.val < 4 then 4321 else (if jt.2.val < 5 then 4323 else 4322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3642 else (if jt.2.val < 2 then 3644 else 3647)) else (if jt.2.val < 4 then 3643 else (if jt.2.val < 5 then 3646 else 3645)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4451 else (if jt.2.val < 2 then 4463 else 4454)) else (if jt.2.val < 4 then 4461 else (if jt.2.val < 5 then 4462 else 4449))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3360 else (if jt.2.val < 2 then 3374 else 3365)) else (if jt.2.val < 4 then 3369 else (if jt.2.val < 5 then 3370 else 3358)))))

checked_coverage fastCoverage0459 pairing0459 template0459 witness0459

theorem coverage0459 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0459) (maskBits m))
    cores template0459 witness0459 := by
  rw [← coresFast_eq]
  exact fastCoverage0459

theorem coverageSize0459 : ∀ q : Pattern,
    (cores (witness0459 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0459 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0459
#print axioms coverageSize0459

noncomputable def pairing0460 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0460 : List (Fin 4935) := templateData0460

noncomputable def witness0460 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 384 else 932) else if t 2 = 1 then (if t 3 = 0 then 386 else if t 3 = 1 then 382 else 928) else (if t 3 = 0 then 396 else if t 3 = 1 then 394 else 929)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 379 else if t 3 = 1 then 356 else 358) else if t 2 = 1 then (if t 3 = 0 then 371 else if t 3 = 1 then 336 else 342) else (if t 3 = 0 then 372 else if t 3 = 1 then 339 else 343)) else (if t 2 = 0 then (if t 3 = 0 then 4036 else if t 3 = 1 then 3929 else 3930) else if t 2 = 1 then (if t 3 = 0 then 2737 else if t 3 = 1 then 2728 else 2731) else (if t 3 = 0 then 3344 else if t 3 = 1 then 3203 else 3205))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 383 else 930) else if t 2 = 1 then (if t 3 = 0 then 385 else if t 3 = 1 then 381 else 924) else (if t 3 = 0 then 395 else if t 3 = 1 then 393 else 926)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 375 else if t 3 = 1 then 346 else 352) else if t 2 = 1 then (if t 3 = 0 then 363 else if t 3 = 1 then 318 else 328) else (if t 3 = 0 then 365 else if t 3 = 1 then 322 else 330)) else (if t 2 = 0 then (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 353) else if t 2 = 1 then (if t 3 = 0 then 364 else if t 3 = 1 then 320 else 329) else (if t 3 = 0 then 366 else if t 3 = 1 then 323 else 331))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 401 else 3345) else if t 2 = 1 then (if t 3 = 0 then 1500 else if t 3 = 1 then 399 else 1788) else (if t 3 = 0 then 3952 else if t 3 = 1 then 405 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 894 else if t 3 = 1 then 350 else 354) else if t 2 = 1 then (if t 3 = 0 then 888 else if t 3 = 1 then 324 else 332) else (if t 3 = 0 then 890 else if t 3 = 1 then 326 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 895 else if t 3 = 1 then 351 else 355) else if t 2 = 1 then (if t 3 = 0 then 889 else if t 3 = 1 then 325 else 333) else (if t 3 = 0 then 891 else if t 3 = 1 then 327 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4314 else (if jt.2.val < 2 then 4366 else 4325)) else (if jt.2.val < 4 then 4365 else (if jt.2.val < 5 then 4367 else 4322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4290 else (if jt.2.val < 2 then 4301 else 4292)) else (if jt.2.val < 4 then 4299 else (if jt.2.val < 5 then 4300 else 4287)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 312 else (if jt.2.val < 2 then 314 else 349)) else (if jt.2.val < 4 then 313 else (if jt.2.val < 5 then 348 else 321))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1247 else (if jt.2.val < 2 then 1249 else 1253)) else (if jt.2.val < 4 then 1248 else (if jt.2.val < 5 then 1252 else 1250)))))

checked_coverage fastCoverage0460 pairing0460 template0460 witness0460

theorem coverage0460 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0460) (maskBits m))
    cores template0460 witness0460 := by
  rw [← coresFast_eq]
  exact fastCoverage0460

theorem coverageSize0460 : ∀ q : Pattern,
    (cores (witness0460 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0460 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0460
#print axioms coverageSize0460

noncomputable def pairing0461 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0461 : List (Fin 4935) := templateData0461

noncomputable def witness0461 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 1004 else 308) else if t 2 = 1 then (if t 3 = 0 then 1006 else if t 3 = 1 then 1000 else 304) else (if t 3 = 0 then 1012 else if t 3 = 1 then 1001 else 305)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 995 else if t 3 = 1 then 977 else 979) else if t 2 = 1 then (if t 3 = 0 then 991 else if t 3 = 1 then 957 else 963) else (if t 3 = 0 then 992 else if t 3 = 1 then 960 else 964)) else (if t 2 = 0 then (if t 3 = 0 then 3905 else if t 3 = 1 then 4046 else 4047) else if t 2 = 1 then (if t 3 = 0 then 2979 else if t 3 = 1 then 2970 else 2973) else (if t 3 = 0 then 3226 else if t 3 = 1 then 3338 else 3340))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 1002 else 306) else if t 2 = 1 then (if t 3 = 0 then 1005 else if t 3 = 1 then 996 else 300) else (if t 3 = 0 then 1011 else if t 3 = 1 then 998 else 302)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 993 else if t 3 = 1 then 967 else 973) else if t 2 = 1 then (if t 3 = 0 then 987 else if t 3 = 1 then 939 else 949) else (if t 3 = 0 then 989 else if t 3 = 1 then 943 else 951)) else (if t 2 = 0 then (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 974) else if t 2 = 1 then (if t 3 = 0 then 988 else if t 3 = 1 then 941 else 950) else (if t 3 = 0 then 990 else if t 3 = 1 then 944 else 952))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 102 else 3229) else if t 2 = 1 then (if t 3 = 0 then 1806 else if t 3 = 1 then 96 else 1476) else (if t 3 = 0 then 4059 else if t 3 = 1 then 98 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 176 else if t 3 = 1 then 971 else 975) else if t 2 = 1 then (if t 3 = 0 then 166 else if t 3 = 1 then 945 else 953) else (if t 3 = 0 then 168 else if t 3 = 1 then 947 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 177 else if t 3 = 1 then 972 else 976) else if t 2 = 1 then (if t 3 = 0 then 167 else if t 3 = 1 then 946 else 954) else (if t 3 = 0 then 169 else if t 3 = 1 then 948 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4368 else (if jt.2.val < 2 then 4393 else 4379)) else (if jt.2.val < 4 then 4392 else (if jt.2.val < 5 then 4394 else 4376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4296 else (if jt.2.val < 2 then 4304 else 4298)) else (if jt.2.val < 4 then 4302 else (if jt.2.val < 5 then 4303 else 4293)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 933 else (if jt.2.val < 2 then 935 else 970)) else (if jt.2.val < 4 then 934 else (if jt.2.val < 5 then 969 else 942))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1250 else (if jt.2.val < 2 then 1257 else 1253)) else (if jt.2.val < 4 then 1256 else (if jt.2.val < 5 then 1259 else 1247)))))

checked_coverage fastCoverage0461 pairing0461 template0461 witness0461

theorem coverage0461 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0461) (maskBits m))
    cores template0461 witness0461 := by
  rw [← coresFast_eq]
  exact fastCoverage0461

theorem coverageSize0461 : ∀ q : Pattern,
    (cores (witness0461 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0461 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0461
#print axioms coverageSize0461

noncomputable def pairing0462 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0462 : List (Fin 4935) := templateData0462

noncomputable def witness0462 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 768 else 1148) else if t 2 = 1 then (if t 3 = 0 then 770 else if t 3 = 1 then 766 else 1144) else (if t 3 = 0 then 780 else if t 3 = 1 then 778 else 1145)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 763 else if t 3 = 1 then 740 else 742) else if t 2 = 1 then (if t 3 = 0 then 755 else if t 3 = 1 then 720 else 725) else (if t 3 = 0 then 756 else if t 3 = 1 then 722 else 726)) else (if t 2 = 0 then (if t 3 = 0 then 3312 else if t 3 = 1 then 3191 else 3192) else if t 2 = 1 then (if t 3 = 0 then 2794 else if t 3 = 1 then 2785 else 2788) else (if t 3 = 0 then 4060 else if t 3 = 1 then 3939 else 3941))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 767 else 1146) else if t 2 = 1 then (if t 3 = 0 then 769 else if t 3 = 1 then 765 else 1140) else (if t 3 = 0 then 779 else if t 3 = 1 then 777 else 1142)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 759 else if t 3 = 1 then 732 else 736) else if t 2 = 1 then (if t 3 = 0 then 747 else if t 3 = 1 then 704 else 712) else (if t 3 = 0 then 749 else if t 3 = 1 then 706 else 714)) else (if t 2 = 0 then (if t 3 = 0 then 760 else if t 3 = 1 then 733 else 737) else if t 2 = 1 then (if t 3 = 0 then 748 else if t 3 = 1 then 705 else 713) else (if t 3 = 0 then 750 else if t 3 = 1 then 707 else 715))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 785 else 4061) else if t 2 = 1 then (if t 3 = 0 then 1548 else if t 3 = 1 then 783 else 1824) else (if t 3 = 0 then 3216 else if t 3 = 1 then 789 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1110 else if t 3 = 1 then 734 else 738) else if t 2 = 1 then (if t 3 = 0 then 1104 else if t 3 = 1 then 708 else 716) else (if t 3 = 0 then 1106 else if t 3 = 1 then 710 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 1111 else if t 3 = 1 then 735 else 739) else if t 2 = 1 then (if t 3 = 0 then 1105 else if t 3 = 1 then 709 else 717) else (if t 3 = 0 then 1107 else if t 3 = 1 then 711 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4395 else (if jt.2.val < 2 then 4429 else 4406)) else (if jt.2.val < 4 then 4428 else (if jt.2.val < 5 then 4430 else 4403))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3639 else (if jt.2.val < 2 then 3662 else 3641)) else (if jt.2.val < 4 then 3660 else (if jt.2.val < 5 then 3661 else 3636)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 321 else (if jt.2.val < 2 then 730 else 349)) else (if jt.2.val < 4 then 729 else (if jt.2.val < 5 then 731 else 312))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1281 else (if jt.2.val < 2 then 1283 else 1289)) else (if jt.2.val < 4 then 1282 else (if jt.2.val < 5 then 1288 else 1286)))))

checked_coverage fastCoverage0462 pairing0462 template0462 witness0462

theorem coverage0462 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0462) (maskBits m))
    cores template0462 witness0462 := by
  rw [← coresFast_eq]
  exact fastCoverage0462

theorem coverageSize0462 : ∀ q : Pattern,
    (cores (witness0462 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0462 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0462
#print axioms coverageSize0462

noncomputable def pairing0463 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0463 : List (Fin 4935) := templateData0463

noncomputable def witness0463 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1214 else 698) else if t 2 = 1 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1210 else 694) else (if t 3 = 0 then 1222 else if t 3 = 1 then 1211 else 695)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1205 else if t 3 = 1 then 1187 else 1189) else if t 2 = 1 then (if t 3 = 0 then 1201 else if t 3 = 1 then 1167 else 1172) else (if t 3 = 0 then 1202 else if t 3 = 1 then 1169 else 1173)) else (if t 2 = 0 then (if t 3 = 0 then 3152 else if t 3 = 1 then 3329 else 3330) else if t 2 = 1 then (if t 3 = 0 then 3002 else if t 3 = 1 then 2993 else 2996) else (if t 3 = 0 then 3954 else if t 3 = 1 then 4054 else 4056))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1212 else 696) else if t 2 = 1 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1206 else 690) else (if t 3 = 0 then 1221 else if t 3 = 1 then 1208 else 692)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1203 else if t 3 = 1 then 1179 else 1183) else if t 2 = 1 then (if t 3 = 0 then 1197 else if t 3 = 1 then 1151 else 1159) else (if t 3 = 0 then 1199 else if t 3 = 1 then 1153 else 1161)) else (if t 2 = 0 then (if t 3 = 0 then 1204 else if t 3 = 1 then 1180 else 1184) else if t 2 = 1 then (if t 3 = 0 then 1198 else if t 3 = 1 then 1152 else 1160) else (if t 3 = 0 then 1200 else if t 3 = 1 then 1154 else 1162))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 504 else 3960) else if t 2 = 1 then (if t 3 = 0 then 1836 else if t 3 = 1 then 498 else 1524) else (if t 3 = 0 then 3343 else if t 3 = 1 then 500 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 572 else if t 3 = 1 then 1181 else 1185) else if t 2 = 1 then (if t 3 = 0 then 562 else if t 3 = 1 then 1155 else 1163) else (if t 3 = 0 then 564 else if t 3 = 1 then 1157 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 573 else if t 3 = 1 then 1182 else 1186) else if t 2 = 1 then (if t 3 = 0 then 563 else if t 3 = 1 then 1156 else 1164) else (if t 3 = 0 then 565 else if t 3 = 1 then 1158 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4431 else (if jt.2.val < 2 then 4447 else 4442)) else (if jt.2.val < 4 then 4446 else (if jt.2.val < 5 then 4448 else 4439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3645 else (if jt.2.val < 2 then 3665 else 3647)) else (if jt.2.val < 4 then 3663 else (if jt.2.val < 5 then 3664 else 3642)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 942 else (if jt.2.val < 2 then 1177 else 970)) else (if jt.2.val < 4 then 1176 else (if jt.2.val < 5 then 1178 else 933))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1286 else (if jt.2.val < 2 then 1291 else 1289)) else (if jt.2.val < 4 then 1290 else (if jt.2.val < 5 then 1295 else 1281)))))

checked_coverage fastCoverage0463 pairing0463 template0463 witness0463

theorem coverage0463 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0463) (maskBits m))
    cores template0463 witness0463 := by
  rw [← coresFast_eq]
  exact fastCoverage0463

theorem coverageSize0463 : ∀ q : Pattern,
    (cores (witness0463 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0463 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0463
#print axioms coverageSize0463

noncomputable def pairing0464 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0464 : List (Fin 4935) := templateData0464

noncomputable def witness0464 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 3965) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3235) else (if t 3 = 0 then 3352 else if t 3 = 1 then 3351 else 2547)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1650) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1649) else (if t 3 = 0 then 1882 else if t 3 = 1 then 1880 else 1670)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1611 else 878) else if t 2 = 1 then (if t 3 = 0 then 1612 else if t 3 = 1 then 1610 else 1853) else (if t 3 = 0 then 497 else if t 3 = 1 then 1619 else 2174))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1331) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1330) else (if t 3 = 0 then 1723 else if t 3 = 1 then 1721 else 1355)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3074) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4505) else (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4507)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3161 else 3314) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4518) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4516 else 4520))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2073 else 456) else if t 2 = 1 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2072 else 1344) else (if t 3 = 0 then 841 else if t 3 = 1 then 1735 else 1361)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3465 else 3084) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4506) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4499 else 4513)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 3164 else 3316) else if t 2 = 1 then (if t 3 = 0 then 3916 else if t 3 = 1 then 4515 else 4519) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4517 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4470 else (if jt.2.val < 2 then 4490 else 4491)) else (if jt.2.val < 4 then 4487 else (if jt.2.val < 5 then 4489 else 4488))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4602 else (if jt.2.val < 2 then 4604 else 4607)) else (if jt.2.val < 4 then 4603 else (if jt.2.val < 5 then 4606 else 4605)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4576 else (if jt.2.val < 2 then 4580 else 4581)) else (if jt.2.val < 4 then 4577 else (if jt.2.val < 5 then 4579 else 4578))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4549 else (if jt.2.val < 2 then 4553 else 4554)) else (if jt.2.val < 4 then 4550 else (if jt.2.val < 5 then 4552 else 4551)))))

checked_coverage fastCoverage0464 pairing0464 template0464 witness0464

theorem coverage0464 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0464) (maskBits m))
    cores template0464 witness0464 := by
  rw [← coresFast_eq]
  exact fastCoverage0464

theorem coverageSize0464 : ∀ q : Pattern,
    (cores (witness0464 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0464 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0464
#print axioms coverageSize0464

noncomputable def pairing0465 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0465 : List (Fin 4935) := templateData0465

noncomputable def witness0465 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4530) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 3234) else (if t 3 = 0 then 2751 else if t 3 = 1 then 2749 else 3342)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 1648) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 1647) else (if t 3 = 0 then 539 else if t 3 = 1 then 535 else 553)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1084 else 1690) else if t 2 = 1 then (if t 3 = 0 then 1090 else if t 3 = 1 then 1078 else 1080) else (if t 3 = 0 then 2150 else if t 3 = 1 then 595 else 597))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 1329) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 1328) else (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 260)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 3073) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3827) else (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3846)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2957) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3853) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3856 else 3857))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 33 else 2126) else if t 2 = 1 then (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 52) else (if t 3 = 0 then 1472 else if t 3 = 1 then 919 else 923)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2474) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3837) else (if t 3 = 0 then 3849 else if t 3 = 1 then 3848 else 3850)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2503 else 2505) else if t 2 = 1 then (if t 3 = 0 then 4039 else if t 3 = 1 then 3854 else 3855) else (if t 3 = 0 then 4526 else if t 3 = 1 then 3858 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4395 else (if jt.2.val < 2 then 4405 else 4406)) else (if jt.2.val < 4 then 4402 else (if jt.2.val < 5 then 4404 else 4403))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4293 else (if jt.2.val < 2 then 4295 else 4298)) else (if jt.2.val < 4 then 4294 else (if jt.2.val < 5 then 4297 else 4296)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3804 else (if jt.2.val < 2 then 3842 else 3844)) else (if jt.2.val < 4 then 3839 else (if jt.2.val < 5 then 3841 else 3840))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4551 else (if jt.2.val < 2 then 4562 else 4554)) else (if jt.2.val < 4 then 4560 else (if jt.2.val < 5 then 4561 else 4549)))))

checked_coverage fastCoverage0465 pairing0465 template0465 witness0465

theorem coverage0465 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0465) (maskBits m))
    cores template0465 witness0465 := by
  rw [← coresFast_eq]
  exact fastCoverage0465

theorem coverageSize0465 : ∀ q : Pattern,
    (cores (witness0465 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0465 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0465
#print axioms coverageSize0465

noncomputable def pairing0466 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0466 : List (Fin 4935) := templateData0466

noncomputable def witness0466 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3258 else 2770) else if t 2 = 1 then (if t 3 = 0 then 3254 else if t 3 = 1 then 3250 else 2769) else (if t 3 = 0 then 4537 else if t 3 = 1 then 4064 else 3946)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3256 else 144) else if t 2 = 1 then (if t 3 = 0 then 3252 else if t 3 = 1 then 3248 else 142) else (if t 3 = 0 then 1879 else if t 3 = 1 then 1877 else 158)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 88 else 2129) else if t 2 = 1 then (if t 3 = 0 then 87 else if t 3 = 1 then 86 else 898) else (if t 3 = 0 then 1523 else if t 3 = 1 then 94 else 900))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3257 else 638) else if t 2 = 1 then (if t 3 = 0 then 3253 else if t 3 = 1 then 3249 else 636) else (if t 3 = 0 then 1720 else if t 3 = 1 then 1718 else 651)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3255 else 3091) else if t 2 = 1 then (if t 3 = 0 then 3251 else if t 3 = 1 then 3247 else 3291) else (if t 3 = 0 then 3269 else if t 3 = 1 then 3267 else 3292)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 3165 else 3500) else if t 2 = 1 then (if t 3 = 0 then 2717 else if t 3 = 1 then 3295 else 3299) else (if t 3 = 0 then 2719 else if t 3 = 1 then 3296 else 3300))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1043 else 1520) else if t 2 = 1 then (if t 3 = 0 then 1040 else if t 3 = 1 then 1039 else 664) else (if t 3 = 0 then 2147 else if t 3 = 1 then 1055 else 671)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 3278 else 3095) else if t 2 = 1 then (if t 3 = 0 then 2837 else if t 3 = 1 then 3276 else 3293) else (if t 3 = 0 then 2841 else if t 3 = 1 then 3279 else 3294)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 3167 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2724 else if t 3 = 1 then 3297 else 3301) else (if t 3 = 0 then 2725 else if t 3 = 1 then 3298 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4368 else (if jt.2.val < 2 then 4378 else 4379)) else (if jt.2.val < 4 then 4375 else (if jt.2.val < 5 then 4377 else 4376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3636 else (if jt.2.val < 2 then 3638 else 3641)) else (if jt.2.val < 4 then 3637 else (if jt.2.val < 5 then 3640 else 3639)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4578 else (if jt.2.val < 2 then 4589 else 4581)) else (if jt.2.val < 4 then 4587 else (if jt.2.val < 5 then 4588 else 4576))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3244 else (if jt.2.val < 2 then 3289 else 3290)) else (if jt.2.val < 4 then 3286 else (if jt.2.val < 5 then 3288 else 3287)))))

checked_coverage fastCoverage0466 pairing0466 template0466 witness0466

theorem coverage0466 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0466) (maskBits m))
    cores template0466 witness0466 := by
  rw [← coresFast_eq]
  exact fastCoverage0466

theorem coverageSize0466 : ∀ q : Pattern,
    (cores (witness0466 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0466 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0466
#print axioms coverageSize0466

noncomputable def pairing0467 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0467 : List (Fin 4935) := templateData0467

noncomputable def witness0467 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2598 else 3320) else if t 2 = 1 then (if t 3 = 0 then 2602 else if t 3 = 1 then 2594 else 3172) else (if t 3 = 0 then 3925 else if t 3 = 1 then 3923 else 4541)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2596 else 141) else if t 2 = 1 then (if t 3 = 0 then 2600 else if t 3 = 1 then 2592 else 139) else (if t 3 = 0 then 538 else if t 3 = 1 then 534 else 1537)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2104 else 205) else if t 2 = 1 then (if t 3 = 0 then 2107 else if t 3 = 1 then 2101 else 193) else (if t 3 = 0 then 1120 else if t 3 = 1 then 589 else 1546))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2597 else 635) else if t 2 = 1 then (if t 3 = 0 then 2601 else if t 3 = 1 then 2593 else 633) else (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 1463)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2595 else 2622) else if t 2 = 1 then (if t 3 = 0 then 2599 else if t 3 = 1 then 2591 else 2620) else (if t 3 = 0 then 2614 else if t 3 = 1 then 2611 else 2625)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2650 else 2652) else if t 2 = 1 then (if t 3 = 0 then 2902 else if t 3 = 1 then 2640 else 2642) else (if t 3 = 0 then 2903 else if t 3 = 1 then 2641 else 2643))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1583 else 1136) else if t 2 = 1 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1581 else 663) else (if t 3 = 0 then 275 else if t 3 = 1 then 273 else 2171)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2897 else 2900) else if t 2 = 1 then (if t 3 = 0 then 2632 else if t 3 = 1 then 2629 else 2636) else (if t 3 = 0 then 2635 else if t 3 = 1 then 2634 else 2638)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3183 else 3928) else if t 2 = 1 then (if t 3 = 0 then 3321 else if t 3 = 1 then 2644 else 2646) else (if t 3 = 0 then 3322 else if t 3 = 1 then 2645 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4338 else (if jt.2.val < 2 then 4342 else 4343)) else (if jt.2.val < 4 then 4339 else (if jt.2.val < 5 then 4341 else 4340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3678 else (if jt.2.val < 2 then 3680 else 3683)) else (if jt.2.val < 4 then 3679 else (if jt.2.val < 5 then 3682 else 3681)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3840 else (if jt.2.val < 2 then 3924 else 3844)) else (if jt.2.val < 4 then 3921 else (if jt.2.val < 5 then 3922 else 3804))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3287 else (if jt.2.val < 2 then 3319 else 3290)) else (if jt.2.val < 4 then 3317 else (if jt.2.val < 5 then 3318 else 3244)))))

checked_coverage fastCoverage0467 pairing0467 template0467 witness0467

theorem coverage0467 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0467) (maskBits m))
    cores template0467 witness0467 := by
  rw [← coresFast_eq]
  exact fastCoverage0467

theorem coverageSize0467 : ∀ q : Pattern,
    (cores (witness0467 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0467 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0467
#print axioms coverageSize0467

noncomputable def pairing0468 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0468 : List (Fin 4935) := templateData0468

noncomputable def witness0468 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1437 else 1222) else if t 2 = 1 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1435 else 1777) else (if t 3 = 0 then 396 else if t 3 = 1 then 1450 else 2119)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1432 else if t 3 = 1 then 1422 else 1202) else if t 2 = 1 then (if t 3 = 0 then 1427 else if t 3 = 1 then 1408 else 1414) else (if t 3 = 0 then 372 else if t 3 = 1 then 1412 else 1416)) else (if t 2 = 0 then (if t 3 = 0 then 4525 else if t 3 = 1 then 3953 else 3954) else if t 2 = 1 then (if t 3 = 0 then 3225 else if t 3 = 1 then 3219 else 2855) else (if t 3 = 0 then 3344 else if t 3 = 1 then 2482 else 2485))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1436 else 1221) else if t 2 = 1 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1434 else 1776) else (if t 3 = 0 then 395 else if t 3 = 1 then 1449 else 2118)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1428 else if t 3 = 1 then 1418 else 1199) else if t 2 = 1 then (if t 3 = 0 then 1423 else if t 3 = 1 then 1389 else 1400) else (if t 3 = 0 then 365 else if t 3 = 1 then 1396 else 1404)) else (if t 2 = 0 then (if t 3 = 0 then 1429 else if t 3 = 1 then 1419 else 1200) else if t 2 = 1 then (if t 3 = 0 then 1424 else if t 3 = 1 then 1391 else 1401) else (if t 3 = 0 then 366 else if t 3 = 1 then 1397 else 1405))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 590 else 3343) else if t 2 = 1 then (if t 3 = 0 then 194 else if t 3 = 1 then 1446 else 1779) else (if t 3 = 0 then 3952 else if t 3 = 1 then 1452 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2115 else if t 3 = 1 then 558 else 564) else if t 2 = 1 then (if t 3 = 0 then 162 else if t 3 = 1 then 1393 else 1402) else (if t 3 = 0 then 890 else if t 3 = 1 then 1398 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 2116 else if t 3 = 1 then 559 else 565) else if t 2 = 1 then (if t 3 = 0 then 163 else if t 3 = 1 then 1394 else 1403) else (if t 3 = 0 then 891 else if t 3 = 1 then 1399 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4338 else (if jt.2.val < 2 then 4357 else 4343)) else (if jt.2.val < 4 then 4356 else (if jt.2.val < 5 then 4358 else 4340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4605 else (if jt.2.val < 2 then 4610 else 4607)) else (if jt.2.val < 4 then 4608 else (if jt.2.val < 5 then 4609 else 4602)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1983 else (if jt.2.val < 2 then 1985 else 1992)) else (if jt.2.val < 4 then 1984 else (if jt.2.val < 5 then 1991 else 1990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1766 else (if jt.2.val < 2 then 1768 else 1772)) else (if jt.2.val < 4 then 1767 else (if jt.2.val < 5 then 1771 else 1770)))))

checked_coverage fastCoverage0468 pairing0468 template0468 witness0468

theorem coverage0468 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0468) (maskBits m))
    cores template0468 witness0468 := by
  rw [← coresFast_eq]
  exact fastCoverage0468

theorem coverageSize0468 : ∀ q : Pattern,
    (cores (witness0468 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0468 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0468
#print axioms coverageSize0468

noncomputable def pairing0469 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0469 : List (Fin 4935) := templateData0469

noncomputable def witness0469 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 1004 else 1376) else if t 2 = 1 then (if t 3 = 0 then 1006 else if t 3 = 1 then 1000 else 1001) else (if t 3 = 0 then 2140 else if t 3 = 1 then 304 else 305)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 995 else if t 3 = 1 then 977 else 1801) else if t 2 = 1 then (if t 3 = 0 then 991 else if t 3 = 1 then 957 else 960) else (if t 3 = 0 then 373 else if t 3 = 1 then 963 else 964)) else (if t 2 = 0 then (if t 3 = 0 then 3905 else if t 3 = 1 then 4046 else 4532) else if t 2 = 1 then (if t 3 = 0 then 2979 else if t 3 = 1 then 2970 else 3338) else (if t 3 = 0 then 2738 else if t 3 = 1 then 2973 else 3340))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 1002 else 1374) else if t 2 = 1 then (if t 3 = 0 then 1005 else if t 3 = 1 then 996 else 998) else (if t 3 = 0 then 2139 else if t 3 = 1 then 300 else 302)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 993 else if t 3 = 1 then 967 else 1795) else if t 2 = 1 then (if t 3 = 0 then 987 else if t 3 = 1 then 939 else 943) else (if t 3 = 0 then 367 else if t 3 = 1 then 949 else 951)) else (if t 2 = 0 then (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 1796) else if t 2 = 1 then (if t 3 = 0 then 988 else if t 3 = 1 then 941 else 944) else (if t 3 = 0 then 368 else if t 3 = 1 then 950 else 952))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 102 else 2744) else if t 2 = 1 then (if t 3 = 0 then 1806 else if t 3 = 1 then 96 else 98) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1476 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 176 else if t 3 = 1 then 971 else 2136) else if t 2 = 1 then (if t 3 = 0 then 166 else if t 3 = 1 then 945 else 947) else (if t 3 = 0 then 1494 else if t 3 = 1 then 953 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 177 else if t 3 = 1 then 972 else 2137) else if t 2 = 1 then (if t 3 = 0 then 167 else if t 3 = 1 then 946 else 948) else (if t 3 = 0 then 1495 else if t 3 = 1 then 954 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4368 else (if jt.2.val < 2 then 4393 else 4379)) else (if jt.2.val < 4 then 4392 else (if jt.2.val < 5 then 4394 else 4376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4296 else (if jt.2.val < 2 then 4304 else 4298)) else (if jt.2.val < 4 then 4302 else (if jt.2.val < 5 then 4303 else 4293)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2130 else (if jt.2.val < 2 then 2132 else 2135)) else (if jt.2.val < 4 then 2131 else (if jt.2.val < 5 then 2134 else 2133))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1770 else (if jt.2.val < 2 then 1804 else 1772)) else (if jt.2.val < 4 then 1803 else (if jt.2.val < 5 then 1805 else 1766)))))

checked_coverage fastCoverage0469 pairing0469 template0469 witness0469

theorem coverage0469 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0469) (maskBits m))
    cores template0469 witness0469 := by
  rw [← coresFast_eq]
  exact fastCoverage0469

theorem coverageSize0469 : ∀ q : Pattern,
    (cores (witness0469 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0469 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0469
#print axioms coverageSize0469

noncomputable def pairing0470 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0470 : List (Fin 4935) := templateData0470

noncomputable def witness0470 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 770 else 2161) else if t 2 = 1 then (if t 3 = 0 then 768 else if t 3 = 1 then 766 else 1144) else (if t 3 = 0 then 1498 else if t 3 = 1 then 778 else 1145)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 763 else if t 3 = 1 then 755 else 757) else if t 2 = 1 then (if t 3 = 0 then 740 else if t 3 = 1 then 720 else 725) else (if t 3 = 0 then 1489 else if t 3 = 1 then 722 else 726)) else (if t 2 = 0 then (if t 3 = 0 then 3312 else if t 3 = 1 then 2794 else 2795) else if t 2 = 1 then (if t 3 = 0 then 3191 else if t 3 = 1 then 2785 else 2788) else (if t 3 = 0 then 4539 else if t 3 = 1 then 3939 else 3941))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 769 else 2160) else if t 2 = 1 then (if t 3 = 0 then 767 else if t 3 = 1 then 765 else 1140) else (if t 3 = 0 then 1497 else if t 3 = 1 then 777 else 1142)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 759 else if t 3 = 1 then 747 else 751) else if t 2 = 1 then (if t 3 = 0 then 732 else if t 3 = 1 then 704 else 712) else (if t 3 = 0 then 1483 else if t 3 = 1 then 706 else 714)) else (if t 2 = 0 then (if t 3 = 0 then 760 else if t 3 = 1 then 748 else 752) else if t 2 = 1 then (if t 3 = 0 then 733 else if t 3 = 1 then 705 else 713) else (if t 3 = 0 then 1484 else if t 3 = 1 then 707 else 715))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 1548 else 4542) else if t 2 = 1 then (if t 3 = 0 then 785 else if t 3 = 1 then 783 else 1824) else (if t 3 = 0 then 2801 else if t 3 = 1 then 789 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1110 else if t 3 = 1 then 1104 else 1542) else if t 2 = 1 then (if t 3 = 0 then 734 else if t 3 = 1 then 708 else 716) else (if t 3 = 0 then 2157 else if t 3 = 1 then 710 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 1111 else if t 3 = 1 then 1105 else 1543) else if t 2 = 1 then (if t 3 = 0 then 735 else if t 3 = 1 then 709 else 717) else (if t 3 = 0 then 2158 else if t 3 = 1 then 711 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4395 else (if jt.2.val < 2 then 4429 else 4406)) else (if jt.2.val < 4 then 4428 else (if jt.2.val < 5 then 4430 else 4403))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3639 else (if jt.2.val < 2 then 3662 else 3641)) else (if jt.2.val < 4 then 3660 else (if jt.2.val < 5 then 3661 else 3636)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1990 else (if jt.2.val < 2 then 2029 else 1992)) else (if jt.2.val < 4 then 2028 else (if jt.2.val < 5 then 2030 else 1983))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2151 else (if jt.2.val < 2 then 2153 else 2156)) else (if jt.2.val < 4 then 2152 else (if jt.2.val < 5 then 2155 else 2154)))))

checked_coverage fastCoverage0470 pairing0470 template0470 witness0470

theorem coverage0470 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0470) (maskBits m))
    cores template0470 witness0470 := by
  rw [← coresFast_eq]
  exact fastCoverage0470

theorem coverageSize0470 : ∀ q : Pattern,
    (cores (witness0470 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0470 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0470
#print axioms coverageSize0470

noncomputable def pairing0471 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0471 : List (Fin 4935) := templateData0471

noncomputable def witness0471 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2225 else 698) else if t 2 = 1 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2222 else 688) else (if t 3 = 0 then 932 else if t 3 = 1 then 298 else 1475)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2207 else 1189) else if t 2 = 1 then (if t 3 = 0 then 2213 else if t 3 = 1 then 2193 else 2196) else (if t 3 = 0 then 358 else if t 3 = 1 then 2195 else 2197)) else (if t 2 = 0 then (if t 3 = 0 then 2706 else if t 3 = 1 then 2939 else 3330) else if t 2 = 1 then (if t 3 = 0 then 2690 else if t 3 = 1 then 3528 else 3530) else (if t 3 = 0 then 3930 else if t 3 = 1 then 4211 else 4546))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2223 else 696) else if t 2 = 1 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2220 else 684) else (if t 3 = 0 then 930 else if t 3 = 1 then 294 else 1473)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2205 else 1183) else if t 2 = 1 then (if t 3 = 0 then 2211 else if t 3 = 1 then 2177 else 2181) else (if t 3 = 0 then 352 else if t 3 = 1 then 2179 else 2183)) else (if t 2 = 0 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2206 else 1184) else if t 2 = 1 then (if t 3 = 0 then 2212 else if t 3 = 1 then 2178 else 2182) else (if t 3 = 0 then 353 else if t 3 = 1 then 2180 else 2184))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1620 else 3960) else if t 2 = 1 then (if t 3 = 0 then 1854 else if t 3 = 1 then 1614 else 686) else (if t 3 = 0 then 3345 else if t 3 = 1 then 296 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1673 else if t 3 = 1 then 1889 else 1185) else if t 2 = 1 then (if t 3 = 0 then 1658 else if t 3 = 1 then 2185 else 2189) else (if t 3 = 0 then 354 else if t 3 = 1 then 2187 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 1674 else if t 3 = 1 then 1890 else 1186) else if t 2 = 1 then (if t 3 = 0 then 1659 else if t 3 = 1 then 2186 else 2190) else (if t 3 = 0 then 355 else if t 3 = 1 then 2188 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4470 else (if jt.2.val < 2 then 4544 else 4491)) else (if jt.2.val < 4 then 4543 else (if jt.2.val < 5 then 4545 else 4488))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3681 else (if jt.2.val < 2 then 3689 else 3683)) else (if jt.2.val < 4 then 3687 else (if jt.2.val < 5 then 3688 else 3678)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2133 else (if jt.2.val < 2 then 2203 else 2135)) else (if jt.2.val < 4 then 2202 else (if jt.2.val < 5 then 2204 else 2130))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2154 else (if jt.2.val < 2 then 2209 else 2156)) else (if jt.2.val < 4 then 2208 else (if jt.2.val < 5 then 2210 else 2151)))))

checked_coverage fastCoverage0471 pairing0471 template0471 witness0471

theorem coverage0471 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0471) (maskBits m))
    cores template0471 witness0471 := by
  rw [← coresFast_eq]
  exact fastCoverage0471

theorem coverageSize0471 : ∀ q : Pattern,
    (cores (witness0471 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0471 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0471
#print axioms coverageSize0471

noncomputable def pairing0472 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0472 : List (Fin 4935) := templateData0472

noncomputable def witness0472 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 4066) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3351) else (if t 3 = 0 then 3236 else if t 3 = 1 then 3235 else 2547)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1881) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1880) else (if t 3 = 0 then 1651 else if t 3 = 1 then 1649 else 1670)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1611 else 95) else if t 2 = 1 then (if t 3 = 0 then 1612 else if t 3 = 1 then 1610 else 1619) else (if t 3 = 0 then 1094 else if t 3 = 1 then 1853 else 2174))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1722) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1721) else (if t 3 = 0 then 1332 else if t 3 = 1 then 1330 else 1355)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3270) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4498) else (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4507)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3161 else 3166) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4516) else (if t 3 = 0 then 4038 else if t 3 = 1 then 4518 else 4520))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2073 else 1057) else if t 2 = 1 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2072 else 1735) else (if t 3 = 0 then 54 else if t 3 = 1 then 1344 else 1361)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3465 else 3280) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4499) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4506 else 4513)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 3164 else 3168) else if t 2 = 1 then (if t 3 = 0 then 3916 else if t 3 = 1 then 4515 else 4517) else (if t 3 = 0 then 4040 else if t 3 = 1 then 4519 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4470 else (if jt.2.val < 2 then 4490 else 4491)) else (if jt.2.val < 4 then 4487 else (if jt.2.val < 5 then 4489 else 4488))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4602 else (if jt.2.val < 2 then 4604 else 4607)) else (if jt.2.val < 4 then 4603 else (if jt.2.val < 5 then 4606 else 4605)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4468 else (if jt.2.val < 2 then 4503 else 4504)) else (if jt.2.val < 4 then 4500 else (if jt.2.val < 5 then 4502 else 4501))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4593 else (if jt.2.val < 2 then 4597 else 4598)) else (if jt.2.val < 4 then 4594 else (if jt.2.val < 5 then 4596 else 4595)))))

checked_coverage fastCoverage0472 pairing0472 template0472 witness0472

theorem coverage0472 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0472) (maskBits m))
    cores template0472 witness0472 := by
  rw [← coresFast_eq]
  exact fastCoverage0472

theorem coverageSize0472 : ∀ q : Pattern,
    (cores (witness0472 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0472 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0472
#print axioms coverageSize0472

noncomputable def pairing0473 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0473 : List (Fin 4935) := templateData0473

noncomputable def witness0473 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 4537) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 3350) else (if t 3 = 0 then 2751 else if t 3 = 1 then 2750 else 3210)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 1879) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 1878) else (if t 3 = 0 then 539 else if t 3 = 1 then 537 else 554)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 489 else 1523) else if t 2 = 1 then (if t 3 = 0 then 490 else if t 3 = 1 then 488 else 496) else (if t 3 = 0 then 2150 else if t 3 = 1 then 1114 else 1116))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 1720) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 1719) else (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 261)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 3269) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 3993) else (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4016)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2719) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4020) else (if t 3 = 0 then 4191 else if t 3 = 1 then 4023 else 4024))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 820 else 2147) else if t 2 = 1 then (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 839) else (if t 3 = 0 then 1472 else if t 3 = 1 then 274 else 281)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2841) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4003) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4017 else 4018)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2723 else 2725) else if t 2 = 1 then (if t 3 = 0 then 3919 else if t 3 = 1 then 4021 else 4022) else (if t 3 = 0 then 4526 else if t 3 = 1 then 4025 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4431 else (if jt.2.val < 2 then 4441 else 4442)) else (if jt.2.val < 4 then 4438 else (if jt.2.val < 5 then 4440 else 4439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4287 else (if jt.2.val < 2 then 4289 else 4292)) else (if jt.2.val < 4 then 4288 else (if jt.2.val < 5 then 4291 else 4290)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3970 else (if jt.2.val < 2 then 4013 else 4014)) else (if jt.2.val < 4 then 4010 else (if jt.2.val < 5 then 4012 else 4011))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4595 else (if jt.2.val < 2 then 4601 else 4598)) else (if jt.2.val < 4 then 4599 else (if jt.2.val < 5 then 4600 else 4593)))))

checked_coverage fastCoverage0473 pairing0473 template0473 witness0473

theorem coverage0473 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0473) (maskBits m))
    cores template0473 witness0473 := by
  rw [← coresFast_eq]
  exact fastCoverage0473

theorem coverageSize0473 : ∀ q : Pattern,
    (cores (witness0473 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0473 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0473
#print axioms coverageSize0473

noncomputable def pairing0474 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0474 : List (Fin 4935) := templateData0474

noncomputable def witness0474 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3062 else 2770) else if t 2 = 1 then (if t 3 = 0 then 3058 else if t 3 = 1 then 3054 else 2768) else (if t 3 = 0 then 4530 else if t 3 = 1 then 3963 else 4058)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3060 else 144) else if t 2 = 1 then (if t 3 = 0 then 3056 else if t 3 = 1 then 3052 else 140) else (if t 3 = 0 then 1648 else if t 3 = 1 then 1646 else 157)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 874 else 2129) else if t 2 = 1 then (if t 3 = 0 then 868 else if t 3 = 1 then 862 else 199) else (if t 3 = 0 then 1690 else if t 3 = 1 then 864 else 201))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3061 else 638) else if t 2 = 1 then (if t 3 = 0 then 3057 else if t 3 = 1 then 3053 else 634) else (if t 3 = 0 then 1329 else if t 3 = 1 then 1327 else 650)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3059 else 3091) else if t 2 = 1 then (if t 3 = 0 then 3055 else if t 3 = 1 then 3051 else 3089) else (if t 3 = 0 then 3073 else if t 3 = 1 then 3071 else 3092)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 3313 else 3500) else if t 2 = 1 then (if t 3 = 0 then 2956 else if t 3 = 1 then 3098 else 3102) else (if t 3 = 0 then 2957 else if t 3 = 1 then 3099 else 3103))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 442 else 1520) else if t 2 = 1 then (if t 3 = 0 then 439 else if t 3 = 1 then 438 else 1135) else (if t 3 = 0 then 2126 else if t 3 = 1 then 454 else 1139)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 3082 else 3095) else if t 2 = 1 then (if t 3 = 0 then 2470 else if t 3 = 1 then 3080 else 3094) else (if t 3 = 0 then 2474 else if t 3 = 1 then 3083 else 3096)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 3315 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2504 else if t 3 = 1 then 3100 else 3104) else (if t 3 = 0 then 2505 else if t 3 = 1 then 3101 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4314 else (if jt.2.val < 2 then 4324 else 4325)) else (if jt.2.val < 4 then 4321 else (if jt.2.val < 5 then 4323 else 4322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3642 else (if jt.2.val < 2 then 3644 else 3647)) else (if jt.2.val < 4 then 3643 else (if jt.2.val < 5 then 3646 else 3645)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4501 else (if jt.2.val < 2 then 4529 else 4504)) else (if jt.2.val < 4 then 4527 else (if jt.2.val < 5 then 4528 else 4468))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3048 else (if jt.2.val < 2 then 3088 else 3090)) else (if jt.2.val < 4 then 3085 else (if jt.2.val < 5 then 3087 else 3086)))))

checked_coverage fastCoverage0474 pairing0474 template0474 witness0474

theorem coverage0474 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0474) (maskBits m))
    cores template0474 witness0474 := by
  rw [← coresFast_eq]
  exact fastCoverage0474

theorem coverageSize0474 : ∀ q : Pattern,
    (cores (witness0474 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0474 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0474
#print axioms coverageSize0474

noncomputable def pairing0475 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0475 : List (Fin 4935) := templateData0475

noncomputable def witness0475 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2602 else 3174) else if t 2 = 1 then (if t 3 = 0 then 2598 else if t 3 = 1 then 2594 else 3172) else (if t 3 = 0 then 4044 else if t 3 = 1 then 3923 else 4541)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2600 else 143) else if t 2 = 1 then (if t 3 = 0 then 2596 else if t 3 = 1 then 2592 else 139) else (if t 3 = 0 then 536 else if t 3 = 1 then 534 else 1537)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2107 else 904) else if t 2 = 1 then (if t 3 = 0 then 2104 else if t 3 = 1 then 2101 else 193) else (if t 3 = 0 then 601 else if t 3 = 1 then 589 else 1546))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2601 else 637) else if t 2 = 1 then (if t 3 = 0 then 2597 else if t 3 = 1 then 2593 else 633) else (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 1463)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2599 else 2623) else if t 2 = 1 then (if t 3 = 0 then 2595 else if t 3 = 1 then 2591 else 2620) else (if t 3 = 0 then 2613 else if t 3 = 1 then 2611 else 2625)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2902 else 2904) else if t 2 = 1 then (if t 3 = 0 then 2650 else if t 3 = 1 then 2640 else 2642) else (if t 3 = 0 then 2651 else if t 3 = 1 then 2641 else 2643))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1585 else 665) else if t 2 = 1 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1581 else 663) else (if t 3 = 0 then 920 else if t 3 = 1 then 273 else 2171)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2632 else 2637) else if t 2 = 1 then (if t 3 = 0 then 2897 else if t 3 = 1 then 2629 else 2636) else (if t 3 = 0 then 2899 else if t 3 = 1 then 2634 else 2638)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3321 else 4045) else if t 2 = 1 then (if t 3 = 0 then 3183 else if t 3 = 1 then 2644 else 2646) else (if t 3 = 0 then 3184 else if t 3 = 1 then 2645 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4338 else (if jt.2.val < 2 then 4342 else 4343)) else (if jt.2.val < 4 then 4339 else (if jt.2.val < 5 then 4341 else 4340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3678 else (if jt.2.val < 2 then 3680 else 3683)) else (if jt.2.val < 4 then 3679 else (if jt.2.val < 5 then 3682 else 3681)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4011 else (if jt.2.val < 2 then 4043 else 4014)) else (if jt.2.val < 4 then 4041 else (if jt.2.val < 5 then 4042 else 3970))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3086 else (if jt.2.val < 2 then 3173 else 3090)) else (if jt.2.val < 4 then 3169 else (if jt.2.val < 5 then 3170 else 3048)))))

checked_coverage fastCoverage0475 pairing0475 template0475 witness0475

theorem coverage0475 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0475) (maskBits m))
    cores template0475 witness0475 := by
  rw [← coresFast_eq]
  exact fastCoverage0475

theorem coverageSize0475 : ∀ q : Pattern,
    (cores (witness0475 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0475 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0475
#print axioms coverageSize0475

noncomputable def pairing0476 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0476 : List (Fin 4935) := templateData0476

noncomputable def witness0476 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1437 else 780) else if t 2 = 1 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1435 else 1450) else (if t 3 = 0 then 1012 else if t 3 = 1 then 1777 else 2119)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1432 else if t 3 = 1 then 1422 else 756) else if t 2 = 1 then (if t 3 = 0 then 1427 else if t 3 = 1 then 1408 else 1412) else (if t 3 = 0 then 992 else if t 3 = 1 then 1414 else 1416)) else (if t 2 = 0 then (if t 3 = 0 then 4525 else if t 3 = 1 then 3953 else 4060) else if t 2 = 1 then (if t 3 = 0 then 3225 else if t 3 = 1 then 3219 else 2482) else (if t 3 = 0 then 3226 else if t 3 = 1 then 2855 else 2485))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1436 else 779) else if t 2 = 1 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1434 else 1449) else (if t 3 = 0 then 1011 else if t 3 = 1 then 1776 else 2118)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1428 else if t 3 = 1 then 1418 else 749) else if t 2 = 1 then (if t 3 = 0 then 1423 else if t 3 = 1 then 1389 else 1396) else (if t 3 = 0 then 989 else if t 3 = 1 then 1400 else 1404)) else (if t 2 = 0 then (if t 3 = 0 then 1429 else if t 3 = 1 then 1419 else 750) else if t 2 = 1 then (if t 3 = 0 then 1424 else if t 3 = 1 then 1391 else 1397) else (if t 3 = 0 then 990 else if t 3 = 1 then 1401 else 1405))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 590 else 3216) else if t 2 = 1 then (if t 3 = 0 then 194 else if t 3 = 1 then 1446 else 1452) else (if t 3 = 0 then 4059 else if t 3 = 1 then 1779 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2115 else if t 3 = 1 then 558 else 1106) else if t 2 = 1 then (if t 3 = 0 then 162 else if t 3 = 1 then 1393 else 1398) else (if t 3 = 0 then 168 else if t 3 = 1 then 1402 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 2116 else if t 3 = 1 then 559 else 1107) else if t 2 = 1 then (if t 3 = 0 then 163 else if t 3 = 1 then 1394 else 1399) else (if t 3 = 0 then 169 else if t 3 = 1 then 1403 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4338 else (if jt.2.val < 2 then 4357 else 4343)) else (if jt.2.val < 4 then 4356 else (if jt.2.val < 5 then 4358 else 4340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4605 else (if jt.2.val < 2 then 4610 else 4607)) else (if jt.2.val < 4 then 4608 else (if jt.2.val < 5 then 4609 else 4602)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2280 else (if jt.2.val < 2 then 2282 else 2285)) else (if jt.2.val < 4 then 2281 else (if jt.2.val < 5 then 2284 else 2283))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1380 else (if jt.2.val < 2 then 1382 else 1426)) else (if jt.2.val < 4 then 1381 else (if jt.2.val < 5 then 1425 else 1395)))))

checked_coverage fastCoverage0476 pairing0476 template0476 witness0476

theorem coverage0476 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0476) (maskBits m))
    cores template0476 witness0476 := by
  rw [← coresFast_eq]
  exact fastCoverage0476

theorem coverageSize0476 : ∀ q : Pattern,
    (cores (witness0476 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0476 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0476
#print axioms coverageSize0476

noncomputable def pairing0477 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0477 : List (Fin 4935) := templateData0477

noncomputable def witness0477 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 384 else 1498) else if t 2 = 1 then (if t 3 = 0 then 386 else if t 3 = 1 then 382 else 394) else (if t 3 = 0 then 2140 else if t 3 = 1 then 928 else 929)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 379 else if t 3 = 1 then 356 else 1489) else if t 2 = 1 then (if t 3 = 0 then 371 else if t 3 = 1 then 336 else 339) else (if t 3 = 0 then 373 else if t 3 = 1 then 342 else 343)) else (if t 2 = 0 then (if t 3 = 0 then 4036 else if t 3 = 1 then 3929 else 4539) else if t 2 = 1 then (if t 3 = 0 then 2737 else if t 3 = 1 then 2728 else 3203) else (if t 3 = 0 then 2738 else if t 3 = 1 then 2731 else 3205))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 383 else 1497) else if t 2 = 1 then (if t 3 = 0 then 385 else if t 3 = 1 then 381 else 393) else (if t 3 = 0 then 2139 else if t 3 = 1 then 924 else 926)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 375 else if t 3 = 1 then 346 else 1483) else if t 2 = 1 then (if t 3 = 0 then 363 else if t 3 = 1 then 318 else 322) else (if t 3 = 0 then 367 else if t 3 = 1 then 328 else 330)) else (if t 2 = 0 then (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 1484) else if t 2 = 1 then (if t 3 = 0 then 364 else if t 3 = 1 then 320 else 323) else (if t 3 = 0 then 368 else if t 3 = 1 then 329 else 331))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 401 else 2801) else if t 2 = 1 then (if t 3 = 0 then 1500 else if t 3 = 1 then 399 else 405) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1788 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 894 else if t 3 = 1 then 350 else 2157) else if t 2 = 1 then (if t 3 = 0 then 888 else if t 3 = 1 then 324 else 326) else (if t 3 = 0 then 1494 else if t 3 = 1 then 332 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 895 else if t 3 = 1 then 351 else 2158) else if t 2 = 1 then (if t 3 = 0 then 889 else if t 3 = 1 then 325 else 327) else (if t 3 = 0 then 1495 else if t 3 = 1 then 333 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4314 else (if jt.2.val < 2 then 4366 else 4325)) else (if jt.2.val < 4 then 4365 else (if jt.2.val < 5 then 4367 else 4322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4290 else (if jt.2.val < 2 then 4301 else 4292)) else (if jt.2.val < 4 then 4299 else (if jt.2.val < 5 then 4300 else 4287)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2337 else (if jt.2.val < 2 then 2339 else 2342)) else (if jt.2.val < 4 then 2338 else (if jt.2.val < 5 then 2341 else 2340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1395 else (if jt.2.val < 2 then 1492 else 1426)) else (if jt.2.val < 4 then 1491 else (if jt.2.val < 5 then 1493 else 1380)))))

checked_coverage fastCoverage0477 pairing0477 template0477 witness0477

theorem coverage0477 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0477) (maskBits m))
    cores template0477 witness0477 := by
  rw [← coresFast_eq]
  exact fastCoverage0477

theorem coverageSize0477 : ∀ q : Pattern,
    (cores (witness0477 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0477 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0477
#print axioms coverageSize0477

noncomputable def pairing0478 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0478 : List (Fin 4935) := templateData0478

noncomputable def witness0478 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1216 else 2161) else if t 2 = 1 then (if t 3 = 0 then 1214 else if t 3 = 1 then 1210 else 694) else (if t 3 = 0 then 1376 else if t 3 = 1 then 1211 else 695)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1205 else if t 3 = 1 then 1201 else 757) else if t 2 = 1 then (if t 3 = 0 then 1187 else if t 3 = 1 then 1167 else 1172) else (if t 3 = 0 then 1801 else if t 3 = 1 then 1169 else 1173)) else (if t 2 = 0 then (if t 3 = 0 then 3152 else if t 3 = 1 then 3002 else 2795) else if t 2 = 1 then (if t 3 = 0 then 3329 else if t 3 = 1 then 2993 else 2996) else (if t 3 = 0 then 4532 else if t 3 = 1 then 4054 else 4056))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1215 else 2160) else if t 2 = 1 then (if t 3 = 0 then 1212 else if t 3 = 1 then 1206 else 690) else (if t 3 = 0 then 1374 else if t 3 = 1 then 1208 else 692)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1203 else if t 3 = 1 then 1197 else 751) else if t 2 = 1 then (if t 3 = 0 then 1179 else if t 3 = 1 then 1151 else 1159) else (if t 3 = 0 then 1795 else if t 3 = 1 then 1153 else 1161)) else (if t 2 = 0 then (if t 3 = 0 then 1204 else if t 3 = 1 then 1198 else 752) else if t 2 = 1 then (if t 3 = 0 then 1180 else if t 3 = 1 then 1152 else 1160) else (if t 3 = 0 then 1796 else if t 3 = 1 then 1154 else 1162))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 1836 else 4542) else if t 2 = 1 then (if t 3 = 0 then 504 else if t 3 = 1 then 498 else 1524) else (if t 3 = 0 then 2744 else if t 3 = 1 then 500 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 572 else if t 3 = 1 then 562 else 1542) else if t 2 = 1 then (if t 3 = 0 then 1181 else if t 3 = 1 then 1155 else 1163) else (if t 3 = 0 then 2136 else if t 3 = 1 then 1157 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 573 else if t 3 = 1 then 563 else 1543) else if t 2 = 1 then (if t 3 = 0 then 1182 else if t 3 = 1 then 1156 else 1164) else (if t 3 = 0 then 2137 else if t 3 = 1 then 1158 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4431 else (if jt.2.val < 2 then 4447 else 4442)) else (if jt.2.val < 4 then 4446 else (if jt.2.val < 5 then 4448 else 4439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3645 else (if jt.2.val < 2 then 3665 else 3647)) else (if jt.2.val < 4 then 3663 else (if jt.2.val < 5 then 3664 else 3642)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2283 else (if jt.2.val < 2 then 2311 else 2285)) else (if jt.2.val < 4 then 2310 else (if jt.2.val < 5 then 2312 else 2280))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2346 else (if jt.2.val < 2 then 2348 else 2351)) else (if jt.2.val < 4 then 2347 else (if jt.2.val < 5 then 2350 else 2349)))))

checked_coverage fastCoverage0478 pairing0478 template0478 witness0478

theorem coverage0478 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0478) (maskBits m))
    cores template0478 witness0478 := by
  rw [← coresFast_eq]
  exact fastCoverage0478

theorem coverageSize0478 : ∀ q : Pattern,
    (cores (witness0478 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0478 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0478
#print axioms coverageSize0478

noncomputable def pairing0479 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0479 : List (Fin 4935) := templateData0479

noncomputable def witness0479 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2228 else 1148) else if t 2 = 1 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2222 else 688) else (if t 3 = 0 then 308 else if t 3 = 1 then 298 else 1475)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2213 else 742) else if t 2 = 1 then (if t 3 = 0 then 2207 else if t 3 = 1 then 2193 else 2196) else (if t 3 = 0 then 979 else if t 3 = 1 then 2195 else 2197)) else (if t 2 = 0 then (if t 3 = 0 then 2706 else if t 3 = 1 then 2690 else 3192) else if t 2 = 1 then (if t 3 = 0 then 2939 else if t 3 = 1 then 3528 else 3530) else (if t 3 = 0 then 4047 else if t 3 = 1 then 4211 else 4546))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2226 else 1146) else if t 2 = 1 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2220 else 684) else (if t 3 = 0 then 306 else if t 3 = 1 then 294 else 1473)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2211 else 736) else if t 2 = 1 then (if t 3 = 0 then 2205 else if t 3 = 1 then 2177 else 2181) else (if t 3 = 0 then 973 else if t 3 = 1 then 2179 else 2183)) else (if t 2 = 0 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2212 else 737) else if t 2 = 1 then (if t 3 = 0 then 2206 else if t 3 = 1 then 2178 else 2182) else (if t 3 = 0 then 974 else if t 3 = 1 then 2180 else 2184))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1854 else 4061) else if t 2 = 1 then (if t 3 = 0 then 1620 else if t 3 = 1 then 1614 else 686) else (if t 3 = 0 then 3229 else if t 3 = 1 then 296 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1673 else if t 3 = 1 then 1658 else 738) else if t 2 = 1 then (if t 3 = 0 then 1889 else if t 3 = 1 then 2185 else 2189) else (if t 3 = 0 then 975 else if t 3 = 1 then 2187 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 1674 else if t 3 = 1 then 1659 else 739) else if t 2 = 1 then (if t 3 = 0 then 1890 else if t 3 = 1 then 2186 else 2190) else (if t 3 = 0 then 976 else if t 3 = 1 then 2188 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4470 else (if jt.2.val < 2 then 4544 else 4491)) else (if jt.2.val < 4 then 4543 else (if jt.2.val < 5 then 4545 else 4488))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3681 else (if jt.2.val < 2 then 3689 else 3683)) else (if jt.2.val < 4 then 3687 else (if jt.2.val < 5 then 3688 else 3678)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2340 else (if jt.2.val < 2 then 2356 else 2342)) else (if jt.2.val < 4 then 2355 else (if jt.2.val < 5 then 2357 else 2337))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2349 else (if jt.2.val < 2 then 2353 else 2351)) else (if jt.2.val < 4 then 2352 else (if jt.2.val < 5 then 2354 else 2346)))))

checked_coverage fastCoverage0479 pairing0479 template0479 witness0479

theorem coverage0479 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0479) (maskBits m))
    cores template0479 witness0479 := by
  rw [← coresFast_eq]
  exact fastCoverage0479

theorem coverageSize0479 : ∀ q : Pattern,
    (cores (witness0479 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0479 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0479
#print axioms coverageSize0479

end Crown.CertificateData
