import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0017

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0680 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0680 : List (Fin 4935) := templateData0680

noncomputable def witness0680 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 3959) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3227) else (if t 3 = 0 then 3532 else if t 3 = 1 then 3531 else 2649)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1611) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1610) else (if t 3 = 0 then 2200 else if t 3 = 1 then 2198 else 1616)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1881 else 95) else if t 2 = 1 then (if t 3 = 0 then 1882 else if t 3 = 1 then 1880 else 1619) else (if t 3 = 0 then 1190 else if t 3 = 1 then 1892 else 1622))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1443) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1442) else (if t 3 = 0 then 2074 else if t 3 = 1 then 2072 else 1448)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3161) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4514) else (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4515)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3270 else 3166) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4516) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4499 else 4517))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1331 else 1223) else if t 2 = 1 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1330 else 1778) else (if t 3 = 0 then 54 else if t 3 = 1 then 1344 else 1781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3074 else 3314) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4518) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4506 else 4519)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 3093 else 3501) else if t 2 = 1 then (if t 3 = 0 then 3847 else if t 3 = 1 then 4507 else 4520) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4513 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4836 else (if jt.2.val < 2 then 4840 else 4841)) else (if jt.2.val < 4 then 4837 else (if jt.2.val < 5 then 4839 else 4838))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4469 else (if jt.2.val < 2 then 4496 else 4497)) else (if jt.2.val < 4 then 4493 else (if jt.2.val < 5 then 4495 else 4494)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4737 else (if jt.2.val < 2 then 4741 else 4742)) else (if jt.2.val < 4 then 4738 else (if jt.2.val < 5 then 4740 else 4739))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4467 else (if jt.2.val < 2 then 4509 else 4512)) else (if jt.2.val < 4 then 4508 else (if jt.2.val < 5 then 4511 else 4510)))))

checked_coverage fastCoverage0680 pairing0680 template0680 witness0680

theorem coverage0680 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0680) (maskBits m))
    cores template0680 witness0680 := by
  rw [← coresFast_eq]
  exact fastCoverage0680

theorem coverageSize0680 : ∀ q : Pattern,
    (cores (witness0680 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0680 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0680
#print axioms coverageSize0680

noncomputable def pairing0681 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0681 : List (Fin 4935) := templateData0681

noncomputable def witness0681 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4525) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 3225) else (if t 3 = 0 then 2779 else if t 3 = 1 then 2775 else 3524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 1597) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 1593) else (if t 3 = 0 then 682 else if t 3 = 1 then 654 else 656)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 475 else 1849) else if t 2 = 1 then (if t 3 = 0 then 490 else if t 3 = 1 then 462 else 464) else (if t 3 = 0 then 1526 else if t 3 = 1 then 1132 else 1134))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 1429) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 1424) else (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 163)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 3146) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3875) else (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3878)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2698) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3881) else (if t 3 = 0 then 3919 else if t 3 = 1 then 3882 else 3883))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 994 else 1431) else if t 2 = 1 then (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 990) else (if t 3 = 0 then 1808 else if t 3 = 1 then 167 else 169)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2950) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3885) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3886 else 3887)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2700 else 2702) else if t 2 = 1 then (if t 3 = 0 then 4191 else if t 3 = 1 then 3888 else 3889) else (if t 3 = 0 then 4526 else if t 3 = 1 then 3890 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4815 else (if jt.2.val < 2 then 4817 else 4820)) else (if jt.2.val < 4 then 4816 else (if jt.2.val < 5 then 4819 else 4818))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4107 else (if jt.2.val < 2 then 4109 else 4116)) else (if jt.2.val < 4 then 4108 else (if jt.2.val < 5 then 4115 else 4114)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4110 else (if jt.2.val < 2 then 4112 else 4118)) else (if jt.2.val < 4 then 4111 else (if jt.2.val < 5 then 4117 else 4113))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4510 else (if jt.2.val < 2 then 4524 else 4512)) else (if jt.2.val < 4 then 4522 else (if jt.2.val < 5 then 4523 else 4467)))))

checked_coverage fastCoverage0681 pairing0681 template0681 witness0681

theorem coverage0681 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0681) (maskBits m))
    cores template0681 witness0681 := by
  rw [← coresFast_eq]
  exact fastCoverage0681

theorem coverageSize0681 : ∀ q : Pattern,
    (cores (witness0681 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0681 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0681
#print axioms coverageSize0681

noncomputable def pairing0682 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0682 : List (Fin 4935) := templateData0682

noncomputable def witness0682 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3453 else 2760) else if t 2 = 1 then (if t 3 = 0 then 3449 else if t 3 = 1 then 3445 else 2759) else (if t 3 = 0 then 4546 else if t 3 = 1 then 4211 else 3927)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3451 else 292) else if t 2 = 1 then (if t 3 = 0 then 3447 else if t 3 = 1 then 3443 else 290) else (if t 3 = 0 then 2197 else if t 3 = 1 then 2195 else 298)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 965 else 1478) else if t 2 = 1 then (if t 3 = 0 then 964 else if t 3 = 1 then 963 else 304) else (if t 3 = 0 then 1802 else if t 3 = 1 then 979 else 308))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3452 else 586) else if t 2 = 1 then (if t 3 = 0 then 3448 else if t 3 = 1 then 3444 else 584) else (if t 3 = 0 then 2071 else if t 3 = 1 then 2069 else 592)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3450 else 3163) else if t 2 = 1 then (if t 3 = 0 then 3446 else if t 3 = 1 then 3442 else 3488) else (if t 3 = 0 then 3464 else if t 3 = 1 then 3462 else 3489)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 3278 else 3167) else if t 2 = 1 then (if t 3 = 0 then 2838 else if t 3 = 1 then 3472 else 3490) else (if t 3 = 0 then 2842 else if t 3 = 1 then 3473 else 3491))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 442 else 1838) else if t 2 = 1 then (if t 3 = 0 then 441 else if t 3 = 1 then 440 else 1117) else (if t 3 = 0 then 1512 else if t 3 = 1 then 455 else 1121)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 3082 else 3315) else if t 2 = 1 then (if t 3 = 0 then 2471 else if t 3 = 1 then 3479 else 3492) else (if t 3 = 0 then 2475 else if t 3 = 1 then 3480 else 3493)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 3095 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2489 else if t 3 = 1 then 3486 else 3494) else (if t 3 = 0 then 2491 else if t 3 = 1 then 3487 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4791 else (if jt.2.val < 2 then 4795 else 4796)) else (if jt.2.val < 4 then 4792 else (if jt.2.val < 5 then 4794 else 4793))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3440 else (if jt.2.val < 2 then 3470 else 3471)) else (if jt.2.val < 4 then 3467 else (if jt.2.val < 5 then 3469 else 3468)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4739 else (if jt.2.val < 2 then 4745 else 4742)) else (if jt.2.val < 4 then 4743 else (if jt.2.val < 5 then 4744 else 4737))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3537 else (if jt.2.val < 2 then 3545 else 3548)) else (if jt.2.val < 4 then 3544 else (if jt.2.val < 5 then 3547 else 3546)))))

checked_coverage fastCoverage0682 pairing0682 template0682 witness0682

theorem coverage0682 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0682) (maskBits m))
    cores template0682 witness0682 := by
  rw [← coresFast_eq]
  exact fastCoverage0682

theorem coverageSize0682 : ∀ q : Pattern,
    (cores (witness0682 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0682 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0682
#print axioms coverageSize0682

noncomputable def pairing0683 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0683 : List (Fin 4935) := templateData0683

noncomputable def witness0683 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2560 else 3499) else if t 2 = 1 then (if t 3 = 0 then 2565 else if t 3 = 1 then 2544 else 3209) else (if t 3 = 0 then 3951 else if t 3 = 1 then 3945 else 4541)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2558 else 277) else if t 2 = 1 then (if t 3 = 0 then 2563 else if t 3 = 1 then 2538 else 251) else (if t 3 = 0 then 681 else if t 3 = 1 then 641 else 1459)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1357 else 922) else if t 2 = 1 then (if t 3 = 0 then 1372 else if t 3 = 1 then 1350 else 254) else (if t 3 = 0 then 695 else if t 3 = 1 then 644 else 1786))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2559 else 571) else if t 2 = 1 then (if t 3 = 0 then 2564 else if t 3 = 1 then 2541 else 545) else (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 1532)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2548 else 2550) else if t 2 = 1 then (if t 3 = 0 then 2562 else if t 3 = 1 then 2519 else 2523) else (if t 3 = 0 then 2570 else if t 3 = 1 then 2521 else 2524)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2878 else 2880) else if t 2 = 1 then (if t 3 = 0 then 2576 else if t 3 = 1 then 2526 else 2528) else (if t 3 = 0 then 2578 else if t 3 = 1 then 2527 else 2529))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1903 else 573) else if t 2 = 1 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1900 else 549) else (if t 3 = 0 then 902 else if t 3 = 1 then 153 else 1536)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2554 else 2556) else if t 2 = 1 then (if t 3 = 0 then 2883 else if t 3 = 1 then 2530 else 2532) else (if t 3 = 0 then 2885 else if t 3 = 1 then 2531 else 2533)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3196 else 3934) else if t 2 = 1 then (if t 3 = 0 then 3506 else if t 3 = 1 then 2534 else 2536) else (if t 3 = 0 then 3507 else if t 3 = 1 then 2535 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4773 else (if jt.2.val < 2 then 4775 else 4778)) else (if jt.2.val < 4 then 4774 else (if jt.2.val < 5 then 4777 else 4776))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3417 else (if jt.2.val < 2 then 3419 else 3422)) else (if jt.2.val < 4 then 3418 else (if jt.2.val < 5 then 3421 else 3420)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4113 else (if jt.2.val < 2 then 4123 else 4118)) else (if jt.2.val < 4 then 4122 else (if jt.2.val < 5 then 4124 else 4110))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3546 else (if jt.2.val < 2 then 3554 else 3548)) else (if jt.2.val < 4 then 3552 else (if jt.2.val < 5 then 3553 else 3537)))))

checked_coverage fastCoverage0683 pairing0683 template0683 witness0683

theorem coverage0683 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0683) (maskBits m))
    cores template0683 witness0683 := by
  rw [← coresFast_eq]
  exact fastCoverage0683

theorem coverageSize0683 : ∀ q : Pattern,
    (cores (witness0683 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0683 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0683
#print axioms coverageSize0683

noncomputable def pairing0684 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0684 : List (Fin 4935) := templateData0684

noncomputable def witness0684 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1707 else 780) else if t 2 = 1 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1705 else 1450) else (if t 3 = 0 then 837 else if t 3 = 1 then 1733 else 1453)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1703 else if t 3 = 1 then 1699 else 778) else if t 2 = 1 then (if t 3 = 0 then 1701 else if t 3 = 1 then 1697 else 1753) else (if t 3 = 0 then 833 else if t 3 = 1 then 1730 else 1756)) else (if t 2 = 0 then (if t 3 = 0 then 4537 else if t 3 = 1 then 4064 else 3943) else if t 2 = 1 then (if t 3 = 0 then 3350 else if t 3 = 1 then 3348 else 2500) else (if t 3 = 0 then 3514 else if t 3 = 1 then 2938 else 2506))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1706 else 779) else if t 2 = 1 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1704 else 1449) else (if t 3 = 0 then 836 else if t 3 = 1 then 1732 else 1452)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1702 else if t 3 = 1 then 1698 else 777) else if t 2 = 1 then (if t 3 = 0 then 1700 else if t 3 = 1 then 1696 else 1752) else (if t 3 = 0 then 832 else if t 3 = 1 then 1729 else 1755)) else (if t 2 = 0 then (if t 3 = 0 then 1720 else if t 3 = 1 then 1718 else 781) else if t 2 = 1 then (if t 3 = 0 then 1719 else if t 3 = 1 then 1716 else 1754) else (if t 3 = 0 then 839 else if t 3 = 1 then 1734 else 1757))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 647 else 3523) else if t 2 = 1 then (if t 3 = 0 then 257 else if t 3 = 1 then 1352 else 2118) else (if t 3 = 0 then 3942 else if t 3 = 1 then 1358 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1461 else if t 3 = 1 then 645 else 1142) else if t 2 = 1 then (if t 3 = 0 then 255 else if t 3 = 1 then 1746 else 1758) else (if t 3 = 0 then 278 else if t 3 = 1 then 1749 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 1464 else if t 3 = 1 then 651 else 1143) else if t 2 = 1 then (if t 3 = 0 then 261 else if t 3 = 1 then 1748 else 1759) else (if t 3 = 0 then 281 else if t 3 = 1 then 1751 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4773 else (if jt.2.val < 2 then 4781 else 4778)) else (if jt.2.val < 4 then 4779 else (if jt.2.val < 5 then 4780 else 4776))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4494 else (if jt.2.val < 2 then 4536 else 4497)) else (if jt.2.val < 4 then 4534 else (if jt.2.val < 5 then 4535 else 4469)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1694 else (if jt.2.val < 2 then 1728 else 1731)) else (if jt.2.val < 4 then 1725 else (if jt.2.val < 5 then 1727 else 1726))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1917 else (if jt.2.val < 2 then 1923 else 1928)) else (if jt.2.val < 4 then 1922 else (if jt.2.val < 5 then 1927 else 1926)))))

checked_coverage fastCoverage0684 pairing0684 template0684 witness0684

theorem coverage0684 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0684) (maskBits m))
    cores template0684 witness0684 := by
  rw [← coresFast_eq]
  exact fastCoverage0684

theorem coverageSize0684 : ∀ q : Pattern,
    (cores (witness0684 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0684 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0684
#print axioms coverageSize0684

noncomputable def pairing0685 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0685 : List (Fin 4935) := templateData0685

noncomputable def witness0685 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 379 else 1775) else if t 2 = 1 then (if t 3 = 0 then 386 else if t 3 = 1 then 371 else 372) else (if t 3 = 0 then 1501 else if t 3 = 1 then 892 else 893)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 384 else if t 3 = 1 then 356 else 1489) else if t 2 = 1 then (if t 3 = 0 then 382 else if t 3 = 1 then 336 else 339) else (if t 3 = 0 then 400 else if t 3 = 1 then 340 else 341)) else (if t 2 = 0 then (if t 3 = 0 then 3935 else if t 3 = 1 then 3929 else 4539) else if t 2 = 1 then (if t 3 = 0 then 2740 else if t 3 = 1 then 2728 else 3203) else (if t 3 = 0 then 2743 else if t 3 = 1 then 2730 else 3505))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 375 else 1773) else if t 2 = 1 then (if t 3 = 0 then 385 else if t 3 = 1 then 363 else 365) else (if t 3 = 0 then 1500 else if t 3 = 1 then 888 else 890)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 383 else if t 3 = 1 then 346 else 1483) else if t 2 = 1 then (if t 3 = 0 then 381 else if t 3 = 1 then 318 else 322) else (if t 3 = 0 then 399 else if t 3 = 1 then 324 else 326)) else (if t 2 = 0 then (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 1484) else if t 2 = 1 then (if t 3 = 0 then 389 else if t 3 = 1 then 320 else 323) else (if t 3 = 0 then 403 else if t 3 = 1 then 325 else 327))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 377 else 2796) else if t 2 = 1 then (if t 3 = 0 then 2139 else if t 3 = 1 then 367 else 369) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1494 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 930 else if t 3 = 1 then 352 else 1487) else if t 2 = 1 then (if t 3 = 0 then 924 else if t 3 = 1 then 328 else 330) else (if t 3 = 0 then 1788 else if t 3 = 1 then 332 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 931 else if t 3 = 1 then 353 else 1488) else if t 2 = 1 then (if t 3 = 0 then 925 else if t 3 = 1 then 329 else 331) else (if t 3 = 0 then 1789 else if t 3 = 1 then 333 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4791 else (if jt.2.val < 2 then 4807 else 4796)) else (if jt.2.val < 4 then 4806 else (if jt.2.val < 5 then 4808 else 4793))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4114 else (if jt.2.val < 2 then 4129 else 4116)) else (if jt.2.val < 4 then 4128 else (if jt.2.val < 5 then 4130 else 4107)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1479 else (if jt.2.val < 2 then 1481 else 1486)) else (if jt.2.val < 4 then 1480 else (if jt.2.val < 5 then 1485 else 1482))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1926 else (if jt.2.val < 2 then 1940 else 1928)) else (if jt.2.val < 4 then 1938 else (if jt.2.val < 5 then 1939 else 1917)))))

checked_coverage fastCoverage0685 pairing0685 template0685 witness0685

theorem coverage0685 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0685) (maskBits m))
    cores template0685 witness0685 := by
  rw [← coresFast_eq]
  exact fastCoverage0685

theorem coverageSize0685 : ∀ q : Pattern,
    (cores (witness0685 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0685 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0685
#print axioms coverageSize0685

noncomputable def pairing0686 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0686 : List (Fin 4935) := templateData0686

noncomputable def witness0686 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1031 else 1549) else if t 2 = 1 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1027 else 595) else (if t 3 = 0 then 1816 else if t 3 = 1 then 1051 else 601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1025 else if t 3 = 1 then 1023 else 784) else if t 2 = 1 then (if t 3 = 0 then 1021 else if t 3 = 1 then 1019 else 1078) else (if t 3 = 0 then 1813 else if t 3 = 1 then 1046 else 1084)) else (if t 2 = 0 then (if t 3 = 0 then 3520 else if t 3 = 1 then 2972 else 2800) else if t 2 = 1 then (if t 3 = 0 then 3338 else if t 3 = 1 then 2970 else 2980) else (if t 3 = 0 then 4532 else if t 3 = 1 then 4046 else 3860))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1030 else 1548) else if t 2 = 1 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1026 else 594) else (if t 3 = 0 then 1815 else if t 3 = 1 then 1050 else 600)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1024 else if t 3 = 1 then 1022 else 783) else if t 2 = 1 then (if t 3 = 0 then 1020 else if t 3 = 1 then 1018 else 1077) else (if t 3 = 0 then 1812 else if t 3 = 1 then 1045 else 1083)) else (if t 2 = 0 then (if t 3 = 0 then 1040 else if t 3 = 1 then 1039 else 787) else if t 2 = 1 then (if t 3 = 0 then 1038 else if t 3 = 1 then 1037 else 1081) else (if t 3 = 0 then 1817 else if t 3 = 1 then 1054 else 1085))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 1518 else 4542) else if t 2 = 1 then (if t 3 = 0 then 468 else if t 3 = 1 then 466 else 2148) else (if t 3 = 0 then 2739 else if t 3 = 1 then 476 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 660 else if t 3 = 1 then 658 else 1824) else if t 2 = 1 then (if t 3 = 0 then 1070 else if t 3 = 1 then 1068 else 1086) else (if t 3 = 0 then 1598 else if t 3 = 1 then 1074 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 665 else if t 3 = 1 then 664 else 1825) else if t 2 = 1 then (if t 3 = 0 then 1073 else if t 3 = 1 then 1072 else 1087) else (if t 3 = 0 then 1601 else if t 3 = 1 then 1076 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4815 else (if jt.2.val < 2 then 4823 else 4820)) else (if jt.2.val < 4 then 4821 else (if jt.2.val < 5 then 4822 else 4818))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3468 else (if jt.2.val < 2 then 3519 else 3471)) else (if jt.2.val < 4 then 3517 else (if jt.2.val < 5 then 3518 else 3440)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1726 else (if jt.2.val < 2 then 1814 else 1731)) else (if jt.2.val < 4 then 1809 else (if jt.2.val < 5 then 1810 else 1694))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1944 else (if jt.2.val < 2 then 1946 else 1949)) else (if jt.2.val < 4 then 1945 else (if jt.2.val < 5 then 1948 else 1947)))))

checked_coverage fastCoverage0686 pairing0686 template0686 witness0686

theorem coverage0686 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0686) (maskBits m))
    cores template0686 witness0686 := by
  rw [← coresFast_eq]
  exact fastCoverage0686

theorem coverageSize0686 : ∀ q : Pattern,
    (cores (witness0686 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0686 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0686
#print axioms coverageSize0686

noncomputable def pairing0687 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0687 : List (Fin 4935) := templateData0687

noncomputable def witness0687 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1675 else 1112) else if t 2 = 1 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1669 else 553) else (if t 3 = 0 then 201 else if t 3 = 1 then 157 else 1835)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1660 else 741) else if t 2 = 1 then (if t 3 = 0 then 1678 else if t 3 = 1 then 1644 else 1647) else (if t 3 = 0 then 864 else if t 3 = 1 then 1646 else 1648)) else (if t 2 = 0 then (if t 3 = 0 then 2722 else if t 3 = 1 then 2689 else 3522) else if t 2 = 1 then (if t 3 = 0 then 2860 else if t 3 = 1 then 3232 else 3234) else (if t 3 = 0 then 3967 else if t 3 = 1 then 3963 else 4530))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1671 else 1110) else if t 2 = 1 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1665 else 546) else (if t 3 = 0 then 200 else if t 3 = 1 then 150 else 1833)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1656 else 734) else if t 2 = 1 then (if t 3 = 0 then 1677 else if t 3 = 1 then 1628 else 1632) else (if t 3 = 0 then 863 else if t 3 = 1 then 1630 else 1634)) else (if t 2 = 0 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1657 else 735) else if t 2 = 1 then (if t 3 = 0 then 1685 else if t 3 = 1 then 1629 else 1633) else (if t 3 = 0 then 866 else if t 3 = 1 then 1631 else 1635))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1673 else 3966) else if t 2 = 1 then (if t 3 = 0 then 2172 else if t 3 = 1 then 1667 else 550) else (if t 3 = 0 then 3525 else if t 3 = 1 then 154 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1854 else if t 3 = 1 then 1658 else 738) else if t 2 = 1 then (if t 3 = 0 then 1851 else if t 3 = 1 then 1636 else 1640) else (if t 3 = 0 then 876 else if t 3 = 1 then 1638 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 1855 else if t 3 = 1 then 1659 else 739) else if t 2 = 1 then (if t 3 = 0 then 1852 else if t 3 = 1 then 1637 else 1641) else (if t 3 = 0 then 877 else if t 3 = 1 then 1639 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4836 else (if jt.2.val < 2 then 4843 else 4841)) else (if jt.2.val < 4 then 4842 else (if jt.2.val < 5 then 4844 else 4838))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3420 else (if jt.2.val < 2 then 3436 else 3422)) else (if jt.2.val < 4 then 3435 else (if jt.2.val < 5 then 3437 else 3417)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1482 else (if jt.2.val < 2 then 1654 else 1486)) else (if jt.2.val < 4 then 1653 else (if jt.2.val < 5 then 1655 else 1479))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1947 else (if jt.2.val < 2 then 1964 else 1949)) else (if jt.2.val < 4 then 1959 else (if jt.2.val < 5 then 1960 else 1944)))))

checked_coverage fastCoverage0687 pairing0687 template0687 witness0687

theorem coverage0687 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0687) (maskBits m))
    cores template0687 witness0687 := by
  rw [← coresFast_eq]
  exact fastCoverage0687

theorem coverageSize0687 : ∀ q : Pattern,
    (cores (witness0687 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0687 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0687
#print axioms coverageSize0687

noncomputable def pairing0688 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0688 : List (Fin 4935) := templateData0688

noncomputable def witness0688 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 4213) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3531) else (if t 3 = 0 then 3228 else if t 3 = 1 then 3227 else 2649)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 2199) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 2198) else (if t 3 = 0 then 1612 else if t 3 = 1 then 1610 else 1616)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1881 else 980) else if t 2 = 1 then (if t 3 = 0 then 1882 else if t 3 = 1 then 1880 else 1892) else (if t 3 = 0 then 497 else if t 3 = 1 then 1619 else 1622))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 2073) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 2072) else (if t 3 = 0 then 1444 else if t 3 = 1 then 1442 else 1448)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3465) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4492) else (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4515)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3270 else 3280) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4499) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4516 else 4517))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1331 else 456) else if t 2 = 1 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1330 else 1344) else (if t 3 = 0 then 1013 else if t 3 = 1 then 1778 else 1781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3074 else 3084) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4506) else (if t 3 = 0 then 4038 else if t 3 = 1 then 4518 else 4519)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 3093 else 3097) else if t 2 = 1 then (if t 3 = 0 then 3847 else if t 3 = 1 then 4507 else 4513) else (if t 3 = 0 then 4192 else if t 3 = 1 then 4520 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4836 else (if jt.2.val < 2 then 4840 else 4841)) else (if jt.2.val < 4 then 4837 else (if jt.2.val < 5 then 4839 else 4838))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4469 else (if jt.2.val < 2 then 4496 else 4497)) else (if jt.2.val < 4 then 4493 else (if jt.2.val < 5 then 4495 else 4494)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4548 else (if jt.2.val < 2 then 4556 else 4559)) else (if jt.2.val < 4 then 4555 else (if jt.2.val < 5 then 4558 else 4557))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4746 else (if jt.2.val < 2 then 4750 else 4751)) else (if jt.2.val < 4 then 4747 else (if jt.2.val < 5 then 4749 else 4748)))))

checked_coverage fastCoverage0688 pairing0688 template0688 witness0688

theorem coverage0688 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0688) (maskBits m))
    cores template0688 witness0688 := by
  rw [← coresFast_eq]
  exact fastCoverage0688

theorem coverageSize0688 : ∀ q : Pattern,
    (cores (witness0688 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0688 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0688
#print axioms coverageSize0688

noncomputable def pairing0689 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0689 : List (Fin 4935) := templateData0689

noncomputable def witness0689 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 4546) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 3530) else (if t 3 = 0 then 2779 else if t 3 = 1 then 2778 else 3182)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 2197) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 2196) else (if t 3 = 0 then 682 else if t 3 = 1 then 680 else 688)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1173 else 1802) else if t 2 = 1 then (if t 3 = 0 then 1174 else if t 3 = 1 then 1172 else 1189) else (if t 3 = 0 then 1526 else if t 3 = 1 then 694 else 698))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 2071) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 2070) else (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 196)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 3464) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4155) else (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4180)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2842) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4164) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4181 else 4182))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 35 else 1512) else if t 2 = 1 then (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 53) else (if t 3 = 0 then 1808 else if t 3 = 1 then 901 else 905)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2475) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4171) else (if t 3 = 0 then 4039 else if t 3 = 1 then 4183 else 4184)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2487 else 2491) else if t 2 = 1 then (if t 3 = 0 then 3849 else if t 3 = 1 then 4177 else 4178) else (if t 3 = 0 then 4526 else if t 3 = 1 then 4185 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4827 else (if jt.2.val < 2 then 4831 else 4832)) else (if jt.2.val < 4 then 4828 else (if jt.2.val < 5 then 4830 else 4829))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4133 else (if jt.2.val < 2 then 4161 else 4162)) else (if jt.2.val < 4 then 4158 else (if jt.2.val < 5 then 4160 else 4159)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4215 else (if jt.2.val < 2 then 4223 else 4226)) else (if jt.2.val < 4 then 4222 else (if jt.2.val < 5 then 4225 else 4224))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4748 else (if jt.2.val < 2 then 4754 else 4751)) else (if jt.2.val < 4 then 4752 else (if jt.2.val < 5 then 4753 else 4746)))))

checked_coverage fastCoverage0689 pairing0689 template0689 witness0689

theorem coverage0689 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0689) (maskBits m))
    cores template0689 witness0689 := by
  rw [← coresFast_eq]
  exact fastCoverage0689

theorem coverageSize0689 : ∀ q : Pattern,
    (cores (witness0689 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0689 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0689
#print axioms coverageSize0689

noncomputable def pairing0690 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0690 : List (Fin 4935) := templateData0690

noncomputable def witness0690 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3156 else 2760) else if t 2 = 1 then (if t 3 = 0 then 3151 else if t 3 = 1 then 3144 else 2756) else (if t 3 = 0 then 4525 else if t 3 = 1 then 3953 else 4207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3154 else 292) else if t 2 = 1 then (if t 3 = 0 then 3149 else if t 3 = 1 then 3138 else 264) else (if t 3 = 0 then 1597 else if t 3 = 1 then 1589 else 266)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 88 else 1478) else if t 2 = 1 then (if t 3 = 0 then 73 else if t 3 = 1 then 60 else 916) else (if t 3 = 0 then 1849 else if t 3 = 1 then 62 else 918))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3155 else 586) else if t 2 = 1 then (if t 3 = 0 then 3150 else if t 3 = 1 then 3141 else 557) else (if t 3 = 0 then 1429 else if t 3 = 1 then 1419 else 559)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3153 else 3163) else if t 2 = 1 then (if t 3 = 0 then 3145 else if t 3 = 1 then 3119 else 3123) else (if t 3 = 0 then 3146 else if t 3 = 1 then 3121 else 3124)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 3165 else 3167) else if t 2 = 1 then (if t 3 = 0 then 2697 else if t 3 = 1 then 3126 else 3128) else (if t 3 = 0 then 2698 else if t 3 = 1 then 3127 else 3129))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1219 else 1838) else if t 2 = 1 then (if t 3 = 0 then 1204 else if t 3 = 1 then 1198 else 563) else (if t 3 = 0 then 1431 else if t 3 = 1 then 1200 else 565)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 3313 else 3315) else if t 2 = 1 then (if t 3 = 0 then 2949 else if t 3 = 1 then 3130 else 3132) else (if t 3 = 0 then 2950 else if t 3 = 1 then 3131 else 3133)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 3500 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2701 else if t 3 = 1 then 3134 else 3136) else (if t 3 = 0 then 2702 else if t 3 = 1 then 3135 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4761 else (if jt.2.val < 2 then 4763 else 4766)) else (if jt.2.val < 4 then 4762 else (if jt.2.val < 5 then 4765 else 4764))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3396 else (if jt.2.val < 2 then 3398 else 3405)) else (if jt.2.val < 4 then 3397 else (if jt.2.val < 5 then 3404 else 3403)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4557 else (if jt.2.val < 2 then 4565 else 4559)) else (if jt.2.val < 4 then 4563 else (if jt.2.val < 5 then 4564 else 4548))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3399 else (if jt.2.val < 2 then 3401 else 3407)) else (if jt.2.val < 4 then 3400 else (if jt.2.val < 5 then 3406 else 3402)))))

checked_coverage fastCoverage0690 pairing0690 template0690 witness0690

theorem coverage0690 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0690) (maskBits m))
    cores template0690 witness0690 := by
  rw [← coresFast_eq]
  exact fastCoverage0690

theorem coverageSize0690 : ∀ q : Pattern,
    (cores (witness0690 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0690 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0690
#print axioms coverageSize0690

noncomputable def pairing0691 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0691 : List (Fin 4935) := templateData0691

noncomputable def witness0691 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2565 else 3215) else if t 2 = 1 then (if t 3 = 0 then 2560 else if t 3 = 1 then 2544 else 3209) else (if t 3 = 0 then 4190 else if t 3 = 1 then 3945 else 4541)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2563 else 291) else if t 2 = 1 then (if t 3 = 0 then 2558 else if t 3 = 1 then 2538 else 251) else (if t 3 = 0 then 667 else if t 3 = 1 then 641 else 1459)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1372 else 305) else if t 2 = 1 then (if t 3 = 0 then 1357 else if t 3 = 1 then 1350 else 254) else (if t 3 = 0 then 1138 else if t 3 = 1 then 644 else 1786))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2564 else 585) else if t 2 = 1 then (if t 3 = 0 then 2559 else if t 3 = 1 then 2541 else 545) else (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 1532)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2562 else 2572) else if t 2 = 1 then (if t 3 = 0 then 2548 else if t 3 = 1 then 2519 else 2523) else (if t 3 = 0 then 2549 else if t 3 = 1 then 2521 else 2524)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2576 else 2579) else if t 2 = 1 then (if t 3 = 0 then 2878 else if t 3 = 1 then 2526 else 2528) else (if t 3 = 0 then 2879 else if t 3 = 1 then 2527 else 2529))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1915 else 1118) else if t 2 = 1 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1900 else 549) else (if t 3 = 0 then 177 else if t 3 = 1 then 153 else 1536)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2883 else 2886) else if t 2 = 1 then (if t 3 = 0 then 2554 else if t 3 = 1 then 2530 else 2532) else (if t 3 = 0 then 2555 else if t 3 = 1 then 2531 else 2533)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3506 else 4197) else if t 2 = 1 then (if t 3 = 0 then 3196 else if t 3 = 1 then 2534 else 2536) else (if t 3 = 0 then 3197 else if t 3 = 1 then 2535 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4773 else (if jt.2.val < 2 then 4775 else 4778)) else (if jt.2.val < 4 then 4774 else (if jt.2.val < 5 then 4777 else 4776))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3417 else (if jt.2.val < 2 then 3419 else 3422)) else (if jt.2.val < 4 then 3418 else (if jt.2.val < 5 then 3421 else 3420)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4224 else (if jt.2.val < 2 then 4232 else 4226)) else (if jt.2.val < 4 then 4230 else (if jt.2.val < 5 then 4231 else 4215))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3402 else (if jt.2.val < 2 then 3424 else 3407)) else (if jt.2.val < 4 then 3423 else (if jt.2.val < 5 then 3425 else 3399)))))

checked_coverage fastCoverage0691 pairing0691 template0691 witness0691

theorem coverage0691 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0691) (maskBits m))
    cores template0691 witness0691 := by
  rw [← coresFast_eq]
  exact fastCoverage0691

theorem coverageSize0691 : ∀ q : Pattern,
    (cores (witness0691 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0691 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0691
#print axioms coverageSize0691

noncomputable def pairing0692 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0692 : List (Fin 4935) := templateData0692

noncomputable def witness0692 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1707 else 1053) else if t 2 = 1 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1705 else 1733) else (if t 3 = 0 then 396 else if t 3 = 1 then 1450 else 1453)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1703 else if t 3 = 1 then 1699 else 1049) else if t 2 = 1 then (if t 3 = 0 then 1701 else if t 3 = 1 then 1697 else 1730) else (if t 3 = 0 then 394 else if t 3 = 1 then 1753 else 1756)) else (if t 2 = 0 then (if t 3 = 0 then 4537 else if t 3 = 1 then 4064 else 4198) else if t 2 = 1 then (if t 3 = 0 then 3350 else if t 3 = 1 then 3348 else 2938) else (if t 3 = 0 then 3207 else if t 3 = 1 then 2500 else 2506))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1706 else 1052) else if t 2 = 1 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1704 else 1732) else (if t 3 = 0 then 395 else if t 3 = 1 then 1449 else 1452)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1702 else if t 3 = 1 then 1698 else 1048) else if t 2 = 1 then (if t 3 = 0 then 1700 else if t 3 = 1 then 1696 else 1729) else (if t 3 = 0 then 393 else if t 3 = 1 then 1752 else 1755)) else (if t 2 = 0 then (if t 3 = 0 then 1720 else if t 3 = 1 then 1718 else 1055) else if t 2 = 1 then (if t 3 = 0 then 1719 else if t 3 = 1 then 1716 else 1734) else (if t 3 = 0 then 397 else if t 3 = 1 then 1754 else 1757))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 647 else 3206) else if t 2 = 1 then (if t 3 = 0 then 257 else if t 3 = 1 then 1352 else 1358) else (if t 3 = 0 then 4206 else if t 3 = 1 then 2118 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1461 else if t 3 = 1 then 645 else 668) else if t 2 = 1 then (if t 3 = 0 then 255 else if t 3 = 1 then 1746 else 1749) else (if t 3 = 0 then 926 else if t 3 = 1 then 1758 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 1464 else if t 3 = 1 then 651 else 671) else if t 2 = 1 then (if t 3 = 0 then 261 else if t 3 = 1 then 1748 else 1751) else (if t 3 = 0 then 927 else if t 3 = 1 then 1759 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4773 else (if jt.2.val < 2 then 4781 else 4778)) else (if jt.2.val < 4 then 4779 else (if jt.2.val < 5 then 4780 else 4776))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4494 else (if jt.2.val < 2 then 4536 else 4497)) else (if jt.2.val < 4 then 4534 else (if jt.2.val < 5 then 4535 else 4469)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2376 else (if jt.2.val < 2 then 2378 else 2381)) else (if jt.2.val < 4 then 2377 else (if jt.2.val < 5 then 2380 else 2379))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2269 else (if jt.2.val < 2 then 2273 else 2274)) else (if jt.2.val < 4 then 2270 else (if jt.2.val < 5 then 2272 else 2271)))))

checked_coverage fastCoverage0692 pairing0692 template0692 witness0692

theorem coverage0692 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0692) (maskBits m))
    cores template0692 witness0692 := by
  rw [← coresFast_eq]
  exact fastCoverage0692

theorem coverageSize0692 : ∀ q : Pattern,
    (cores (witness0692 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0692 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0692
#print axioms coverageSize0692

noncomputable def pairing0693 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0693 : List (Fin 4935) := templateData0693

noncomputable def witness0693 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 807 else 1816) else if t 2 = 1 then (if t 3 = 0 then 809 else if t 3 = 1 then 805 else 835) else (if t 3 = 0 then 1501 else if t 3 = 1 then 199 else 205)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 803 else if t 3 = 1 then 799 else 1813) else if t 2 = 1 then (if t 3 = 0 then 801 else if t 3 = 1 then 797 else 830) else (if t 3 = 0 then 400 else if t 3 = 1 then 862 else 868)) else (if t 2 = 0 then (if t 3 = 0 then 4203 else if t 3 = 1 then 4054 else 4532) else if t 2 = 1 then (if t 3 = 0 then 2995 else if t 3 = 1 then 2993 else 3329) else (if t 3 = 0 then 2743 else if t 3 = 1 then 3003 else 3106))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 806 else 1815) else if t 2 = 1 then (if t 3 = 0 then 808 else if t 3 = 1 then 804 else 834) else (if t 3 = 0 then 1500 else if t 3 = 1 then 198 else 204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 802 else if t 3 = 1 then 798 else 1812) else if t 2 = 1 then (if t 3 = 0 then 800 else if t 3 = 1 then 796 else 829) else (if t 3 = 0 then 399 else if t 3 = 1 then 861 else 867)) else (if t 2 = 0 then (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 1817) else if t 2 = 1 then (if t 3 = 0 then 819 else if t 3 = 1 then 816 else 838) else (if t 3 = 0 then 403 else if t 3 = 1 then 865 else 869))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 66 else 2739) else if t 2 = 1 then (if t 3 = 0 then 1470 else if t 3 = 1 then 64 else 74) else (if t 3 = 0 then 4540 else if t 3 = 1 then 2127 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 270 else if t 3 = 1 then 854 else 1598) else if t 2 = 1 then (if t 3 = 0 then 268 else if t 3 = 1 then 852 else 858) else (if t 3 = 0 then 1788 else if t 3 = 1 then 870 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 275 else if t 3 = 1 then 857 else 1601) else if t 2 = 1 then (if t 3 = 0 then 274 else if t 3 = 1 then 856 else 860) else (if t 3 = 0 then 1789 else if t 3 = 1 then 871 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4761 else (if jt.2.val < 2 then 4787 else 4766)) else (if jt.2.val < 4 then 4785 else (if jt.2.val < 5 then 4786 else 4764))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4159 else (if jt.2.val < 2 then 4202 else 4162)) else (if jt.2.val < 4 then 4200 else (if jt.2.val < 5 then 4201 else 4133)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2388 else (if jt.2.val < 2 then 2390 else 2393)) else (if jt.2.val < 4 then 2389 else (if jt.2.val < 5 then 2392 else 2391))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2271 else (if jt.2.val < 2 then 2289 else 2274)) else (if jt.2.val < 4 then 2286 else (if jt.2.val < 5 then 2287 else 2269)))))

checked_coverage fastCoverage0693 pairing0693 template0693 witness0693

theorem coverage0693 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0693) (maskBits m))
    cores template0693 witness0693 := by
  rw [← coresFast_eq]
  exact fastCoverage0693

theorem coverageSize0693 : ∀ q : Pattern,
    (cores (witness0693 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0693 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0693
#print axioms coverageSize0693

noncomputable def pairing0694 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0694 : List (Fin 4935) := templateData0694

noncomputable def witness0694 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 770 else 1549) else if t 2 = 1 then (if t 3 = 0 then 763 else if t 3 = 1 then 755 else 1108) else (if t 3 = 0 then 1775 else if t 3 = 1 then 756 else 1109)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 768 else if t 3 = 1 then 766 else 784) else if t 2 = 1 then (if t 3 = 0 then 740 else if t 3 = 1 then 720 else 723) else (if t 3 = 0 then 1489 else if t 3 = 1 then 722 else 724)) else (if t 2 = 0 then (if t 3 = 0 then 3198 else if t 3 = 1 then 2797 else 2800) else if t 2 = 1 then (if t 3 = 0 then 3191 else if t 3 = 1 then 2785 else 2787) else (if t 3 = 0 then 4539 else if t 3 = 1 then 3939 else 4196))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 769 else 1548) else if t 2 = 1 then (if t 3 = 0 then 759 else if t 3 = 1 then 747 else 1104) else (if t 3 = 0 then 1773 else if t 3 = 1 then 749 else 1106)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 767 else if t 3 = 1 then 765 else 783) else if t 2 = 1 then (if t 3 = 0 then 732 else if t 3 = 1 then 704 else 708) else (if t 3 = 0 then 1483 else if t 3 = 1 then 706 else 710)) else (if t 2 = 0 then (if t 3 = 0 then 774 else if t 3 = 1 then 773 else 787) else if t 2 = 1 then (if t 3 = 0 then 733 else if t 3 = 1 then 705 else 709) else (if t 3 = 0 then 1484 else if t 3 = 1 then 707 else 711))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 2160 else 4542) else if t 2 = 1 then (if t 3 = 0 then 761 else if t 3 = 1 then 751 else 1542) else (if t 3 = 0 then 2796 else if t 3 = 1 then 753 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1146 else if t 3 = 1 then 1140 else 1824) else if t 2 = 1 then (if t 3 = 0 then 736 else if t 3 = 1 then 712 else 716) else (if t 3 = 0 then 1487 else if t 3 = 1 then 714 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 1147 else if t 3 = 1 then 1141 else 1825) else if t 2 = 1 then (if t 3 = 0 then 737 else if t 3 = 1 then 713 else 717) else (if t 3 = 0 then 1488 else if t 3 = 1 then 715 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4827 else (if jt.2.val < 2 then 4834 else 4832)) else (if jt.2.val < 4 then 4833 else (if jt.2.val < 5 then 4835 else 4829))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3403 else (if jt.2.val < 2 then 3430 else 3405)) else (if jt.2.val < 4 then 3429 else (if jt.2.val < 5 then 3431 else 3396)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2379 else (if jt.2.val < 2 then 2402 else 2381)) else (if jt.2.val < 4 then 2400 else (if jt.2.val < 5 then 2401 else 2376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2022 else (if jt.2.val < 2 then 2024 else 2027)) else (if jt.2.val < 4 then 2023 else (if jt.2.val < 5 then 2026 else 2025)))))

checked_coverage fastCoverage0694 pairing0694 template0694 witness0694

theorem coverage0694 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0694) (maskBits m))
    cores template0694 witness0694 := by
  rw [← coresFast_eq]
  exact fastCoverage0694

theorem coverageSize0694 : ∀ q : Pattern,
    (cores (witness0694 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0694 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0694
#print axioms coverageSize0694

noncomputable def pairing0695 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0695 : List (Fin 4935) := templateData0695

noncomputable def witness0695 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1682 else 597) else if t 2 = 1 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1669 else 553) else (if t 3 = 0 then 896 else if t 3 = 1 then 157 else 1835)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1678 else 1080) else if t 2 = 1 then (if t 3 = 0 then 1660 else if t 3 = 1 then 1644 else 1647) else (if t 3 = 0 then 357 else if t 3 = 1 then 1646 else 1648)) else (if t 2 = 0 then (if t 3 = 0 then 2722 else if t 3 = 1 then 2860 else 3242) else if t 2 = 1 then (if t 3 = 0 then 2689 else if t 3 = 1 then 3232 else 3234) else (if t 3 = 0 then 4205 else if t 3 = 1 then 3963 else 4530))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1681 else 596) else if t 2 = 1 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1665 else 546) else (if t 3 = 0 then 894 else if t 3 = 1 then 150 else 1833)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1677 else 1079) else if t 2 = 1 then (if t 3 = 0 then 1656 else if t 3 = 1 then 1628 else 1632) else (if t 3 = 0 then 350 else if t 3 = 1 then 1630 else 1634)) else (if t 2 = 0 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1685 else 1082) else if t 2 = 1 then (if t 3 = 0 then 1657 else if t 3 = 1 then 1629 else 1633) else (if t 3 = 0 then 351 else if t 3 = 1 then 1631 else 1635))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 2172 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1673 else if t 3 = 1 then 1667 else 550) else (if t 3 = 0 then 3240 else if t 3 = 1 then 154 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1854 else if t 3 = 1 then 1851 else 1092) else if t 2 = 1 then (if t 3 = 0 then 1658 else if t 3 = 1 then 1636 else 1640) else (if t 3 = 0 then 354 else if t 3 = 1 then 1638 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 1855 else if t 3 = 1 then 1852 else 1093) else if t 2 = 1 then (if t 3 = 0 then 1659 else if t 3 = 1 then 1637 else 1641) else (if t 3 = 0 then 355 else if t 3 = 1 then 1639 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4836 else (if jt.2.val < 2 then 4843 else 4841)) else (if jt.2.val < 4 then 4842 else (if jt.2.val < 5 then 4844 else 4838))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3420 else (if jt.2.val < 2 then 3436 else 3422)) else (if jt.2.val < 4 then 3435 else (if jt.2.val < 5 then 3437 else 3417)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2391 else (if jt.2.val < 2 then 2408 else 2393)) else (if jt.2.val < 4 then 2406 else (if jt.2.val < 5 then 2407 else 2388))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2025 else (if jt.2.val < 2 then 2038 else 2027)) else (if jt.2.val < 4 then 2037 else (if jt.2.val < 5 then 2039 else 2022)))))

checked_coverage fastCoverage0695 pairing0695 template0695 witness0695

theorem coverage0695 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0695) (maskBits m))
    cores template0695 witness0695 := by
  rw [← coresFast_eq]
  exact fastCoverage0695

theorem coverageSize0695 : ∀ q : Pattern,
    (cores (witness0695 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0695 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0695
#print axioms coverageSize0695

noncomputable def pairing0696 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0696 : List (Fin 4935) := templateData0696

noncomputable def witness0696 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 4056) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2996) else (if t 3 = 0 then 3532 else if t 3 = 1 then 3530 else 3330)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 1173) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 1172) else (if t 3 = 0 then 2200 else if t 3 = 1 then 2196 else 1189)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 681 else 695) else if t 2 = 1 then (if t 3 = 0 then 682 else if t 3 = 1 then 680 else 694) else (if t 3 = 0 then 689 else if t 3 = 1 then 688 else 698))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 822) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 821) else (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 840)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2829) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4163) else (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4164)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2578) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4181) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4180 else 4182))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 35 else 71) else if t 2 = 1 then (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 70) else (if t 3 = 0 then 54 else if t 3 = 1 then 53 else 77)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2487) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4177) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4171 else 4178)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2885 else 3507) else if t 2 = 1 then (if t 3 = 0 then 4039 else if t 3 = 1 then 4183 else 4185) else (if t 3 = 0 then 4040 else if t 3 = 1 then 4184 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4827 else (if jt.2.val < 2 then 4831 else 4832)) else (if jt.2.val < 4 then 4828 else (if jt.2.val < 5 then 4830 else 4829))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4305 else (if jt.2.val < 2 then 4307 else 4310)) else (if jt.2.val < 4 then 4306 else (if jt.2.val < 5 then 4309 else 4308)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4728 else (if jt.2.val < 2 then 4732 else 4733)) else (if jt.2.val < 4 then 4729 else (if jt.2.val < 5 then 4731 else 4730))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4278 else (if jt.2.val < 2 then 4282 else 4283)) else (if jt.2.val < 4 then 4279 else (if jt.2.val < 5 then 4281 else 4280)))))

checked_coverage fastCoverage0696 pairing0696 template0696 witness0696

theorem coverage0696 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0696) (maskBits m))
    cores template0696 witness0696 := by
  rw [← coresFast_eq]
  exact fastCoverage0696

theorem coverageSize0696 : ∀ q : Pattern,
    (cores (witness0696 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0696 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0696
#print axioms coverageSize0696

noncomputable def pairing0697 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0697 : List (Fin 4935) := templateData0697

noncomputable def witness0697 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 4203) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2995) else (if t 3 = 0 then 3352 else if t 3 = 1 then 3350 else 3514)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 1171) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 1170) else (if t 3 = 0 then 1882 else if t 3 = 1 then 1878 else 1188)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 489 else 503) else if t 2 = 1 then (if t 3 = 0 then 490 else if t 3 = 1 then 488 else 502) else (if t 3 = 0 then 497 else if t 3 = 1 then 496 else 506))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 820) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 819) else (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 839)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2828) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4000) else (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4003)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2723) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4021) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4020 else 4022))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 243 else 275) else if t 2 = 1 then (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 274) else (if t 3 = 0 then 262 else if t 3 = 1 then 261 else 281)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2635) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4017) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4016 else 4018)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2903 else 3322) else if t 2 = 1 then (if t 3 = 0 then 4191 else if t 3 = 1 then 4023 else 4025) else (if t 3 = 0 then 4192 else if t 3 = 1 then 4024 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4809 else (if jt.2.val < 2 then 4813 else 4814)) else (if jt.2.val < 4 then 4810 else (if jt.2.val < 5 then 4812 else 4811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4287 else (if jt.2.val < 2 then 4289 else 4292)) else (if jt.2.val < 4 then 4288 else (if jt.2.val < 5 then 4291 else 4290)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4566 else (if jt.2.val < 2 then 4570 else 4571)) else (if jt.2.val < 4 then 4567 else (if jt.2.val < 5 then 4569 else 4568))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4280 else (if jt.2.val < 2 then 4286 else 4283)) else (if jt.2.val < 4 then 4284 else (if jt.2.val < 5 then 4285 else 4278)))))

checked_coverage fastCoverage0697 pairing0697 template0697 witness0697

theorem coverage0697 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0697) (maskBits m))
    cores template0697 witness0697 := by
  rw [← coresFast_eq]
  exact fastCoverage0697

theorem coverageSize0697 : ∀ q : Pattern,
    (cores (witness0697 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0697 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0697
#print axioms coverageSize0697

noncomputable def pairing0698 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0698 : List (Fin 4935) := templateData0698

noncomputable def witness0698 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3340) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2973) else (if t 3 = 0 then 4213 else if t 3 = 1 then 4211 else 4047)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 964) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 963) else (if t 3 = 0 then 2199 else if t 3 = 1 then 2195 else 979)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 291 else 305) else if t 2 = 1 then (if t 3 = 0 then 292 else if t 3 = 1 then 290 else 304) else (if t 3 = 0 then 299 else if t 3 = 1 then 298 else 308))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 1042) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 1041) else (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 1056)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2838) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3472) else (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3473)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2572 else 2579) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3488 else 3490) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3489 else 3491))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 441 else 473) else if t 2 = 1 then (if t 3 = 0 then 442 else if t 3 = 1 then 440 else 472) else (if t 3 = 0 then 456 else if t 3 = 1 then 455 else 479)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2471 else 2489) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3479 else 3486) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3480 else 3487)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2886 else 4197) else if t 2 = 1 then (if t 3 = 0 then 3315 else if t 3 = 1 then 3492 else 3494) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3493 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4791 else (if jt.2.val < 2 then 4795 else 4796)) else (if jt.2.val < 4 then 4792 else (if jt.2.val < 5 then 4794 else 4793))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3672 else (if jt.2.val < 2 then 3674 else 3677)) else (if jt.2.val < 4 then 3673 else (if jt.2.val < 5 then 3676 else 3675)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4730 else (if jt.2.val < 2 then 4736 else 4733)) else (if jt.2.val < 4 then 4734 else (if jt.2.val < 5 then 4735 else 4728))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3627 else (if jt.2.val < 2 then 3631 else 3632)) else (if jt.2.val < 4 then 3628 else (if jt.2.val < 5 then 3630 else 3629)))))

checked_coverage fastCoverage0698 pairing0698 template0698 witness0698

theorem coverage0698 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0698) (maskBits m))
    cores template0698 witness0698 := by
  rw [← coresFast_eq]
  exact fastCoverage0698

theorem coverageSize0698 : ∀ q : Pattern,
    (cores (witness0698 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0698 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0698
#print axioms coverageSize0698

noncomputable def pairing0699 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0699 : List (Fin 4935) := templateData0699

noncomputable def witness0699 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3520) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2972) else (if t 3 = 0 then 4066 else if t 3 = 1 then 4064 else 4198)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 962) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 961) else (if t 3 = 0 then 1881 else if t 3 = 1 then 1877 else 978)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 87 else 101) else if t 2 = 1 then (if t 3 = 0 then 88 else if t 3 = 1 then 86 else 100) else (if t 3 = 0 then 95 else if t 3 = 1 then 94 else 104))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 1040) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 1039) else (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 1055)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2837) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3276) else (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3279)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2717 else 2724) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3295 else 3297) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3296 else 3298))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 637 else 665) else if t 2 = 1 then (if t 3 = 0 then 638 else if t 3 = 1 then 636 else 664) else (if t 3 = 0 then 652 else if t 3 = 1 then 651 else 671)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2623 else 2637) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3291 else 3293) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3292 else 3294)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2904 else 4045) else if t 2 = 1 then (if t 3 = 0 then 3500 else if t 3 = 1 then 3299 else 3301) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3300 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4755 else (if jt.2.val < 2 then 4759 else 4760)) else (if jt.2.val < 4 then 4756 else (if jt.2.val < 5 then 4758 else 4757))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3636 else (if jt.2.val < 2 then 3638 else 3641)) else (if jt.2.val < 4 then 3637 else (if jt.2.val < 5 then 3640 else 3639)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4568 else (if jt.2.val < 2 then 4574 else 4571)) else (if jt.2.val < 4 then 4572 else (if jt.2.val < 5 then 4573 else 4566))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3629 else (if jt.2.val < 2 then 3635 else 3632)) else (if jt.2.val < 4 then 3633 else (if jt.2.val < 5 then 3634 else 3627)))))

checked_coverage fastCoverage0699 pairing0699 template0699 witness0699

theorem coverage0699 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0699) (maskBits m))
    cores template0699 witness0699 := by
  rw [← coresFast_eq]
  exact fastCoverage0699

theorem coverageSize0699 : ∀ q : Pattern,
    (cores (witness0699 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0699 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0699
#print axioms coverageSize0699

noncomputable def pairing0700 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0700 : List (Fin 4935) := templateData0700

noncomputable def witness0700 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 183 else 201) else if t 2 = 1 then (if t 3 = 0 then 185 else if t 3 = 1 then 181 else 199) else (if t 3 = 0 then 195 else if t 3 = 1 then 193 else 205)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 178 else if t 3 = 1 then 156 else 157) else if t 2 = 1 then (if t 3 = 0 then 170 else if t 3 = 1 then 136 else 140) else (if t 3 = 0 then 171 else if t 3 = 1 then 139 else 141)) else (if t 2 = 0 then (if t 3 = 0 then 4190 else if t 3 = 1 then 3945 else 4058) else if t 2 = 1 then (if t 3 = 0 then 2775 else if t 3 = 1 then 2766 else 2768) else (if t 3 = 0 then 3524 else if t 3 = 1 then 3172 else 3320))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 182 else 200) else if t 2 = 1 then (if t 3 = 0 then 184 else if t 3 = 1 then 180 else 198) else (if t 3 = 0 then 194 else if t 3 = 1 then 192 else 204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 174 else if t 3 = 1 then 146 else 150) else if t 2 = 1 then (if t 3 = 0 then 160 else if t 3 = 1 then 117 else 124) else (if t 3 = 0 then 162 else if t 3 = 1 then 121 else 126)) else (if t 2 = 0 then (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 151) else if t 2 = 1 then (if t 3 = 0 then 161 else if t 3 = 1 then 119 else 125) else (if t 3 = 0 then 163 else if t 3 = 1 then 122 else 127))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 899 else 3525) else if t 2 = 1 then (if t 3 = 0 then 1806 else if t 3 = 1 then 897 else 2127) else (if t 3 = 0 then 4059 else if t 3 = 1 then 903 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 176 else if t 3 = 1 then 152 else 154) else if t 2 = 1 then (if t 3 = 0 then 166 else if t 3 = 1 then 128 else 132) else (if t 3 = 0 then 168 else if t 3 = 1 then 130 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 177 else if t 3 = 1 then 153 else 155) else if t 2 = 1 then (if t 3 = 0 then 167 else if t 3 = 1 then 129 else 133) else (if t 3 = 0 then 169 else if t 3 = 1 then 131 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4755 else (if jt.2.val < 2 then 4789 else 4760)) else (if jt.2.val < 4 then 4788 else (if jt.2.val < 5 then 4790 else 4757))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4308 else (if jt.2.val < 2 then 4313 else 4310)) else (if jt.2.val < 4 then 4311 else (if jt.2.val < 5 then 4312 else 4305)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 111 else (if jt.2.val < 2 then 113 else 149)) else (if jt.2.val < 4 then 112 else (if jt.2.val < 5 then 148 else 120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 108 else (if jt.2.val < 2 then 110 else 165)) else (if jt.2.val < 4 then 109 else (if jt.2.val < 5 then 164 else 123)))))

checked_coverage fastCoverage0700 pairing0700 template0700 witness0700

theorem coverage0700 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0700) (maskBits m))
    cores template0700 witness0700 := by
  rw [← coresFast_eq]
  exact fastCoverage0700

theorem coverageSize0700 : ∀ q : Pattern,
    (cores (witness0700 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0700 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0700
#print axioms coverageSize0700

noncomputable def pairing0701 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0701 : List (Fin 4935) := templateData0701

noncomputable def witness0701 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 384 else 402) else if t 2 = 1 then (if t 3 = 0 then 386 else if t 3 = 1 then 382 else 400) else (if t 3 = 0 then 396 else if t 3 = 1 then 394 else 406)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 379 else if t 3 = 1 then 356 else 357) else if t 2 = 1 then (if t 3 = 0 then 371 else if t 3 = 1 then 336 else 340) else (if t 3 = 0 then 372 else if t 3 = 1 then 339 else 341)) else (if t 2 = 0 then (if t 3 = 0 then 4036 else if t 3 = 1 then 3929 else 4205) else if t 2 = 1 then (if t 3 = 0 then 2737 else if t 3 = 1 then 2728 else 2730) else (if t 3 = 0 then 3344 else if t 3 = 1 then 3203 else 3505))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 383 else 401) else if t 2 = 1 then (if t 3 = 0 then 385 else if t 3 = 1 then 381 else 399) else (if t 3 = 0 then 395 else if t 3 = 1 then 393 else 405)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 375 else if t 3 = 1 then 346 else 350) else if t 2 = 1 then (if t 3 = 0 then 363 else if t 3 = 1 then 318 else 324) else (if t 3 = 0 then 365 else if t 3 = 1 then 322 else 326)) else (if t 2 = 0 then (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 351) else if t 2 = 1 then (if t 3 = 0 then 364 else if t 3 = 1 then 320 else 325) else (if t 3 = 0 then 366 else if t 3 = 1 then 323 else 327))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 930 else 3345) else if t 2 = 1 then (if t 3 = 0 then 2139 else if t 3 = 1 then 924 else 1788) else (if t 3 = 0 then 4206 else if t 3 = 1 then 926 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 377 else if t 3 = 1 then 352 else 354) else if t 2 = 1 then (if t 3 = 0 then 367 else if t 3 = 1 then 328 else 332) else (if t 3 = 0 then 369 else if t 3 = 1 then 330 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 378 else if t 3 = 1 then 353 else 355) else if t 2 = 1 then (if t 3 = 0 then 368 else if t 3 = 1 then 329 else 333) else (if t 3 = 0 then 370 else if t 3 = 1 then 331 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4791 else (if jt.2.val < 2 then 4807 else 4796)) else (if jt.2.val < 4 then 4806 else (if jt.2.val < 5 then 4808 else 4793))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4290 else (if jt.2.val < 2 then 4301 else 4292)) else (if jt.2.val < 4 then 4299 else (if jt.2.val < 5 then 4300 else 4287)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 312 else (if jt.2.val < 2 then 314 else 349)) else (if jt.2.val < 4 then 313 else (if jt.2.val < 5 then 348 else 321))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 123 else (if jt.2.val < 2 then 361 else 165)) else (if jt.2.val < 4 then 360 else (if jt.2.val < 5 then 362 else 108)))))

checked_coverage fastCoverage0701 pairing0701 template0701 witness0701

theorem coverage0701 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0701) (maskBits m))
    cores template0701 witness0701 := by
  rw [← coresFast_eq]
  exact fastCoverage0701

theorem coverageSize0701 : ∀ q : Pattern,
    (cores (witness0701 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0701 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0701
#print axioms coverageSize0701

noncomputable def pairing0702 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0702 : List (Fin 4935) := templateData0702

noncomputable def witness0702 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 579 else 597) else if t 2 = 1 then (if t 3 = 0 then 581 else if t 3 = 1 then 577 else 595) else (if t 3 = 0 then 591 else if t 3 = 1 then 589 else 601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 574 else if t 3 = 1 then 552 else 553) else if t 2 = 1 then (if t 3 = 0 then 566 else if t 3 = 1 then 532 else 535) else (if t 3 = 0 then 567 else if t 3 = 1 then 534 else 536)) else (if t 2 = 0 then (if t 3 = 0 then 3499 else if t 3 = 1 then 3209 else 3342) else if t 2 = 1 then (if t 3 = 0 then 2756 else if t 3 = 1 then 2747 else 2749) else (if t 3 = 0 then 4207 else if t 3 = 1 then 3923 else 4044))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 578 else 596) else if t 2 = 1 then (if t 3 = 0 then 580 else if t 3 = 1 then 576 else 594) else (if t 3 = 0 then 590 else if t 3 = 1 then 588 else 600)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 570 else if t 3 = 1 then 544 else 546) else if t 2 = 1 then (if t 3 = 0 then 556 else if t 3 = 1 then 515 else 520) else (if t 3 = 0 then 558 else if t 3 = 1 then 517 else 522)) else (if t 2 = 0 then (if t 3 = 0 then 571 else if t 3 = 1 then 545 else 547) else if t 2 = 1 then (if t 3 = 0 then 557 else if t 3 = 1 then 516 else 521) else (if t 3 = 0 then 559 else if t 3 = 1 then 518 else 523))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 1115 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1836 else if t 3 = 1 then 1113 else 2148) else (if t 3 = 0 then 3343 else if t 3 = 1 then 1119 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 572 else if t 3 = 1 then 548 else 550) else if t 2 = 1 then (if t 3 = 0 then 562 else if t 3 = 1 then 524 else 528) else (if t 3 = 0 then 564 else if t 3 = 1 then 526 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 573 else if t 3 = 1 then 549 else 551) else if t 2 = 1 then (if t 3 = 0 then 563 else if t 3 = 1 then 525 else 529) else (if t 3 = 0 then 565 else if t 3 = 1 then 527 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4809 else (if jt.2.val < 2 then 4825 else 4814)) else (if jt.2.val < 4 then 4824 else (if jt.2.val < 5 then 4826 else 4811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3675 else (if jt.2.val < 2 then 3686 else 3677)) else (if jt.2.val < 4 then 3684 else (if jt.2.val < 5 then 3685 else 3672)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 120 else (if jt.2.val < 2 then 542 else 149)) else (if jt.2.val < 4 then 541 else (if jt.2.val < 5 then 543 else 111))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 510 else (if jt.2.val < 2 then 512 else 561)) else (if jt.2.val < 4 then 511 else (if jt.2.val < 5 then 560 else 519)))))

checked_coverage fastCoverage0702 pairing0702 template0702 witness0702

theorem coverage0702 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0702) (maskBits m))
    cores template0702 witness0702 := by
  rw [← coresFast_eq]
  exact fastCoverage0702

theorem coverageSize0702 : ∀ q : Pattern,
    (cores (witness0702 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0702 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0702
#print axioms coverageSize0702

noncomputable def pairing0703 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0703 : List (Fin 4935) := templateData0703

noncomputable def witness0703 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 768 else 786) else if t 2 = 1 then (if t 3 = 0 then 770 else if t 3 = 1 then 766 else 784) else (if t 3 = 0 then 780 else if t 3 = 1 then 778 else 790)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 763 else if t 3 = 1 then 740 else 741) else if t 2 = 1 then (if t 3 = 0 then 755 else if t 3 = 1 then 720 else 723) else (if t 3 = 0 then 756 else if t 3 = 1 then 722 else 724)) else (if t 2 = 0 then (if t 3 = 0 then 3312 else if t 3 = 1 then 3191 else 3522) else if t 2 = 1 then (if t 3 = 0 then 2794 else if t 3 = 1 then 2785 else 2787) else (if t 3 = 0 then 4060 else if t 3 = 1 then 3939 else 4196))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 767 else 785) else if t 2 = 1 then (if t 3 = 0 then 769 else if t 3 = 1 then 765 else 783) else (if t 3 = 0 then 779 else if t 3 = 1 then 777 else 789)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 759 else if t 3 = 1 then 732 else 734) else if t 2 = 1 then (if t 3 = 0 then 747 else if t 3 = 1 then 704 else 708) else (if t 3 = 0 then 749 else if t 3 = 1 then 706 else 710)) else (if t 2 = 0 then (if t 3 = 0 then 760 else if t 3 = 1 then 733 else 735) else if t 2 = 1 then (if t 3 = 0 then 748 else if t 3 = 1 then 705 else 709) else (if t 3 = 0 then 750 else if t 3 = 1 then 707 else 711))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 1146 else 4061) else if t 2 = 1 then (if t 3 = 0 then 2160 else if t 3 = 1 then 1140 else 1824) else (if t 3 = 0 then 3523 else if t 3 = 1 then 1142 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 761 else if t 3 = 1 then 736 else 738) else if t 2 = 1 then (if t 3 = 0 then 751 else if t 3 = 1 then 712 else 716) else (if t 3 = 0 then 753 else if t 3 = 1 then 714 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 762 else if t 3 = 1 then 737 else 739) else if t 2 = 1 then (if t 3 = 0 then 752 else if t 3 = 1 then 713 else 717) else (if t 3 = 0 then 754 else if t 3 = 1 then 715 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4827 else (if jt.2.val < 2 then 4834 else 4832)) else (if jt.2.val < 4 then 4833 else (if jt.2.val < 5 then 4835 else 4829))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3639 else (if jt.2.val < 2 then 3662 else 3641)) else (if jt.2.val < 4 then 3660 else (if jt.2.val < 5 then 3661 else 3636)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 321 else (if jt.2.val < 2 then 730 else 349)) else (if jt.2.val < 4 then 729 else (if jt.2.val < 5 then 731 else 312))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 519 else (if jt.2.val < 2 then 745 else 561)) else (if jt.2.val < 4 then 744 else (if jt.2.val < 5 then 746 else 510)))))

checked_coverage fastCoverage0703 pairing0703 template0703 witness0703

theorem coverage0703 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0703) (maskBits m))
    cores template0703 witness0703 := by
  rw [← coresFast_eq]
  exact fastCoverage0703

theorem coverageSize0703 : ∀ q : Pattern,
    (cores (witness0703 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0703 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0703
#print axioms coverageSize0703

noncomputable def pairing0704 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0704 : List (Fin 4935) := templateData0704

noncomputable def witness0704 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 4066) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3351) else (if t 3 = 0 then 3532 else if t 3 = 1 then 3531 else 2940)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1881) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1880) else (if t 3 = 0 then 2200 else if t 3 = 1 then 2198 else 1892)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1611 else 95) else if t 2 = 1 then (if t 3 = 0 then 1612 else if t 3 = 1 then 1610 else 1619) else (if t 3 = 0 then 689 else if t 3 = 1 then 1616 else 1622))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1722) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1721) else (if t 3 = 0 then 2074 else if t 3 = 1 then 2072 else 1735)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3270) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4498) else (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4499)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3161 else 3166) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4516) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4515 else 4517))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1331 else 652) else if t 2 = 1 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1330 else 1355) else (if t 3 = 0 then 54 else if t 3 = 1 then 1344 else 1361)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3074 else 3093) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4507) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4506 else 4513)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 3314 else 3501) else if t 2 = 1 then (if t 3 = 0 then 4038 else if t 3 = 1 then 4518 else 4520) else (if t 3 = 0 then 4040 else if t 3 = 1 then 4519 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4836 else (if jt.2.val < 2 then 4840 else 4841)) else (if jt.2.val < 4 then 4837 else (if jt.2.val < 5 then 4839 else 4838))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4602 else (if jt.2.val < 2 then 4604 else 4607)) else (if jt.2.val < 4 then 4603 else (if jt.2.val < 5 then 4606 else 4605)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4737 else (if jt.2.val < 2 then 4741 else 4742)) else (if jt.2.val < 4 then 4738 else (if jt.2.val < 5 then 4740 else 4739))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4593 else (if jt.2.val < 2 then 4597 else 4598)) else (if jt.2.val < 4 then 4594 else (if jt.2.val < 5 then 4596 else 4595)))))

checked_coverage fastCoverage0704 pairing0704 template0704 witness0704

theorem coverage0704 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0704) (maskBits m))
    cores template0704 witness0704 := by
  rw [← coresFast_eq]
  exact fastCoverage0704

theorem coverageSize0704 : ∀ q : Pattern,
    (cores (witness0704 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0704 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0704
#print axioms coverageSize0704

noncomputable def pairing0705 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0705 : List (Fin 4935) := templateData0705

noncomputable def witness0705 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 4537) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 3350) else (if t 3 = 0 then 2997 else if t 3 = 1 then 2995 else 3514)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 1879) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 1878) else (if t 3 = 0 then 1174 else if t 3 = 1 then 1170 else 1188)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 489 else 1523) else if t 2 = 1 then (if t 3 = 0 then 490 else if t 3 = 1 then 488 else 496) else (if t 3 = 0 then 1526 else if t 3 = 1 then 502 else 506))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 1720) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 1719) else (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 839)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 3269) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 3993) else (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4003)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2719) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4020) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4021 else 4022))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 243 else 1464) else if t 2 = 1 then (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 261) else (if t 3 = 0 then 1472 else if t 3 = 1 then 274 else 281)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2627) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4016) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4017 else 4018)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2903 else 2905) else if t 2 = 1 then (if t 3 = 0 then 4191 else if t 3 = 1 then 4023 else 4024) else (if t 3 = 0 then 4526 else if t 3 = 1 then 4025 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4809 else (if jt.2.val < 2 then 4813 else 4814)) else (if jt.2.val < 4 then 4810 else (if jt.2.val < 5 then 4812 else 4811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4287 else (if jt.2.val < 2 then 4289 else 4292)) else (if jt.2.val < 4 then 4288 else (if jt.2.val < 5 then 4291 else 4290)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4234 else (if jt.2.val < 2 then 4238 else 4239)) else (if jt.2.val < 4 then 4235 else (if jt.2.val < 5 then 4237 else 4236))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4595 else (if jt.2.val < 2 then 4601 else 4598)) else (if jt.2.val < 4 then 4599 else (if jt.2.val < 5 then 4600 else 4593)))))

checked_coverage fastCoverage0705 pairing0705 template0705 witness0705

theorem coverage0705 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0705) (maskBits m))
    cores template0705 witness0705 := by
  rw [← coresFast_eq]
  exact fastCoverage0705

theorem coverageSize0705 : ∀ q : Pattern,
    (cores (witness0705 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0705 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0705
#print axioms coverageSize0705

noncomputable def pairing0706 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0706 : List (Fin 4935) := templateData0706

noncomputable def witness0706 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3453 else 2974) else if t 2 = 1 then (if t 3 = 0 then 3449 else if t 3 = 1 then 3445 else 2973) else (if t 3 = 0 then 4546 else if t 3 = 1 then 4211 else 4047)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3451 else 965) else if t 2 = 1 then (if t 3 = 0 then 3447 else if t 3 = 1 then 3443 else 963) else (if t 3 = 0 then 2197 else if t 3 = 1 then 2195 else 979)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 292 else 1478) else if t 2 = 1 then (if t 3 = 0 then 291 else if t 3 = 1 then 290 else 304) else (if t 3 = 0 then 1475 else if t 3 = 1 then 298 else 308))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3452 else 1043) else if t 2 = 1 then (if t 3 = 0 then 3448 else if t 3 = 1 then 3444 else 1041) else (if t 3 = 0 then 2071 else if t 3 = 1 then 2069 else 1056)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3450 else 3278) else if t 2 = 1 then (if t 3 = 0 then 3446 else if t 3 = 1 then 3442 else 3472) else (if t 3 = 0 then 3464 else if t 3 = 1 then 3462 else 3473)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 3163 else 3167) else if t 2 = 1 then (if t 3 = 0 then 2572 else if t 3 = 1 then 3488 else 3490) else (if t 3 = 0 then 2574 else if t 3 = 1 then 3489 else 3491))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 442 else 1520) else if t 2 = 1 then (if t 3 = 0 then 441 else if t 3 = 1 then 440 else 472) else (if t 3 = 0 then 1512 else if t 3 = 1 then 455 else 479)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 3082 else 3095) else if t 2 = 1 then (if t 3 = 0 then 2471 else if t 3 = 1 then 3479 else 3486) else (if t 3 = 0 then 2475 else if t 3 = 1 then 3480 else 3487)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 3315 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2886 else if t 3 = 1 then 3492 else 3494) else (if t 3 = 0 then 2887 else if t 3 = 1 then 3493 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4791 else (if jt.2.val < 2 then 4795 else 4796)) else (if jt.2.val < 4 then 4792 else (if jt.2.val < 5 then 4794 else 4793))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3672 else (if jt.2.val < 2 then 3674 else 3677)) else (if jt.2.val < 4 then 3673 else (if jt.2.val < 5 then 3676 else 3675)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4739 else (if jt.2.val < 2 then 4745 else 4742)) else (if jt.2.val < 4 then 4743 else (if jt.2.val < 5 then 4744 else 4737))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3601 else (if jt.2.val < 2 then 3605 else 3606)) else (if jt.2.val < 4 then 3602 else (if jt.2.val < 5 then 3604 else 3603)))))

checked_coverage fastCoverage0706 pairing0706 template0706 witness0706

theorem coverage0706 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0706) (maskBits m))
    cores template0706 witness0706 := by
  rw [← coresFast_eq]
  exact fastCoverage0706

theorem coverageSize0706 : ∀ q : Pattern,
    (cores (witness0706 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0706 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0706
#print axioms coverageSize0706

noncomputable def pairing0707 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0707 : List (Fin 4935) := templateData0707

noncomputable def witness0707 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2813 else 3520) else if t 2 = 1 then (if t 3 = 0 then 2817 else if t 3 = 1 then 2809 else 3338) else (if t 3 = 0 then 4056 else if t 3 = 1 then 4054 else 4532)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2811 else 962) else if t 2 = 1 then (if t 3 = 0 then 2815 else if t 3 = 1 then 2807 else 960) else (if t 3 = 0 then 1173 else if t 3 = 1 then 1169 else 1801)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1371 else 101) else if t 2 = 1 then (if t 3 = 0 then 1372 else if t 3 = 1 then 1370 else 1001) else (if t 3 = 0 then 695 else if t 3 = 1 then 1211 else 1376))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2812 else 1040) else if t 2 = 1 then (if t 3 = 0 then 2816 else if t 3 = 1 then 2808 else 1038) else (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 1817)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2810 else 2837) else if t 2 = 1 then (if t 3 = 0 then 2814 else if t 3 = 1 then 2806 else 2835) else (if t 3 = 0 then 2829 else if t 3 = 1 then 2826 else 2840)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2721 else 2724) else if t 2 = 1 then (if t 3 = 0 then 2576 else if t 3 = 1 then 2859 else 2862) else (if t 3 = 0 then 2578 else if t 3 = 1 then 2861 else 2863))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1585 else 665) else if t 2 = 1 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1584 else 1073) else (if t 3 = 0 then 71 else if t 3 = 1 then 857 else 1601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2632 else 2637) else if t 2 = 1 then (if t 3 = 0 then 2484 else if t 3 = 1 then 2854 else 2857) else (if t 3 = 0 then 2487 else if t 3 = 1 then 2856 else 2858)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3321 else 4045) else if t 2 = 1 then (if t 3 = 0 then 3506 else if t 3 = 1 then 2864 else 2866) else (if t 3 = 0 then 3507 else if t 3 = 1 then 2865 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4767 else (if jt.2.val < 2 then 4771 else 4772)) else (if jt.2.val < 4 then 4768 else (if jt.2.val < 5 then 4770 else 4769))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3648 else (if jt.2.val < 2 then 3650 else 3653)) else (if jt.2.val < 4 then 3649 else (if jt.2.val < 5 then 3652 else 3651)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4236 else (if jt.2.val < 2 then 4253 else 4239)) else (if jt.2.val < 4 then 4251 else (if jt.2.val < 5 then 4252 else 4234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3603 else (if jt.2.val < 2 then 3614 else 3606)) else (if jt.2.val < 4 then 3612 else (if jt.2.val < 5 then 3613 else 3601)))))

checked_coverage fastCoverage0707 pairing0707 template0707 witness0707

theorem coverage0707 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0707) (maskBits m))
    cores template0707 witness0707 := by
  rw [← coresFast_eq]
  exact fastCoverage0707

theorem coverageSize0707 : ∀ q : Pattern,
    (cores (witness0707 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0707 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0707
#print axioms coverageSize0707

noncomputable def pairing0708 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0708 : List (Fin 4935) := templateData0708

noncomputable def witness0708 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1437 else 780) else if t 2 = 1 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1435 else 1450) else (if t 3 = 0 then 195 else if t 3 = 1 then 1447 else 1453)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1432 else if t 3 = 1 then 1422 else 756) else if t 2 = 1 then (if t 3 = 0 then 1427 else if t 3 = 1 then 1408 else 1412) else (if t 3 = 0 then 171 else if t 3 = 1 then 1411 else 1413)) else (if t 2 = 0 then (if t 3 = 0 then 4525 else if t 3 = 1 then 3953 else 4060) else if t 2 = 1 then (if t 3 = 0 then 3225 else if t 3 = 1 then 3219 else 2482) else (if t 3 = 0 then 3524 else if t 3 = 1 then 2630 else 2898))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1436 else 779) else if t 2 = 1 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1434 else 1449) else (if t 3 = 0 then 194 else if t 3 = 1 then 1446 else 1452)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1428 else if t 3 = 1 then 1418 else 749) else if t 2 = 1 then (if t 3 = 0 then 1423 else if t 3 = 1 then 1389 else 1396) else (if t 3 = 0 then 162 else if t 3 = 1 then 1393 else 1398)) else (if t 2 = 0 then (if t 3 = 0 then 1429 else if t 3 = 1 then 1419 else 750) else if t 2 = 1 then (if t 3 = 0 then 1424 else if t 3 = 1 then 1391 else 1397) else (if t 3 = 0 then 163 else if t 3 = 1 then 1394 else 1399))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1221 else 3523) else if t 2 = 1 then (if t 3 = 0 then 1011 else if t 3 = 1 then 1776 else 2118) else (if t 3 = 0 then 4059 else if t 3 = 1 then 1779 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1430 else if t 3 = 1 then 1199 else 753) else if t 2 = 1 then (if t 3 = 0 then 989 else if t 3 = 1 then 1400 else 1404) else (if t 3 = 0 then 168 else if t 3 = 1 then 1402 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 1431 else if t 3 = 1 then 1200 else 754) else if t 2 = 1 then (if t 3 = 0 then 990 else if t 3 = 1 then 1401 else 1405) else (if t 3 = 0 then 169 else if t 3 = 1 then 1403 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4767 else (if jt.2.val < 2 then 4783 else 4772)) else (if jt.2.val < 4 then 4782 else (if jt.2.val < 5 then 4784 else 4769))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4605 else (if jt.2.val < 2 then 4610 else 4607)) else (if jt.2.val < 4 then 4608 else (if jt.2.val < 5 then 4609 else 4602)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1383 else (if jt.2.val < 2 then 1385 else 1421)) else (if jt.2.val < 4 then 1384 else (if jt.2.val < 5 then 1420 else 1392))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1380 else (if jt.2.val < 2 then 1382 else 1426)) else (if jt.2.val < 4 then 1381 else (if jt.2.val < 5 then 1425 else 1395)))))

checked_coverage fastCoverage0708 pairing0708 template0708 witness0708

theorem coverage0708 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0708) (maskBits m))
    cores template0708 witness0708 := by
  rw [← coresFast_eq]
  exact fastCoverage0708

theorem coverageSize0708 : ∀ q : Pattern,
    (cores (witness0708 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0708 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0708
#print axioms coverageSize0708

noncomputable def pairing0709 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0709 : List (Fin 4935) := templateData0709

noncomputable def witness0709 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 384 else 1498) else if t 2 = 1 then (if t 3 = 0 then 386 else if t 3 = 1 then 382 else 394) else (if t 3 = 0 then 1501 else if t 3 = 1 then 400 else 406)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 379 else if t 3 = 1 then 356 else 1489) else if t 2 = 1 then (if t 3 = 0 then 371 else if t 3 = 1 then 336 else 339) else (if t 3 = 0 then 892 else if t 3 = 1 then 340 else 341)) else (if t 2 = 0 then (if t 3 = 0 then 4036 else if t 3 = 1 then 3929 else 4539) else if t 2 = 1 then (if t 3 = 0 then 2737 else if t 3 = 1 then 2728 else 3203) else (if t 3 = 0 then 2987 else if t 3 = 1 then 2730 else 3505))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 383 else 1497) else if t 2 = 1 then (if t 3 = 0 then 385 else if t 3 = 1 then 381 else 393) else (if t 3 = 0 then 1500 else if t 3 = 1 then 399 else 405)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 375 else if t 3 = 1 then 346 else 1483) else if t 2 = 1 then (if t 3 = 0 then 363 else if t 3 = 1 then 318 else 322) else (if t 3 = 0 then 888 else if t 3 = 1 then 324 else 326)) else (if t 2 = 0 then (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 1484) else if t 2 = 1 then (if t 3 = 0 then 364 else if t 3 = 1 then 320 else 323) else (if t 3 = 0 then 889 else if t 3 = 1 then 325 else 327))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 930 else 2990) else if t 2 = 1 then (if t 3 = 0 then 2139 else if t 3 = 1 then 924 else 926) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1788 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 377 else if t 3 = 1 then 352 else 1487) else if t 2 = 1 then (if t 3 = 0 then 367 else if t 3 = 1 then 328 else 330) else (if t 3 = 0 then 1494 else if t 3 = 1 then 332 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 378 else if t 3 = 1 then 353 else 1488) else if t 2 = 1 then (if t 3 = 0 then 368 else if t 3 = 1 then 329 else 331) else (if t 3 = 0 then 1495 else if t 3 = 1 then 333 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4791 else (if jt.2.val < 2 then 4807 else 4796)) else (if jt.2.val < 4 then 4806 else (if jt.2.val < 5 then 4808 else 4793))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4290 else (if jt.2.val < 2 then 4301 else 4292)) else (if jt.2.val < 4 then 4299 else (if jt.2.val < 5 then 4300 else 4287)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1479 else (if jt.2.val < 2 then 1481 else 1486)) else (if jt.2.val < 4 then 1480 else (if jt.2.val < 5 then 1485 else 1482))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1395 else (if jt.2.val < 2 then 1492 else 1426)) else (if jt.2.val < 4 then 1491 else (if jt.2.val < 5 then 1493 else 1380)))))

checked_coverage fastCoverage0709 pairing0709 template0709 witness0709

theorem coverage0709 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0709) (maskBits m))
    cores template0709 witness0709 := by
  rw [← coresFast_eq]
  exact fastCoverage0709

theorem coverageSize0709 : ∀ q : Pattern,
    (cores (witness0709 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0709 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0709
#print axioms coverageSize0709

noncomputable def pairing0710 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0710 : List (Fin 4935) := templateData0710

noncomputable def witness0710 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 581 else 1549) else if t 2 = 1 then (if t 3 = 0 then 579 else if t 3 = 1 then 577 else 595) else (if t 3 = 0 then 1546 else if t 3 = 1 then 589 else 601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 574 else if t 3 = 1 then 566 else 1108) else if t 2 = 1 then (if t 3 = 0 then 552 else if t 3 = 1 then 532 else 535) else (if t 3 = 0 then 1537 else if t 3 = 1 then 534 else 536)) else (if t 2 = 0 then (if t 3 = 0 then 3499 else if t 3 = 1 then 2756 else 2983) else if t 2 = 1 then (if t 3 = 0 then 3209 else if t 3 = 1 then 2747 else 2749) else (if t 3 = 0 then 4541 else if t 3 = 1 then 3923 else 4044))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 580 else 1548) else if t 2 = 1 then (if t 3 = 0 then 578 else if t 3 = 1 then 576 else 594) else (if t 3 = 0 then 1545 else if t 3 = 1 then 588 else 600)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 570 else if t 3 = 1 then 556 else 1104) else if t 2 = 1 then (if t 3 = 0 then 544 else if t 3 = 1 then 515 else 520) else (if t 3 = 0 then 1531 else if t 3 = 1 then 517 else 522)) else (if t 2 = 0 then (if t 3 = 0 then 571 else if t 3 = 1 then 557 else 1105) else if t 2 = 1 then (if t 3 = 0 then 545 else if t 3 = 1 then 516 else 521) else (if t 3 = 0 then 1532 else if t 3 = 1 then 518 else 523))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 1836 else 4542) else if t 2 = 1 then (if t 3 = 0 then 1115 else if t 3 = 1 then 1113 else 2148) else (if t 3 = 0 then 2986 else if t 3 = 1 then 1119 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 572 else if t 3 = 1 then 562 else 1542) else if t 2 = 1 then (if t 3 = 0 then 548 else if t 3 = 1 then 524 else 528) else (if t 3 = 0 then 1535 else if t 3 = 1 then 526 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 573 else if t 3 = 1 then 563 else 1543) else if t 2 = 1 then (if t 3 = 0 then 549 else if t 3 = 1 then 525 else 529) else (if t 3 = 0 then 1536 else if t 3 = 1 then 527 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4809 else (if jt.2.val < 2 then 4825 else 4814)) else (if jt.2.val < 4 then 4824 else (if jt.2.val < 5 then 4826 else 4811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3675 else (if jt.2.val < 2 then 3686 else 3677)) else (if jt.2.val < 4 then 3684 else (if jt.2.val < 5 then 3685 else 3672)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1392 else (if jt.2.val < 2 then 1540 else 1421)) else (if jt.2.val < 4 then 1539 else (if jt.2.val < 5 then 1541 else 1383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1527 else (if jt.2.val < 2 then 1529 else 1534)) else (if jt.2.val < 4 then 1528 else (if jt.2.val < 5 then 1533 else 1530)))))

checked_coverage fastCoverage0710 pairing0710 template0710 witness0710

theorem coverage0710 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0710) (maskBits m))
    cores template0710 witness0710 := by
  rw [← coresFast_eq]
  exact fastCoverage0710

theorem coverageSize0710 : ∀ q : Pattern,
    (cores (witness0710 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0710 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0710
#print axioms coverageSize0710

noncomputable def pairing0711 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0711 : List (Fin 4935) := templateData0711

noncomputable def witness0711 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1680 else 786) else if t 2 = 1 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1678 else 1080) else (if t 3 = 0 then 201 else if t 3 = 1 then 864 else 1690)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1660 else 741) else if t 2 = 1 then (if t 3 = 0 then 1669 else if t 3 = 1 then 1644 else 1647) else (if t 3 = 0 then 157 else if t 3 = 1 then 1646 else 1648)) else (if t 2 = 0 then (if t 3 = 0 then 2882 else if t 3 = 1 then 2689 else 3522) else if t 2 = 1 then (if t 3 = 0 then 2545 else if t 3 = 1 then 3232 else 3234) else (if t 3 = 0 then 4058 else if t 3 = 1 then 3963 else 4530))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1679 else 785) else if t 2 = 1 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1677 else 1079) else (if t 3 = 0 then 200 else if t 3 = 1 then 863 else 1689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1656 else 734) else if t 2 = 1 then (if t 3 = 0 then 1665 else if t 3 = 1 then 1628 else 1632) else (if t 3 = 0 then 150 else if t 3 = 1 then 1630 else 1634)) else (if t 2 = 0 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1657 else 735) else if t 2 = 1 then (if t 3 = 0 then 1666 else if t 3 = 1 then 1629 else 1633) else (if t 3 = 0 then 151 else if t 3 = 1 then 1631 else 1635))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1854 else 4061) else if t 2 = 1 then (if t 3 = 0 then 2172 else if t 3 = 1 then 1851 else 1092) else (if t 3 = 0 then 3525 else if t 3 = 1 then 876 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1673 else if t 3 = 1 then 1658 else 738) else if t 2 = 1 then (if t 3 = 0 then 1667 else if t 3 = 1 then 1636 else 1640) else (if t 3 = 0 then 154 else if t 3 = 1 then 1638 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 1674 else if t 3 = 1 then 1659 else 739) else if t 2 = 1 then (if t 3 = 0 then 1668 else if t 3 = 1 then 1637 else 1641) else (if t 3 = 0 then 155 else if t 3 = 1 then 1639 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4836 else (if jt.2.val < 2 then 4843 else 4841)) else (if jt.2.val < 4 then 4842 else (if jt.2.val < 5 then 4844 else 4838))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3651 else (if jt.2.val < 2 then 3668 else 3653)) else (if jt.2.val < 4 then 3666 else (if jt.2.val < 5 then 3667 else 3648)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1482 else (if jt.2.val < 2 then 1654 else 1486)) else (if jt.2.val < 4 then 1653 else (if jt.2.val < 5 then 1655 else 1479))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1530 else (if jt.2.val < 2 then 1663 else 1534)) else (if jt.2.val < 4 then 1662 else (if jt.2.val < 5 then 1664 else 1527)))))

checked_coverage fastCoverage0711 pairing0711 template0711 witness0711

theorem coverage0711 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0711) (maskBits m))
    cores template0711 witness0711 := by
  rw [← coresFast_eq]
  exact fastCoverage0711

theorem coverageSize0711 : ∀ q : Pattern,
    (cores (witness0711 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0711 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0711
#print axioms coverageSize0711

noncomputable def pairing0712 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0712 : List (Fin 4935) := templateData0712

noncomputable def witness0712 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 4213) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3531) else (if t 3 = 0 then 3352 else if t 3 = 1 then 3351 else 2940)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 2199) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 2198) else (if t 3 = 0 then 1882 else if t 3 = 1 then 1880 else 1892)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1611 else 299) else if t 2 = 1 then (if t 3 = 0 then 1612 else if t 3 = 1 then 1610 else 1616) else (if t 3 = 0 then 497 else if t 3 = 1 then 1619 else 1622))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 2073) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 2072) else (if t 3 = 0 then 1723 else if t 3 = 1 then 1721 else 1735)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3465) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4492) else (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4499)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3161 else 3164) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4515) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4516 else 4517))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1331 else 456) else if t 2 = 1 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1330 else 1344) else (if t 3 = 0 then 262 else if t 3 = 1 then 1355 else 1361)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3074 else 3084) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4506) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4507 else 4513)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 3314 else 3316) else if t 2 = 1 then (if t 3 = 0 then 4038 else if t 3 = 1 then 4518 else 4519) else (if t 3 = 0 then 4192 else if t 3 = 1 then 4520 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4836 else (if jt.2.val < 2 then 4840 else 4841)) else (if jt.2.val < 4 then 4837 else (if jt.2.val < 5 then 4839 else 4838))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4602 else (if jt.2.val < 2 then 4604 else 4607)) else (if jt.2.val < 4 then 4603 else (if jt.2.val < 5 then 4606 else 4605)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4576 else (if jt.2.val < 2 then 4580 else 4581)) else (if jt.2.val < 4 then 4577 else (if jt.2.val < 5 then 4579 else 4578))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4746 else (if jt.2.val < 2 then 4750 else 4751)) else (if jt.2.val < 4 then 4747 else (if jt.2.val < 5 then 4749 else 4748)))))

checked_coverage fastCoverage0712 pairing0712 template0712 witness0712

theorem coverage0712 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0712) (maskBits m))
    cores template0712 witness0712 := by
  rw [← coresFast_eq]
  exact fastCoverage0712

theorem coverageSize0712 : ∀ q : Pattern,
    (cores (witness0712 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0712 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0712
#print axioms coverageSize0712

noncomputable def pairing0713 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0713 : List (Fin 4935) := templateData0713

noncomputable def witness0713 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 4546) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 3530) else (if t 3 = 0 then 2997 else if t 3 = 1 then 2996 else 3330)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 2197) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 2196) else (if t 3 = 0 then 1174 else if t 3 = 1 then 1172 else 1189)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 681 else 1475) else if t 2 = 1 then (if t 3 = 0 then 682 else if t 3 = 1 then 680 else 688) else (if t 3 = 0 then 1526 else if t 3 = 1 then 694 else 698))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 2071) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 2070) else (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 840)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 3464) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4155) else (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4164)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2574) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4180) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4181 else 4182))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 35 else 1512) else if t 2 = 1 then (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 53) else (if t 3 = 0 then 1472 else if t 3 = 1 then 70 else 77)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2475) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4171) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4177 else 4178)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2885 else 2887) else if t 2 = 1 then (if t 3 = 0 then 4039 else if t 3 = 1 then 4183 else 4184) else (if t 3 = 0 then 4526 else if t 3 = 1 then 4185 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4827 else (if jt.2.val < 2 then 4831 else 4832)) else (if jt.2.val < 4 then 4828 else (if jt.2.val < 5 then 4830 else 4829))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4305 else (if jt.2.val < 2 then 4307 else 4310)) else (if jt.2.val < 4 then 4306 else (if jt.2.val < 5 then 4309 else 4308)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4261 else (if jt.2.val < 2 then 4265 else 4266)) else (if jt.2.val < 4 then 4262 else (if jt.2.val < 5 then 4264 else 4263))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4748 else (if jt.2.val < 2 then 4754 else 4751)) else (if jt.2.val < 4 then 4752 else (if jt.2.val < 5 then 4753 else 4746)))))

checked_coverage fastCoverage0713 pairing0713 template0713 witness0713

theorem coverage0713 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0713) (maskBits m))
    cores template0713 witness0713 := by
  rw [← coresFast_eq]
  exact fastCoverage0713

theorem coverageSize0713 : ∀ q : Pattern,
    (cores (witness0713 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0713 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0713
#print axioms coverageSize0713

noncomputable def pairing0714 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0714 : List (Fin 4935) := templateData0714

noncomputable def witness0714 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3258 else 2974) else if t 2 = 1 then (if t 3 = 0 then 3254 else if t 3 = 1 then 3250 else 2972) else (if t 3 = 0 then 4537 else if t 3 = 1 then 4064 else 4198)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3256 else 965) else if t 2 = 1 then (if t 3 = 0 then 3252 else if t 3 = 1 then 3248 else 961) else (if t 3 = 0 then 1879 else if t 3 = 1 then 1877 else 978)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 88 else 1478) else if t 2 = 1 then (if t 3 = 0 then 87 else if t 3 = 1 then 86 else 100) else (if t 3 = 0 then 1523 else if t 3 = 1 then 94 else 104))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3257 else 1043) else if t 2 = 1 then (if t 3 = 0 then 3253 else if t 3 = 1 then 3249 else 1039) else (if t 3 = 0 then 1720 else if t 3 = 1 then 1718 else 1055)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3255 else 3278) else if t 2 = 1 then (if t 3 = 0 then 3251 else if t 3 = 1 then 3247 else 3276) else (if t 3 = 0 then 3269 else if t 3 = 1 then 3267 else 3279)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 3165 else 3167) else if t 2 = 1 then (if t 3 = 0 then 2717 else if t 3 = 1 then 3295 else 3297) else (if t 3 = 0 then 2719 else if t 3 = 1 then 3296 else 3298))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 638 else 1520) else if t 2 = 1 then (if t 3 = 0 then 637 else if t 3 = 1 then 636 else 664) else (if t 3 = 0 then 1464 else if t 3 = 1 then 651 else 671)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 3091 else 3095) else if t 2 = 1 then (if t 3 = 0 then 2623 else if t 3 = 1 then 3291 else 3293) else (if t 3 = 0 then 2627 else if t 3 = 1 then 3292 else 3294)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 3500 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2904 else if t 3 = 1 then 3299 else 3301) else (if t 3 = 0 then 2905 else if t 3 = 1 then 3300 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4755 else (if jt.2.val < 2 then 4759 else 4760)) else (if jt.2.val < 4 then 4756 else (if jt.2.val < 5 then 4758 else 4757))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3636 else (if jt.2.val < 2 then 3638 else 3641)) else (if jt.2.val < 4 then 3637 else (if jt.2.val < 5 then 3640 else 3639)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4578 else (if jt.2.val < 2 then 4589 else 4581)) else (if jt.2.val < 4 then 4587 else (if jt.2.val < 5 then 4588 else 4576))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3556 else (if jt.2.val < 2 then 3560 else 3561)) else (if jt.2.val < 4 then 3557 else (if jt.2.val < 5 then 3559 else 3558)))))

checked_coverage fastCoverage0714 pairing0714 template0714 witness0714

theorem coverage0714 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0714) (maskBits m))
    cores template0714 witness0714 := by
  rw [← coresFast_eq]
  exact fastCoverage0714

theorem coverageSize0714 : ∀ q : Pattern,
    (cores (witness0714 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0714 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0714
#print axioms coverageSize0714

noncomputable def pairing0715 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0715 : List (Fin 4935) := templateData0715

noncomputable def witness0715 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2817 else 3340) else if t 2 = 1 then (if t 3 = 0 then 2813 else if t 3 = 1 then 2809 else 3338) else (if t 3 = 0 then 4203 else if t 3 = 1 then 4054 else 4532)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2815 else 964) else if t 2 = 1 then (if t 3 = 0 then 2811 else if t 3 = 1 then 2807 else 960) else (if t 3 = 0 then 1171 else if t 3 = 1 then 1169 else 1801)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1372 else 305) else if t 2 = 1 then (if t 3 = 0 then 1371 else if t 3 = 1 then 1370 else 1001) else (if t 3 = 0 then 503 else if t 3 = 1 then 1211 else 1376))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2816 else 1042) else if t 2 = 1 then (if t 3 = 0 then 2812 else if t 3 = 1 then 2808 else 1038) else (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 1817)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2814 else 2838) else if t 2 = 1 then (if t 3 = 0 then 2810 else if t 3 = 1 then 2806 else 2835) else (if t 3 = 0 then 2828 else if t 3 = 1 then 2826 else 2840)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2576 else 2579) else if t 2 = 1 then (if t 3 = 0 then 2721 else if t 3 = 1 then 2859 else 2862) else (if t 3 = 0 then 2723 else if t 3 = 1 then 2861 else 2863))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1586 else 473) else if t 2 = 1 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1584 else 1073) else (if t 3 = 0 then 275 else if t 3 = 1 then 857 else 1601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2484 else 2489) else if t 2 = 1 then (if t 3 = 0 then 2632 else if t 3 = 1 then 2854 else 2857) else (if t 3 = 0 then 2635 else if t 3 = 1 then 2856 else 2858)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3506 else 4197) else if t 2 = 1 then (if t 3 = 0 then 3321 else if t 3 = 1 then 2864 else 2866) else (if t 3 = 0 then 3322 else if t 3 = 1 then 2865 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4767 else (if jt.2.val < 2 then 4771 else 4772)) else (if jt.2.val < 4 then 4768 else (if jt.2.val < 5 then 4770 else 4769))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3648 else (if jt.2.val < 2 then 3650 else 3653)) else (if jt.2.val < 4 then 3649 else (if jt.2.val < 5 then 3652 else 3651)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4263 else (if jt.2.val < 2 then 4274 else 4266)) else (if jt.2.val < 4 then 4272 else (if jt.2.val < 5 then 4273 else 4261))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3558 else (if jt.2.val < 2 then 3576 else 3561)) else (if jt.2.val < 4 then 3573 else (if jt.2.val < 5 then 3574 else 3556)))))

checked_coverage fastCoverage0715 pairing0715 template0715 witness0715

theorem coverage0715 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0715) (maskBits m))
    cores template0715 witness0715 := by
  rw [← coresFast_eq]
  exact fastCoverage0715

theorem coverageSize0715 : ∀ q : Pattern,
    (cores (witness0715 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0715 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0715
#print axioms coverageSize0715

noncomputable def pairing0716 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0716 : List (Fin 4935) := templateData0716

noncomputable def witness0716 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1437 else 591) else if t 2 = 1 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1435 else 1447) else (if t 3 = 0 then 396 else if t 3 = 1 then 1450 else 1453)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1432 else if t 3 = 1 then 1422 else 567) else if t 2 = 1 then (if t 3 = 0 then 1427 else if t 3 = 1 then 1408 else 1411) else (if t 3 = 0 then 372 else if t 3 = 1 then 1412 else 1413)) else (if t 2 = 0 then (if t 3 = 0 then 4525 else if t 3 = 1 then 3953 else 4207) else if t 2 = 1 then (if t 3 = 0 then 3225 else if t 3 = 1 then 3219 else 2630) else (if t 3 = 0 then 3344 else if t 3 = 1 then 2482 else 2898))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1436 else 590) else if t 2 = 1 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1434 else 1446) else (if t 3 = 0 then 395 else if t 3 = 1 then 1449 else 1452)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1428 else if t 3 = 1 then 1418 else 558) else if t 2 = 1 then (if t 3 = 0 then 1423 else if t 3 = 1 then 1389 else 1393) else (if t 3 = 0 then 365 else if t 3 = 1 then 1396 else 1398)) else (if t 2 = 0 then (if t 3 = 0 then 1429 else if t 3 = 1 then 1419 else 559) else if t 2 = 1 then (if t 3 = 0 then 1424 else if t 3 = 1 then 1391 else 1394) else (if t 3 = 0 then 366 else if t 3 = 1 then 1397 else 1399))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1221 else 3343) else if t 2 = 1 then (if t 3 = 0 then 1011 else if t 3 = 1 then 1776 else 1779) else (if t 3 = 0 then 4206 else if t 3 = 1 then 2118 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1430 else if t 3 = 1 then 1199 else 564) else if t 2 = 1 then (if t 3 = 0 then 989 else if t 3 = 1 then 1400 else 1402) else (if t 3 = 0 then 369 else if t 3 = 1 then 1404 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 1431 else if t 3 = 1 then 1200 else 565) else if t 2 = 1 then (if t 3 = 0 then 990 else if t 3 = 1 then 1401 else 1403) else (if t 3 = 0 then 370 else if t 3 = 1 then 1405 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4767 else (if jt.2.val < 2 then 4783 else 4772)) else (if jt.2.val < 4 then 4782 else (if jt.2.val < 5 then 4784 else 4769))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4605 else (if jt.2.val < 2 then 4610 else 4607)) else (if jt.2.val < 4 then 4608 else (if jt.2.val < 5 then 4609 else 4602)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1983 else (if jt.2.val < 2 then 1985 else 1992)) else (if jt.2.val < 4 then 1984 else (if jt.2.val < 5 then 1991 else 1990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1986 else (if jt.2.val < 2 then 1988 else 1994)) else (if jt.2.val < 4 then 1987 else (if jt.2.val < 5 then 1993 else 1989)))))

checked_coverage fastCoverage0716 pairing0716 template0716 witness0716

theorem coverage0716 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0716) (maskBits m))
    cores template0716 witness0716 := by
  rw [← coresFast_eq]
  exact fastCoverage0716

theorem coverageSize0716 : ∀ q : Pattern,
    (cores (witness0716 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0716 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0716
#print axioms coverageSize0716

noncomputable def pairing0717 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0717 : List (Fin 4935) := templateData0717

noncomputable def witness0717 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 183 else 1546) else if t 2 = 1 then (if t 3 = 0 then 185 else if t 3 = 1 then 181 else 193) else (if t 3 = 0 then 1501 else if t 3 = 1 then 199 else 205)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 178 else if t 3 = 1 then 156 else 1537) else if t 2 = 1 then (if t 3 = 0 then 170 else if t 3 = 1 then 136 else 139) else (if t 3 = 0 then 892 else if t 3 = 1 then 140 else 141)) else (if t 2 = 0 then (if t 3 = 0 then 4190 else if t 3 = 1 then 3945 else 4541) else if t 2 = 1 then (if t 3 = 0 then 2775 else if t 3 = 1 then 2766 else 3172) else (if t 3 = 0 then 2987 else if t 3 = 1 then 2768 else 3320))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 182 else 1545) else if t 2 = 1 then (if t 3 = 0 then 184 else if t 3 = 1 then 180 else 192) else (if t 3 = 0 then 1500 else if t 3 = 1 then 198 else 204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 174 else if t 3 = 1 then 146 else 1531) else if t 2 = 1 then (if t 3 = 0 then 160 else if t 3 = 1 then 117 else 121) else (if t 3 = 0 then 888 else if t 3 = 1 then 124 else 126)) else (if t 2 = 0 then (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 1532) else if t 2 = 1 then (if t 3 = 0 then 161 else if t 3 = 1 then 119 else 122) else (if t 3 = 0 then 889 else if t 3 = 1 then 125 else 127))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 899 else 2986) else if t 2 = 1 then (if t 3 = 0 then 1806 else if t 3 = 1 then 897 else 903) else (if t 3 = 0 then 4540 else if t 3 = 1 then 2127 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 176 else if t 3 = 1 then 152 else 1535) else if t 2 = 1 then (if t 3 = 0 then 166 else if t 3 = 1 then 128 else 130) else (if t 3 = 0 then 1494 else if t 3 = 1 then 132 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 177 else if t 3 = 1 then 153 else 1536) else if t 2 = 1 then (if t 3 = 0 then 167 else if t 3 = 1 then 129 else 131) else (if t 3 = 0 then 1495 else if t 3 = 1 then 133 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4755 else (if jt.2.val < 2 then 4789 else 4760)) else (if jt.2.val < 4 then 4788 else (if jt.2.val < 5 then 4790 else 4757))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4308 else (if jt.2.val < 2 then 4313 else 4310)) else (if jt.2.val < 4 then 4311 else (if jt.2.val < 5 then 4312 else 4305)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2004 else (if jt.2.val < 2 then 2006 else 2009)) else (if jt.2.val < 4 then 2005 else (if jt.2.val < 5 then 2008 else 2007))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1989 else (if jt.2.val < 2 then 2011 else 1994)) else (if jt.2.val < 4 then 2010 else (if jt.2.val < 5 then 2012 else 1986)))))

checked_coverage fastCoverage0717 pairing0717 template0717 witness0717

theorem coverage0717 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0717) (maskBits m))
    cores template0717 witness0717 := by
  rw [← coresFast_eq]
  exact fastCoverage0717

theorem coverageSize0717 : ∀ q : Pattern,
    (cores (witness0717 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0717 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0717
#print axioms coverageSize0717

noncomputable def pairing0718 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0718 : List (Fin 4935) := templateData0718

noncomputable def witness0718 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 770 else 1549) else if t 2 = 1 then (if t 3 = 0 then 768 else if t 3 = 1 then 766 else 784) else (if t 3 = 0 then 1498 else if t 3 = 1 then 778 else 790)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 763 else if t 3 = 1 then 755 else 1108) else if t 2 = 1 then (if t 3 = 0 then 740 else if t 3 = 1 then 720 else 723) else (if t 3 = 0 then 1489 else if t 3 = 1 then 722 else 724)) else (if t 2 = 0 then (if t 3 = 0 then 3312 else if t 3 = 1 then 2794 else 2983) else if t 2 = 1 then (if t 3 = 0 then 3191 else if t 3 = 1 then 2785 else 2787) else (if t 3 = 0 then 4539 else if t 3 = 1 then 3939 else 4196))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 769 else 1548) else if t 2 = 1 then (if t 3 = 0 then 767 else if t 3 = 1 then 765 else 783) else (if t 3 = 0 then 1497 else if t 3 = 1 then 777 else 789)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 759 else if t 3 = 1 then 747 else 1104) else if t 2 = 1 then (if t 3 = 0 then 732 else if t 3 = 1 then 704 else 708) else (if t 3 = 0 then 1483 else if t 3 = 1 then 706 else 710)) else (if t 2 = 0 then (if t 3 = 0 then 760 else if t 3 = 1 then 748 else 1105) else if t 2 = 1 then (if t 3 = 0 then 733 else if t 3 = 1 then 705 else 709) else (if t 3 = 0 then 1484 else if t 3 = 1 then 707 else 711))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 2160 else 4542) else if t 2 = 1 then (if t 3 = 0 then 1146 else if t 3 = 1 then 1140 else 1824) else (if t 3 = 0 then 2990 else if t 3 = 1 then 1142 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 761 else if t 3 = 1 then 751 else 1542) else if t 2 = 1 then (if t 3 = 0 then 736 else if t 3 = 1 then 712 else 716) else (if t 3 = 0 then 1487 else if t 3 = 1 then 714 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 762 else if t 3 = 1 then 752 else 1543) else if t 2 = 1 then (if t 3 = 0 then 737 else if t 3 = 1 then 713 else 717) else (if t 3 = 0 then 1488 else if t 3 = 1 then 715 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4827 else (if jt.2.val < 2 then 4834 else 4832)) else (if jt.2.val < 4 then 4833 else (if jt.2.val < 5 then 4835 else 4829))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3639 else (if jt.2.val < 2 then 3662 else 3641)) else (if jt.2.val < 4 then 3660 else (if jt.2.val < 5 then 3661 else 3636)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1990 else (if jt.2.val < 2 then 2029 else 1992)) else (if jt.2.val < 4 then 2028 else (if jt.2.val < 5 then 2030 else 1983))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2022 else (if jt.2.val < 2 then 2024 else 2027)) else (if jt.2.val < 4 then 2023 else (if jt.2.val < 5 then 2026 else 2025)))))

checked_coverage fastCoverage0718 pairing0718 template0718 witness0718

theorem coverage0718 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0718) (maskBits m))
    cores template0718 witness0718 := by
  rw [← coresFast_eq]
  exact fastCoverage0718

theorem coverageSize0718 : ∀ q : Pattern,
    (cores (witness0718 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0718 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0718
#print axioms coverageSize0718

noncomputable def pairing0719 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0719 : List (Fin 4935) := templateData0719

noncomputable def witness0719 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1682 else 597) else if t 2 = 1 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1678 else 1080) else (if t 3 = 0 then 402 else if t 3 = 1 then 864 else 1690)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1669 else 553) else if t 2 = 1 then (if t 3 = 0 then 1660 else if t 3 = 1 then 1644 else 1647) else (if t 3 = 0 then 357 else if t 3 = 1 then 1646 else 1648)) else (if t 2 = 0 then (if t 3 = 0 then 2882 else if t 3 = 1 then 2545 else 3342) else if t 2 = 1 then (if t 3 = 0 then 2689 else if t 3 = 1 then 3232 else 3234) else (if t 3 = 0 then 4205 else if t 3 = 1 then 3963 else 4530))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1681 else 596) else if t 2 = 1 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1677 else 1079) else (if t 3 = 0 then 401 else if t 3 = 1 then 863 else 1689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1665 else 546) else if t 2 = 1 then (if t 3 = 0 then 1656 else if t 3 = 1 then 1628 else 1632) else (if t 3 = 0 then 350 else if t 3 = 1 then 1630 else 1634)) else (if t 2 = 0 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1666 else 547) else if t 2 = 1 then (if t 3 = 0 then 1657 else if t 3 = 1 then 1629 else 1633) else (if t 3 = 0 then 351 else if t 3 = 1 then 1631 else 1635))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 2172 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1854 else if t 3 = 1 then 1851 else 1092) else (if t 3 = 0 then 3345 else if t 3 = 1 then 876 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1673 else if t 3 = 1 then 1667 else 550) else if t 2 = 1 then (if t 3 = 0 then 1658 else if t 3 = 1 then 1636 else 1640) else (if t 3 = 0 then 354 else if t 3 = 1 then 1638 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 1674 else if t 3 = 1 then 1668 else 551) else if t 2 = 1 then (if t 3 = 0 then 1659 else if t 3 = 1 then 1637 else 1641) else (if t 3 = 0 then 355 else if t 3 = 1 then 1639 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4836 else (if jt.2.val < 2 then 4843 else 4841)) else (if jt.2.val < 4 then 4842 else (if jt.2.val < 5 then 4844 else 4838))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3651 else (if jt.2.val < 2 then 3668 else 3653)) else (if jt.2.val < 4 then 3666 else (if jt.2.val < 5 then 3667 else 3648)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2007 else (if jt.2.val < 2 then 2041 else 2009)) else (if jt.2.val < 4 then 2040 else (if jt.2.val < 5 then 2042 else 2004))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2025 else (if jt.2.val < 2 then 2038 else 2027)) else (if jt.2.val < 4 then 2037 else (if jt.2.val < 5 then 2039 else 2022)))))

checked_coverage fastCoverage0719 pairing0719 template0719 witness0719

theorem coverage0719 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0719) (maskBits m))
    cores template0719 witness0719 := by
  rw [← coresFast_eq]
  exact fastCoverage0719

theorem coverageSize0719 : ∀ q : Pattern,
    (cores (witness0719 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0719 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0719
#print axioms coverageSize0719

end Crown.CertificateData
