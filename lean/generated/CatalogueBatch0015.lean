import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0014

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0560 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0560 : List (Fin 4935) := templateData0560

noncomputable def witness0560 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 3959) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3227) else (if t 3 = 0 then 3532 else if t 3 = 1 then 3531 else 2649)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1611) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1610) else (if t 3 = 0 then 2200 else if t 3 = 1 then 2198 else 1616)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1650 else 878) else if t 2 = 1 then (if t 3 = 0 then 1651 else if t 3 = 1 then 1649 else 1853) else (if t 3 = 0 then 743 else if t 3 = 1 then 1661 else 1856))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1443) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1442) else (if t 3 = 0 then 2074 else if t 3 = 1 then 2072 else 1448)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3161) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4514) else (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4515)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3074 else 3314) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4518) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4506 else 4519))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1722 else 782) else if t 2 = 1 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1721 else 1451) else (if t 3 = 0 then 841 else if t 3 = 1 then 1735 else 1454)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3270 else 3166) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4516) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4499 else 4517)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 3093 else 3501) else if t 2 = 1 then (if t 3 = 0 then 3847 else if t 3 = 1 then 4507 else 4520) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4513 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4710 else (if jt.2.val < 2 then 4720 else 4721)) else (if jt.2.val < 4 then 4717 else (if jt.2.val < 5 then 4719 else 4718))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4575 else (if jt.2.val < 2 then 4585 else 4586)) else (if jt.2.val < 4 then 4582 else (if jt.2.val < 5 then 4584 else 4583)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4737 else (if jt.2.val < 2 then 4741 else 4742)) else (if jt.2.val < 4 then 4738 else (if jt.2.val < 5 then 4740 else 4739))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4467 else (if jt.2.val < 2 then 4509 else 4512)) else (if jt.2.val < 4 then 4508 else (if jt.2.val < 5 then 4511 else 4510)))))

checked_coverage fastCoverage0560 pairing0560 template0560 witness0560

theorem coverage0560 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0560) (maskBits m))
    cores template0560 witness0560 := by
  rw [← coresFast_eq]
  exact fastCoverage0560

theorem coverageSize0560 : ∀ q : Pattern,
    (cores (witness0560 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0560 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0560
#print axioms coverageSize0560

noncomputable def pairing0561 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0561 : List (Fin 4935) := templateData0561

noncomputable def witness0561 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4525) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 3225) else (if t 3 = 0 then 2779 else if t 3 = 1 then 2775 else 3524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 1597) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 1593) else (if t 3 = 0 then 682 else if t 3 = 1 then 654 else 656)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1075 else 1599) else if t 2 = 1 then (if t 3 = 0 then 1090 else if t 3 = 1 then 1069 else 1071) else (if t 3 = 0 then 1826 else if t 3 = 1 then 659 else 661))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 1429) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 1424) else (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 163)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 3146) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3875) else (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3878)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2950) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3885) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3886 else 3887))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 376 else 1774) else if t 2 = 1 then (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 366) else (if t 3 = 0 then 1502 else if t 3 = 1 then 889 else 891)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2698) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3881) else (if t 3 = 0 then 3919 else if t 3 = 1 then 3882 else 3883)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2700 else 2702) else if t 2 = 1 then (if t 3 = 0 then 4191 else if t 3 = 1 then 3888 else 3889) else (if t 3 = 0 then 4526 else if t 3 = 1 then 3890 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4680 else (if jt.2.val < 2 then 4682 else 4685)) else (if jt.2.val < 4 then 4681 else (if jt.2.val < 5 then 4684 else 4683))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4245 else (if jt.2.val < 2 then 4247 else 4250)) else (if jt.2.val < 4 then 4246 else (if jt.2.val < 5 then 4249 else 4248)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4110 else (if jt.2.val < 2 then 4112 else 4118)) else (if jt.2.val < 4 then 4111 else (if jt.2.val < 5 then 4117 else 4113))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4510 else (if jt.2.val < 2 then 4524 else 4512)) else (if jt.2.val < 4 then 4522 else (if jt.2.val < 5 then 4523 else 4467)))))

checked_coverage fastCoverage0561 pairing0561 template0561 witness0561

theorem coverage0561 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0561) (maskBits m))
    cores template0561 witness0561 := by
  rw [← coresFast_eq]
  exact fastCoverage0561

theorem coverageSize0561 : ∀ q : Pattern,
    (cores (witness0561 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0561 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0561
#print axioms coverageSize0561

noncomputable def pairing0562 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0562 : List (Fin 4935) := templateData0562

noncomputable def witness0562 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3453 else 2760) else if t 2 = 1 then (if t 3 = 0 then 3449 else if t 3 = 1 then 3445 else 2759) else (if t 3 = 0 then 4546 else if t 3 = 1 then 4211 else 3927)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3451 else 292) else if t 2 = 1 then (if t 3 = 0 then 3447 else if t 3 = 1 then 3443 else 290) else (if t 3 = 0 then 2197 else if t 3 = 1 then 2195 else 298)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 344 else 1790) else if t 2 = 1 then (if t 3 = 0 then 343 else if t 3 = 1 then 342 else 928) else (if t 3 = 0 then 1490 else if t 3 = 1 then 358 else 932))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3452 else 586) else if t 2 = 1 then (if t 3 = 0 then 3448 else if t 3 = 1 then 3444 else 584) else (if t 3 = 0 then 2071 else if t 3 = 1 then 2069 else 592)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3450 else 3163) else if t 2 = 1 then (if t 3 = 0 then 3446 else if t 3 = 1 then 3442 else 3488) else (if t 3 = 0 then 3464 else if t 3 = 1 then 3462 else 3489)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 3082 else 3315) else if t 2 = 1 then (if t 3 = 0 then 2471 else if t 3 = 1 then 3479 else 3492) else (if t 3 = 0 then 2475 else if t 3 = 1 then 3480 else 3493))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1043 else 1550) else if t 2 = 1 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1041 else 598) else (if t 3 = 0 then 1818 else if t 3 = 1 then 1056 else 602)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 3278 else 3167) else if t 2 = 1 then (if t 3 = 0 then 2838 else if t 3 = 1 then 3472 else 3490) else (if t 3 = 0 then 2842 else if t 3 = 1 then 3473 else 3491)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 3095 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2489 else if t 3 = 1 then 3486 else 3494) else (if t 3 = 0 then 2491 else if t 3 = 1 then 3487 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4647 else (if jt.2.val < 2 then 4657 else 4658)) else (if jt.2.val < 4 then 4654 else (if jt.2.val < 5 then 4656 else 4655))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3600 else (if jt.2.val < 2 then 3610 else 3611)) else (if jt.2.val < 4 then 3607 else (if jt.2.val < 5 then 3609 else 3608)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4739 else (if jt.2.val < 2 then 4745 else 4742)) else (if jt.2.val < 4 then 4743 else (if jt.2.val < 5 then 4744 else 4737))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3537 else (if jt.2.val < 2 then 3545 else 3548)) else (if jt.2.val < 4 then 3544 else (if jt.2.val < 5 then 3547 else 3546)))))

checked_coverage fastCoverage0562 pairing0562 template0562 witness0562

theorem coverage0562 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0562) (maskBits m))
    cores template0562 witness0562 := by
  rw [← coresFast_eq]
  exact fastCoverage0562

theorem coverageSize0562 : ∀ q : Pattern,
    (cores (witness0562 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0562 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0562
#print axioms coverageSize0562

noncomputable def pairing0563 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0563 : List (Fin 4935) := templateData0563

noncomputable def witness0563 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2560 else 3499) else if t 2 = 1 then (if t 3 = 0 then 2565 else if t 3 = 1 then 2544 else 3209) else (if t 3 = 0 then 3951 else if t 3 = 1 then 3945 else 4541)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2558 else 277) else if t 2 = 1 then (if t 3 = 0 then 2563 else if t 3 = 1 then 2538 else 251) else (if t 3 = 0 then 681 else if t 3 = 1 then 641 else 1459)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1750 else 279) else if t 2 = 1 then (if t 3 = 0 then 1762 else if t 3 = 1 then 1747 else 256) else (if t 3 = 0 then 1145 else if t 3 = 1 then 646 else 1462))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2559 else 571) else if t 2 = 1 then (if t 3 = 0 then 2564 else if t 3 = 1 then 2541 else 545) else (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 1532)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2548 else 2550) else if t 2 = 1 then (if t 3 = 0 then 2562 else if t 3 = 1 then 2519 else 2523) else (if t 3 = 0 then 2570 else if t 3 = 1 then 2521 else 2524)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2554 else 2556) else if t 2 = 1 then (if t 3 = 0 then 2883 else if t 3 = 1 then 2530 else 2532) else (if t 3 = 0 then 2885 else if t 3 = 1 then 2531 else 2533))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1672 else 1111) else if t 2 = 1 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1666 else 547) else (if t 3 = 0 then 203 else if t 3 = 1 then 151 else 1834)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2878 else 2880) else if t 2 = 1 then (if t 3 = 0 then 2576 else if t 3 = 1 then 2526 else 2528) else (if t 3 = 0 then 2578 else if t 3 = 1 then 2527 else 2529)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3196 else 3934) else if t 2 = 1 then (if t 3 = 0 then 3506 else if t 3 = 1 then 2534 else 2536) else (if t 3 = 0 then 3507 else if t 3 = 1 then 2535 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4629 else (if jt.2.val < 2 then 4631 else 4634)) else (if jt.2.val < 4 then 4630 else (if jt.2.val < 5 then 4633 else 4632))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3582 else (if jt.2.val < 2 then 3584 else 3587)) else (if jt.2.val < 4 then 3583 else (if jt.2.val < 5 then 3586 else 3585)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4113 else (if jt.2.val < 2 then 4123 else 4118)) else (if jt.2.val < 4 then 4122 else (if jt.2.val < 5 then 4124 else 4110))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3546 else (if jt.2.val < 2 then 3554 else 3548)) else (if jt.2.val < 4 then 3552 else (if jt.2.val < 5 then 3553 else 3537)))))

checked_coverage fastCoverage0563 pairing0563 template0563 witness0563

theorem coverage0563 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0563) (maskBits m))
    cores template0563 witness0563 := by
  rw [← coresFast_eq]
  exact fastCoverage0563

theorem coverageSize0563 : ∀ q : Pattern,
    (cores (witness0563 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0563 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0563
#print axioms coverageSize0563

noncomputable def pairing0564 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0564 : List (Fin 4935) := templateData0564

noncomputable def witness0564 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1316 else 1222) else if t 2 = 1 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1314 else 1777) else (if t 3 = 0 then 50 else if t 3 = 1 then 1342 else 1780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1312 else if t 3 = 1 then 1308 else 1211) else if t 2 = 1 then (if t 3 = 0 then 1310 else if t 3 = 1 then 1306 else 1370) else (if t 3 = 0 then 46 else if t 3 = 1 then 1339 else 1371)) else (if t 2 = 0 then (if t 3 = 0 then 4530 else if t 3 = 1 then 3963 else 3967) else if t 2 = 1 then (if t 3 = 0 then 3234 else if t 3 = 1 then 3232 else 2860) else (if t 3 = 0 then 3522 else if t 3 = 1 then 2689 else 2722))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1315 else 1221) else if t 2 = 1 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1313 else 1776) else (if t 3 = 0 then 49 else if t 3 = 1 then 1341 else 1779)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1311 else if t 3 = 1 then 1307 else 1208) else if t 2 = 1 then (if t 3 = 0 then 1309 else if t 3 = 1 then 1305 else 1362) else (if t 3 = 0 then 45 else if t 3 = 1 then 1338 else 1364)) else (if t 2 = 0 then (if t 3 = 0 then 1329 else if t 3 = 1 then 1327 else 1209) else if t 2 = 1 then (if t 3 = 0 then 1328 else if t 3 = 1 then 1325 else 1363) else (if t 3 = 0 then 52 else if t 3 = 1 then 1343 else 1365))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 647 else 3523) else if t 2 = 1 then (if t 3 = 0 then 257 else if t 3 = 1 then 1352 else 2118) else (if t 3 = 0 then 3942 else if t 3 = 1 then 1358 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1785 else if t 3 = 1 then 643 else 692) else if t 2 = 1 then (if t 3 = 0 then 253 else if t 3 = 1 then 1349 else 1366) else (if t 3 = 0 then 921 else if t 3 = 1 then 1356 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 1787 else if t 3 = 1 then 650 else 693) else if t 2 = 1 then (if t 3 = 0 then 260 else if t 3 = 1 then 1354 else 1367) else (if t 3 = 0 then 923 else if t 3 = 1 then 1360 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4629 else (if jt.2.val < 2 then 4637 else 4634)) else (if jt.2.val < 4 then 4635 else (if jt.2.val < 5 then 4636 else 4632))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4583 else (if jt.2.val < 2 then 4592 else 4586)) else (if jt.2.val < 4 then 4590 else (if jt.2.val < 5 then 4591 else 4575)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1303 else (if jt.2.val < 2 then 1337 else 1340)) else (if jt.2.val < 4 then 1334 else (if jt.2.val < 5 then 1336 else 1335))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1931 else (if jt.2.val < 2 then 1933 else 1937)) else (if jt.2.val < 4 then 1932 else (if jt.2.val < 5 then 1936 else 1935)))))

checked_coverage fastCoverage0564 pairing0564 template0564 witness0564

theorem coverage0564 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0564) (maskBits m))
    cores template0564 witness0564 := by
  rw [← coresFast_eq]
  exact fastCoverage0564

theorem coverageSize0564 : ∀ q : Pattern,
    (cores (witness0564 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0564 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0564
#print axioms coverageSize0564

noncomputable def pairing0565 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0565 : List (Fin 4935) := templateData0565

noncomputable def witness0565 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 995 else 1433) else if t 2 = 1 then (if t 3 = 0 then 1006 else if t 3 = 1 then 991 else 992) else (if t 3 = 0 then 1807 else if t 3 = 1 then 172 else 173)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1004 else if t 3 = 1 then 977 else 1801) else if t 2 = 1 then (if t 3 = 0 then 1000 else if t 3 = 1 then 957 else 960) else (if t 3 = 0 then 100 else if t 3 = 1 then 961 else 962)) else (if t 2 = 0 then (if t 3 = 0 then 3860 else if t 3 = 1 then 4046 else 4532) else if t 2 = 1 then (if t 3 = 0 then 2980 else if t 3 = 1 then 2970 else 3338) else (if t 3 = 0 then 2800 else if t 3 = 1 then 2972 else 3520))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 993 else 1430) else if t 2 = 1 then (if t 3 = 0 then 1005 else if t 3 = 1 then 987 else 989) else (if t 3 = 0 then 1806 else if t 3 = 1 then 166 else 168)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1002 else if t 3 = 1 then 967 else 1795) else if t 2 = 1 then (if t 3 = 0 then 996 else if t 3 = 1 then 939 else 943) else (if t 3 = 0 then 96 else if t 3 = 1 then 945 else 947)) else (if t 2 = 0 then (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 1796) else if t 2 = 1 then (if t 3 = 0 then 997 else if t 3 = 1 then 941 else 944) else (if t 3 = 0 then 97 else if t 3 = 1 then 946 else 948))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 377 else 2796) else if t 2 = 1 then (if t 3 = 0 then 2139 else if t 3 = 1 then 367 else 369) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1494 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 306 else if t 3 = 1 then 973 else 1799) else if t 2 = 1 then (if t 3 = 0 then 300 else if t 3 = 1 then 949 else 951) else (if t 3 = 0 then 1476 else if t 3 = 1 then 953 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 307 else if t 3 = 1 then 974 else 1800) else if t 2 = 1 then (if t 3 = 0 then 301 else if t 3 = 1 then 950 else 952) else (if t 3 = 0 then 1477 else if t 3 = 1 then 954 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4647 else (if jt.2.val < 2 then 4672 else 4658)) else (if jt.2.val < 4 then 4671 else (if jt.2.val < 5 then 4673 else 4655))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4248 else (if jt.2.val < 2 then 4258 else 4250)) else (if jt.2.val < 4 then 4257 else (if jt.2.val < 5 then 4259 else 4245)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1791 else (if jt.2.val < 2 then 1793 else 1798)) else (if jt.2.val < 4 then 1792 else (if jt.2.val < 5 then 1797 else 1794))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1935 else (if jt.2.val < 2 then 1943 else 1937)) else (if jt.2.val < 4 then 1941 else (if jt.2.val < 5 then 1942 else 1931)))))

checked_coverage fastCoverage0565 pairing0565 template0565 witness0565

theorem coverage0565 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0565) (maskBits m))
    cores template0565 witness0565 := by
  rw [← coresFast_eq]
  exact fastCoverage0565

theorem coverageSize0565 : ∀ q : Pattern,
    (cores (witness0565 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0565 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0565
#print axioms coverageSize0565

noncomputable def pairing0566 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0566 : List (Fin 4935) := templateData0566

noncomputable def witness0566 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 430 else 1837) else if t 2 = 1 then (if t 3 = 0 then 428 else if t 3 = 1 then 426 else 1114) else (if t 3 = 0 then 1510 else if t 3 = 1 then 450 else 1120)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 424 else if t 3 = 1 then 422 else 502) else if t 2 = 1 then (if t 3 = 0 then 420 else if t 3 = 1 then 418 else 488) else (if t 3 = 0 then 1507 else if t 3 = 1 then 445 else 489)) else (if t 2 = 0 then (if t 3 = 0 then 3505 else if t 3 = 1 then 2730 else 2743) else if t 2 = 1 then (if t 3 = 0 then 3203 else if t 3 = 1 then 2728 else 2740) else (if t 3 = 0 then 4539 else if t 3 = 1 then 3929 else 3935))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 429 else 1836) else if t 2 = 1 then (if t 3 = 0 then 427 else if t 3 = 1 then 425 else 1113) else (if t 3 = 0 then 1509 else if t 3 = 1 then 449 else 1119)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 423 else if t 3 = 1 then 421 else 498) else if t 2 = 1 then (if t 3 = 0 then 419 else if t 3 = 1 then 417 else 480) else (if t 3 = 0 then 1506 else if t 3 = 1 then 444 else 482)) else (if t 2 = 0 then (if t 3 = 0 then 439 else if t 3 = 1 then 438 else 499) else if t 2 = 1 then (if t 3 = 0 then 437 else if t 3 = 1 then 436 else 481) else (if t 3 = 0 then 1511 else if t 3 = 1 then 453 else 483))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 1518 else 4542) else if t 2 = 1 then (if t 3 = 0 then 468 else if t 3 = 1 then 466 else 2148) else (if t 3 = 0 then 2739 else if t 3 = 1 then 476 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1133 else if t 3 = 1 then 1131 else 1524) else if t 2 = 1 then (if t 3 = 0 then 463 else if t 3 = 1 then 461 else 484) else (if t 3 = 0 then 1848 else if t 3 = 1 then 474 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 1136 else if t 3 = 1 then 1135 else 1525) else if t 2 = 1 then (if t 3 = 0 then 471 else if t 3 = 1 then 470 else 485) else (if t 3 = 0 then 1850 else if t 3 = 1 then 478 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4680 else (if jt.2.val < 2 then 4688 else 4685)) else (if jt.2.val < 4 then 4686 else (if jt.2.val < 5 then 4687 else 4683))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3608 else (if jt.2.val < 2 then 3623 else 3611)) else (if jt.2.val < 4 then 3621 else (if jt.2.val < 5 then 3622 else 3600)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1335 else (if jt.2.val < 2 then 1508 else 1340)) else (if jt.2.val < 4 then 1503 else (if jt.2.val < 5 then 1504 else 1303))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1950 else (if jt.2.val < 2 then 1952 else 1955)) else (if jt.2.val < 4 then 1951 else (if jt.2.val < 5 then 1954 else 1953)))))

checked_coverage fastCoverage0566 pairing0566 template0566 witness0566

theorem coverage0566 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0566) (maskBits m))
    cores template0566 witness0566 := by
  rw [← coresFast_eq]
  exact fastCoverage0566

theorem coverageSize0566 : ∀ q : Pattern,
    (cores (witness0566 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0566 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0566
#print axioms coverageSize0566

noncomputable def pairing0567 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0567 : List (Fin 4935) := templateData0567

noncomputable def witness0567 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1904 else 575) else if t 2 = 1 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1901 else 554) else (if t 3 = 0 then 900 else if t 3 = 1 then 158 else 1538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1891 else 1188) else if t 2 = 1 then (if t 3 = 0 then 1907 else if t 3 = 1 then 1875 else 1878) else (if t 3 = 0 then 94 else if t 3 = 1 then 1877 else 1879)) else (if t 2 = 0 then (if t 3 = 0 then 2506 else if t 3 = 1 then 2938 else 3514) else if t 2 = 1 then (if t 3 = 0 then 2500 else if t 3 = 1 then 3348 else 3350) else (if t 3 = 0 then 3943 else if t 3 = 1 then 4064 else 4537))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1902 else 572) else if t 2 = 1 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1899 else 548) else (if t 3 = 0 then 899 else if t 3 = 1 then 152 else 1535)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1887 else 1181) else if t 2 = 1 then (if t 3 = 0 then 1905 else if t 3 = 1 then 1859 else 1863) else (if t 3 = 0 then 90 else if t 3 = 1 then 1861 else 1865)) else (if t 2 = 0 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1888 else 1182) else if t 2 = 1 then (if t 3 = 0 then 1906 else if t 3 = 1 then 1860 else 1864) else (if t 3 = 0 then 91 else if t 3 = 1 then 1862 else 1866))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1673 else 3966) else if t 2 = 1 then (if t 3 = 0 then 2172 else if t 3 = 1 then 1667 else 550) else (if t 3 = 0 then 3525 else if t 3 = 1 then 154 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1620 else if t 3 = 1 then 1889 else 1185) else if t 2 = 1 then (if t 3 = 0 then 1617 else if t 3 = 1 then 1867 else 1871) else (if t 3 = 0 then 92 else if t 3 = 1 then 1869 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 1621 else if t 3 = 1 then 1890 else 1186) else if t 2 = 1 then (if t 3 = 0 then 1618 else if t 3 = 1 then 1868 else 1872) else (if t 3 = 0 then 93 else if t 3 = 1 then 1870 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4710 else (if jt.2.val < 2 then 4726 else 4721)) else (if jt.2.val < 4 then 4725 else (if jt.2.val < 5 then 4727 else 4718))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3585 else (if jt.2.val < 2 then 3598 else 3587)) else (if jt.2.val < 4 then 3597 else (if jt.2.val < 5 then 3599 else 3582)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1794 else (if jt.2.val < 2 then 1885 else 1798)) else (if jt.2.val < 4 then 1884 else (if jt.2.val < 5 then 1886 else 1791))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1953 else (if jt.2.val < 2 then 1970 else 1955)) else (if jt.2.val < 4 then 1967 else (if jt.2.val < 5 then 1968 else 1950)))))

checked_coverage fastCoverage0567 pairing0567 template0567 witness0567

theorem coverage0567 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0567) (maskBits m))
    cores template0567 witness0567 := by
  rw [← coresFast_eq]
  exact fastCoverage0567

theorem coverageSize0567 : ∀ q : Pattern,
    (cores (witness0567 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0567 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0567
#print axioms coverageSize0567

noncomputable def pairing0568 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0568 : List (Fin 4935) := templateData0568

noncomputable def witness0568 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 4213) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3531) else (if t 3 = 0 then 3228 else if t 3 = 1 then 3227 else 2649)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 2199) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 2198) else (if t 3 = 0 then 1612 else if t 3 = 1 then 1610 else 1616)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1650 else 359) else if t 2 = 1 then (if t 3 = 0 then 1651 else if t 3 = 1 then 1649 else 1661) else (if t 3 = 0 then 1094 else if t 3 = 1 then 1853 else 1856))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 2073) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 2072) else (if t 3 = 0 then 1444 else if t 3 = 1 then 1442 else 1448)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3465) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4492) else (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4515)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3074 else 3084) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4506) else (if t 3 = 0 then 4038 else if t 3 = 1 then 4518 else 4519))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1722 else 1057) else if t 2 = 1 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1721 else 1735) else (if t 3 = 0 then 398 else if t 3 = 1 then 1451 else 1454)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3270 else 3280) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4499) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4516 else 4517)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 3093 else 3097) else if t 2 = 1 then (if t 3 = 0 then 3847 else if t 3 = 1 then 4507 else 4513) else (if t 3 = 0 then 4192 else if t 3 = 1 then 4520 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4710 else (if jt.2.val < 2 then 4720 else 4721)) else (if jt.2.val < 4 then 4717 else (if jt.2.val < 5 then 4719 else 4718))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4575 else (if jt.2.val < 2 then 4585 else 4586)) else (if jt.2.val < 4 then 4582 else (if jt.2.val < 5 then 4584 else 4583)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4548 else (if jt.2.val < 2 then 4556 else 4559)) else (if jt.2.val < 4 then 4555 else (if jt.2.val < 5 then 4558 else 4557))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4746 else (if jt.2.val < 2 then 4750 else 4751)) else (if jt.2.val < 4 then 4747 else (if jt.2.val < 5 then 4749 else 4748)))))

checked_coverage fastCoverage0568 pairing0568 template0568 witness0568

theorem coverage0568 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0568) (maskBits m))
    cores template0568 witness0568 := by
  rw [← coresFast_eq]
  exact fastCoverage0568

theorem coverageSize0568 : ∀ q : Pattern,
    (cores (witness0568 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0568 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0568
#print axioms coverageSize0568

noncomputable def pairing0569 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0569 : List (Fin 4935) := templateData0569

noncomputable def witness0569 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 4546) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 3530) else (if t 3 = 0 then 2779 else if t 3 = 1 then 2778 else 3182)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 2197) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 2196) else (if t 3 = 0 then 682 else if t 3 = 1 then 680 else 688)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 726 else 1490) else if t 2 = 1 then (if t 3 = 0 then 727 else if t 3 = 1 then 725 else 742) else (if t 3 = 0 then 1826 else if t 3 = 1 then 1144 else 1148))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 2071) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 2070) else (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 196)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 3464) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4155) else (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4180)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2475) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4171) else (if t 3 = 0 then 4039 else if t 3 = 1 then 4183 else 4184))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 822 else 1818) else if t 2 = 1 then (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 840) else (if t 3 = 0 then 1502 else if t 3 = 1 then 202 else 206)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2842) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4164) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4181 else 4182)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2487 else 2491) else if t 2 = 1 then (if t 3 = 0 then 3849 else if t 3 = 1 then 4177 else 4178) else (if t 3 = 0 then 4526 else if t 3 = 1 then 4185 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4692 else (if jt.2.val < 2 then 4702 else 4703)) else (if jt.2.val < 4 then 4699 else (if jt.2.val < 5 then 4701 else 4700))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4260 else (if jt.2.val < 2 then 4270 else 4271)) else (if jt.2.val < 4 then 4267 else (if jt.2.val < 5 then 4269 else 4268)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4215 else (if jt.2.val < 2 then 4223 else 4226)) else (if jt.2.val < 4 then 4222 else (if jt.2.val < 5 then 4225 else 4224))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4748 else (if jt.2.val < 2 then 4754 else 4751)) else (if jt.2.val < 4 then 4752 else (if jt.2.val < 5 then 4753 else 4746)))))

checked_coverage fastCoverage0569 pairing0569 template0569 witness0569

theorem coverage0569 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0569) (maskBits m))
    cores template0569 witness0569 := by
  rw [← coresFast_eq]
  exact fastCoverage0569

theorem coverageSize0569 : ∀ q : Pattern,
    (cores (witness0569 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0569 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0569
#print axioms coverageSize0569

noncomputable def pairing0570 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0570 : List (Fin 4935) := templateData0570

noncomputable def witness0570 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3156 else 2760) else if t 2 = 1 then (if t 3 = 0 then 3151 else if t 3 = 1 then 3144 else 2756) else (if t 3 = 0 then 4525 else if t 3 = 1 then 3953 else 4207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3154 else 292) else if t 2 = 1 then (if t 3 = 0 then 3149 else if t 3 = 1 then 3138 else 264) else (if t 3 = 0 then 1597 else if t 3 = 1 then 1589 else 266)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 874 else 1790) else if t 2 = 1 then (if t 3 = 0 then 859 else if t 3 = 1 then 853 else 269) else (if t 3 = 0 then 1599 else if t 3 = 1 then 855 else 271))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3155 else 586) else if t 2 = 1 then (if t 3 = 0 then 3150 else if t 3 = 1 then 3141 else 557) else (if t 3 = 0 then 1429 else if t 3 = 1 then 1419 else 559)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3153 else 3163) else if t 2 = 1 then (if t 3 = 0 then 3145 else if t 3 = 1 then 3119 else 3123) else (if t 3 = 0 then 3146 else if t 3 = 1 then 3121 else 3124)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 3313 else 3315) else if t 2 = 1 then (if t 3 = 0 then 2949 else if t 3 = 1 then 3130 else 3132) else (if t 3 = 0 then 2950 else if t 3 = 1 then 3131 else 3133))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 775 else 1550) else if t 2 = 1 then (if t 3 = 0 then 760 else if t 3 = 1 then 748 else 1105) else (if t 3 = 0 then 1774 else if t 3 = 1 then 750 else 1107)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 3165 else 3167) else if t 2 = 1 then (if t 3 = 0 then 2697 else if t 3 = 1 then 3126 else 3128) else (if t 3 = 0 then 2698 else if t 3 = 1 then 3127 else 3129)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 3500 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2701 else if t 3 = 1 then 3134 else 3136) else (if t 3 = 0 then 2702 else if t 3 = 1 then 3135 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4617 else (if jt.2.val < 2 then 4619 else 4622)) else (if jt.2.val < 4 then 4618 else (if jt.2.val < 5 then 4621 else 4620))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3567 else (if jt.2.val < 2 then 3569 else 3572)) else (if jt.2.val < 4 then 3568 else (if jt.2.val < 5 then 3571 else 3570)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4557 else (if jt.2.val < 2 then 4565 else 4559)) else (if jt.2.val < 4 then 4563 else (if jt.2.val < 5 then 4564 else 4548))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3399 else (if jt.2.val < 2 then 3401 else 3407)) else (if jt.2.val < 4 then 3400 else (if jt.2.val < 5 then 3406 else 3402)))))

checked_coverage fastCoverage0570 pairing0570 template0570 witness0570

theorem coverage0570 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0570) (maskBits m))
    cores template0570 witness0570 := by
  rw [← coresFast_eq]
  exact fastCoverage0570

theorem coverageSize0570 : ∀ q : Pattern,
    (cores (witness0570 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0570 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0570
#print axioms coverageSize0570

noncomputable def pairing0571 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0571 : List (Fin 4935) := templateData0571

noncomputable def witness0571 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2565 else 3215) else if t 2 = 1 then (if t 3 = 0 then 2560 else if t 3 = 1 then 2544 else 3209) else (if t 3 = 0 then 4190 else if t 3 = 1 then 3945 else 4541)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2563 else 291) else if t 2 = 1 then (if t 3 = 0 then 2558 else if t 3 = 1 then 2538 else 251) else (if t 3 = 0 then 667 else if t 3 = 1 then 641 else 1459)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1762 else 929) else if t 2 = 1 then (if t 3 = 0 then 1750 else if t 3 = 1 then 1747 else 256) else (if t 3 = 0 then 669 else if t 3 = 1 then 646 else 1462))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2564 else 585) else if t 2 = 1 then (if t 3 = 0 then 2559 else if t 3 = 1 then 2541 else 545) else (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 1532)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2562 else 2572) else if t 2 = 1 then (if t 3 = 0 then 2548 else if t 3 = 1 then 2519 else 2523) else (if t 3 = 0 then 2549 else if t 3 = 1 then 2521 else 2524)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2883 else 2886) else if t 2 = 1 then (if t 3 = 0 then 2554 else if t 3 = 1 then 2530 else 2532) else (if t 3 = 0 then 2555 else if t 3 = 1 then 2531 else 2533))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1687 else 599) else if t 2 = 1 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1666 else 547) else (if t 3 = 0 then 895 else if t 3 = 1 then 151 else 1834)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2576 else 2579) else if t 2 = 1 then (if t 3 = 0 then 2878 else if t 3 = 1 then 2526 else 2528) else (if t 3 = 0 then 2879 else if t 3 = 1 then 2527 else 2529)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3506 else 4197) else if t 2 = 1 then (if t 3 = 0 then 3196 else if t 3 = 1 then 2534 else 2536) else (if t 3 = 0 then 3197 else if t 3 = 1 then 2535 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4629 else (if jt.2.val < 2 then 4631 else 4634)) else (if jt.2.val < 4 then 4630 else (if jt.2.val < 5 then 4633 else 4632))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3582 else (if jt.2.val < 2 then 3584 else 3587)) else (if jt.2.val < 4 then 3583 else (if jt.2.val < 5 then 3586 else 3585)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4224 else (if jt.2.val < 2 then 4232 else 4226)) else (if jt.2.val < 4 then 4230 else (if jt.2.val < 5 then 4231 else 4215))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3402 else (if jt.2.val < 2 then 3424 else 3407)) else (if jt.2.val < 4 then 3423 else (if jt.2.val < 5 then 3425 else 3399)))))

checked_coverage fastCoverage0571 pairing0571 template0571 witness0571

theorem coverage0571 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0571) (maskBits m))
    cores template0571 witness0571 := by
  rw [← coresFast_eq]
  exact fastCoverage0571

theorem coverageSize0571 : ∀ q : Pattern,
    (cores (witness0571 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0571 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0571
#print axioms coverageSize0571

noncomputable def pairing0572 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0572 : List (Fin 4935) := templateData0572

noncomputable def witness0572 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1316 else 452) else if t 2 = 1 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1314 else 1342) else (if t 3 = 0 then 1012 else if t 3 = 1 then 1777 else 1780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1312 else if t 3 = 1 then 1308 else 448) else if t 2 = 1 then (if t 3 = 0 then 1310 else if t 3 = 1 then 1306 else 1339) else (if t 3 = 0 then 1001 else if t 3 = 1 then 1370 else 1371)) else (if t 2 = 0 then (if t 3 = 0 then 4530 else if t 3 = 1 then 3963 else 4205) else if t 2 = 1 then (if t 3 = 0 then 3234 else if t 3 = 1 then 3232 else 2689) else (if t 3 = 0 then 3242 else if t 3 = 1 then 2860 else 2722))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1315 else 451) else if t 2 = 1 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1313 else 1341) else (if t 3 = 0 then 1011 else if t 3 = 1 then 1776 else 1779)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1311 else if t 3 = 1 then 1307 else 447) else if t 2 = 1 then (if t 3 = 0 then 1309 else if t 3 = 1 then 1305 else 1338) else (if t 3 = 0 then 998 else if t 3 = 1 then 1362 else 1364)) else (if t 2 = 0 then (if t 3 = 0 then 1329 else if t 3 = 1 then 1327 else 454) else if t 2 = 1 then (if t 3 = 0 then 1328 else if t 3 = 1 then 1325 else 1343) else (if t 3 = 0 then 999 else if t 3 = 1 then 1363 else 1365))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 647 else 3206) else if t 2 = 1 then (if t 3 = 0 then 257 else if t 3 = 1 then 1352 else 1358) else (if t 3 = 0 then 4206 else if t 3 = 1 then 2118 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1785 else if t 3 = 1 then 643 else 1137) else if t 2 = 1 then (if t 3 = 0 then 253 else if t 3 = 1 then 1349 else 1356) else (if t 3 = 0 then 302 else if t 3 = 1 then 1366 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 1787 else if t 3 = 1 then 650 else 1139) else if t 2 = 1 then (if t 3 = 0 then 260 else if t 3 = 1 then 1354 else 1360) else (if t 3 = 0 then 303 else if t 3 = 1 then 1367 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4629 else (if jt.2.val < 2 then 4637 else 4634)) else (if jt.2.val < 4 then 4635 else (if jt.2.val < 5 then 4636 else 4632))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4583 else (if jt.2.val < 2 then 4592 else 4586)) else (if jt.2.val < 4 then 4590 else (if jt.2.val < 5 then 4591 else 4575)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2382 else (if jt.2.val < 2 then 2384 else 2387)) else (if jt.2.val < 4 then 2383 else (if jt.2.val < 5 then 2386 else 2385))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1972 else (if jt.2.val < 2 then 1976 else 1977)) else (if jt.2.val < 4 then 1973 else (if jt.2.val < 5 then 1975 else 1974)))))

checked_coverage fastCoverage0572 pairing0572 template0572 witness0572

theorem coverage0572 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0572) (maskBits m))
    cores template0572 witness0572 := by
  rw [← coresFast_eq]
  exact fastCoverage0572

theorem coverageSize0572 : ∀ q : Pattern,
    (cores (witness0572 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0572 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0572
#print axioms coverageSize0572

noncomputable def pairing0573 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0573 : List (Fin 4935) := templateData0573

noncomputable def witness0573 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 20 else 1510) else if t 2 = 1 then (if t 3 = 0 then 22 else if t 3 = 1 then 18 else 48) else (if t 3 = 0 then 1807 else if t 3 = 1 then 898 else 904)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 16 else if t 3 = 1 then 12 else 1507) else if t 2 = 1 then (if t 3 = 0 then 14 else if t 3 = 1 then 10 else 43) else (if t 3 = 0 then 100 else if t 3 = 1 then 86 else 87)) else (if t 2 = 0 then (if t 3 = 0 then 4196 else if t 3 = 1 then 3939 else 4539) else if t 2 = 1 then (if t 3 = 0 then 2787 else if t 3 = 1 then 2785 else 3191) else (if t 3 = 0 then 2800 else if t 3 = 1 then 2797 else 3198))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 19 else 1509) else if t 2 = 1 then (if t 3 = 0 then 21 else if t 3 = 1 then 17 else 47) else (if t 3 = 0 then 1806 else if t 3 = 1 then 897 else 903)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 15 else if t 3 = 1 then 11 else 1506) else if t 2 = 1 then (if t 3 = 0 then 13 else if t 3 = 1 then 9 else 42) else (if t 3 = 0 then 96 else if t 3 = 1 then 78 else 80)) else (if t 2 = 0 then (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 1511) else if t 2 = 1 then (if t 3 = 0 then 32 else if t 3 = 1 then 29 else 51) else (if t 3 = 0 then 97 else if t 3 = 1 then 79 else 81))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 66 else 2739) else if t 2 = 1 then (if t 3 = 0 then 1470 else if t 3 = 1 then 64 else 74) else (if t 3 = 0 then 4540 else if t 3 = 1 then 2127 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 917 else if t 3 = 1 then 61 else 1848) else if t 2 = 1 then (if t 3 = 0 then 915 else if t 3 = 1 then 59 else 72) else (if t 3 = 0 then 1476 else if t 3 = 1 then 82 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 920 else if t 3 = 1 then 69 else 1850) else if t 2 = 1 then (if t 3 = 0 then 919 else if t 3 = 1 then 68 else 76) else (if t 3 = 0 then 1477 else if t 3 = 1 then 83 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4617 else (if jt.2.val < 2 then 4643 else 4622)) else (if jt.2.val < 4 then 4641 else (if jt.2.val < 5 then 4642 else 4620))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4268 else (if jt.2.val < 2 then 4277 else 4271)) else (if jt.2.val < 4 then 4275 else (if jt.2.val < 5 then 4276 else 4260)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2394 else (if jt.2.val < 2 then 2396 else 2399)) else (if jt.2.val < 4 then 2395 else (if jt.2.val < 5 then 2398 else 2397))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1974 else (if jt.2.val < 2 then 1998 else 1977)) else (if jt.2.val < 4 then 1995 else (if jt.2.val < 5 then 1996 else 1972)))))

checked_coverage fastCoverage0573 pairing0573 template0573 witness0573

theorem coverage0573 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0573) (maskBits m))
    cores template0573 witness0573 := by
  rw [← coresFast_eq]
  exact fastCoverage0573

theorem coverageSize0573 : ∀ q : Pattern,
    (cores (witness0573 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0573 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0573
#print axioms coverageSize0573

noncomputable def pairing0574 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0574 : List (Fin 4935) := templateData0574

noncomputable def witness0574 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1216 else 1837) else if t 2 = 1 then (if t 3 = 0 then 1205 else if t 3 = 1 then 1201 else 568) else (if t 3 = 0 then 1433 else if t 3 = 1 then 1202 else 569)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1214 else if t 3 = 1 then 1210 else 502) else if t 2 = 1 then (if t 3 = 0 then 1187 else if t 3 = 1 then 1167 else 1170) else (if t 3 = 0 then 1801 else if t 3 = 1 then 1169 else 1171)) else (if t 2 = 0 then (if t 3 = 0 then 3106 else if t 3 = 1 then 3003 else 2743) else if t 2 = 1 then (if t 3 = 0 then 3329 else if t 3 = 1 then 2993 else 2995) else (if t 3 = 0 then 4532 else if t 3 = 1 then 4054 else 4203))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1215 else 1836) else if t 2 = 1 then (if t 3 = 0 then 1203 else if t 3 = 1 then 1197 else 562) else (if t 3 = 0 then 1430 else if t 3 = 1 then 1199 else 564)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1212 else if t 3 = 1 then 1206 else 498) else if t 2 = 1 then (if t 3 = 0 then 1179 else if t 3 = 1 then 1151 else 1155) else (if t 3 = 0 then 1795 else if t 3 = 1 then 1153 else 1157)) else (if t 2 = 0 then (if t 3 = 0 then 1213 else if t 3 = 1 then 1207 else 499) else if t 2 = 1 then (if t 3 = 0 then 1180 else if t 3 = 1 then 1152 else 1156) else (if t 3 = 0 then 1796 else if t 3 = 1 then 1154 else 1158))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 2160 else 4542) else if t 2 = 1 then (if t 3 = 0 then 761 else if t 3 = 1 then 751 else 1542) else (if t 3 = 0 then 2796 else if t 3 = 1 then 753 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 696 else if t 3 = 1 then 690 else 1524) else if t 2 = 1 then (if t 3 = 0 then 1183 else if t 3 = 1 then 1159 else 1163) else (if t 3 = 0 then 1799 else if t 3 = 1 then 1161 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 697 else if t 3 = 1 then 691 else 1525) else if t 2 = 1 then (if t 3 = 0 then 1184 else if t 3 = 1 then 1160 else 1164) else (if t 3 = 0 then 1800 else if t 3 = 1 then 1162 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4692 else (if jt.2.val < 2 then 4708 else 4703)) else (if jt.2.val < 4 then 4707 else (if jt.2.val < 5 then 4709 else 4700))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3570 else (if jt.2.val < 2 then 3592 else 3572)) else (if jt.2.val < 4 then 3591 else (if jt.2.val < 5 then 3593 else 3567)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2385 else (if jt.2.val < 2 then 2405 else 2387)) else (if jt.2.val < 4 then 2403 else (if jt.2.val < 5 then 2404 else 2382))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2304 else (if jt.2.val < 2 then 2306 else 2309)) else (if jt.2.val < 4 then 2305 else (if jt.2.val < 5 then 2308 else 2307)))))

checked_coverage fastCoverage0574 pairing0574 template0574 witness0574

theorem coverage0574 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0574) (maskBits m))
    cores template0574 witness0574 := by
  rw [← coresFast_eq]
  exact fastCoverage0574

theorem coverageSize0574 : ∀ q : Pattern,
    (cores (witness0574 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0574 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0574
#print axioms coverageSize0574

noncomputable def pairing0575 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0575 : List (Fin 4935) := templateData0575

noncomputable def witness0575 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1912 else 1116) else if t 2 = 1 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1901 else 554) else (if t 3 = 0 then 179 else if t 3 = 1 then 158 else 1538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1907 else 496) else if t 2 = 1 then (if t 3 = 0 then 1891 else if t 3 = 1 then 1875 else 1878) else (if t 3 = 0 then 978 else if t 3 = 1 then 1877 else 1879)) else (if t 2 = 0 then (if t 3 = 0 then 2506 else if t 3 = 1 then 2500 else 3207) else if t 2 = 1 then (if t 3 = 0 then 2938 else if t 3 = 1 then 3348 else 3350) else (if t 3 = 0 then 4198 else if t 3 = 1 then 4064 else 4537))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1911 else 1115) else if t 2 = 1 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1899 else 548) else (if t 3 = 0 then 176 else if t 3 = 1 then 152 else 1535)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1905 else 492) else if t 2 = 1 then (if t 3 = 0 then 1887 else if t 3 = 1 then 1859 else 1863) else (if t 3 = 0 then 971 else if t 3 = 1 then 1861 else 1865)) else (if t 2 = 0 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1906 else 493) else if t 2 = 1 then (if t 3 = 0 then 1888 else if t 3 = 1 then 1860 else 1864) else (if t 3 = 0 then 972 else if t 3 = 1 then 1862 else 1866))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 2172 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1673 else if t 3 = 1 then 1667 else 550) else (if t 3 = 0 then 3240 else if t 3 = 1 then 154 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1620 else if t 3 = 1 then 1617 else 494) else if t 2 = 1 then (if t 3 = 0 then 1889 else if t 3 = 1 then 1867 else 1871) else (if t 3 = 0 then 975 else if t 3 = 1 then 1869 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 1621 else if t 3 = 1 then 1618 else 495) else if t 2 = 1 then (if t 3 = 0 then 1890 else if t 3 = 1 then 1868 else 1872) else (if t 3 = 0 then 976 else if t 3 = 1 then 1870 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4710 else (if jt.2.val < 2 then 4726 else 4721)) else (if jt.2.val < 4 then 4725 else (if jt.2.val < 5 then 4727 else 4718))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3585 else (if jt.2.val < 2 then 3598 else 3587)) else (if jt.2.val < 4 then 3597 else (if jt.2.val < 5 then 3599 else 3582)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2397 else (if jt.2.val < 2 then 2411 else 2399)) else (if jt.2.val < 4 then 2409 else (if jt.2.val < 5 then 2410 else 2394))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2307 else (if jt.2.val < 2 then 2317 else 2309)) else (if jt.2.val < 4 then 2316 else (if jt.2.val < 5 then 2318 else 2304)))))

checked_coverage fastCoverage0575 pairing0575 template0575 witness0575

theorem coverage0575 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0575) (maskBits m))
    cores template0575 witness0575 := by
  rw [← coresFast_eq]
  exact fastCoverage0575

theorem coverageSize0575 : ∀ q : Pattern,
    (cores (witness0575 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0575 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0575
#print axioms coverageSize0575

noncomputable def pairing0576 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0576 : List (Fin 4935) := templateData0576

noncomputable def witness0576 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 3941) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2788) else (if t 3 = 0 then 3532 else if t 3 = 1 then 3530 else 3192)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 726) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 725) else (if t 3 = 0 then 2200 else if t 3 = 1 then 2196 else 742)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 681 else 1145) else if t 2 = 1 then (if t 3 = 0 then 682 else if t 3 = 1 then 680 else 1144) else (if t 3 = 0 then 689 else if t 3 = 1 then 688 else 1148))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 35) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 34) else (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 53)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2462) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4170) else (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4171)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2885) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4183) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4180 else 4184))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 822 else 71) else if t 2 = 1 then (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 70) else (if t 3 = 0 then 841 else if t 3 = 1 then 840 else 77)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2487) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4177) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4164 else 4178)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2578 else 3507) else if t 2 = 1 then (if t 3 = 0 then 3919 else if t 3 = 1 then 4181 else 4185) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4182 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4692 else (if jt.2.val < 2 then 4702 else 4703)) else (if jt.2.val < 4 then 4699 else (if jt.2.val < 5 then 4701 else 4700))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4305 else (if jt.2.val < 2 then 4307 else 4310)) else (if jt.2.val < 4 then 4306 else (if jt.2.val < 5 then 4309 else 4308)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4728 else (if jt.2.val < 2 then 4732 else 4733)) else (if jt.2.val < 4 then 4729 else (if jt.2.val < 5 then 4731 else 4730))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4216 else (if jt.2.val < 2 then 4220 else 4221)) else (if jt.2.val < 4 then 4217 else (if jt.2.val < 5 then 4219 else 4218)))))

checked_coverage fastCoverage0576 pairing0576 template0576 witness0576

theorem coverage0576 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0576) (maskBits m))
    cores template0576 witness0576 := by
  rw [← coresFast_eq]
  exact fastCoverage0576

theorem coverageSize0576 : ∀ q : Pattern,
    (cores (witness0576 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0576 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0576
#print axioms coverageSize0576

noncomputable def pairing0577 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0577 : List (Fin 4935) := templateData0577

noncomputable def witness0577 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4196) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2787) else (if t 3 = 0 then 3236 else if t 3 = 1 then 3234 else 3522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 724) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 723) else (if t 3 = 0 then 1651 else if t 3 = 1 then 1647 else 741)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1084 else 790) else if t 2 = 1 then (if t 3 = 0 then 1090 else if t 3 = 1 then 1078 else 784) else (if t 3 = 0 then 1094 else if t 3 = 1 then 1080 else 786))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 33) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 32) else (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 52)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2461) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3834) else (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3837)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2503) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3854) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3853 else 3855))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 241 else 920) else if t 2 = 1 then (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 919) else (if t 3 = 0 then 262 else if t 3 = 1 then 260 else 923)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2899) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3848) else (if t 3 = 0 then 3847 else if t 3 = 1 then 3846 else 3850)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2651 else 3184) else if t 2 = 1 then (if t 3 = 0 then 4191 else if t 3 = 1 then 3856 else 3858) else (if t 3 = 0 then 4192 else if t 3 = 1 then 3857 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4674 else (if jt.2.val < 2 then 4678 else 4679)) else (if jt.2.val < 4 then 4675 else (if jt.2.val < 5 then 4677 else 4676))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4293 else (if jt.2.val < 2 then 4295 else 4298)) else (if jt.2.val < 4 then 4294 else (if jt.2.val < 5 then 4297 else 4296)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4449 else (if jt.2.val < 2 then 4453 else 4454)) else (if jt.2.val < 4 then 4450 else (if jt.2.val < 5 then 4452 else 4451))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4218 else (if jt.2.val < 2 then 4229 else 4221)) else (if jt.2.val < 4 then 4227 else (if jt.2.val < 5 then 4228 else 4216)))))

checked_coverage fastCoverage0577 pairing0577 template0577 witness0577

theorem coverage0577 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0577) (maskBits m))
    cores template0577 witness0577 := by
  rw [← coresFast_eq]
  exact fastCoverage0577

theorem coverageSize0577 : ∀ q : Pattern,
    (cores (witness0577 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0577 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0577
#print axioms coverageSize0577

noncomputable def pairing0578 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0578 : List (Fin 4935) := templateData0578

noncomputable def witness0578 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3205) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2731) else (if t 3 = 0 then 4213 else if t 3 = 1 then 4211 else 3930)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 343) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 342) else (if t 3 = 0 then 2199 else if t 3 = 1 then 2195 else 358)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 291 else 929) else if t 2 = 1 then (if t 3 = 0 then 292 else if t 3 = 1 then 290 else 928) else (if t 3 = 0 then 299 else if t 3 = 1 then 298 else 932))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 441) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 440) else (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 455)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2471) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3479) else (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3480)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2572 else 2886) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3488 else 3492) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3489 else 3493))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1042 else 473) else if t 2 = 1 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1041 else 472) else (if t 3 = 0 then 1057 else if t 3 = 1 then 1056 else 479)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2838 else 2489) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3472 else 3486) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3473 else 3487)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2579 else 4197) else if t 2 = 1 then (if t 3 = 0 then 3167 else if t 3 = 1 then 3490 else 3494) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3491 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4647 else (if jt.2.val < 2 then 4657 else 4658)) else (if jt.2.val < 4 then 4654 else (if jt.2.val < 5 then 4656 else 4655))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3672 else (if jt.2.val < 2 then 3674 else 3677)) else (if jt.2.val < 4 then 3673 else (if jt.2.val < 5 then 3676 else 3675)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4730 else (if jt.2.val < 2 then 4736 else 4733)) else (if jt.2.val < 4 then 4734 else (if jt.2.val < 5 then 4735 else 4728))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3538 else (if jt.2.val < 2 then 3542 else 3543)) else (if jt.2.val < 4 then 3539 else (if jt.2.val < 5 then 3541 else 3540)))))

checked_coverage fastCoverage0578 pairing0578 template0578 witness0578

theorem coverage0578 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0578) (maskBits m))
    cores template0578 witness0578 := by
  rw [← coresFast_eq]
  exact fastCoverage0578

theorem coverageSize0578 : ∀ q : Pattern,
    (cores (witness0578 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0578 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0578
#print axioms coverageSize0578

noncomputable def pairing0579 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0579 : List (Fin 4935) := templateData0579

noncomputable def witness0579 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3505) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 2730) else (if t 3 = 0 then 3965 else if t 3 = 1 then 3963 else 4205)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 341) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 340) else (if t 3 = 0 then 1650 else if t 3 = 1 then 1646 else 357)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 868 else 406) else if t 2 = 1 then (if t 3 = 0 then 874 else if t 3 = 1 then 862 else 400) else (if t 3 = 0 then 878 else if t 3 = 1 then 864 else 402))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 439) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 438) else (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 454)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2470) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3080) else (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3083)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2956 else 2504) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3098 else 3100) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3099 else 3101))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 635 else 1136) else if t 2 = 1 then (if t 3 = 0 then 638 else if t 3 = 1 then 634 else 1135) else (if t 3 = 0 then 652 else if t 3 = 1 then 650 else 1139)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2622 else 2900) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3089 else 3094) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3092 else 3096)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2652 else 3928) else if t 2 = 1 then (if t 3 = 0 then 3500 else if t 3 = 1 then 3102 else 3104) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3103 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4611 else (if jt.2.val < 2 then 4615 else 4616)) else (if jt.2.val < 4 then 4612 else (if jt.2.val < 5 then 4614 else 4613))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3642 else (if jt.2.val < 2 then 3644 else 3647)) else (if jt.2.val < 4 then 3643 else (if jt.2.val < 5 then 3646 else 3645)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4451 else (if jt.2.val < 2 then 4463 else 4454)) else (if jt.2.val < 4 then 4461 else (if jt.2.val < 5 then 4462 else 4449))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3540 else (if jt.2.val < 2 then 3551 else 3543)) else (if jt.2.val < 4 then 3549 else (if jt.2.val < 5 then 3550 else 3538)))))

checked_coverage fastCoverage0579 pairing0579 template0579 witness0579

theorem coverage0579 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0579) (maskBits m))
    cores template0579 witness0579 := by
  rw [← coresFast_eq]
  exact fastCoverage0579

theorem coverageSize0579 : ∀ q : Pattern,
    (cores (witness0579 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0579 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0579
#print axioms coverageSize0579

noncomputable def pairing0580 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0580 : List (Fin 4935) := templateData0580

noncomputable def witness0580 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 183 else 900) else if t 2 = 1 then (if t 3 = 0 then 185 else if t 3 = 1 then 181 else 898) else (if t 3 = 0 then 195 else if t 3 = 1 then 193 else 904)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 178 else if t 3 = 1 then 156 else 158) else if t 2 = 1 then (if t 3 = 0 then 170 else if t 3 = 1 then 136 else 142) else (if t 3 = 0 then 171 else if t 3 = 1 then 139 else 143)) else (if t 2 = 0 then (if t 3 = 0 then 4190 else if t 3 = 1 then 3945 else 3946) else if t 2 = 1 then (if t 3 = 0 then 2775 else if t 3 = 1 then 2766 else 2769) else (if t 3 = 0 then 3524 else if t 3 = 1 then 3172 else 3174))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 182 else 899) else if t 2 = 1 then (if t 3 = 0 then 184 else if t 3 = 1 then 180 else 897) else (if t 3 = 0 then 194 else if t 3 = 1 then 192 else 903)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 174 else if t 3 = 1 then 146 else 152) else if t 2 = 1 then (if t 3 = 0 then 160 else if t 3 = 1 then 117 else 128) else (if t 3 = 0 then 162 else if t 3 = 1 then 121 else 130)) else (if t 2 = 0 then (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 153) else if t 2 = 1 then (if t 3 = 0 then 161 else if t 3 = 1 then 119 else 129) else (if t 3 = 0 then 163 else if t 3 = 1 then 122 else 131))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 200 else 3525) else if t 2 = 1 then (if t 3 = 0 then 1500 else if t 3 = 1 then 198 else 2127) else (if t 3 = 0 then 3952 else if t 3 = 1 then 204 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 894 else if t 3 = 1 then 150 else 154) else if t 2 = 1 then (if t 3 = 0 then 888 else if t 3 = 1 then 124 else 132) else (if t 3 = 0 then 890 else if t 3 = 1 then 126 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 895 else if t 3 = 1 then 151 else 155) else if t 2 = 1 then (if t 3 = 0 then 889 else if t 3 = 1 then 125 else 133) else (if t 3 = 0 then 891 else if t 3 = 1 then 127 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4611 else (if jt.2.val < 2 then 4645 else 4616)) else (if jt.2.val < 4 then 4644 else (if jt.2.val < 5 then 4646 else 4613))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4308 else (if jt.2.val < 2 then 4313 else 4310)) else (if jt.2.val < 4 then 4311 else (if jt.2.val < 5 then 4312 else 4305)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 111 else (if jt.2.val < 2 then 113 else 149)) else (if jt.2.val < 4 then 112 else (if jt.2.val < 5 then 148 else 120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 881 else (if jt.2.val < 2 then 883 else 887)) else (if jt.2.val < 4 then 882 else (if jt.2.val < 5 then 886 else 885)))))

checked_coverage fastCoverage0580 pairing0580 template0580 witness0580

theorem coverage0580 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0580) (maskBits m))
    cores template0580 witness0580 := by
  rw [← coresFast_eq]
  exact fastCoverage0580

theorem coverageSize0580 : ∀ q : Pattern,
    (cores (witness0580 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0580 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0580
#print axioms coverageSize0580

noncomputable def pairing0581 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0581 : List (Fin 4935) := templateData0581

noncomputable def witness0581 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 1004 else 104) else if t 2 = 1 then (if t 3 = 0 then 1006 else if t 3 = 1 then 1000 else 100) else (if t 3 = 0 then 1012 else if t 3 = 1 then 1001 else 101)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 995 else if t 3 = 1 then 977 else 978) else if t 2 = 1 then (if t 3 = 0 then 991 else if t 3 = 1 then 957 else 961) else (if t 3 = 0 then 992 else if t 3 = 1 then 960 else 962)) else (if t 2 = 0 then (if t 3 = 0 then 3905 else if t 3 = 1 then 4046 else 4198) else if t 2 = 1 then (if t 3 = 0 then 2979 else if t 3 = 1 then 2970 else 2972) else (if t 3 = 0 then 3226 else if t 3 = 1 then 3338 else 3520))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 1002 else 102) else if t 2 = 1 then (if t 3 = 0 then 1005 else if t 3 = 1 then 996 else 96) else (if t 3 = 0 then 1011 else if t 3 = 1 then 998 else 98)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 993 else if t 3 = 1 then 967 else 971) else if t 2 = 1 then (if t 3 = 0 then 987 else if t 3 = 1 then 939 else 945) else (if t 3 = 0 then 989 else if t 3 = 1 then 943 else 947)) else (if t 2 = 0 then (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 972) else if t 2 = 1 then (if t 3 = 0 then 988 else if t 3 = 1 then 941 else 946) else (if t 3 = 0 then 990 else if t 3 = 1 then 944 else 948))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 306 else 3229) else if t 2 = 1 then (if t 3 = 0 then 2139 else if t 3 = 1 then 300 else 1476) else (if t 3 = 0 then 4206 else if t 3 = 1 then 302 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 377 else if t 3 = 1 then 973 else 975) else if t 2 = 1 then (if t 3 = 0 then 367 else if t 3 = 1 then 949 else 953) else (if t 3 = 0 then 369 else if t 3 = 1 then 951 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 378 else if t 3 = 1 then 974 else 976) else if t 2 = 1 then (if t 3 = 0 then 368 else if t 3 = 1 then 950 else 954) else (if t 3 = 0 then 370 else if t 3 = 1 then 952 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4647 else (if jt.2.val < 2 then 4672 else 4658)) else (if jt.2.val < 4 then 4671 else (if jt.2.val < 5 then 4673 else 4655))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4296 else (if jt.2.val < 2 then 4304 else 4298)) else (if jt.2.val < 4 then 4302 else (if jt.2.val < 5 then 4303 else 4293)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 933 else (if jt.2.val < 2 then 935 else 970)) else (if jt.2.val < 4 then 934 else (if jt.2.val < 5 then 969 else 942))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 885 else (if jt.2.val < 2 then 985 else 887)) else (if jt.2.val < 4 then 984 else (if jt.2.val < 5 then 986 else 881)))))

checked_coverage fastCoverage0581 pairing0581 template0581 witness0581

theorem coverage0581 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0581) (maskBits m))
    cores template0581 witness0581 := by
  rw [← coresFast_eq]
  exact fastCoverage0581

theorem coverageSize0581 : ∀ q : Pattern,
    (cores (witness0581 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0581 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0581
#print axioms coverageSize0581

noncomputable def pairing0582 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0582 : List (Fin 4935) := templateData0582

noncomputable def witness0582 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 579 else 1116) else if t 2 = 1 then (if t 3 = 0 then 581 else if t 3 = 1 then 577 else 1114) else (if t 3 = 0 then 591 else if t 3 = 1 then 589 else 1120)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 574 else if t 3 = 1 then 552 else 554) else if t 2 = 1 then (if t 3 = 0 then 566 else if t 3 = 1 then 532 else 537) else (if t 3 = 0 then 567 else if t 3 = 1 then 534 else 538)) else (if t 2 = 0 then (if t 3 = 0 then 3499 else if t 3 = 1 then 3209 else 3210) else if t 2 = 1 then (if t 3 = 0 then 2756 else if t 3 = 1 then 2747 else 2750) else (if t 3 = 0 then 4207 else if t 3 = 1 then 3923 else 3925))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 578 else 1115) else if t 2 = 1 then (if t 3 = 0 then 580 else if t 3 = 1 then 576 else 1113) else (if t 3 = 0 then 590 else if t 3 = 1 then 588 else 1119)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 570 else if t 3 = 1 then 544 else 548) else if t 2 = 1 then (if t 3 = 0 then 556 else if t 3 = 1 then 515 else 524) else (if t 3 = 0 then 558 else if t 3 = 1 then 517 else 526)) else (if t 2 = 0 then (if t 3 = 0 then 571 else if t 3 = 1 then 545 else 549) else if t 2 = 1 then (if t 3 = 0 then 557 else if t 3 = 1 then 516 else 525) else (if t 3 = 0 then 559 else if t 3 = 1 then 518 else 527))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 596 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1548 else if t 3 = 1 then 594 else 2148) else (if t 3 = 0 then 3216 else if t 3 = 1 then 600 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1110 else if t 3 = 1 then 546 else 550) else if t 2 = 1 then (if t 3 = 0 then 1104 else if t 3 = 1 then 520 else 528) else (if t 3 = 0 then 1106 else if t 3 = 1 then 522 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 1111 else if t 3 = 1 then 547 else 551) else if t 2 = 1 then (if t 3 = 0 then 1105 else if t 3 = 1 then 521 else 529) else (if t 3 = 0 then 1107 else if t 3 = 1 then 523 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4674 else (if jt.2.val < 2 then 4690 else 4679)) else (if jt.2.val < 4 then 4689 else (if jt.2.val < 5 then 4691 else 4676))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3675 else (if jt.2.val < 2 then 3686 else 3677)) else (if jt.2.val < 4 then 3684 else (if jt.2.val < 5 then 3685 else 3672)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 120 else (if jt.2.val < 2 then 542 else 149)) else (if jt.2.val < 4 then 541 else (if jt.2.val < 5 then 543 else 111))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1095 else (if jt.2.val < 2 then 1097 else 1103)) else (if jt.2.val < 4 then 1096 else (if jt.2.val < 5 then 1102 else 1101)))))

checked_coverage fastCoverage0582 pairing0582 template0582 witness0582

theorem coverage0582 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0582) (maskBits m))
    cores template0582 witness0582 := by
  rw [← coresFast_eq]
  exact fastCoverage0582

theorem coverageSize0582 : ∀ q : Pattern,
    (cores (witness0582 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0582 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0582
#print axioms coverageSize0582

noncomputable def pairing0583 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0583 : List (Fin 4935) := templateData0583

noncomputable def witness0583 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1214 else 506) else if t 2 = 1 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1210 else 502) else (if t 3 = 0 then 1222 else if t 3 = 1 then 1211 else 503)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1205 else if t 3 = 1 then 1187 else 1188) else if t 2 = 1 then (if t 3 = 0 then 1201 else if t 3 = 1 then 1167 else 1170) else (if t 3 = 0 then 1202 else if t 3 = 1 then 1169 else 1171)) else (if t 2 = 0 then (if t 3 = 0 then 3152 else if t 3 = 1 then 3329 else 3514) else if t 2 = 1 then (if t 3 = 0 then 3002 else if t 3 = 1 then 2993 else 2995) else (if t 3 = 0 then 3954 else if t 3 = 1 then 4054 else 4203))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1212 else 504) else if t 2 = 1 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1206 else 498) else (if t 3 = 0 then 1221 else if t 3 = 1 then 1208 else 500)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1203 else if t 3 = 1 then 1179 else 1181) else if t 2 = 1 then (if t 3 = 0 then 1197 else if t 3 = 1 then 1151 else 1155) else (if t 3 = 0 then 1199 else if t 3 = 1 then 1153 else 1157)) else (if t 2 = 0 then (if t 3 = 0 then 1204 else if t 3 = 1 then 1180 else 1182) else if t 2 = 1 then (if t 3 = 0 then 1198 else if t 3 = 1 then 1152 else 1156) else (if t 3 = 0 then 1200 else if t 3 = 1 then 1154 else 1158))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 696 else 3960) else if t 2 = 1 then (if t 3 = 0 then 2160 else if t 3 = 1 then 690 else 1524) else (if t 3 = 0 then 3523 else if t 3 = 1 then 692 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 761 else if t 3 = 1 then 1183 else 1185) else if t 2 = 1 then (if t 3 = 0 then 751 else if t 3 = 1 then 1159 else 1163) else (if t 3 = 0 then 753 else if t 3 = 1 then 1161 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 762 else if t 3 = 1 then 1184 else 1186) else if t 2 = 1 then (if t 3 = 0 then 752 else if t 3 = 1 then 1160 else 1164) else (if t 3 = 0 then 754 else if t 3 = 1 then 1162 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4692 else (if jt.2.val < 2 then 4708 else 4703)) else (if jt.2.val < 4 then 4707 else (if jt.2.val < 5 then 4709 else 4700))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3645 else (if jt.2.val < 2 then 3665 else 3647)) else (if jt.2.val < 4 then 3663 else (if jt.2.val < 5 then 3664 else 3642)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 942 else (if jt.2.val < 2 then 1177 else 970)) else (if jt.2.val < 4 then 1176 else (if jt.2.val < 5 then 1178 else 933))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1101 else (if jt.2.val < 2 then 1195 else 1103)) else (if jt.2.val < 4 then 1194 else (if jt.2.val < 5 then 1196 else 1095)))))

checked_coverage fastCoverage0583 pairing0583 template0583 witness0583

theorem coverage0583 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0583) (maskBits m))
    cores template0583 witness0583 := by
  rw [← coresFast_eq]
  exact fastCoverage0583

theorem coverageSize0583 : ∀ q : Pattern,
    (cores (witness0583 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0583 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0583
#print axioms coverageSize0583

noncomputable def pairing0584 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0584 : List (Fin 4935) := templateData0584

noncomputable def witness0584 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 3965) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3235) else (if t 3 = 0 then 3532 else if t 3 = 1 then 3531 else 2691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1650) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1649) else (if t 3 = 0 then 2200 else if t 3 = 1 then 2198 else 1661)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1611 else 878) else if t 2 = 1 then (if t 3 = 0 then 1612 else if t 3 = 1 then 1610 else 1853) else (if t 3 = 0 then 689 else if t 3 = 1 then 1616 else 1856))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1331) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1330) else (if t 3 = 0 then 2074 else if t 3 = 1 then 2072 else 1344)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3074) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4505) else (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4506)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3161 else 3314) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4518) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4515 else 4519))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1722 else 652) else if t 2 = 1 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1721 else 1355) else (if t 3 = 0 then 841 else if t 3 = 1 then 1735 else 1361)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3270 else 3093) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4507) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4499 else 4513)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 3166 else 3501) else if t 2 = 1 then (if t 3 = 0 then 3918 else if t 3 = 1 then 4516 else 4520) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4517 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4710 else (if jt.2.val < 2 then 4720 else 4721)) else (if jt.2.val < 4 then 4717 else (if jt.2.val < 5 then 4719 else 4718))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4602 else (if jt.2.val < 2 then 4604 else 4607)) else (if jt.2.val < 4 then 4603 else (if jt.2.val < 5 then 4606 else 4605)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4737 else (if jt.2.val < 2 then 4741 else 4742)) else (if jt.2.val < 4 then 4738 else (if jt.2.val < 5 then 4740 else 4739))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4549 else (if jt.2.val < 2 then 4553 else 4554)) else (if jt.2.val < 4 then 4550 else (if jt.2.val < 5 then 4552 else 4551)))))

checked_coverage fastCoverage0584 pairing0584 template0584 witness0584

theorem coverage0584 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0584) (maskBits m))
    cores template0584 witness0584 := by
  rw [← coresFast_eq]
  exact fastCoverage0584

theorem coverageSize0584 : ∀ q : Pattern,
    (cores (witness0584 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0584 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0584
#print axioms coverageSize0584

noncomputable def pairing0585 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0585 : List (Fin 4935) := templateData0585

noncomputable def witness0585 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4530) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 3234) else (if t 3 = 0 then 2789 else if t 3 = 1 then 2787 else 3522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 1648) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 1647) else (if t 3 = 0 then 727 else if t 3 = 1 then 723 else 741)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1084 else 1690) else if t 2 = 1 then (if t 3 = 0 then 1090 else if t 3 = 1 then 1078 else 1080) else (if t 3 = 0 then 1826 else if t 3 = 1 then 784 else 786))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 1329) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 1328) else (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 52)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 3073) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3827) else (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3837)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2957) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3853) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3854 else 3855))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 241 else 1787) else if t 2 = 1 then (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 260) else (if t 3 = 0 then 1472 else if t 3 = 1 then 919 else 923)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2626) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3846) else (if t 3 = 0 then 3849 else if t 3 = 1 then 3848 else 3850)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2651 else 2653) else if t 2 = 1 then (if t 3 = 0 then 4191 else if t 3 = 1 then 3856 else 3857) else (if t 3 = 0 then 4526 else if t 3 = 1 then 3858 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4674 else (if jt.2.val < 2 then 4678 else 4679)) else (if jt.2.val < 4 then 4675 else (if jt.2.val < 5 then 4677 else 4676))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4293 else (if jt.2.val < 2 then 4295 else 4298)) else (if jt.2.val < 4 then 4294 else (if jt.2.val < 5 then 4297 else 4296)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4096 else (if jt.2.val < 2 then 4100 else 4101)) else (if jt.2.val < 4 then 4097 else (if jt.2.val < 5 then 4099 else 4098))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4551 else (if jt.2.val < 2 then 4562 else 4554)) else (if jt.2.val < 4 then 4560 else (if jt.2.val < 5 then 4561 else 4549)))))

checked_coverage fastCoverage0585 pairing0585 template0585 witness0585

theorem coverage0585 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0585) (maskBits m))
    cores template0585 witness0585 := by
  rw [← coresFast_eq]
  exact fastCoverage0585

theorem coverageSize0585 : ∀ q : Pattern,
    (cores (witness0585 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0585 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0585
#print axioms coverageSize0585

noncomputable def pairing0586 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0586 : List (Fin 4935) := templateData0586

noncomputable def witness0586 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3453 else 2732) else if t 2 = 1 then (if t 3 = 0 then 3449 else if t 3 = 1 then 3445 else 2731) else (if t 3 = 0 then 4546 else if t 3 = 1 then 4211 else 3930)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3451 else 344) else if t 2 = 1 then (if t 3 = 0 then 3447 else if t 3 = 1 then 3443 else 342) else (if t 3 = 0 then 2197 else if t 3 = 1 then 2195 else 358)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 292 else 1790) else if t 2 = 1 then (if t 3 = 0 then 291 else if t 3 = 1 then 290 else 928) else (if t 3 = 0 then 1475 else if t 3 = 1 then 298 else 932))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3452 else 442) else if t 2 = 1 then (if t 3 = 0 then 3448 else if t 3 = 1 then 3444 else 440) else (if t 3 = 0 then 2071 else if t 3 = 1 then 2069 else 455)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3450 else 3082) else if t 2 = 1 then (if t 3 = 0 then 3446 else if t 3 = 1 then 3442 else 3479) else (if t 3 = 0 then 3464 else if t 3 = 1 then 3462 else 3480)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 3163 else 3315) else if t 2 = 1 then (if t 3 = 0 then 2572 else if t 3 = 1 then 3488 else 3492) else (if t 3 = 0 then 2574 else if t 3 = 1 then 3489 else 3493))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1043 else 1520) else if t 2 = 1 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1041 else 472) else (if t 3 = 0 then 1818 else if t 3 = 1 then 1056 else 479)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 3278 else 3095) else if t 2 = 1 then (if t 3 = 0 then 2838 else if t 3 = 1 then 3472 else 3486) else (if t 3 = 0 then 2842 else if t 3 = 1 then 3473 else 3487)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 3167 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2579 else if t 3 = 1 then 3490 else 3494) else (if t 3 = 0 then 2580 else if t 3 = 1 then 3491 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4647 else (if jt.2.val < 2 then 4657 else 4658)) else (if jt.2.val < 4 then 4654 else (if jt.2.val < 5 then 4656 else 4655))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3672 else (if jt.2.val < 2 then 3674 else 3677)) else (if jt.2.val < 4 then 3673 else (if jt.2.val < 5 then 3676 else 3675)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4739 else (if jt.2.val < 2 then 4745 else 4742)) else (if jt.2.val < 4 then 4743 else (if jt.2.val < 5 then 4744 else 4737))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3439 else (if jt.2.val < 2 then 3477 else 3478)) else (if jt.2.val < 4 then 3474 else (if jt.2.val < 5 then 3476 else 3475)))))

checked_coverage fastCoverage0586 pairing0586 template0586 witness0586

theorem coverage0586 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0586) (maskBits m))
    cores template0586 witness0586 := by
  rw [← coresFast_eq]
  exact fastCoverage0586

theorem coverageSize0586 : ∀ q : Pattern,
    (cores (witness0586 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0586 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0586
#print axioms coverageSize0586

noncomputable def pairing0587 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0587 : List (Fin 4935) := templateData0587

noncomputable def witness0587 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2446 else 3505) else if t 2 = 1 then (if t 3 = 0 then 2450 else if t 3 = 1 then 2442 else 3203) else (if t 3 = 0 then 3941 else if t 3 = 1 then 3939 else 4539)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2444 else 341) else if t 2 = 1 then (if t 3 = 0 then 2448 else if t 3 = 1 then 2440 else 339) else (if t 3 = 0 then 726 else if t 3 = 1 then 722 else 1489)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1756 else 406) else if t 2 = 1 then (if t 3 = 0 then 1762 else if t 3 = 1 then 1753 else 394) else (if t 3 = 0 then 1145 else if t 3 = 1 then 778 else 1498))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2445 else 439) else if t 2 = 1 then (if t 3 = 0 then 2449 else if t 3 = 1 then 2441 else 437) else (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 1511)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2443 else 2470) else if t 2 = 1 then (if t 3 = 0 then 2447 else if t 3 = 1 then 2439 else 2468) else (if t 3 = 0 then 2462 else if t 3 = 1 then 2459 else 2473)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2502 else 2504) else if t 2 = 1 then (if t 3 = 0 then 2883 else if t 3 = 1 then 2492 else 2494) else (if t 3 = 0 then 2885 else if t 3 = 1 then 2493 else 2495))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1583 else 1136) else if t 2 = 1 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1582 else 471) else (if t 3 = 0 then 71 else if t 3 = 1 then 69 else 1850)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2897 else 2900) else if t 2 = 1 then (if t 3 = 0 then 2484 else if t 3 = 1 then 2481 else 2488) else (if t 3 = 0 then 2487 else if t 3 = 1 then 2486 else 2490)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3183 else 3928) else if t 2 = 1 then (if t 3 = 0 then 3506 else if t 3 = 1 then 2496 else 2498) else (if t 3 = 0 then 3507 else if t 3 = 1 then 2497 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4623 else (if jt.2.val < 2 then 4627 else 4628)) else (if jt.2.val < 4 then 4624 else (if jt.2.val < 5 then 4626 else 4625))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3654 else (if jt.2.val < 2 then 3656 else 3659)) else (if jt.2.val < 4 then 3655 else (if jt.2.val < 5 then 3658 else 3657)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4098 else (if jt.2.val < 2 then 4121 else 4101)) else (if jt.2.val < 4 then 4119 else (if jt.2.val < 5 then 4120 else 4096))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3475 else (if jt.2.val < 2 then 3504 else 3478)) else (if jt.2.val < 4 then 3502 else (if jt.2.val < 5 then 3503 else 3439)))))

checked_coverage fastCoverage0587 pairing0587 template0587 witness0587

theorem coverage0587 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0587) (maskBits m))
    cores template0587 witness0587 := by
  rw [← coresFast_eq]
  exact fastCoverage0587

theorem coverageSize0587 : ∀ q : Pattern,
    (cores (witness0587 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0587 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0587
#print axioms coverageSize0587

noncomputable def pairing0588 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0588 : List (Fin 4935) := templateData0588

noncomputable def witness0588 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1437 else 1222) else if t 2 = 1 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1435 else 1777) else (if t 3 = 0 then 195 else if t 3 = 1 then 1447 else 1780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1432 else if t 3 = 1 then 1422 else 1202) else if t 2 = 1 then (if t 3 = 0 then 1427 else if t 3 = 1 then 1408 else 1414) else (if t 3 = 0 then 171 else if t 3 = 1 then 1411 else 1415)) else (if t 2 = 0 then (if t 3 = 0 then 4525 else if t 3 = 1 then 3953 else 3954) else if t 2 = 1 then (if t 3 = 0 then 3225 else if t 3 = 1 then 3219 else 2855) else (if t 3 = 0 then 3524 else if t 3 = 1 then 2630 else 2633))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1436 else 1221) else if t 2 = 1 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1434 else 1776) else (if t 3 = 0 then 194 else if t 3 = 1 then 1446 else 1779)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1428 else if t 3 = 1 then 1418 else 1199) else if t 2 = 1 then (if t 3 = 0 then 1423 else if t 3 = 1 then 1389 else 1400) else (if t 3 = 0 then 162 else if t 3 = 1 then 1393 else 1402)) else (if t 2 = 0 then (if t 3 = 0 then 1429 else if t 3 = 1 then 1419 else 1200) else if t 2 = 1 then (if t 3 = 0 then 1424 else if t 3 = 1 then 1391 else 1401) else (if t 3 = 0 then 163 else if t 3 = 1 then 1394 else 1403))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 779 else 3523) else if t 2 = 1 then (if t 3 = 0 then 395 else if t 3 = 1 then 1449 else 2118) else (if t 3 = 0 then 3952 else if t 3 = 1 then 1452 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1773 else if t 3 = 1 then 749 else 753) else if t 2 = 1 then (if t 3 = 0 then 365 else if t 3 = 1 then 1396 else 1404) else (if t 3 = 0 then 890 else if t 3 = 1 then 1398 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 1774 else if t 3 = 1 then 750 else 754) else if t 2 = 1 then (if t 3 = 0 then 366 else if t 3 = 1 then 1397 else 1405) else (if t 3 = 0 then 891 else if t 3 = 1 then 1399 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4623 else (if jt.2.val < 2 then 4639 else 4628)) else (if jt.2.val < 4 then 4638 else (if jt.2.val < 5 then 4640 else 4625))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4605 else (if jt.2.val < 2 then 4610 else 4607)) else (if jt.2.val < 4 then 4608 else (if jt.2.val < 5 then 4609 else 4602)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1383 else (if jt.2.val < 2 then 1385 else 1421)) else (if jt.2.val < 4 then 1384 else (if jt.2.val < 5 then 1420 else 1392))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1766 else (if jt.2.val < 2 then 1768 else 1772)) else (if jt.2.val < 4 then 1767 else (if jt.2.val < 5 then 1771 else 1770)))))

checked_coverage fastCoverage0588 pairing0588 template0588 witness0588

theorem coverage0588 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0588) (maskBits m))
    cores template0588 witness0588 := by
  rw [← coresFast_eq]
  exact fastCoverage0588

theorem coverageSize0588 : ∀ q : Pattern,
    (cores (witness0588 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0588 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0588
#print axioms coverageSize0588

noncomputable def pairing0589 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0589 : List (Fin 4935) := templateData0589

noncomputable def witness0589 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 1004 else 1376) else if t 2 = 1 then (if t 3 = 0 then 1006 else if t 3 = 1 then 1000 else 1001) else (if t 3 = 0 then 1807 else if t 3 = 1 then 100 else 101)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 995 else if t 3 = 1 then 977 else 1801) else if t 2 = 1 then (if t 3 = 0 then 991 else if t 3 = 1 then 957 else 960) else (if t 3 = 0 then 172 else if t 3 = 1 then 961 else 962)) else (if t 2 = 0 then (if t 3 = 0 then 3905 else if t 3 = 1 then 4046 else 4532) else if t 2 = 1 then (if t 3 = 0 then 2979 else if t 3 = 1 then 2970 else 3338) else (if t 3 = 0 then 2776 else if t 3 = 1 then 2972 else 3520))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 1002 else 1374) else if t 2 = 1 then (if t 3 = 0 then 1005 else if t 3 = 1 then 996 else 998) else (if t 3 = 0 then 1806 else if t 3 = 1 then 96 else 98)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 993 else if t 3 = 1 then 967 else 1795) else if t 2 = 1 then (if t 3 = 0 then 987 else if t 3 = 1 then 939 else 943) else (if t 3 = 0 then 166 else if t 3 = 1 then 945 else 947)) else (if t 2 = 0 then (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 1796) else if t 2 = 1 then (if t 3 = 0 then 988 else if t 3 = 1 then 941 else 944) else (if t 3 = 0 then 167 else if t 3 = 1 then 946 else 948))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 306 else 2782) else if t 2 = 1 then (if t 3 = 0 then 2139 else if t 3 = 1 then 300 else 302) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1476 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 377 else if t 3 = 1 then 973 else 1799) else if t 2 = 1 then (if t 3 = 0 then 367 else if t 3 = 1 then 949 else 951) else (if t 3 = 0 then 1494 else if t 3 = 1 then 953 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 378 else if t 3 = 1 then 974 else 1800) else if t 2 = 1 then (if t 3 = 0 then 368 else if t 3 = 1 then 950 else 952) else (if t 3 = 0 then 1495 else if t 3 = 1 then 954 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4647 else (if jt.2.val < 2 then 4672 else 4658)) else (if jt.2.val < 4 then 4671 else (if jt.2.val < 5 then 4673 else 4655))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4296 else (if jt.2.val < 2 then 4304 else 4298)) else (if jt.2.val < 4 then 4302 else (if jt.2.val < 5 then 4303 else 4293)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1791 else (if jt.2.val < 2 then 1793 else 1798)) else (if jt.2.val < 4 then 1792 else (if jt.2.val < 5 then 1797 else 1794))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1770 else (if jt.2.val < 2 then 1804 else 1772)) else (if jt.2.val < 4 then 1803 else (if jt.2.val < 5 then 1805 else 1766)))))

checked_coverage fastCoverage0589 pairing0589 template0589 witness0589

theorem coverage0589 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0589) (maskBits m))
    cores template0589 witness0589 := by
  rw [← coresFast_eq]
  exact fastCoverage0589

theorem coverageSize0589 : ∀ q : Pattern,
    (cores (witness0589 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0589 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0589
#print axioms coverageSize0589

noncomputable def pairing0590 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0590 : List (Fin 4935) := templateData0590

noncomputable def witness0590 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 581 else 1837) else if t 2 = 1 then (if t 3 = 0 then 579 else if t 3 = 1 then 577 else 1114) else (if t 3 = 0 then 1546 else if t 3 = 1 then 589 else 1120)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 574 else if t 3 = 1 then 566 else 568) else if t 2 = 1 then (if t 3 = 0 then 552 else if t 3 = 1 then 532 else 537) else (if t 3 = 0 then 1537 else if t 3 = 1 then 534 else 538)) else (if t 2 = 0 then (if t 3 = 0 then 3499 else if t 3 = 1 then 2756 else 2757) else if t 2 = 1 then (if t 3 = 0 then 3209 else if t 3 = 1 then 2747 else 2750) else (if t 3 = 0 then 4541 else if t 3 = 1 then 3923 else 3925))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 580 else 1836) else if t 2 = 1 then (if t 3 = 0 then 578 else if t 3 = 1 then 576 else 1113) else (if t 3 = 0 then 1545 else if t 3 = 1 then 588 else 1119)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 570 else if t 3 = 1 then 556 else 562) else if t 2 = 1 then (if t 3 = 0 then 544 else if t 3 = 1 then 515 else 524) else (if t 3 = 0 then 1531 else if t 3 = 1 then 517 else 526)) else (if t 2 = 0 then (if t 3 = 0 then 571 else if t 3 = 1 then 557 else 563) else if t 2 = 1 then (if t 3 = 0 then 545 else if t 3 = 1 then 516 else 525) else (if t 3 = 0 then 1532 else if t 3 = 1 then 518 else 527))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 1548 else 4542) else if t 2 = 1 then (if t 3 = 0 then 596 else if t 3 = 1 then 594 else 2148) else (if t 3 = 0 then 2763 else if t 3 = 1 then 600 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1110 else if t 3 = 1 then 1104 else 1542) else if t 2 = 1 then (if t 3 = 0 then 546 else if t 3 = 1 then 520 else 528) else (if t 3 = 0 then 1833 else if t 3 = 1 then 522 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 1111 else if t 3 = 1 then 1105 else 1543) else if t 2 = 1 then (if t 3 = 0 then 547 else if t 3 = 1 then 521 else 529) else (if t 3 = 0 then 1834 else if t 3 = 1 then 523 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4674 else (if jt.2.val < 2 then 4690 else 4679)) else (if jt.2.val < 4 then 4689 else (if jt.2.val < 5 then 4691 else 4676))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3675 else (if jt.2.val < 2 then 3686 else 3677)) else (if jt.2.val < 4 then 3684 else (if jt.2.val < 5 then 3685 else 3672)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1392 else (if jt.2.val < 2 then 1540 else 1421)) else (if jt.2.val < 4 then 1539 else (if jt.2.val < 5 then 1541 else 1383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1827 else (if jt.2.val < 2 then 1829 else 1832)) else (if jt.2.val < 4 then 1828 else (if jt.2.val < 5 then 1831 else 1830)))))

checked_coverage fastCoverage0590 pairing0590 template0590 witness0590

theorem coverage0590 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0590) (maskBits m))
    cores template0590 witness0590 := by
  rw [← coresFast_eq]
  exact fastCoverage0590

theorem coverageSize0590 : ∀ q : Pattern,
    (cores (witness0590 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0590 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0590
#print axioms coverageSize0590

noncomputable def pairing0591 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0591 : List (Fin 4935) := templateData0591

noncomputable def witness0591 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1910 else 506) else if t 2 = 1 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1907 else 496) else (if t 3 = 0 then 900 else if t 3 = 1 then 94 else 1523)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1891 else 1188) else if t 2 = 1 then (if t 3 = 0 then 1901 else if t 3 = 1 then 1875 else 1878) else (if t 3 = 0 then 158 else if t 3 = 1 then 1877 else 1879)) else (if t 2 = 0 then (if t 3 = 0 then 2561 else if t 3 = 1 then 2938 else 3514) else if t 2 = 1 then (if t 3 = 0 then 2546 else if t 3 = 1 then 3348 else 3350) else (if t 3 = 0 then 3946 else if t 3 = 1 then 4064 else 4537))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1908 else 504) else if t 2 = 1 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1905 else 492) else (if t 3 = 0 then 899 else if t 3 = 1 then 90 else 1521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1887 else 1181) else if t 2 = 1 then (if t 3 = 0 then 1899 else if t 3 = 1 then 1859 else 1863) else (if t 3 = 0 then 152 else if t 3 = 1 then 1861 else 1865)) else (if t 2 = 0 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1888 else 1182) else if t 2 = 1 then (if t 3 = 0 then 1900 else if t 3 = 1 then 1860 else 1864) else (if t 3 = 0 then 153 else if t 3 = 1 then 1862 else 1866))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1620 else 3960) else if t 2 = 1 then (if t 3 = 0 then 2172 else if t 3 = 1 then 1617 else 494) else (if t 3 = 0 then 3525 else if t 3 = 1 then 92 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1673 else if t 3 = 1 then 1889 else 1185) else if t 2 = 1 then (if t 3 = 0 then 1667 else if t 3 = 1 then 1867 else 1871) else (if t 3 = 0 then 154 else if t 3 = 1 then 1869 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 1674 else if t 3 = 1 then 1890 else 1186) else if t 2 = 1 then (if t 3 = 0 then 1668 else if t 3 = 1 then 1868 else 1872) else (if t 3 = 0 then 155 else if t 3 = 1 then 1870 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4710 else (if jt.2.val < 2 then 4726 else 4721)) else (if jt.2.val < 4 then 4725 else (if jt.2.val < 5 then 4727 else 4718))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3657 else (if jt.2.val < 2 then 3671 else 3659)) else (if jt.2.val < 4 then 3669 else (if jt.2.val < 5 then 3670 else 3654)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1794 else (if jt.2.val < 2 then 1885 else 1798)) else (if jt.2.val < 4 then 1884 else (if jt.2.val < 5 then 1886 else 1791))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1830 else (if jt.2.val < 2 then 1897 else 1832)) else (if jt.2.val < 4 then 1896 else (if jt.2.val < 5 then 1898 else 1827)))))

checked_coverage fastCoverage0591 pairing0591 template0591 witness0591

theorem coverage0591 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0591) (maskBits m))
    cores template0591 witness0591 := by
  rw [← coresFast_eq]
  exact fastCoverage0591

theorem coverageSize0591 : ∀ q : Pattern,
    (cores (witness0591 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0591 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0591
#print axioms coverageSize0591

noncomputable def pairing0592 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0592 : List (Fin 4935) := templateData0592

noncomputable def witness0592 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 4213) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3531) else (if t 3 = 0 then 3236 else if t 3 = 1 then 3235 else 2691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 2199) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 2198) else (if t 3 = 0 then 1651 else if t 3 = 1 then 1649 else 1661)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1611 else 299) else if t 2 = 1 then (if t 3 = 0 then 1612 else if t 3 = 1 then 1610 else 1616) else (if t 3 = 0 then 1094 else if t 3 = 1 then 1853 else 1856))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 2073) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 2072) else (if t 3 = 0 then 1332 else if t 3 = 1 then 1330 else 1344)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3465) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4492) else (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4506)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3161 else 3164) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4515) else (if t 3 = 0 then 4038 else if t 3 = 1 then 4518 else 4519))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1722 else 1057) else if t 2 = 1 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1721 else 1735) else (if t 3 = 0 then 262 else if t 3 = 1 then 1355 else 1361)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3270 else 3280) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4499) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4507 else 4513)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 3166 else 3168) else if t 2 = 1 then (if t 3 = 0 then 3918 else if t 3 = 1 then 4516 else 4517) else (if t 3 = 0 then 4192 else if t 3 = 1 then 4520 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4710 else (if jt.2.val < 2 then 4720 else 4721)) else (if jt.2.val < 4 then 4717 else (if jt.2.val < 5 then 4719 else 4718))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4602 else (if jt.2.val < 2 then 4604 else 4607)) else (if jt.2.val < 4 then 4603 else (if jt.2.val < 5 then 4606 else 4605)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4468 else (if jt.2.val < 2 then 4503 else 4504)) else (if jt.2.val < 4 then 4500 else (if jt.2.val < 5 then 4502 else 4501))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4746 else (if jt.2.val < 2 then 4750 else 4751)) else (if jt.2.val < 4 then 4747 else (if jt.2.val < 5 then 4749 else 4748)))))

checked_coverage fastCoverage0592 pairing0592 template0592 witness0592

theorem coverage0592 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0592) (maskBits m))
    cores template0592 witness0592 := by
  rw [← coresFast_eq]
  exact fastCoverage0592

theorem coverageSize0592 : ∀ q : Pattern,
    (cores (witness0592 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0592 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0592
#print axioms coverageSize0592

noncomputable def pairing0593 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0593 : List (Fin 4935) := templateData0593

noncomputable def witness0593 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 4546) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 3530) else (if t 3 = 0 then 2789 else if t 3 = 1 then 2788 else 3192)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 2197) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 2196) else (if t 3 = 0 then 727 else if t 3 = 1 then 725 else 742)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 681 else 1475) else if t 2 = 1 then (if t 3 = 0 then 682 else if t 3 = 1 then 680 else 688) else (if t 3 = 0 then 1826 else if t 3 = 1 then 1144 else 1148))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 2071) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 2070) else (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 53)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 3464) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4155) else (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4171)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2574) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4180) else (if t 3 = 0 then 4039 else if t 3 = 1 then 4183 else 4184))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 822 else 1818) else if t 2 = 1 then (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 840) else (if t 3 = 0 then 1472 else if t 3 = 1 then 70 else 77)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2842) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4164) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4177 else 4178)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2578 else 2580) else if t 2 = 1 then (if t 3 = 0 then 3919 else if t 3 = 1 then 4181 else 4182) else (if t 3 = 0 then 4526 else if t 3 = 1 then 4185 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4692 else (if jt.2.val < 2 then 4702 else 4703)) else (if jt.2.val < 4 then 4699 else (if jt.2.val < 5 then 4701 else 4700))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4305 else (if jt.2.val < 2 then 4307 else 4310)) else (if jt.2.val < 4 then 4306 else (if jt.2.val < 5 then 4309 else 4308)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4132 else (if jt.2.val < 2 then 4168 else 4169)) else (if jt.2.val < 4 then 4165 else (if jt.2.val < 5 then 4167 else 4166))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4748 else (if jt.2.val < 2 then 4754 else 4751)) else (if jt.2.val < 4 then 4752 else (if jt.2.val < 5 then 4753 else 4746)))))

checked_coverage fastCoverage0593 pairing0593 template0593 witness0593

theorem coverage0593 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0593) (maskBits m))
    cores template0593 witness0593 := by
  rw [← coresFast_eq]
  exact fastCoverage0593

theorem coverageSize0593 : ∀ q : Pattern,
    (cores (witness0593 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0593 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0593
#print axioms coverageSize0593

noncomputable def pairing0594 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0594 : List (Fin 4935) := templateData0594

noncomputable def witness0594 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3062 else 2732) else if t 2 = 1 then (if t 3 = 0 then 3058 else if t 3 = 1 then 3054 else 2730) else (if t 3 = 0 then 4530 else if t 3 = 1 then 3963 else 4205)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3060 else 344) else if t 2 = 1 then (if t 3 = 0 then 3056 else if t 3 = 1 then 3052 else 340) else (if t 3 = 0 then 1648 else if t 3 = 1 then 1646 else 357)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 874 else 1790) else if t 2 = 1 then (if t 3 = 0 then 868 else if t 3 = 1 then 862 else 400) else (if t 3 = 0 then 1690 else if t 3 = 1 then 864 else 402))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3061 else 442) else if t 2 = 1 then (if t 3 = 0 then 3057 else if t 3 = 1 then 3053 else 438) else (if t 3 = 0 then 1329 else if t 3 = 1 then 1327 else 454)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3059 else 3082) else if t 2 = 1 then (if t 3 = 0 then 3055 else if t 3 = 1 then 3051 else 3080) else (if t 3 = 0 then 3073 else if t 3 = 1 then 3071 else 3083)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 3313 else 3315) else if t 2 = 1 then (if t 3 = 0 then 2956 else if t 3 = 1 then 3098 else 3100) else (if t 3 = 0 then 2957 else if t 3 = 1 then 3099 else 3101))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 638 else 1520) else if t 2 = 1 then (if t 3 = 0 then 635 else if t 3 = 1 then 634 else 1135) else (if t 3 = 0 then 1787 else if t 3 = 1 then 650 else 1139)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 3091 else 3095) else if t 2 = 1 then (if t 3 = 0 then 2622 else if t 3 = 1 then 3089 else 3094) else (if t 3 = 0 then 2626 else if t 3 = 1 then 3092 else 3096)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 3500 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2652 else if t 3 = 1 then 3102 else 3104) else (if t 3 = 0 then 2653 else if t 3 = 1 then 3103 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4611 else (if jt.2.val < 2 then 4615 else 4616)) else (if jt.2.val < 4 then 4612 else (if jt.2.val < 5 then 4614 else 4613))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3642 else (if jt.2.val < 2 then 3644 else 3647)) else (if jt.2.val < 4 then 3643 else (if jt.2.val < 5 then 3646 else 3645)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4501 else (if jt.2.val < 2 then 4529 else 4504)) else (if jt.2.val < 4 then 4527 else (if jt.2.val < 5 then 4528 else 4468))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3385 else (if jt.2.val < 2 then 3389 else 3390)) else (if jt.2.val < 4 then 3386 else (if jt.2.val < 5 then 3388 else 3387)))))

checked_coverage fastCoverage0594 pairing0594 template0594 witness0594

theorem coverage0594 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0594) (maskBits m))
    cores template0594 witness0594 := by
  rw [← coresFast_eq]
  exact fastCoverage0594

theorem coverageSize0594 : ∀ q : Pattern,
    (cores (witness0594 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0594 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0594
#print axioms coverageSize0594

noncomputable def pairing0595 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0595 : List (Fin 4935) := templateData0595

noncomputable def witness0595 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2450 else 3205) else if t 2 = 1 then (if t 3 = 0 then 2446 else if t 3 = 1 then 2442 else 3203) else (if t 3 = 0 then 4196 else if t 3 = 1 then 3939 else 4539)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2448 else 343) else if t 2 = 1 then (if t 3 = 0 then 2444 else if t 3 = 1 then 2440 else 339) else (if t 3 = 0 then 724 else if t 3 = 1 then 722 else 1489)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1762 else 929) else if t 2 = 1 then (if t 3 = 0 then 1756 else if t 3 = 1 then 1753 else 394) else (if t 3 = 0 then 790 else if t 3 = 1 then 778 else 1498))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2449 else 441) else if t 2 = 1 then (if t 3 = 0 then 2445 else if t 3 = 1 then 2441 else 437) else (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 1511)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2447 else 2471) else if t 2 = 1 then (if t 3 = 0 then 2443 else if t 3 = 1 then 2439 else 2468) else (if t 3 = 0 then 2461 else if t 3 = 1 then 2459 else 2473)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2883 else 2886) else if t 2 = 1 then (if t 3 = 0 then 2502 else if t 3 = 1 then 2492 else 2494) else (if t 3 = 0 then 2503 else if t 3 = 1 then 2493 else 2495))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1586 else 473) else if t 2 = 1 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1582 else 471) else (if t 3 = 0 then 920 else if t 3 = 1 then 69 else 1850)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2484 else 2489) else if t 2 = 1 then (if t 3 = 0 then 2897 else if t 3 = 1 then 2481 else 2488) else (if t 3 = 0 then 2899 else if t 3 = 1 then 2486 else 2490)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3506 else 4197) else if t 2 = 1 then (if t 3 = 0 then 3183 else if t 3 = 1 then 2496 else 2498) else (if t 3 = 0 then 3184 else if t 3 = 1 then 2497 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4623 else (if jt.2.val < 2 then 4627 else 4628)) else (if jt.2.val < 4 then 4624 else (if jt.2.val < 5 then 4626 else 4625))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3654 else (if jt.2.val < 2 then 3656 else 3659)) else (if jt.2.val < 4 then 3655 else (if jt.2.val < 5 then 3658 else 3657)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4166 else (if jt.2.val < 2 then 4195 else 4169)) else (if jt.2.val < 4 then 4193 else (if jt.2.val < 5 then 4194 else 4132))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3387 else (if jt.2.val < 2 then 3411 else 3390)) else (if jt.2.val < 4 then 3408 else (if jt.2.val < 5 then 3409 else 3385)))))

checked_coverage fastCoverage0595 pairing0595 template0595 witness0595

theorem coverage0595 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0595) (maskBits m))
    cores template0595 witness0595 := by
  rw [← coresFast_eq]
  exact fastCoverage0595

theorem coverageSize0595 : ∀ q : Pattern,
    (cores (witness0595 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0595 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0595
#print axioms coverageSize0595

noncomputable def pairing0596 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0596 : List (Fin 4935) := templateData0596

noncomputable def witness0596 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1437 else 591) else if t 2 = 1 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1435 else 1447) else (if t 3 = 0 then 1012 else if t 3 = 1 then 1777 else 1780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1432 else if t 3 = 1 then 1422 else 567) else if t 2 = 1 then (if t 3 = 0 then 1427 else if t 3 = 1 then 1408 else 1411) else (if t 3 = 0 then 992 else if t 3 = 1 then 1414 else 1415)) else (if t 2 = 0 then (if t 3 = 0 then 4525 else if t 3 = 1 then 3953 else 4207) else if t 2 = 1 then (if t 3 = 0 then 3225 else if t 3 = 1 then 3219 else 2630) else (if t 3 = 0 then 3226 else if t 3 = 1 then 2855 else 2633))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1436 else 590) else if t 2 = 1 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1434 else 1446) else (if t 3 = 0 then 1011 else if t 3 = 1 then 1776 else 1779)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1428 else if t 3 = 1 then 1418 else 558) else if t 2 = 1 then (if t 3 = 0 then 1423 else if t 3 = 1 then 1389 else 1393) else (if t 3 = 0 then 989 else if t 3 = 1 then 1400 else 1402)) else (if t 2 = 0 then (if t 3 = 0 then 1429 else if t 3 = 1 then 1419 else 559) else if t 2 = 1 then (if t 3 = 0 then 1424 else if t 3 = 1 then 1391 else 1394) else (if t 3 = 0 then 990 else if t 3 = 1 then 1401 else 1403))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 779 else 3216) else if t 2 = 1 then (if t 3 = 0 then 395 else if t 3 = 1 then 1449 else 1452) else (if t 3 = 0 then 4206 else if t 3 = 1 then 2118 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1773 else if t 3 = 1 then 749 else 1106) else if t 2 = 1 then (if t 3 = 0 then 365 else if t 3 = 1 then 1396 else 1398) else (if t 3 = 0 then 369 else if t 3 = 1 then 1404 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 1774 else if t 3 = 1 then 750 else 1107) else if t 2 = 1 then (if t 3 = 0 then 366 else if t 3 = 1 then 1397 else 1399) else (if t 3 = 0 then 370 else if t 3 = 1 then 1405 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4623 else (if jt.2.val < 2 then 4639 else 4628)) else (if jt.2.val < 4 then 4638 else (if jt.2.val < 5 then 4640 else 4625))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4605 else (if jt.2.val < 2 then 4610 else 4607)) else (if jt.2.val < 4 then 4608 else (if jt.2.val < 5 then 4609 else 4602)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2280 else (if jt.2.val < 2 then 2282 else 2285)) else (if jt.2.val < 4 then 2281 else (if jt.2.val < 5 then 2284 else 2283))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1986 else (if jt.2.val < 2 then 1988 else 1994)) else (if jt.2.val < 4 then 1987 else (if jt.2.val < 5 then 1993 else 1989)))))

checked_coverage fastCoverage0596 pairing0596 template0596 witness0596

theorem coverage0596 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0596) (maskBits m))
    cores template0596 witness0596 := by
  rw [← coresFast_eq]
  exact fastCoverage0596

theorem coverageSize0596 : ∀ q : Pattern,
    (cores (witness0596 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0596 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0596
#print axioms coverageSize0596

noncomputable def pairing0597 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0597 : List (Fin 4935) := templateData0597

noncomputable def witness0597 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 183 else 1546) else if t 2 = 1 then (if t 3 = 0 then 185 else if t 3 = 1 then 181 else 193) else (if t 3 = 0 then 1807 else if t 3 = 1 then 898 else 904)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 178 else if t 3 = 1 then 156 else 1537) else if t 2 = 1 then (if t 3 = 0 then 170 else if t 3 = 1 then 136 else 139) else (if t 3 = 0 then 172 else if t 3 = 1 then 142 else 143)) else (if t 2 = 0 then (if t 3 = 0 then 4190 else if t 3 = 1 then 3945 else 4541) else if t 2 = 1 then (if t 3 = 0 then 2775 else if t 3 = 1 then 2766 else 3172) else (if t 3 = 0 then 2776 else if t 3 = 1 then 2769 else 3174))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 182 else 1545) else if t 2 = 1 then (if t 3 = 0 then 184 else if t 3 = 1 then 180 else 192) else (if t 3 = 0 then 1806 else if t 3 = 1 then 897 else 903)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 174 else if t 3 = 1 then 146 else 1531) else if t 2 = 1 then (if t 3 = 0 then 160 else if t 3 = 1 then 117 else 121) else (if t 3 = 0 then 166 else if t 3 = 1 then 128 else 130)) else (if t 2 = 0 then (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 1532) else if t 2 = 1 then (if t 3 = 0 then 161 else if t 3 = 1 then 119 else 122) else (if t 3 = 0 then 167 else if t 3 = 1 then 129 else 131))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 200 else 2763) else if t 2 = 1 then (if t 3 = 0 then 1500 else if t 3 = 1 then 198 else 204) else (if t 3 = 0 then 4540 else if t 3 = 1 then 2127 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 894 else if t 3 = 1 then 150 else 1833) else if t 2 = 1 then (if t 3 = 0 then 888 else if t 3 = 1 then 124 else 126) else (if t 3 = 0 then 1494 else if t 3 = 1 then 132 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 895 else if t 3 = 1 then 151 else 1834) else if t 2 = 1 then (if t 3 = 0 then 889 else if t 3 = 1 then 125 else 127) else (if t 3 = 0 then 1495 else if t 3 = 1 then 133 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4611 else (if jt.2.val < 2 then 4645 else 4616)) else (if jt.2.val < 4 then 4644 else (if jt.2.val < 5 then 4646 else 4613))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4308 else (if jt.2.val < 2 then 4313 else 4310)) else (if jt.2.val < 4 then 4311 else (if jt.2.val < 5 then 4312 else 4305)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2295 else (if jt.2.val < 2 then 2297 else 2300)) else (if jt.2.val < 4 then 2296 else (if jt.2.val < 5 then 2299 else 2298))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1989 else (if jt.2.val < 2 then 2011 else 1994)) else (if jt.2.val < 4 then 2010 else (if jt.2.val < 5 then 2012 else 1986)))))

checked_coverage fastCoverage0597 pairing0597 template0597 witness0597

theorem coverage0597 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0597) (maskBits m))
    cores template0597 witness0597 := by
  rw [← coresFast_eq]
  exact fastCoverage0597

theorem coverageSize0597 : ∀ q : Pattern,
    (cores (witness0597 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0597 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0597
#print axioms coverageSize0597

noncomputable def pairing0598 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0598 : List (Fin 4935) := templateData0598

noncomputable def witness0598 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1216 else 1837) else if t 2 = 1 then (if t 3 = 0 then 1214 else if t 3 = 1 then 1210 else 502) else (if t 3 = 0 then 1376 else if t 3 = 1 then 1211 else 503)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1205 else if t 3 = 1 then 1201 else 568) else if t 2 = 1 then (if t 3 = 0 then 1187 else if t 3 = 1 then 1167 else 1170) else (if t 3 = 0 then 1801 else if t 3 = 1 then 1169 else 1171)) else (if t 2 = 0 then (if t 3 = 0 then 3152 else if t 3 = 1 then 3002 else 2757) else if t 2 = 1 then (if t 3 = 0 then 3329 else if t 3 = 1 then 2993 else 2995) else (if t 3 = 0 then 4532 else if t 3 = 1 then 4054 else 4203))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1215 else 1836) else if t 2 = 1 then (if t 3 = 0 then 1212 else if t 3 = 1 then 1206 else 498) else (if t 3 = 0 then 1374 else if t 3 = 1 then 1208 else 500)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1203 else if t 3 = 1 then 1197 else 562) else if t 2 = 1 then (if t 3 = 0 then 1179 else if t 3 = 1 then 1151 else 1155) else (if t 3 = 0 then 1795 else if t 3 = 1 then 1153 else 1157)) else (if t 2 = 0 then (if t 3 = 0 then 1204 else if t 3 = 1 then 1198 else 563) else if t 2 = 1 then (if t 3 = 0 then 1180 else if t 3 = 1 then 1152 else 1156) else (if t 3 = 0 then 1796 else if t 3 = 1 then 1154 else 1158))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 2160 else 4542) else if t 2 = 1 then (if t 3 = 0 then 696 else if t 3 = 1 then 690 else 1524) else (if t 3 = 0 then 2782 else if t 3 = 1 then 692 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 761 else if t 3 = 1 then 751 else 1542) else if t 2 = 1 then (if t 3 = 0 then 1183 else if t 3 = 1 then 1159 else 1163) else (if t 3 = 0 then 1799 else if t 3 = 1 then 1161 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 762 else if t 3 = 1 then 752 else 1543) else if t 2 = 1 then (if t 3 = 0 then 1184 else if t 3 = 1 then 1160 else 1164) else (if t 3 = 0 then 1800 else if t 3 = 1 then 1162 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4692 else (if jt.2.val < 2 then 4708 else 4703)) else (if jt.2.val < 4 then 4707 else (if jt.2.val < 5 then 4709 else 4700))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3645 else (if jt.2.val < 2 then 3665 else 3647)) else (if jt.2.val < 4 then 3663 else (if jt.2.val < 5 then 3664 else 3642)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2283 else (if jt.2.val < 2 then 2311 else 2285)) else (if jt.2.val < 4 then 2310 else (if jt.2.val < 5 then 2312 else 2280))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2304 else (if jt.2.val < 2 then 2306 else 2309)) else (if jt.2.val < 4 then 2305 else (if jt.2.val < 5 then 2308 else 2307)))))

checked_coverage fastCoverage0598 pairing0598 template0598 witness0598

theorem coverage0598 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0598) (maskBits m))
    cores template0598 witness0598 := by
  rw [← coresFast_eq]
  exact fastCoverage0598

theorem coverageSize0598 : ∀ q : Pattern,
    (cores (witness0598 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0598 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0598
#print axioms coverageSize0598

noncomputable def pairing0599 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0599 : List (Fin 4935) := templateData0599

noncomputable def witness0599 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1912 else 1116) else if t 2 = 1 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1907 else 496) else (if t 3 = 0 then 104 else if t 3 = 1 then 94 else 1523)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1901 else 554) else if t 2 = 1 then (if t 3 = 0 then 1891 else if t 3 = 1 then 1875 else 1878) else (if t 3 = 0 then 978 else if t 3 = 1 then 1877 else 1879)) else (if t 2 = 0 then (if t 3 = 0 then 2561 else if t 3 = 1 then 2546 else 3210) else if t 2 = 1 then (if t 3 = 0 then 2938 else if t 3 = 1 then 3348 else 3350) else (if t 3 = 0 then 4198 else if t 3 = 1 then 4064 else 4537))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1911 else 1115) else if t 2 = 1 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1905 else 492) else (if t 3 = 0 then 102 else if t 3 = 1 then 90 else 1521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1899 else 548) else if t 2 = 1 then (if t 3 = 0 then 1887 else if t 3 = 1 then 1859 else 1863) else (if t 3 = 0 then 971 else if t 3 = 1 then 1861 else 1865)) else (if t 2 = 0 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1900 else 549) else if t 2 = 1 then (if t 3 = 0 then 1888 else if t 3 = 1 then 1860 else 1864) else (if t 3 = 0 then 972 else if t 3 = 1 then 1862 else 1866))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 2172 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1620 else if t 3 = 1 then 1617 else 494) else (if t 3 = 0 then 3229 else if t 3 = 1 then 92 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1673 else if t 3 = 1 then 1667 else 550) else if t 2 = 1 then (if t 3 = 0 then 1889 else if t 3 = 1 then 1867 else 1871) else (if t 3 = 0 then 975 else if t 3 = 1 then 1869 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 1674 else if t 3 = 1 then 1668 else 551) else if t 2 = 1 then (if t 3 = 0 then 1890 else if t 3 = 1 then 1868 else 1872) else (if t 3 = 0 then 976 else if t 3 = 1 then 1870 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4710 else (if jt.2.val < 2 then 4726 else 4721)) else (if jt.2.val < 4 then 4725 else (if jt.2.val < 5 then 4727 else 4718))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3657 else (if jt.2.val < 2 then 3671 else 3659)) else (if jt.2.val < 4 then 3669 else (if jt.2.val < 5 then 3670 else 3654)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2298 else (if jt.2.val < 2 then 2320 else 2300)) else (if jt.2.val < 4 then 2319 else (if jt.2.val < 5 then 2321 else 2295))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2307 else (if jt.2.val < 2 then 2317 else 2309)) else (if jt.2.val < 4 then 2316 else (if jt.2.val < 5 then 2318 else 2304)))))

checked_coverage fastCoverage0599 pairing0599 template0599 witness0599

theorem coverage0599 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0599) (maskBits m))
    cores template0599 witness0599 := by
  rw [← coresFast_eq]
  exact fastCoverage0599

theorem coverageSize0599 : ∀ q : Pattern,
    (cores (witness0599 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0599 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0599
#print axioms coverageSize0599

end Crown.CertificateData
