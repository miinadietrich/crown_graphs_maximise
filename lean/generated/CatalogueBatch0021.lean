import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0020

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0800 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0800 : List (Fin 4935) := templateData0800

noncomputable def witness0800 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 3965) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3235) else (if t 3 = 0 then 3532 else if t 3 = 1 then 3531 else 2691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1650) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1649) else (if t 3 = 0 then 2200 else if t 3 = 1 then 2198 else 1661)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1881 else 159) else if t 2 = 1 then (if t 3 = 0 then 1882 else if t 3 = 1 then 1880 else 1670) else (if t 3 = 0 then 1190 else if t 3 = 1 then 1892 else 1676))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1331) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1330) else (if t 3 = 0 then 2074 else if t 3 = 1 then 2072 else 1344)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3074) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4505) else (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4506)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3270 else 3093) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4507) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4499 else 4513))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1443 else 1223) else if t 2 = 1 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1442 else 1778) else (if t 3 = 0 then 197 else if t 3 = 1 then 1448 else 1781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3161 else 3314) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4518) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4515 else 4519)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 3166 else 3501) else if t 2 = 1 then (if t 3 = 0 then 3918 else if t 3 = 1 then 4516 else 4520) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4517 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4926 else (if jt.2.val < 2 then 4928 else 4931)) else (if jt.2.val < 4 then 4927 else (if jt.2.val < 5 then 4930 else 4929))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4469 else (if jt.2.val < 2 then 4496 else 4497)) else (if jt.2.val < 4 then 4493 else (if jt.2.val < 5 then 4495 else 4494)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4737 else (if jt.2.val < 2 then 4741 else 4742)) else (if jt.2.val < 4 then 4738 else (if jt.2.val < 5 then 4740 else 4739))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4549 else (if jt.2.val < 2 then 4553 else 4554)) else (if jt.2.val < 4 then 4550 else (if jt.2.val < 5 then 4552 else 4551)))))

checked_coverage fastCoverage0800 pairing0800 template0800 witness0800

theorem coverage0800 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0800) (maskBits m))
    cores template0800 witness0800 := by
  rw [← coresFast_eq]
  exact fastCoverage0800

theorem coverageSize0800 : ∀ q : Pattern,
    (cores (witness0800 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0800 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0800
#print axioms coverageSize0800

noncomputable def pairing0801 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0801 : List (Fin 4935) := templateData0801

noncomputable def witness0801 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4530) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 3234) else (if t 3 = 0 then 2789 else if t 3 = 1 then 2787 else 3522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 1648) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 1647) else (if t 3 = 0 then 727 else if t 3 = 1 then 723 else 741)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 536 else 1835) else if t 2 = 1 then (if t 3 = 0 then 539 else if t 3 = 1 then 535 else 553) else (if t 3 = 0 then 1544 else if t 3 = 1 then 1108 else 1112))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 1329) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 1328) else (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 52)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 3073) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3827) else (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3837)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2626) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3846) else (if t 3 = 0 then 3849 else if t 3 = 1 then 3848 else 3850))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 1003 else 1375) else if t 2 = 1 then (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 999) else (if t 3 = 0 then 1808 else if t 3 = 1 then 97 else 99)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2957) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3853) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3854 else 3855)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2651 else 2653) else if t 2 = 1 then (if t 3 = 0 then 4191 else if t 3 = 1 then 3856 else 3857) else (if t 3 = 0 then 4526 else if t 3 = 1 then 3858 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4905 else (if jt.2.val < 2 then 4907 else 4910)) else (if jt.2.val < 4 then 4906 else (if jt.2.val < 5 then 4909 else 4908))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4095 else (if jt.2.val < 2 then 4105 else 4106)) else (if jt.2.val < 4 then 4102 else (if jt.2.val < 5 then 4104 else 4103)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4096 else (if jt.2.val < 2 then 4100 else 4101)) else (if jt.2.val < 4 then 4097 else (if jt.2.val < 5 then 4099 else 4098))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4551 else (if jt.2.val < 2 then 4562 else 4554)) else (if jt.2.val < 4 then 4560 else (if jt.2.val < 5 then 4561 else 4549)))))

checked_coverage fastCoverage0801 pairing0801 template0801 witness0801

theorem coverage0801 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0801) (maskBits m))
    cores template0801 witness0801 := by
  rw [← coresFast_eq]
  exact fastCoverage0801

theorem coverageSize0801 : ∀ q : Pattern,
    (cores (witness0801 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0801 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0801
#print axioms coverageSize0801

noncomputable def pairing0802 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0802 : List (Fin 4935) := templateData0802

noncomputable def witness0802 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3453 else 2732) else if t 2 = 1 then (if t 3 = 0 then 3449 else if t 3 = 1 then 3445 else 2731) else (if t 3 = 0 then 4546 else if t 3 = 1 then 4211 else 3930)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3451 else 344) else if t 2 = 1 then (if t 3 = 0 then 3447 else if t 3 = 1 then 3443 else 342) else (if t 3 = 0 then 2197 else if t 3 = 1 then 2195 else 358)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 965 else 1496) else if t 2 = 1 then (if t 3 = 0 then 964 else if t 3 = 1 then 963 else 373) else (if t 3 = 0 then 1802 else if t 3 = 1 then 979 else 380))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3452 else 442) else if t 2 = 1 then (if t 3 = 0 then 3448 else if t 3 = 1 then 3444 else 440) else (if t 3 = 0 then 2071 else if t 3 = 1 then 2069 else 455)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3450 else 3082) else if t 2 = 1 then (if t 3 = 0 then 3446 else if t 3 = 1 then 3442 else 3479) else (if t 3 = 0 then 3464 else if t 3 = 1 then 3462 else 3480)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 3278 else 3095) else if t 2 = 1 then (if t 3 = 0 then 2838 else if t 3 = 1 then 3472 else 3486) else (if t 3 = 0 then 2842 else if t 3 = 1 then 3473 else 3487))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 586 else 1838) else if t 2 = 1 then (if t 3 = 0 then 585 else if t 3 = 1 then 584 else 1117) else (if t 3 = 0 then 1547 else if t 3 = 1 then 592 else 1121)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 3163 else 3315) else if t 2 = 1 then (if t 3 = 0 then 2572 else if t 3 = 1 then 3488 else 3492) else (if t 3 = 0 then 2574 else if t 3 = 1 then 3489 else 3493)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 3167 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2579 else if t 3 = 1 then 3490 else 3494) else (if t 3 = 0 then 2580 else if t 3 = 1 then 3491 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4881 else (if jt.2.val < 2 then 4883 else 4886)) else (if jt.2.val < 4 then 4882 else (if jt.2.val < 5 then 4885 else 4884))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3440 else (if jt.2.val < 2 then 3470 else 3471)) else (if jt.2.val < 4 then 3467 else (if jt.2.val < 5 then 3469 else 3468)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4739 else (if jt.2.val < 2 then 4745 else 4742)) else (if jt.2.val < 4 then 4743 else (if jt.2.val < 5 then 4744 else 4737))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3439 else (if jt.2.val < 2 then 3477 else 3478)) else (if jt.2.val < 4 then 3474 else (if jt.2.val < 5 then 3476 else 3475)))))

checked_coverage fastCoverage0802 pairing0802 template0802 witness0802

theorem coverage0802 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0802) (maskBits m))
    cores template0802 witness0802 := by
  rw [← coresFast_eq]
  exact fastCoverage0802

theorem coverageSize0802 : ∀ q : Pattern,
    (cores (witness0802 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0802 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0802
#print axioms coverageSize0802

noncomputable def pairing0803 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0803 : List (Fin 4935) := templateData0803

noncomputable def witness0803 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2446 else 3505) else if t 2 = 1 then (if t 3 = 0 then 2450 else if t 3 = 1 then 2442 else 3203) else (if t 3 = 0 then 3941 else if t 3 = 1 then 3939 else 4539)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2444 else 341) else if t 2 = 1 then (if t 3 = 0 then 2448 else if t 3 = 1 then 2440 else 339) else (if t 3 = 0 then 726 else if t 3 = 1 then 722 else 1489)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1413 else 893) else if t 2 = 1 then (if t 3 = 0 then 1416 else if t 3 = 1 then 1412 else 372) else (if t 3 = 0 then 758 else if t 3 = 1 then 756 else 1775))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2445 else 439) else if t 2 = 1 then (if t 3 = 0 then 2449 else if t 3 = 1 then 2441 else 437) else (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 1511)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2443 else 2470) else if t 2 = 1 then (if t 3 = 0 then 2447 else if t 3 = 1 then 2439 else 2468) else (if t 3 = 0 then 2462 else if t 3 = 1 then 2459 else 2473)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2897 else 2900) else if t 2 = 1 then (if t 3 = 0 then 2484 else if t 3 = 1 then 2481 else 2488) else (if t 3 = 0 then 2487 else if t 3 = 1 then 2486 else 2490))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1909 else 505) else if t 2 = 1 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1906 else 493) else (if t 3 = 0 then 902 else if t 3 = 1 then 91 else 1522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2502 else 2504) else if t 2 = 1 then (if t 3 = 0 then 2883 else if t 3 = 1 then 2492 else 2494) else (if t 3 = 0 then 2885 else if t 3 = 1 then 2493 else 2495)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3183 else 3928) else if t 2 = 1 then (if t 3 = 0 then 3506 else if t 3 = 1 then 2496 else 2498) else (if t 3 = 0 then 3507 else if t 3 = 1 then 2497 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4863 else (if jt.2.val < 2 then 4865 else 4868)) else (if jt.2.val < 4 then 4864 else (if jt.2.val < 5 then 4867 else 4866))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3410 else (if jt.2.val < 2 then 3415 else 3416)) else (if jt.2.val < 4 then 3412 else (if jt.2.val < 5 then 3414 else 3413)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4098 else (if jt.2.val < 2 then 4121 else 4101)) else (if jt.2.val < 4 then 4119 else (if jt.2.val < 5 then 4120 else 4096))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3475 else (if jt.2.val < 2 then 3504 else 3478)) else (if jt.2.val < 4 then 3502 else (if jt.2.val < 5 then 3503 else 3439)))))

checked_coverage fastCoverage0803 pairing0803 template0803 witness0803

theorem coverage0803 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0803) (maskBits m))
    cores template0803 witness0803 := by
  rw [← coresFast_eq]
  exact fastCoverage0803

theorem coverageSize0803 : ∀ q : Pattern,
    (cores (witness0803 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0803 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0803
#print axioms coverageSize0803

noncomputable def pairing0804 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0804 : List (Fin 4935) := templateData0804

noncomputable def witness0804 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1707 else 648) else if t 2 = 1 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1705 else 1353) else (if t 3 = 0 then 837 else if t 3 = 1 then 1733 else 1359)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1703 else if t 3 = 1 then 1699 else 646) else if t 2 = 1 then (if t 3 = 0 then 1701 else if t 3 = 1 then 1697 else 1747) else (if t 3 = 0 then 833 else if t 3 = 1 then 1730 else 1750)) else (if t 2 = 0 then (if t 3 = 0 then 4537 else if t 3 = 1 then 4064 else 3946) else if t 2 = 1 then (if t 3 = 0 then 3350 else if t 3 = 1 then 3348 else 2546) else (if t 3 = 0 then 3514 else if t 3 = 1 then 2938 else 2561))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1706 else 647) else if t 2 = 1 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1704 else 1352) else (if t 3 = 0 then 836 else if t 3 = 1 then 1732 else 1358)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1702 else if t 3 = 1 then 1698 else 645) else if t 2 = 1 then (if t 3 = 0 then 1700 else if t 3 = 1 then 1696 else 1746) else (if t 3 = 0 then 832 else if t 3 = 1 then 1729 else 1749)) else (if t 2 = 0 then (if t 3 = 0 then 1720 else if t 3 = 1 then 1718 else 651) else if t 2 = 1 then (if t 3 = 0 then 1719 else if t 3 = 1 then 1716 else 1748) else (if t 3 = 0 then 839 else if t 3 = 1 then 1734 else 1751))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 779 else 3523) else if t 2 = 1 then (if t 3 = 0 then 395 else if t 3 = 1 then 1449 else 2118) else (if t 3 = 0 then 3952 else if t 3 = 1 then 1452 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1497 else if t 3 = 1 then 777 else 1142) else if t 2 = 1 then (if t 3 = 0 then 393 else if t 3 = 1 then 1752 else 1758) else (if t 3 = 0 then 405 else if t 3 = 1 then 1755 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 1499 else if t 3 = 1 then 781 else 1143) else if t 2 = 1 then (if t 3 = 0 then 397 else if t 3 = 1 then 1754 else 1759) else (if t 3 = 0 then 407 else if t 3 = 1 then 1757 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4863 else (if jt.2.val < 2 then 4870 else 4868)) else (if jt.2.val < 4 then 4869 else (if jt.2.val < 5 then 4871 else 4866))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4494 else (if jt.2.val < 2 then 4536 else 4497)) else (if jt.2.val < 4 then 4534 else (if jt.2.val < 5 then 4535 else 4469)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1694 else (if jt.2.val < 2 then 1728 else 1731)) else (if jt.2.val < 4 then 1725 else (if jt.2.val < 5 then 1727 else 1726))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1693 else (if jt.2.val < 2 then 1744 else 1745)) else (if jt.2.val < 4 then 1741 else (if jt.2.val < 5 then 1743 else 1742)))))

checked_coverage fastCoverage0804 pairing0804 template0804 witness0804

theorem coverage0804 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0804) (maskBits m))
    cores template0804 witness0804 := by
  rw [← coresFast_eq]
  exact fastCoverage0804

theorem coverageSize0804 : ∀ q : Pattern,
    (cores (witness0804 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0804 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0804
#print axioms coverageSize0804

noncomputable def pairing0805 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0805 : List (Fin 4935) := templateData0805

noncomputable def witness0805 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 224 else 1786) else if t 2 = 1 then (if t 3 = 0 then 230 else if t 3 = 1 then 222 else 254) else (if t 3 = 0 then 1471 else if t 3 = 1 then 916 else 922)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 228 else if t 3 = 1 then 220 else 1459) else if t 2 = 1 then (if t 3 = 0 then 226 else if t 3 = 1 then 218 else 251) else (if t 3 = 0 then 269 else if t 3 = 1 then 264 else 277)) else (if t 2 = 0 then (if t 3 = 0 then 3925 else if t 3 = 1 then 3923 else 4541) else if t 2 = 1 then (if t 3 = 0 then 2750 else if t 3 = 1 then 2747 else 3209) else (if t 3 = 0 then 2757 else if t 3 = 1 then 2756 else 3499))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 223 else 1785) else if t 2 = 1 then (if t 3 = 0 then 229 else if t 3 = 1 then 221 else 253) else (if t 3 = 0 then 1470 else if t 3 = 1 then 915 else 921)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 227 else if t 3 = 1 then 219 else 1458) else if t 2 = 1 then (if t 3 = 0 then 225 else if t 3 = 1 then 217 else 250) else (if t 3 = 0 then 268 else if t 3 = 1 then 263 else 276)) else (if t 2 = 0 then (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 1463) else if t 2 = 1 then (if t 3 = 0 then 242 else if t 3 = 1 then 237 else 259) else (if t 3 = 0 then 274 else if t 3 = 1 then 272 else 280))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 306 else 2782) else if t 2 = 1 then (if t 3 = 0 then 2139 else if t 3 = 1 then 300 else 302) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1476 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 930 else if t 3 = 1 then 294 else 1473) else if t 2 = 1 then (if t 3 = 0 then 924 else if t 3 = 1 then 282 else 284) else (if t 3 = 0 then 1788 else if t 3 = 1 then 286 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 931 else if t 3 = 1 then 295 else 1474) else if t 2 = 1 then (if t 3 = 0 then 925 else if t 3 = 1 then 283 else 285) else (if t 3 = 0 then 1789 else if t 3 = 1 then 287 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4881 else (if jt.2.val < 2 then 4897 else 4886)) else (if jt.2.val < 4 then 4896 else (if jt.2.val < 5 then 4898 else 4884))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4103 else (if jt.2.val < 2 then 4127 else 4106)) else (if jt.2.val < 4 then 4125 else (if jt.2.val < 5 then 4126 else 4095)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1457 else (if jt.2.val < 2 then 1468 else 1469)) else (if jt.2.val < 4 then 1465 else (if jt.2.val < 5 then 1467 else 1466))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1742 else (if jt.2.val < 2 then 1784 else 1745)) else (if jt.2.val < 4 then 1782 else (if jt.2.val < 5 then 1783 else 1693)))))

checked_coverage fastCoverage0805 pairing0805 template0805 witness0805

theorem coverage0805 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0805) (maskBits m))
    cores template0805 witness0805 := by
  rw [← coresFast_eq]
  exact fastCoverage0805

theorem coverageSize0805 : ∀ q : Pattern,
    (cores (witness0805 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0805 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0805
#print axioms coverageSize0805

noncomputable def pairing0806 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0806 : List (Fin 4935) := templateData0806

noncomputable def witness0806 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1031 else 1519) else if t 2 = 1 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1027 else 467) else (if t 3 = 0 then 1816 else if t 3 = 1 then 1051 else 477)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1025 else if t 3 = 1 then 1023 else 659) else if t 2 = 1 then (if t 3 = 0 then 1021 else if t 3 = 1 then 1019 else 1069) else (if t 3 = 0 then 1813 else if t 3 = 1 then 1046 else 1075)) else (if t 2 = 0 then (if t 3 = 0 then 3520 else if t 3 = 1 then 2972 else 2776) else if t 2 = 1 then (if t 3 = 0 then 3338 else if t 3 = 1 then 2970 else 2979) else (if t 3 = 0 then 4532 else if t 3 = 1 then 4046 else 3905))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1030 else 1518) else if t 2 = 1 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1026 else 466) else (if t 3 = 0 then 1815 else if t 3 = 1 then 1050 else 476)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1024 else if t 3 = 1 then 1022 else 658) else if t 2 = 1 then (if t 3 = 0 then 1020 else if t 3 = 1 then 1018 else 1068) else (if t 3 = 0 then 1812 else if t 3 = 1 then 1045 else 1074)) else (if t 2 = 0 then (if t 3 = 0 then 1040 else if t 3 = 1 then 1039 else 664) else if t 2 = 1 then (if t 3 = 0 then 1038 else if t 3 = 1 then 1037 else 1072) else (if t 3 = 0 then 1817 else if t 3 = 1 then 1054 else 1076))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 1548 else 4542) else if t 2 = 1 then (if t 3 = 0 then 596 else if t 3 = 1 then 594 else 2148) else (if t 3 = 0 then 2763 else if t 3 = 1 then 600 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 785 else if t 3 = 1 then 783 else 1824) else if t 2 = 1 then (if t 3 = 0 then 1079 else if t 3 = 1 then 1077 else 1086) else (if t 3 = 0 then 1689 else if t 3 = 1 then 1083 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 788 else if t 3 = 1 then 787 else 1825) else if t 2 = 1 then (if t 3 = 0 then 1082 else if t 3 = 1 then 1081 else 1087) else (if t 3 = 0 then 1691 else if t 3 = 1 then 1085 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4905 else (if jt.2.val < 2 then 4912 else 4910)) else (if jt.2.val < 4 then 4911 else (if jt.2.val < 5 then 4913 else 4908))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3468 else (if jt.2.val < 2 then 3519 else 3471)) else (if jt.2.val < 4 then 3517 else (if jt.2.val < 5 then 3518 else 3440)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1726 else (if jt.2.val < 2 then 1814 else 1731)) else (if jt.2.val < 4 then 1809 else (if jt.2.val < 5 then 1810 else 1694))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1811 else (if jt.2.val < 2 then 1822 else 1823)) else (if jt.2.val < 4 then 1819 else (if jt.2.val < 5 then 1821 else 1820)))))

checked_coverage fastCoverage0806 pairing0806 template0806 witness0806

theorem coverage0806 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0806) (maskBits m))
    cores template0806 witness0806 := by
  rw [← coresFast_eq]
  exact fastCoverage0806

theorem coverageSize0806 : ∀ q : Pattern,
    (cores (witness0806 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0806 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0806
#print axioms coverageSize0806

noncomputable def pairing0807 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0807 : List (Fin 4935) := templateData0807

noncomputable def witness0807 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1568 else 1134) else if t 2 = 1 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1566 else 464) else (if t 3 = 0 then 67 else if t 3 = 1 then 62 else 1849)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1564 else 656) else if t 2 = 1 then (if t 3 = 0 then 1570 else if t 3 = 1 then 1562 else 1593) else (if t 3 = 0 then 855 else if t 3 = 1 then 1589 else 1597)) else (if t 2 = 0 then (if t 3 = 0 then 2633 else if t 3 = 1 then 2630 else 3524) else if t 2 = 1 then (if t 3 = 0 then 2855 else if t 3 = 1 then 3219 else 3225) else (if t 3 = 0 then 3954 else if t 3 = 1 then 3953 else 4525))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1567 else 1133) else if t 2 = 1 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1565 else 463) else (if t 3 = 0 then 66 else if t 3 = 1 then 61 else 1848)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1563 else 655) else if t 2 = 1 then (if t 3 = 0 then 1569 else if t 3 = 1 then 1561 else 1592) else (if t 3 = 0 then 854 else if t 3 = 1 then 1588 else 1596)) else (if t 2 = 0 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1581 else 663) else if t 2 = 1 then (if t 3 = 0 then 1584 else if t 3 = 1 then 1580 else 1595) else (if t 3 = 0 then 857 else if t 3 = 1 then 1591 else 1600))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1620 else 3960) else if t 2 = 1 then (if t 3 = 0 then 2172 else if t 3 = 1 then 1617 else 494) else (if t 3 = 0 then 3525 else if t 3 = 1 then 92 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1854 else if t 3 = 1 then 1614 else 686) else if t 2 = 1 then (if t 3 = 0 then 1851 else if t 3 = 1 then 1602 else 1606) else (if t 3 = 0 then 876 else if t 3 = 1 then 1604 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 1855 else if t 3 = 1 then 1615 else 687) else if t 2 = 1 then (if t 3 = 0 then 1852 else if t 3 = 1 then 1603 else 1607) else (if t 3 = 0 then 877 else if t 3 = 1 then 1605 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4926 else (if jt.2.val < 2 then 4933 else 4931)) else (if jt.2.val < 4 then 4932 else (if jt.2.val < 5 then 4934 else 4929))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3413 else (if jt.2.val < 2 then 3434 else 3416)) else (if jt.2.val < 4 then 3432 else (if jt.2.val < 5 then 3433 else 3410)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1466 else (if jt.2.val < 2 then 1590 else 1469)) else (if jt.2.val < 4 then 1559 else (if jt.2.val < 5 then 1560 else 1457))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1820 else (if jt.2.val < 2 then 1847 else 1823)) else (if jt.2.val < 4 then 1842 else (if jt.2.val < 5 then 1843 else 1811)))))

checked_coverage fastCoverage0807 pairing0807 template0807 witness0807

theorem coverage0807 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0807) (maskBits m))
    cores template0807 witness0807 := by
  rw [← coresFast_eq]
  exact fastCoverage0807

theorem coverageSize0807 : ∀ q : Pattern,
    (cores (witness0807 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0807 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0807
#print axioms coverageSize0807

noncomputable def pairing0808 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0808 : List (Fin 4935) := templateData0808

noncomputable def witness0808 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 4213) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3531) else (if t 3 = 0 then 3236 else if t 3 = 1 then 3235 else 2691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 2199) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 2198) else (if t 3 = 0 then 1651 else if t 3 = 1 then 1649 else 1661)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1881 else 980) else if t 2 = 1 then (if t 3 = 0 then 1882 else if t 3 = 1 then 1880 else 1892) else (if t 3 = 0 then 555 else if t 3 = 1 then 1670 else 1676))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 2073) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 2072) else (if t 3 = 0 then 1332 else if t 3 = 1 then 1330 else 1344)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3465) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4492) else (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4506)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3270 else 3280) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4499) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4507 else 4513))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1443 else 593) else if t 2 = 1 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1442 else 1448) else (if t 3 = 0 then 1013 else if t 3 = 1 then 1778 else 1781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3161 else 3164) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4515) else (if t 3 = 0 then 4038 else if t 3 = 1 then 4518 else 4519)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 3166 else 3168) else if t 2 = 1 then (if t 3 = 0 then 3918 else if t 3 = 1 then 4516 else 4517) else (if t 3 = 0 then 4192 else if t 3 = 1 then 4520 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4926 else (if jt.2.val < 2 then 4928 else 4931)) else (if jt.2.val < 4 then 4927 else (if jt.2.val < 5 then 4930 else 4929))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4469 else (if jt.2.val < 2 then 4496 else 4497)) else (if jt.2.val < 4 then 4493 else (if jt.2.val < 5 then 4495 else 4494)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4468 else (if jt.2.val < 2 then 4503 else 4504)) else (if jt.2.val < 4 then 4500 else (if jt.2.val < 5 then 4502 else 4501))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4746 else (if jt.2.val < 2 then 4750 else 4751)) else (if jt.2.val < 4 then 4747 else (if jt.2.val < 5 then 4749 else 4748)))))

checked_coverage fastCoverage0808 pairing0808 template0808 witness0808

theorem coverage0808 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0808) (maskBits m))
    cores template0808 witness0808 := by
  rw [← coresFast_eq]
  exact fastCoverage0808

theorem coverageSize0808 : ∀ q : Pattern,
    (cores (witness0808 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0808 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0808
#print axioms coverageSize0808

noncomputable def pairing0809 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0809 : List (Fin 4935) := templateData0809

noncomputable def witness0809 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 4546) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 3530) else (if t 3 = 0 then 2789 else if t 3 = 1 then 2788 else 3192)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 2197) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 2196) else (if t 3 = 0 then 727 else if t 3 = 1 then 725 else 742)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1173 else 1802) else if t 2 = 1 then (if t 3 = 0 then 1174 else if t 3 = 1 then 1172 else 1189) else (if t 3 = 0 then 1544 else if t 3 = 1 then 757 else 764))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 2071) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 2070) else (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 53)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 3464) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4155) else (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4171)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2842) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4164) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4177 else 4178))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 189 else 1547) else if t 2 = 1 then (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 196) else (if t 3 = 0 then 1808 else if t 3 = 1 then 901 else 905)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2574) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4180) else (if t 3 = 0 then 4039 else if t 3 = 1 then 4183 else 4184)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2578 else 2580) else if t 2 = 1 then (if t 3 = 0 then 3919 else if t 3 = 1 then 4181 else 4182) else (if t 3 = 0 then 4526 else if t 3 = 1 then 4185 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4917 else (if jt.2.val < 2 then 4919 else 4922)) else (if jt.2.val < 4 then 4918 else (if jt.2.val < 5 then 4921 else 4920))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4133 else (if jt.2.val < 2 then 4161 else 4162)) else (if jt.2.val < 4 then 4158 else (if jt.2.val < 5 then 4160 else 4159)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4132 else (if jt.2.val < 2 then 4168 else 4169)) else (if jt.2.val < 4 then 4165 else (if jt.2.val < 5 then 4167 else 4166))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4748 else (if jt.2.val < 2 then 4754 else 4751)) else (if jt.2.val < 4 then 4752 else (if jt.2.val < 5 then 4753 else 4746)))))

checked_coverage fastCoverage0809 pairing0809 template0809 witness0809

theorem coverage0809 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0809) (maskBits m))
    cores template0809 witness0809 := by
  rw [← coresFast_eq]
  exact fastCoverage0809

theorem coverageSize0809 : ∀ q : Pattern,
    (cores (witness0809 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0809 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0809
#print axioms coverageSize0809

noncomputable def pairing0810 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0810 : List (Fin 4935) := templateData0810

noncomputable def witness0810 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3062 else 2732) else if t 2 = 1 then (if t 3 = 0 then 3058 else if t 3 = 1 then 3054 else 2730) else (if t 3 = 0 then 4530 else if t 3 = 1 then 3963 else 4205)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3060 else 344) else if t 2 = 1 then (if t 3 = 0 then 3056 else if t 3 = 1 then 3052 else 340) else (if t 3 = 0 then 1648 else if t 3 = 1 then 1646 else 357)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 144 else 1496) else if t 2 = 1 then (if t 3 = 0 then 141 else if t 3 = 1 then 140 else 892) else (if t 3 = 0 then 1835 else if t 3 = 1 then 157 else 896))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3061 else 442) else if t 2 = 1 then (if t 3 = 0 then 3057 else if t 3 = 1 then 3053 else 438) else (if t 3 = 0 then 1329 else if t 3 = 1 then 1327 else 454)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3059 else 3082) else if t 2 = 1 then (if t 3 = 0 then 3055 else if t 3 = 1 then 3051 else 3080) else (if t 3 = 0 then 3073 else if t 3 = 1 then 3071 else 3083)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 3091 else 3095) else if t 2 = 1 then (if t 3 = 0 then 2622 else if t 3 = 1 then 3089 else 3094) else (if t 3 = 0 then 2626 else if t 3 = 1 then 3092 else 3096))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1219 else 1838) else if t 2 = 1 then (if t 3 = 0 then 1213 else if t 3 = 1 then 1207 else 499) else (if t 3 = 0 then 1375 else if t 3 = 1 then 1209 else 501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 3313 else 3315) else if t 2 = 1 then (if t 3 = 0 then 2956 else if t 3 = 1 then 3098 else 3100) else (if t 3 = 0 then 2957 else if t 3 = 1 then 3099 else 3101)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 3500 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2652 else if t 3 = 1 then 3102 else 3104) else (if t 3 = 0 then 2653 else if t 3 = 1 then 3103 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4851 else (if jt.2.val < 2 then 4853 else 4856)) else (if jt.2.val < 4 then 4852 else (if jt.2.val < 5 then 4855 else 4854))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3384 else (if jt.2.val < 2 then 3394 else 3395)) else (if jt.2.val < 4 then 3391 else (if jt.2.val < 5 then 3393 else 3392)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4501 else (if jt.2.val < 2 then 4529 else 4504)) else (if jt.2.val < 4 then 4527 else (if jt.2.val < 5 then 4528 else 4468))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3385 else (if jt.2.val < 2 then 3389 else 3390)) else (if jt.2.val < 4 then 3386 else (if jt.2.val < 5 then 3388 else 3387)))))

checked_coverage fastCoverage0810 pairing0810 template0810 witness0810

theorem coverage0810 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0810) (maskBits m))
    cores template0810 witness0810 := by
  rw [← coresFast_eq]
  exact fastCoverage0810

theorem coverageSize0810 : ∀ q : Pattern,
    (cores (witness0810 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0810 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0810
#print axioms coverageSize0810

noncomputable def pairing0811 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0811 : List (Fin 4935) := templateData0811

noncomputable def witness0811 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2450 else 3205) else if t 2 = 1 then (if t 3 = 0 then 2446 else if t 3 = 1 then 2442 else 3203) else (if t 3 = 0 then 4196 else if t 3 = 1 then 3939 else 4539)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2448 else 343) else if t 2 = 1 then (if t 3 = 0 then 2444 else if t 3 = 1 then 2440 else 339) else (if t 3 = 0 then 724 else if t 3 = 1 then 722 else 1489)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1416 else 374) else if t 2 = 1 then (if t 3 = 0 then 1413 else if t 3 = 1 then 1412 else 372) else (if t 3 = 0 then 1109 else if t 3 = 1 then 756 else 1775))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2449 else 441) else if t 2 = 1 then (if t 3 = 0 then 2445 else if t 3 = 1 then 2441 else 437) else (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 1511)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2447 else 2471) else if t 2 = 1 then (if t 3 = 0 then 2443 else if t 3 = 1 then 2439 else 2468) else (if t 3 = 0 then 2461 else if t 3 = 1 then 2459 else 2473)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2484 else 2489) else if t 2 = 1 then (if t 3 = 0 then 2897 else if t 3 = 1 then 2481 else 2488) else (if t 3 = 0 then 2899 else if t 3 = 1 then 2486 else 2490))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1915 else 1118) else if t 2 = 1 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1906 else 493) else (if t 3 = 0 then 103 else if t 3 = 1 then 91 else 1522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2883 else 2886) else if t 2 = 1 then (if t 3 = 0 then 2502 else if t 3 = 1 then 2492 else 2494) else (if t 3 = 0 then 2503 else if t 3 = 1 then 2493 else 2495)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3506 else 4197) else if t 2 = 1 then (if t 3 = 0 then 3183 else if t 3 = 1 then 2496 else 2498) else (if t 3 = 0 then 3184 else if t 3 = 1 then 2497 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4863 else (if jt.2.val < 2 then 4865 else 4868)) else (if jt.2.val < 4 then 4864 else (if jt.2.val < 5 then 4867 else 4866))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3410 else (if jt.2.val < 2 then 3415 else 3416)) else (if jt.2.val < 4 then 3412 else (if jt.2.val < 5 then 3414 else 3413)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4166 else (if jt.2.val < 2 then 4195 else 4169)) else (if jt.2.val < 4 then 4193 else (if jt.2.val < 5 then 4194 else 4132))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3387 else (if jt.2.val < 2 then 3411 else 3390)) else (if jt.2.val < 4 then 3408 else (if jt.2.val < 5 then 3409 else 3385)))))

checked_coverage fastCoverage0811 pairing0811 template0811 witness0811

theorem coverage0811 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0811) (maskBits m))
    cores template0811 witness0811 := by
  rw [← coresFast_eq]
  exact fastCoverage0811

theorem coverageSize0811 : ∀ q : Pattern,
    (cores (witness0811 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0811 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0811
#print axioms coverageSize0811

noncomputable def pairing0812 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0812 : List (Fin 4935) := templateData0812

noncomputable def witness0812 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1707 else 1053) else if t 2 = 1 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1705 else 1733) else (if t 3 = 0 then 258 else if t 3 = 1 then 1353 else 1359)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1703 else if t 3 = 1 then 1699 else 1049) else if t 2 = 1 then (if t 3 = 0 then 1701 else if t 3 = 1 then 1697 else 1730) else (if t 3 = 0 then 256 else if t 3 = 1 then 1747 else 1750)) else (if t 2 = 0 then (if t 3 = 0 then 4537 else if t 3 = 1 then 4064 else 4198) else if t 2 = 1 then (if t 3 = 0 then 3350 else if t 3 = 1 then 3348 else 2938) else (if t 3 = 0 then 3210 else if t 3 = 1 then 2546 else 2561))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1706 else 1052) else if t 2 = 1 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1704 else 1732) else (if t 3 = 0 then 257 else if t 3 = 1 then 1352 else 1358)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1702 else if t 3 = 1 then 1698 else 1048) else if t 2 = 1 then (if t 3 = 0 then 1700 else if t 3 = 1 then 1696 else 1729) else (if t 3 = 0 then 255 else if t 3 = 1 then 1746 else 1749)) else (if t 2 = 0 then (if t 3 = 0 then 1720 else if t 3 = 1 then 1718 else 1055) else if t 2 = 1 then (if t 3 = 0 then 1719 else if t 3 = 1 then 1716 else 1734) else (if t 3 = 0 then 261 else if t 3 = 1 then 1748 else 1751))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 779 else 3216) else if t 2 = 1 then (if t 3 = 0 then 395 else if t 3 = 1 then 1449 else 1452) else (if t 3 = 0 then 4206 else if t 3 = 1 then 2118 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1497 else if t 3 = 1 then 777 else 789) else if t 2 = 1 then (if t 3 = 0 then 393 else if t 3 = 1 then 1752 else 1755) else (if t 3 = 0 then 926 else if t 3 = 1 then 1758 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 1499 else if t 3 = 1 then 781 else 791) else if t 2 = 1 then (if t 3 = 0 then 397 else if t 3 = 1 then 1754 else 1757) else (if t 3 = 0 then 927 else if t 3 = 1 then 1759 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4863 else (if jt.2.val < 2 then 4870 else 4868)) else (if jt.2.val < 4 then 4869 else (if jt.2.val < 5 then 4871 else 4866))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4494 else (if jt.2.val < 2 then 4536 else 4497)) else (if jt.2.val < 4 then 4534 else (if jt.2.val < 5 then 4535 else 4469)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2268 else (if jt.2.val < 2 then 2278 else 2279)) else (if jt.2.val < 4 then 2275 else (if jt.2.val < 5 then 2277 else 2276))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2269 else (if jt.2.val < 2 then 2273 else 2274)) else (if jt.2.val < 4 then 2270 else (if jt.2.val < 5 then 2272 else 2271)))))

checked_coverage fastCoverage0812 pairing0812 template0812 witness0812

theorem coverage0812 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0812) (maskBits m))
    cores template0812 witness0812 := by
  rw [← coresFast_eq]
  exact fastCoverage0812

theorem coverageSize0812 : ∀ q : Pattern,
    (cores (witness0812 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0812 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0812
#print axioms coverageSize0812

noncomputable def pairing0813 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0813 : List (Fin 4935) := templateData0813

noncomputable def witness0813 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 807 else 1816) else if t 2 = 1 then (if t 3 = 0 then 809 else if t 3 = 1 then 805 else 835) else (if t 3 = 0 then 1471 else if t 3 = 1 then 65 else 75)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 803 else if t 3 = 1 then 799 else 1813) else if t 2 = 1 then (if t 3 = 0 then 801 else if t 3 = 1 then 797 else 830) else (if t 3 = 0 then 269 else if t 3 = 1 then 853 else 859)) else (if t 2 = 0 then (if t 3 = 0 then 4203 else if t 3 = 1 then 4054 else 4532) else if t 2 = 1 then (if t 3 = 0 then 2995 else if t 3 = 1 then 2993 else 3329) else (if t 3 = 0 then 2757 else if t 3 = 1 then 3002 else 3152))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 806 else 1815) else if t 2 = 1 then (if t 3 = 0 then 808 else if t 3 = 1 then 804 else 834) else (if t 3 = 0 then 1470 else if t 3 = 1 then 64 else 74)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 802 else if t 3 = 1 then 798 else 1812) else if t 2 = 1 then (if t 3 = 0 then 800 else if t 3 = 1 then 796 else 829) else (if t 3 = 0 then 268 else if t 3 = 1 then 852 else 858)) else (if t 2 = 0 then (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 1817) else if t 2 = 1 then (if t 3 = 0 then 819 else if t 3 = 1 then 816 else 838) else (if t 3 = 0 then 274 else if t 3 = 1 then 856 else 860))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 200 else 2763) else if t 2 = 1 then (if t 3 = 0 then 1500 else if t 3 = 1 then 198 else 204) else (if t 3 = 0 then 4540 else if t 3 = 1 then 2127 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 401 else if t 3 = 1 then 863 else 1689) else if t 2 = 1 then (if t 3 = 0 then 399 else if t 3 = 1 then 861 else 867) else (if t 3 = 0 then 1788 else if t 3 = 1 then 870 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 404 else if t 3 = 1 then 866 else 1691) else if t 2 = 1 then (if t 3 = 0 then 403 else if t 3 = 1 then 865 else 869) else (if t 3 = 0 then 1789 else if t 3 = 1 then 871 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4851 else (if jt.2.val < 2 then 4876 else 4856)) else (if jt.2.val < 4 then 4875 else (if jt.2.val < 5 then 4877 else 4854))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4159 else (if jt.2.val < 2 then 4202 else 4162)) else (if jt.2.val < 4 then 4200 else (if jt.2.val < 5 then 4201 else 4133)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2288 else (if jt.2.val < 2 then 2293 else 2294)) else (if jt.2.val < 4 then 2290 else (if jt.2.val < 5 then 2292 else 2291))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2271 else (if jt.2.val < 2 then 2289 else 2274)) else (if jt.2.val < 4 then 2286 else (if jt.2.val < 5 then 2287 else 2269)))))

checked_coverage fastCoverage0813 pairing0813 template0813 witness0813

theorem coverage0813 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0813) (maskBits m))
    cores template0813 witness0813 := by
  rw [← coresFast_eq]
  exact fastCoverage0813

theorem coverageSize0813 : ∀ q : Pattern,
    (cores (witness0813 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0813 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0813
#print axioms coverageSize0813

noncomputable def pairing0814 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0814 : List (Fin 4935) := templateData0814

noncomputable def witness0814 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 626 else 1519) else if t 2 = 1 then (if t 3 = 0 then 620 else if t 3 = 1 then 618 else 1132) else (if t 3 = 0 then 1786 else if t 3 = 1 then 644 else 1138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 624 else if t 3 = 1 then 622 else 659) else if t 2 = 1 then (if t 3 = 0 then 616 else if t 3 = 1 then 614 else 654) else (if t 3 = 0 then 1459 else if t 3 = 1 then 641 else 667)) else (if t 2 = 0 then (if t 3 = 0 then 3174 else if t 3 = 1 then 2769 else 2776) else if t 2 = 1 then (if t 3 = 0 then 3172 else if t 3 = 1 then 2766 else 2775) else (if t 3 = 0 then 4541 else if t 3 = 1 then 3945 else 4190))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 625 else 1518) else if t 2 = 1 then (if t 3 = 0 then 619 else if t 3 = 1 then 617 else 1131) else (if t 3 = 0 then 1785 else if t 3 = 1 then 643 else 1137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 623 else if t 3 = 1 then 621 else 658) else if t 2 = 1 then (if t 3 = 0 then 615 else if t 3 = 1 then 613 else 653) else (if t 3 = 0 then 1458 else if t 3 = 1 then 640 else 666)) else (if t 2 = 0 then (if t 3 = 0 then 637 else if t 3 = 1 then 636 else 664) else if t 2 = 1 then (if t 3 = 0 then 633 else if t 3 = 1 then 632 else 662) else (if t 3 = 0 then 1463 else if t 3 = 1 then 649 else 670))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 2160 else 4542) else if t 2 = 1 then (if t 3 = 0 then 696 else if t 3 = 1 then 690 else 1524) else (if t 3 = 0 then 2782 else if t 3 = 1 then 692 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1146 else if t 3 = 1 then 1140 else 1824) else if t 2 = 1 then (if t 3 = 0 then 684 else if t 3 = 1 then 672 else 676) else (if t 3 = 0 then 1473 else if t 3 = 1 then 674 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 1147 else if t 3 = 1 then 1141 else 1825) else if t 2 = 1 then (if t 3 = 0 then 685 else if t 3 = 1 then 673 else 677) else (if t 3 = 0 then 1474 else if t 3 = 1 then 675 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4917 else (if jt.2.val < 2 then 4924 else 4922)) else (if jt.2.val < 4 then 4923 else (if jt.2.val < 5 then 4925 else 4920))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3392 else (if jt.2.val < 2 then 3428 else 3395)) else (if jt.2.val < 4 then 3426 else (if jt.2.val < 5 then 3427 else 3384)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2276 else (if jt.2.val < 2 then 2303 else 2279)) else (if jt.2.val < 4 then 2301 else (if jt.2.val < 5 then 2302 else 2268))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2015 else (if jt.2.val < 2 then 2020 else 2021)) else (if jt.2.val < 4 then 2017 else (if jt.2.val < 5 then 2019 else 2018)))))

checked_coverage fastCoverage0814 pairing0814 template0814 witness0814

theorem coverage0814 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0814) (maskBits m))
    cores template0814 witness0814 := by
  rw [← coresFast_eq]
  exact fastCoverage0814

theorem coverageSize0814 : ∀ q : Pattern,
    (cores (witness0814 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0814 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0814
#print axioms coverageSize0814

noncomputable def pairing0815 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0815 : List (Fin 4935) := templateData0815

noncomputable def witness0815 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1574 else 469) else if t 2 = 1 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1566 else 464) else (if t 3 = 0 then 918 else if t 3 = 1 then 62 else 1849)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1570 else 1071) else if t 2 = 1 then (if t 3 = 0 then 1564 else if t 3 = 1 then 1562 else 1593) else (if t 3 = 0 then 266 else if t 3 = 1 then 1589 else 1597)) else (if t 2 = 0 then (if t 3 = 0 then 2633 else if t 3 = 1 then 2855 else 3226) else if t 2 = 1 then (if t 3 = 0 then 2630 else if t 3 = 1 then 3219 else 3225) else (if t 3 = 0 then 4207 else if t 3 = 1 then 3953 else 4525))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1573 else 468) else if t 2 = 1 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1565 else 463) else (if t 3 = 0 then 917 else if t 3 = 1 then 61 else 1848)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1569 else 1070) else if t 2 = 1 then (if t 3 = 0 then 1563 else if t 3 = 1 then 1561 else 1592) else (if t 3 = 0 then 265 else if t 3 = 1 then 1588 else 1596)) else (if t 2 = 0 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1584 else 1073) else if t 2 = 1 then (if t 3 = 0 then 1581 else if t 3 = 1 then 1580 else 1595) else (if t 3 = 0 then 273 else if t 3 = 1 then 1591 else 1600))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 2172 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1620 else if t 3 = 1 then 1617 else 494) else (if t 3 = 0 then 3229 else if t 3 = 1 then 92 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1854 else if t 3 = 1 then 1851 else 1092) else if t 2 = 1 then (if t 3 = 0 then 1614 else if t 3 = 1 then 1602 else 1606) else (if t 3 = 0 then 296 else if t 3 = 1 then 1604 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 1855 else if t 3 = 1 then 1852 else 1093) else if t 2 = 1 then (if t 3 = 0 then 1615 else if t 3 = 1 then 1603 else 1607) else (if t 3 = 0 then 297 else if t 3 = 1 then 1605 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4926 else (if jt.2.val < 2 then 4933 else 4931)) else (if jt.2.val < 4 then 4932 else (if jt.2.val < 5 then 4934 else 4929))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3413 else (if jt.2.val < 2 then 3434 else 3416)) else (if jt.2.val < 4 then 3432 else (if jt.2.val < 5 then 3433 else 3410)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2291 else (if jt.2.val < 2 then 2315 else 2294)) else (if jt.2.val < 4 then 2313 else (if jt.2.val < 5 then 2314 else 2288))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2018 else (if jt.2.val < 2 then 2036 else 2021)) else (if jt.2.val < 4 then 2033 else (if jt.2.val < 5 then 2034 else 2015)))))

checked_coverage fastCoverage0815 pairing0815 template0815 witness0815

theorem coverage0815 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0815) (maskBits m))
    cores template0815 witness0815 := by
  rw [← coresFast_eq]
  exact fastCoverage0815

theorem coverageSize0815 : ∀ q : Pattern,
    (cores (witness0815 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0815 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0815
#print axioms coverageSize0815

noncomputable def pairing0816 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0816 : List (Fin 4935) := templateData0816

noncomputable def witness0816 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 4056) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2996) else (if t 3 = 0 then 3532 else if t 3 = 1 then 3530 else 3330)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 1173) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 1172) else (if t 3 = 0 then 2200 else if t 3 = 1 then 2196 else 1189)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 726 else 758) else if t 2 = 1 then (if t 3 = 0 then 727 else if t 3 = 1 then 725 else 757) else (if t 3 = 0 then 743 else if t 3 = 1 then 742 else 764))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 822) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 821) else (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 840)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2829) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4163) else (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4164)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2487) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4177) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4171 else 4178))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 189 else 203) else if t 2 = 1 then (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 202) else (if t 3 = 0 then 197 else if t 3 = 1 then 196 else 206)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2578) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4181) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4180 else 4182)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2885 else 3507) else if t 2 = 1 then (if t 3 = 0 then 4039 else if t 3 = 1 then 4183 else 4185) else (if t 3 = 0 then 4040 else if t 3 = 1 then 4184 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4917 else (if jt.2.val < 2 then 4919 else 4922)) else (if jt.2.val < 4 then 4918 else (if jt.2.val < 5 then 4921 else 4920))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4260 else (if jt.2.val < 2 then 4270 else 4271)) else (if jt.2.val < 4 then 4267 else (if jt.2.val < 5 then 4269 else 4268)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4728 else (if jt.2.val < 2 then 4732 else 4733)) else (if jt.2.val < 4 then 4729 else (if jt.2.val < 5 then 4731 else 4730))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4278 else (if jt.2.val < 2 then 4282 else 4283)) else (if jt.2.val < 4 then 4279 else (if jt.2.val < 5 then 4281 else 4280)))))

checked_coverage fastCoverage0816 pairing0816 template0816 witness0816

theorem coverage0816 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0816) (maskBits m))
    cores template0816 witness0816 := by
  rw [← coresFast_eq]
  exact fastCoverage0816

theorem coverageSize0816 : ∀ q : Pattern,
    (cores (witness0816 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0816 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0816
#print axioms coverageSize0816

noncomputable def pairing0817 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0817 : List (Fin 4935) := templateData0817

noncomputable def witness0817 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 4203) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2995) else (if t 3 = 0 then 3352 else if t 3 = 1 then 3350 else 3514)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 1171) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 1170) else (if t 3 = 0 then 1882 else if t 3 = 1 then 1878 else 1188)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 538 else 569) else if t 2 = 1 then (if t 3 = 0 then 539 else if t 3 = 1 then 537 else 568) else (if t 3 = 0 then 555 else if t 3 = 1 then 554 else 575))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 820) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 819) else (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 839)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2828) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4000) else (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4003)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2635) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4017) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4016 else 4018))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 390 else 404) else if t 2 = 1 then (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 403) else (if t 3 = 0 then 398 else if t 3 = 1 then 397 else 407)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2723) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4021) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4020 else 4022)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2903 else 3322) else if t 2 = 1 then (if t 3 = 0 then 4191 else if t 3 = 1 then 4023 else 4025) else (if t 3 = 0 then 4192 else if t 3 = 1 then 4024 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4899 else (if jt.2.val < 2 then 4901 else 4904)) else (if jt.2.val < 4 then 4900 else (if jt.2.val < 5 then 4903 else 4902))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4233 else (if jt.2.val < 2 then 4243 else 4244)) else (if jt.2.val < 4 then 4240 else (if jt.2.val < 5 then 4242 else 4241)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4566 else (if jt.2.val < 2 then 4570 else 4571)) else (if jt.2.val < 4 then 4567 else (if jt.2.val < 5 then 4569 else 4568))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4280 else (if jt.2.val < 2 then 4286 else 4283)) else (if jt.2.val < 4 then 4284 else (if jt.2.val < 5 then 4285 else 4278)))))

checked_coverage fastCoverage0817 pairing0817 template0817 witness0817

theorem coverage0817 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0817) (maskBits m))
    cores template0817 witness0817 := by
  rw [← coresFast_eq]
  exact fastCoverage0817

theorem coverageSize0817 : ∀ q : Pattern,
    (cores (witness0817 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0817 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0817
#print axioms coverageSize0817

noncomputable def pairing0818 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0818 : List (Fin 4935) := templateData0818

noncomputable def witness0818 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3340) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2973) else (if t 3 = 0 then 4213 else if t 3 = 1 then 4211 else 4047)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 964) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 963) else (if t 3 = 0 then 2199 else if t 3 = 1 then 2195 else 979)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 343 else 374) else if t 2 = 1 then (if t 3 = 0 then 344 else if t 3 = 1 then 342 else 373) else (if t 3 = 0 then 359 else if t 3 = 1 then 358 else 380))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 1042) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 1041) else (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 1056)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2838) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3472) else (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3473)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2471 else 2489) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3479 else 3486) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3480 else 3487))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 585 else 599) else if t 2 = 1 then (if t 3 = 0 then 586 else if t 3 = 1 then 584 else 598) else (if t 3 = 0 then 593 else if t 3 = 1 then 592 else 602)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2572 else 2579) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3488 else 3490) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3489 else 3491)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2886 else 4197) else if t 2 = 1 then (if t 3 = 0 then 3315 else if t 3 = 1 then 3492 else 3494) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3493 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4881 else (if jt.2.val < 2 then 4883 else 4886)) else (if jt.2.val < 4 then 4882 else (if jt.2.val < 5 then 4885 else 4884))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3600 else (if jt.2.val < 2 then 3610 else 3611)) else (if jt.2.val < 4 then 3607 else (if jt.2.val < 5 then 3609 else 3608)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4730 else (if jt.2.val < 2 then 4736 else 4733)) else (if jt.2.val < 4 then 4734 else (if jt.2.val < 5 then 4735 else 4728))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3627 else (if jt.2.val < 2 then 3631 else 3632)) else (if jt.2.val < 4 then 3628 else (if jt.2.val < 5 then 3630 else 3629)))))

checked_coverage fastCoverage0818 pairing0818 template0818 witness0818

theorem coverage0818 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0818) (maskBits m))
    cores template0818 witness0818 := by
  rw [← coresFast_eq]
  exact fastCoverage0818

theorem coverageSize0818 : ∀ q : Pattern,
    (cores (witness0818 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0818 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0818
#print axioms coverageSize0818

noncomputable def pairing0819 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0819 : List (Fin 4935) := templateData0819

noncomputable def witness0819 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3520) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2972) else (if t 3 = 0 then 4066 else if t 3 = 1 then 4064 else 4198)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 962) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 961) else (if t 3 = 0 then 1881 else if t 3 = 1 then 1877 else 978)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 143 else 173) else if t 2 = 1 then (if t 3 = 0 then 144 else if t 3 = 1 then 142 else 172) else (if t 3 = 0 then 159 else if t 3 = 1 then 158 else 179))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 1040) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 1039) else (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 1055)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2837) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3276) else (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3279)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2623 else 2637) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3291 else 3293) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3292 else 3294))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 774 else 788) else if t 2 = 1 then (if t 3 = 0 then 775 else if t 3 = 1 then 773 else 787) else (if t 3 = 0 then 782 else if t 3 = 1 then 781 else 791)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2717 else 2724) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3295 else 3297) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3296 else 3298)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2904 else 4045) else if t 2 = 1 then (if t 3 = 0 then 3500 else if t 3 = 1 then 3299 else 3301) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3300 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4845 else (if jt.2.val < 2 then 4847 else 4850)) else (if jt.2.val < 4 then 4846 else (if jt.2.val < 5 then 4849 else 4848))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3555 else (if jt.2.val < 2 then 3565 else 3566)) else (if jt.2.val < 4 then 3562 else (if jt.2.val < 5 then 3564 else 3563)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4568 else (if jt.2.val < 2 then 4574 else 4571)) else (if jt.2.val < 4 then 4572 else (if jt.2.val < 5 then 4573 else 4566))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3629 else (if jt.2.val < 2 then 3635 else 3632)) else (if jt.2.val < 4 then 3633 else (if jt.2.val < 5 then 3634 else 3627)))))

checked_coverage fastCoverage0819 pairing0819 template0819 witness0819

theorem coverage0819 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0819) (maskBits m))
    cores template0819 witness0819 := by
  rw [← coresFast_eq]
  exact fastCoverage0819

theorem coverageSize0819 : ∀ q : Pattern,
    (cores (witness0819 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0819 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0819
#print axioms coverageSize0819

noncomputable def pairing0820 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0820 : List (Fin 4935) := templateData0820

noncomputable def witness0820 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 20 else 67) else if t 2 = 1 then (if t 3 = 0 then 22 else if t 3 = 1 then 18 else 65) else (if t 3 = 0 then 50 else if t 3 = 1 then 48 else 75)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 16 else if t 3 = 1 then 12 else 62) else if t 2 = 1 then (if t 3 = 0 then 14 else if t 3 = 1 then 10 else 60) else (if t 3 = 0 then 46 else if t 3 = 1 then 43 else 73)) else (if t 2 = 0 then (if t 3 = 0 then 4196 else if t 3 = 1 then 3939 else 4060) else if t 2 = 1 then (if t 3 = 0 then 2787 else if t 3 = 1 then 2785 else 2794) else (if t 3 = 0 then 3522 else if t 3 = 1 then 3191 else 3312))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 19 else 66) else if t 2 = 1 then (if t 3 = 0 then 21 else if t 3 = 1 then 17 else 64) else (if t 3 = 0 then 49 else if t 3 = 1 then 47 else 74)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 15 else if t 3 = 1 then 11 else 61) else if t 2 = 1 then (if t 3 = 0 then 13 else if t 3 = 1 then 9 else 59) else (if t 3 = 0 then 45 else if t 3 = 1 then 42 else 72)) else (if t 2 = 0 then (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 69) else if t 2 = 1 then (if t 3 = 0 then 32 else if t 3 = 1 then 29 else 68) else (if t 3 = 0 then 52 else if t 3 = 1 then 51 else 76))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 899 else 3525) else if t 2 = 1 then (if t 3 = 0 then 1806 else if t 3 = 1 then 897 else 2127) else (if t 3 = 0 then 4059 else if t 3 = 1 then 903 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 102 else if t 3 = 1 then 90 else 92) else if t 2 = 1 then (if t 3 = 0 then 96 else if t 3 = 1 then 78 else 82) else (if t 3 = 0 then 98 else if t 3 = 1 then 80 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 103 else if t 3 = 1 then 91 else 93) else if t 2 = 1 then (if t 3 = 0 then 97 else if t 3 = 1 then 79 else 83) else (if t 3 = 0 then 99 else if t 3 = 1 then 81 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4845 else (if jt.2.val < 2 then 4879 else 4850)) else (if jt.2.val < 4 then 4878 else (if jt.2.val < 5 then 4880 else 4848))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4268 else (if jt.2.val < 2 then 4277 else 4271)) else (if jt.2.val < 4 then 4275 else (if jt.2.val < 5 then 4276 else 4260)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 7 else (if jt.2.val < 2 then 41 else 44)) else (if jt.2.val < 4 then 38 else (if jt.2.val < 5 then 40 else 39))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 6 else (if jt.2.val < 2 then 58 else 63)) else (if jt.2.val < 4 then 55 else (if jt.2.val < 5 then 57 else 56)))))

checked_coverage fastCoverage0820 pairing0820 template0820 witness0820

theorem coverage0820 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0820) (maskBits m))
    cores template0820 witness0820 := by
  rw [← coresFast_eq]
  exact fastCoverage0820

theorem coverageSize0820 : ∀ q : Pattern,
    (cores (witness0820 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0820 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0820
#print axioms coverageSize0820

noncomputable def pairing0821 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0821 : List (Fin 4935) := templateData0821

noncomputable def witness0821 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 228 else 271) else if t 2 = 1 then (if t 3 = 0 then 230 else if t 3 = 1 then 226 else 269) else (if t 3 = 0 then 258 else if t 3 = 1 then 256 else 279)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 224 else if t 3 = 1 then 220 else 266) else if t 2 = 1 then (if t 3 = 0 then 222 else if t 3 = 1 then 218 else 264) else (if t 3 = 0 then 254 else if t 3 = 1 then 251 else 277)) else (if t 2 = 0 then (if t 3 = 0 then 4044 else if t 3 = 1 then 3923 else 4207) else if t 2 = 1 then (if t 3 = 0 then 2749 else if t 3 = 1 then 2747 else 2756) else (if t 3 = 0 then 3342 else if t 3 = 1 then 3209 else 3499))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 227 else 270) else if t 2 = 1 then (if t 3 = 0 then 229 else if t 3 = 1 then 225 else 268) else (if t 3 = 0 then 257 else if t 3 = 1 then 255 else 278)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 223 else if t 3 = 1 then 219 else 265) else if t 2 = 1 then (if t 3 = 0 then 221 else if t 3 = 1 then 217 else 263) else (if t 3 = 0 then 253 else if t 3 = 1 then 250 else 276)) else (if t 2 = 0 then (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 273) else if t 2 = 1 then (if t 3 = 0 then 240 else if t 3 = 1 then 237 else 272) else (if t 3 = 0 then 260 else if t 3 = 1 then 259 else 280))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 930 else 3345) else if t 2 = 1 then (if t 3 = 0 then 2139 else if t 3 = 1 then 924 else 1788) else (if t 3 = 0 then 4206 else if t 3 = 1 then 926 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 306 else if t 3 = 1 then 294 else 296) else if t 2 = 1 then (if t 3 = 0 then 300 else if t 3 = 1 then 282 else 286) else (if t 3 = 0 then 302 else if t 3 = 1 then 284 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 307 else if t 3 = 1 then 295 else 297) else if t 2 = 1 then (if t 3 = 0 then 301 else if t 3 = 1 then 283 else 287) else (if t 3 = 0 then 303 else if t 3 = 1 then 285 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4881 else (if jt.2.val < 2 then 4897 else 4886)) else (if jt.2.val < 4 then 4896 else (if jt.2.val < 5 then 4898 else 4884))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4241 else (if jt.2.val < 2 then 4256 else 4244)) else (if jt.2.val < 4 then 4254 else (if jt.2.val < 5 then 4255 else 4233)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 215 else (if jt.2.val < 2 then 249 else 252)) else (if jt.2.val < 4 then 246 else (if jt.2.val < 5 then 248 else 247))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 56 else (if jt.2.val < 2 then 267 else 63)) else (if jt.2.val < 4 then 213 else (if jt.2.val < 5 then 214 else 6)))))

checked_coverage fastCoverage0821 pairing0821 template0821 witness0821

theorem coverage0821 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0821) (maskBits m))
    cores template0821 witness0821 := by
  rw [← coresFast_eq]
  exact fastCoverage0821

theorem coverageSize0821 : ∀ q : Pattern,
    (cores (witness0821 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0821 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0821
#print axioms coverageSize0821

noncomputable def pairing0822 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0822 : List (Fin 4935) := templateData0822

noncomputable def witness0822 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 428 else 469) else if t 2 = 1 then (if t 3 = 0 then 430 else if t 3 = 1 then 426 else 467) else (if t 3 = 0 then 452 else if t 3 = 1 then 450 else 477)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 424 else if t 3 = 1 then 420 else 464) else if t 2 = 1 then (if t 3 = 0 then 422 else if t 3 = 1 then 418 else 462) else (if t 3 = 0 then 448 else if t 3 = 1 then 445 else 475)) else (if t 2 = 0 then (if t 3 = 0 then 3505 else if t 3 = 1 then 3203 else 3344) else if t 2 = 1 then (if t 3 = 0 then 2730 else if t 3 = 1 then 2728 else 2737) else (if t 3 = 0 then 4205 else if t 3 = 1 then 3929 else 4036))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 427 else 468) else if t 2 = 1 then (if t 3 = 0 then 429 else if t 3 = 1 then 425 else 466) else (if t 3 = 0 then 451 else if t 3 = 1 then 449 else 476)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 423 else if t 3 = 1 then 419 else 463) else if t 2 = 1 then (if t 3 = 0 then 421 else if t 3 = 1 then 417 else 461) else (if t 3 = 0 then 447 else if t 3 = 1 then 444 else 474)) else (if t 2 = 0 then (if t 3 = 0 then 439 else if t 3 = 1 then 437 else 471) else if t 2 = 1 then (if t 3 = 0 then 438 else if t 3 = 1 then 436 else 470) else (if t 3 = 0 then 454 else if t 3 = 1 then 453 else 478))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 1115 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1836 else if t 3 = 1 then 1113 else 2148) else (if t 3 = 0 then 3343 else if t 3 = 1 then 1119 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 504 else if t 3 = 1 then 492 else 494) else if t 2 = 1 then (if t 3 = 0 then 498 else if t 3 = 1 then 480 else 484) else (if t 3 = 0 then 500 else if t 3 = 1 then 482 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 505 else if t 3 = 1 then 493 else 495) else if t 2 = 1 then (if t 3 = 0 then 499 else if t 3 = 1 then 481 else 485) else (if t 3 = 0 then 501 else if t 3 = 1 then 483 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4899 else (if jt.2.val < 2 then 4915 else 4904)) else (if jt.2.val < 4 then 4914 else (if jt.2.val < 5 then 4916 else 4902))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3608 else (if jt.2.val < 2 then 3623 else 3611)) else (if jt.2.val < 4 then 3621 else (if jt.2.val < 5 then 3622 else 3600)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 39 else (if jt.2.val < 2 then 446 else 44)) else (if jt.2.val < 4 then 414 else (if jt.2.val < 5 then 415 else 7))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 416 else (if jt.2.val < 2 then 460 else 465)) else (if jt.2.val < 4 then 457 else (if jt.2.val < 5 then 459 else 458)))))

checked_coverage fastCoverage0822 pairing0822 template0822 witness0822

theorem coverage0822 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0822) (maskBits m))
    cores template0822 witness0822 := by
  rw [← coresFast_eq]
  exact fastCoverage0822

theorem coverageSize0822 : ∀ q : Pattern,
    (cores (witness0822 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0822 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0822
#print axioms coverageSize0822

noncomputable def pairing0823 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0823 : List (Fin 4935) := templateData0823

noncomputable def witness0823 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 624 else 661) else if t 2 = 1 then (if t 3 = 0 then 626 else if t 3 = 1 then 622 else 659) else (if t 3 = 0 then 648 else if t 3 = 1 then 646 else 669)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 620 else if t 3 = 1 then 616 else 656) else if t 2 = 1 then (if t 3 = 0 then 618 else if t 3 = 1 then 614 else 654) else (if t 3 = 0 then 644 else if t 3 = 1 then 641 else 667)) else (if t 2 = 0 then (if t 3 = 0 then 3320 else if t 3 = 1 then 3172 else 3524) else if t 2 = 1 then (if t 3 = 0 then 2768 else if t 3 = 1 then 2766 else 2775) else (if t 3 = 0 then 4058 else if t 3 = 1 then 3945 else 4190))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 623 else 660) else if t 2 = 1 then (if t 3 = 0 then 625 else if t 3 = 1 then 621 else 658) else (if t 3 = 0 then 647 else if t 3 = 1 then 645 else 668)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 619 else if t 3 = 1 then 615 else 655) else if t 2 = 1 then (if t 3 = 0 then 617 else if t 3 = 1 then 613 else 653) else (if t 3 = 0 then 643 else if t 3 = 1 then 640 else 666)) else (if t 2 = 0 then (if t 3 = 0 then 635 else if t 3 = 1 then 633 else 663) else if t 2 = 1 then (if t 3 = 0 then 634 else if t 3 = 1 then 632 else 662) else (if t 3 = 0 then 650 else if t 3 = 1 then 649 else 670))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 1146 else 4061) else if t 2 = 1 then (if t 3 = 0 then 2160 else if t 3 = 1 then 1140 else 1824) else (if t 3 = 0 then 3523 else if t 3 = 1 then 1142 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 696 else if t 3 = 1 then 684 else 686) else if t 2 = 1 then (if t 3 = 0 then 690 else if t 3 = 1 then 672 else 676) else (if t 3 = 0 then 692 else if t 3 = 1 then 674 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 697 else if t 3 = 1 then 685 else 687) else if t 2 = 1 then (if t 3 = 0 then 691 else if t 3 = 1 then 673 else 677) else (if t 3 = 0 then 693 else if t 3 = 1 then 675 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4917 else (if jt.2.val < 2 then 4924 else 4922)) else (if jt.2.val < 4 then 4923 else (if jt.2.val < 5 then 4925 else 4920))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3563 else (if jt.2.val < 2 then 3590 else 3566)) else (if jt.2.val < 4 then 3588 else (if jt.2.val < 5 then 3589 else 3555)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 247 else (if jt.2.val < 2 then 642 else 252)) else (if jt.2.val < 4 then 611 else (if jt.2.val < 5 then 612 else 215))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 458 else (if jt.2.val < 2 then 657 else 465)) else (if jt.2.val < 4 then 609 else (if jt.2.val < 5 then 610 else 416)))))

checked_coverage fastCoverage0823 pairing0823 template0823 witness0823

theorem coverage0823 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0823) (maskBits m))
    cores template0823 witness0823 := by
  rw [← coresFast_eq]
  exact fastCoverage0823

theorem coverageSize0823 : ∀ q : Pattern,
    (cores (witness0823 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0823 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0823
#print axioms coverageSize0823

noncomputable def pairing0824 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0824 : List (Fin 4935) := templateData0824

noncomputable def witness0824 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 4066) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3351) else (if t 3 = 0 then 3532 else if t 3 = 1 then 3531 else 2940)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1881) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1880) else (if t 3 = 0 then 2200 else if t 3 = 1 then 2198 else 1892)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1650 else 159) else if t 2 = 1 then (if t 3 = 0 then 1651 else if t 3 = 1 then 1649 else 1670) else (if t 3 = 0 then 743 else if t 3 = 1 then 1661 else 1676))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1722) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1721) else (if t 3 = 0 then 2074 else if t 3 = 1 then 2072 else 1735)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3270) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4498) else (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4499)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3074 else 3093) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4507) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4506 else 4513))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1443 else 782) else if t 2 = 1 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1442 else 1451) else (if t 3 = 0 then 197 else if t 3 = 1 then 1448 else 1454)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3161 else 3166) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4516) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4515 else 4517)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 3314 else 3501) else if t 2 = 1 then (if t 3 = 0 then 4038 else if t 3 = 1 then 4518 else 4520) else (if t 3 = 0 then 4040 else if t 3 = 1 then 4519 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4926 else (if jt.2.val < 2 then 4928 else 4931)) else (if jt.2.val < 4 then 4927 else (if jt.2.val < 5 then 4930 else 4929))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4575 else (if jt.2.val < 2 then 4585 else 4586)) else (if jt.2.val < 4 then 4582 else (if jt.2.val < 5 then 4584 else 4583)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4737 else (if jt.2.val < 2 then 4741 else 4742)) else (if jt.2.val < 4 then 4738 else (if jt.2.val < 5 then 4740 else 4739))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4593 else (if jt.2.val < 2 then 4597 else 4598)) else (if jt.2.val < 4 then 4594 else (if jt.2.val < 5 then 4596 else 4595)))))

checked_coverage fastCoverage0824 pairing0824 template0824 witness0824

theorem coverage0824 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0824) (maskBits m))
    cores template0824 witness0824 := by
  rw [← coresFast_eq]
  exact fastCoverage0824

theorem coverageSize0824 : ∀ q : Pattern,
    (cores (witness0824 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0824 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0824
#print axioms coverageSize0824

noncomputable def pairing0825 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0825 : List (Fin 4935) := templateData0825

noncomputable def witness0825 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 4537) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 3350) else (if t 3 = 0 then 2997 else if t 3 = 1 then 2995 else 3514)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 1879) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 1878) else (if t 3 = 0 then 1174 else if t 3 = 1 then 1170 else 1188)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 538 else 1538) else if t 2 = 1 then (if t 3 = 0 then 539 else if t 3 = 1 then 537 else 554) else (if t 3 = 0 then 1544 else if t 3 = 1 then 568 else 575))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 1720) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 1719) else (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 839)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 3269) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 3993) else (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4003)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2627) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4016) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4017 else 4018))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 390 else 1499) else if t 2 = 1 then (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 397) else (if t 3 = 0 then 1502 else if t 3 = 1 then 403 else 407)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2719) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4020) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4021 else 4022)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2903 else 2905) else if t 2 = 1 then (if t 3 = 0 then 4191 else if t 3 = 1 then 4023 else 4024) else (if t 3 = 0 then 4526 else if t 3 = 1 then 4025 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4899 else (if jt.2.val < 2 then 4901 else 4904)) else (if jt.2.val < 4 then 4900 else (if jt.2.val < 5 then 4903 else 4902))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4233 else (if jt.2.val < 2 then 4243 else 4244)) else (if jt.2.val < 4 then 4240 else (if jt.2.val < 5 then 4242 else 4241)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4234 else (if jt.2.val < 2 then 4238 else 4239)) else (if jt.2.val < 4 then 4235 else (if jt.2.val < 5 then 4237 else 4236))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4595 else (if jt.2.val < 2 then 4601 else 4598)) else (if jt.2.val < 4 then 4599 else (if jt.2.val < 5 then 4600 else 4593)))))

checked_coverage fastCoverage0825 pairing0825 template0825 witness0825

theorem coverage0825 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0825) (maskBits m))
    cores template0825 witness0825 := by
  rw [← coresFast_eq]
  exact fastCoverage0825

theorem coverageSize0825 : ∀ q : Pattern,
    (cores (witness0825 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0825 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0825
#print axioms coverageSize0825

noncomputable def pairing0826 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0826 : List (Fin 4935) := templateData0826

noncomputable def witness0826 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3453 else 2974) else if t 2 = 1 then (if t 3 = 0 then 3449 else if t 3 = 1 then 3445 else 2973) else (if t 3 = 0 then 4546 else if t 3 = 1 then 4211 else 4047)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3451 else 965) else if t 2 = 1 then (if t 3 = 0 then 3447 else if t 3 = 1 then 3443 else 963) else (if t 3 = 0 then 2197 else if t 3 = 1 then 2195 else 979)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 344 else 1496) else if t 2 = 1 then (if t 3 = 0 then 343 else if t 3 = 1 then 342 else 373) else (if t 3 = 0 then 1490 else if t 3 = 1 then 358 else 380))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3452 else 1043) else if t 2 = 1 then (if t 3 = 0 then 3448 else if t 3 = 1 then 3444 else 1041) else (if t 3 = 0 then 2071 else if t 3 = 1 then 2069 else 1056)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3450 else 3278) else if t 2 = 1 then (if t 3 = 0 then 3446 else if t 3 = 1 then 3442 else 3472) else (if t 3 = 0 then 3464 else if t 3 = 1 then 3462 else 3473)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 3082 else 3095) else if t 2 = 1 then (if t 3 = 0 then 2471 else if t 3 = 1 then 3479 else 3486) else (if t 3 = 0 then 2475 else if t 3 = 1 then 3480 else 3487))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 586 else 1550) else if t 2 = 1 then (if t 3 = 0 then 585 else if t 3 = 1 then 584 else 598) else (if t 3 = 0 then 1547 else if t 3 = 1 then 592 else 602)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 3163 else 3167) else if t 2 = 1 then (if t 3 = 0 then 2572 else if t 3 = 1 then 3488 else 3490) else (if t 3 = 0 then 2574 else if t 3 = 1 then 3489 else 3491)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 3315 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2886 else if t 3 = 1 then 3492 else 3494) else (if t 3 = 0 then 2887 else if t 3 = 1 then 3493 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4881 else (if jt.2.val < 2 then 4883 else 4886)) else (if jt.2.val < 4 then 4882 else (if jt.2.val < 5 then 4885 else 4884))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3600 else (if jt.2.val < 2 then 3610 else 3611)) else (if jt.2.val < 4 then 3607 else (if jt.2.val < 5 then 3609 else 3608)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4739 else (if jt.2.val < 2 then 4745 else 4742)) else (if jt.2.val < 4 then 4743 else (if jt.2.val < 5 then 4744 else 4737))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3601 else (if jt.2.val < 2 then 3605 else 3606)) else (if jt.2.val < 4 then 3602 else (if jt.2.val < 5 then 3604 else 3603)))))

checked_coverage fastCoverage0826 pairing0826 template0826 witness0826

theorem coverage0826 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0826) (maskBits m))
    cores template0826 witness0826 := by
  rw [← coresFast_eq]
  exact fastCoverage0826

theorem coverageSize0826 : ∀ q : Pattern,
    (cores (witness0826 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0826 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0826
#print axioms coverageSize0826

noncomputable def pairing0827 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0827 : List (Fin 4935) := templateData0827

noncomputable def witness0827 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2813 else 3520) else if t 2 = 1 then (if t 3 = 0 then 2817 else if t 3 = 1 then 2809 else 3338) else (if t 3 = 0 then 4056 else if t 3 = 1 then 4054 else 4532)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2811 else 962) else if t 2 = 1 then (if t 3 = 0 then 2815 else if t 3 = 1 then 2807 else 960) else (if t 3 = 0 then 1173 else if t 3 = 1 then 1169 else 1801)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1415 else 173) else if t 2 = 1 then (if t 3 = 0 then 1416 else if t 3 = 1 then 1414 else 992) else (if t 3 = 0 then 758 else if t 3 = 1 then 1202 else 1433))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2812 else 1040) else if t 2 = 1 then (if t 3 = 0 then 2816 else if t 3 = 1 then 2808 else 1038) else (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 1817)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2810 else 2837) else if t 2 = 1 then (if t 3 = 0 then 2814 else if t 3 = 1 then 2806 else 2835) else (if t 3 = 0 then 2829 else if t 3 = 1 then 2826 else 2840)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2632 else 2637) else if t 2 = 1 then (if t 3 = 0 then 2484 else if t 3 = 1 then 2854 else 2857) else (if t 3 = 0 then 2487 else if t 3 = 1 then 2856 else 2858))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1686 else 788) else if t 2 = 1 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1685 else 1082) else (if t 3 = 0 then 203 else if t 3 = 1 then 866 else 1691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2721 else 2724) else if t 2 = 1 then (if t 3 = 0 then 2576 else if t 3 = 1 then 2859 else 2862) else (if t 3 = 0 then 2578 else if t 3 = 1 then 2861 else 2863)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3321 else 4045) else if t 2 = 1 then (if t 3 = 0 then 3506 else if t 3 = 1 then 2864 else 2866) else (if t 3 = 0 then 3507 else if t 3 = 1 then 2865 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4857 else (if jt.2.val < 2 then 4859 else 4862)) else (if jt.2.val < 4 then 4858 else (if jt.2.val < 5 then 4861 else 4860))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3575 else (if jt.2.val < 2 then 3580 else 3581)) else (if jt.2.val < 4 then 3577 else (if jt.2.val < 5 then 3579 else 3578)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4236 else (if jt.2.val < 2 then 4253 else 4239)) else (if jt.2.val < 4 then 4251 else (if jt.2.val < 5 then 4252 else 4234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3603 else (if jt.2.val < 2 then 3614 else 3606)) else (if jt.2.val < 4 then 3612 else (if jt.2.val < 5 then 3613 else 3601)))))

checked_coverage fastCoverage0827 pairing0827 template0827 witness0827

theorem coverage0827 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0827) (maskBits m))
    cores template0827 witness0827 := by
  rw [← coresFast_eq]
  exact fastCoverage0827

theorem coverageSize0827 : ∀ q : Pattern,
    (cores (witness0827 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0827 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0827
#print axioms coverageSize0827

noncomputable def pairing0828 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0828 : List (Fin 4935) := templateData0828

noncomputable def witness0828 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1316 else 648) else if t 2 = 1 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1314 else 1353) else (if t 3 = 0 then 50 else if t 3 = 1 then 1342 else 1359)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1312 else if t 3 = 1 then 1308 else 644) else if t 2 = 1 then (if t 3 = 0 then 1310 else if t 3 = 1 then 1306 else 1350) else (if t 3 = 0 then 46 else if t 3 = 1 then 1339 else 1357)) else (if t 2 = 0 then (if t 3 = 0 then 4530 else if t 3 = 1 then 3963 else 4058) else if t 2 = 1 then (if t 3 = 0 then 3234 else if t 3 = 1 then 3232 else 2545) else (if t 3 = 0 then 3522 else if t 3 = 1 then 2689 else 2882))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1315 else 647) else if t 2 = 1 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1313 else 1352) else (if t 3 = 0 then 49 else if t 3 = 1 then 1341 else 1358)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1311 else if t 3 = 1 then 1307 else 643) else if t 2 = 1 then (if t 3 = 0 then 1309 else if t 3 = 1 then 1305 else 1349) else (if t 3 = 0 then 45 else if t 3 = 1 then 1338 else 1356)) else (if t 2 = 0 then (if t 3 = 0 then 1329 else if t 3 = 1 then 1327 else 650) else if t 2 = 1 then (if t 3 = 0 then 1328 else if t 3 = 1 then 1325 else 1354) else (if t 3 = 0 then 52 else if t 3 = 1 then 1343 else 1360))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1221 else 3523) else if t 2 = 1 then (if t 3 = 0 then 1011 else if t 3 = 1 then 1776 else 2118) else (if t 3 = 0 then 4059 else if t 3 = 1 then 1779 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1374 else if t 3 = 1 then 1208 else 692) else if t 2 = 1 then (if t 3 = 0 then 998 else if t 3 = 1 then 1362 else 1366) else (if t 3 = 0 then 98 else if t 3 = 1 then 1364 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 1375 else if t 3 = 1 then 1209 else 693) else if t 2 = 1 then (if t 3 = 0 then 999 else if t 3 = 1 then 1363 else 1367) else (if t 3 = 0 then 99 else if t 3 = 1 then 1365 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4857 else (if jt.2.val < 2 then 4873 else 4862)) else (if jt.2.val < 4 then 4872 else (if jt.2.val < 5 then 4874 else 4860))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4583 else (if jt.2.val < 2 then 4592 else 4586)) else (if jt.2.val < 4 then 4590 else (if jt.2.val < 5 then 4591 else 4575)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1303 else (if jt.2.val < 2 then 1337 else 1340)) else (if jt.2.val < 4 then 1334 else (if jt.2.val < 5 then 1336 else 1335))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1302 else (if jt.2.val < 2 then 1348 else 1351)) else (if jt.2.val < 4 then 1345 else (if jt.2.val < 5 then 1347 else 1346)))))

checked_coverage fastCoverage0828 pairing0828 template0828 witness0828

theorem coverage0828 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0828) (maskBits m))
    cores template0828 witness0828 := by
  rw [← coresFast_eq]
  exact fastCoverage0828

theorem coverageSize0828 : ∀ q : Pattern,
    (cores (witness0828 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0828 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0828
#print axioms coverageSize0828

noncomputable def pairing0829 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0829 : List (Fin 4935) := templateData0829

noncomputable def witness0829 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 228 else 1462) else if t 2 = 1 then (if t 3 = 0 then 230 else if t 3 = 1 then 226 else 256) else (if t 3 = 0 then 1471 else if t 3 = 1 then 269 else 279)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 224 else if t 3 = 1 then 220 else 1459) else if t 2 = 1 then (if t 3 = 0 then 222 else if t 3 = 1 then 218 else 251) else (if t 3 = 0 then 916 else if t 3 = 1 then 264 else 277)) else (if t 2 = 0 then (if t 3 = 0 then 4044 else if t 3 = 1 then 3923 else 4541) else if t 2 = 1 then (if t 3 = 0 then 2749 else if t 3 = 1 then 2747 else 3209) else (if t 3 = 0 then 2983 else if t 3 = 1 then 2756 else 3499))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 227 else 1461) else if t 2 = 1 then (if t 3 = 0 then 229 else if t 3 = 1 then 225 else 255) else (if t 3 = 0 then 1470 else if t 3 = 1 then 268 else 278)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 223 else if t 3 = 1 then 219 else 1458) else if t 2 = 1 then (if t 3 = 0 then 221 else if t 3 = 1 then 217 else 250) else (if t 3 = 0 then 915 else if t 3 = 1 then 263 else 276)) else (if t 2 = 0 then (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 1463) else if t 2 = 1 then (if t 3 = 0 then 240 else if t 3 = 1 then 237 else 259) else (if t 3 = 0 then 919 else if t 3 = 1 then 272 else 280))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 930 else 2990) else if t 2 = 1 then (if t 3 = 0 then 2139 else if t 3 = 1 then 924 else 926) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1788 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 306 else if t 3 = 1 then 294 else 1473) else if t 2 = 1 then (if t 3 = 0 then 300 else if t 3 = 1 then 282 else 284) else (if t 3 = 0 then 1476 else if t 3 = 1 then 286 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 307 else if t 3 = 1 then 295 else 1474) else if t 2 = 1 then (if t 3 = 0 then 301 else if t 3 = 1 then 283 else 285) else (if t 3 = 0 then 1477 else if t 3 = 1 then 287 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4881 else (if jt.2.val < 2 then 4897 else 4886)) else (if jt.2.val < 4 then 4896 else (if jt.2.val < 5 then 4898 else 4884))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4241 else (if jt.2.val < 2 then 4256 else 4244)) else (if jt.2.val < 4 then 4254 else (if jt.2.val < 5 then 4255 else 4233)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1457 else (if jt.2.val < 2 then 1468 else 1469)) else (if jt.2.val < 4 then 1465 else (if jt.2.val < 5 then 1467 else 1466))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1346 else (if jt.2.val < 2 then 1460 else 1351)) else (if jt.2.val < 4 then 1455 else (if jt.2.val < 5 then 1456 else 1302)))))

checked_coverage fastCoverage0829 pairing0829 template0829 witness0829

theorem coverage0829 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0829) (maskBits m))
    cores template0829 witness0829 := by
  rw [← coresFast_eq]
  exact fastCoverage0829

theorem coverageSize0829 : ∀ q : Pattern,
    (cores (witness0829 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0829 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0829
#print axioms coverageSize0829

noncomputable def pairing0830 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0830 : List (Fin 4935) := templateData0830

noncomputable def witness0830 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 430 else 1519) else if t 2 = 1 then (if t 3 = 0 then 428 else if t 3 = 1 then 426 else 467) else (if t 3 = 0 then 1510 else if t 3 = 1 then 450 else 477)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 424 else if t 3 = 1 then 422 else 1132) else if t 2 = 1 then (if t 3 = 0 then 420 else if t 3 = 1 then 418 else 462) else (if t 3 = 0 then 1507 else if t 3 = 1 then 445 else 475)) else (if t 2 = 0 then (if t 3 = 0 then 3505 else if t 3 = 1 then 2730 else 2987) else if t 2 = 1 then (if t 3 = 0 then 3203 else if t 3 = 1 then 2728 else 2737) else (if t 3 = 0 then 4539 else if t 3 = 1 then 3929 else 4036))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 429 else 1518) else if t 2 = 1 then (if t 3 = 0 then 427 else if t 3 = 1 then 425 else 466) else (if t 3 = 0 then 1509 else if t 3 = 1 then 449 else 476)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 423 else if t 3 = 1 then 421 else 1131) else if t 2 = 1 then (if t 3 = 0 then 419 else if t 3 = 1 then 417 else 461) else (if t 3 = 0 then 1506 else if t 3 = 1 then 444 else 474)) else (if t 2 = 0 then (if t 3 = 0 then 439 else if t 3 = 1 then 438 else 1135) else if t 2 = 1 then (if t 3 = 0 then 437 else if t 3 = 1 then 436 else 470) else (if t 3 = 0 then 1511 else if t 3 = 1 then 453 else 478))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 1836 else 4542) else if t 2 = 1 then (if t 3 = 0 then 1115 else if t 3 = 1 then 1113 else 2148) else (if t 3 = 0 then 2986 else if t 3 = 1 then 1119 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 504 else if t 3 = 1 then 498 else 1524) else if t 2 = 1 then (if t 3 = 0 then 492 else if t 3 = 1 then 480 else 484) else (if t 3 = 0 then 1521 else if t 3 = 1 then 482 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 505 else if t 3 = 1 then 499 else 1525) else if t 2 = 1 then (if t 3 = 0 then 493 else if t 3 = 1 then 481 else 485) else (if t 3 = 0 then 1522 else if t 3 = 1 then 483 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4899 else (if jt.2.val < 2 then 4915 else 4904)) else (if jt.2.val < 4 then 4914 else (if jt.2.val < 5 then 4916 else 4902))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3608 else (if jt.2.val < 2 then 3623 else 3611)) else (if jt.2.val < 4 then 3621 else (if jt.2.val < 5 then 3622 else 3600)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1335 else (if jt.2.val < 2 then 1508 else 1340)) else (if jt.2.val < 4 then 1503 else (if jt.2.val < 5 then 1504 else 1303))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1505 else (if jt.2.val < 2 then 1516 else 1517)) else (if jt.2.val < 4 then 1513 else (if jt.2.val < 5 then 1515 else 1514)))))

checked_coverage fastCoverage0830 pairing0830 template0830 witness0830

theorem coverage0830 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0830) (maskBits m))
    cores template0830 witness0830 := by
  rw [← coresFast_eq]
  exact fastCoverage0830

theorem coverageSize0830 : ∀ q : Pattern,
    (cores (witness0830 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0830 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0830
#print axioms coverageSize0830

noncomputable def pairing0831 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0831 : List (Fin 4935) := templateData0831

noncomputable def witness0831 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1572 else 661) else if t 2 = 1 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1570 else 1071) else (if t 3 = 0 then 67 else if t 3 = 1 then 855 else 1599)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1564 else 656) else if t 2 = 1 then (if t 3 = 0 then 1566 else if t 3 = 1 then 1562 else 1593) else (if t 3 = 0 then 62 else if t 3 = 1 then 1589 else 1597)) else (if t 2 = 0 then (if t 3 = 0 then 2898 else if t 3 = 1 then 2630 else 3524) else if t 2 = 1 then (if t 3 = 0 then 2482 else if t 3 = 1 then 3219 else 3225) else (if t 3 = 0 then 4060 else if t 3 = 1 then 3953 else 4525))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1571 else 660) else if t 2 = 1 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1569 else 1070) else (if t 3 = 0 then 66 else if t 3 = 1 then 854 else 1598)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1563 else 655) else if t 2 = 1 then (if t 3 = 0 then 1565 else if t 3 = 1 then 1561 else 1592) else (if t 3 = 0 then 61 else if t 3 = 1 then 1588 else 1596)) else (if t 2 = 0 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1581 else 663) else if t 2 = 1 then (if t 3 = 0 then 1582 else if t 3 = 1 then 1580 else 1595) else (if t 3 = 0 then 69 else if t 3 = 1 then 1591 else 1600))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1854 else 4061) else if t 2 = 1 then (if t 3 = 0 then 2172 else if t 3 = 1 then 1851 else 1092) else (if t 3 = 0 then 3525 else if t 3 = 1 then 876 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1620 else if t 3 = 1 then 1614 else 686) else if t 2 = 1 then (if t 3 = 0 then 1617 else if t 3 = 1 then 1602 else 1606) else (if t 3 = 0 then 92 else if t 3 = 1 then 1604 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 1621 else if t 3 = 1 then 1615 else 687) else if t 2 = 1 then (if t 3 = 0 then 1618 else if t 3 = 1 then 1603 else 1607) else (if t 3 = 0 then 93 else if t 3 = 1 then 1605 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4926 else (if jt.2.val < 2 then 4933 else 4931)) else (if jt.2.val < 4 then 4932 else (if jt.2.val < 5 then 4934 else 4929))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3578 else (if jt.2.val < 2 then 3596 else 3581)) else (if jt.2.val < 4 then 3594 else (if jt.2.val < 5 then 3595 else 3575)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1466 else (if jt.2.val < 2 then 1590 else 1469)) else (if jt.2.val < 4 then 1559 else (if jt.2.val < 5 then 1560 else 1457))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1514 else (if jt.2.val < 2 then 1594 else 1517)) else (if jt.2.val < 4 then 1557 else (if jt.2.val < 5 then 1558 else 1505)))))

checked_coverage fastCoverage0831 pairing0831 template0831 witness0831

theorem coverage0831 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0831) (maskBits m))
    cores template0831 witness0831 := by
  rw [← coresFast_eq]
  exact fastCoverage0831

theorem coverageSize0831 : ∀ q : Pattern,
    (cores (witness0831 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0831 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0831
#print axioms coverageSize0831

noncomputable def pairing0832 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0832 : List (Fin 4935) := templateData0832

noncomputable def witness0832 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 4213) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3531) else (if t 3 = 0 then 3352 else if t 3 = 1 then 3351 else 2940)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 2199) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 2198) else (if t 3 = 0 then 1882 else if t 3 = 1 then 1880 else 1892)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1650 else 359) else if t 2 = 1 then (if t 3 = 0 then 1651 else if t 3 = 1 then 1649 else 1661) else (if t 3 = 0 then 555 else if t 3 = 1 then 1670 else 1676))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 2073) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 2072) else (if t 3 = 0 then 1723 else if t 3 = 1 then 1721 else 1735)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3465) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4492) else (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4499)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3074 else 3084) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4506) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4507 else 4513))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1443 else 593) else if t 2 = 1 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1442 else 1448) else (if t 3 = 0 then 398 else if t 3 = 1 then 1451 else 1454)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3161 else 3164) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4515) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4516 else 4517)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 3314 else 3316) else if t 2 = 1 then (if t 3 = 0 then 4038 else if t 3 = 1 then 4518 else 4519) else (if t 3 = 0 then 4192 else if t 3 = 1 then 4520 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4926 else (if jt.2.val < 2 then 4928 else 4931)) else (if jt.2.val < 4 then 4927 else (if jt.2.val < 5 then 4930 else 4929))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4575 else (if jt.2.val < 2 then 4585 else 4586)) else (if jt.2.val < 4 then 4582 else (if jt.2.val < 5 then 4584 else 4583)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4576 else (if jt.2.val < 2 then 4580 else 4581)) else (if jt.2.val < 4 then 4577 else (if jt.2.val < 5 then 4579 else 4578))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4746 else (if jt.2.val < 2 then 4750 else 4751)) else (if jt.2.val < 4 then 4747 else (if jt.2.val < 5 then 4749 else 4748)))))

checked_coverage fastCoverage0832 pairing0832 template0832 witness0832

theorem coverage0832 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0832) (maskBits m))
    cores template0832 witness0832 := by
  rw [← coresFast_eq]
  exact fastCoverage0832

theorem coverageSize0832 : ∀ q : Pattern,
    (cores (witness0832 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0832 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0832
#print axioms coverageSize0832

noncomputable def pairing0833 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0833 : List (Fin 4935) := templateData0833

noncomputable def witness0833 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 4546) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 3530) else (if t 3 = 0 then 2997 else if t 3 = 1 then 2996 else 3330)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 2197) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 2196) else (if t 3 = 0 then 1174 else if t 3 = 1 then 1172 else 1189)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 726 else 1490) else if t 2 = 1 then (if t 3 = 0 then 727 else if t 3 = 1 then 725 else 742) else (if t 3 = 0 then 1544 else if t 3 = 1 then 757 else 764))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 2071) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 2070) else (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 840)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 3464) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4155) else (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4164)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2475) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4171) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4177 else 4178))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 189 else 1547) else if t 2 = 1 then (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 196) else (if t 3 = 0 then 1502 else if t 3 = 1 then 202 else 206)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2574) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4180) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4181 else 4182)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2885 else 2887) else if t 2 = 1 then (if t 3 = 0 then 4039 else if t 3 = 1 then 4183 else 4184) else (if t 3 = 0 then 4526 else if t 3 = 1 then 4185 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4917 else (if jt.2.val < 2 then 4919 else 4922)) else (if jt.2.val < 4 then 4918 else (if jt.2.val < 5 then 4921 else 4920))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4260 else (if jt.2.val < 2 then 4270 else 4271)) else (if jt.2.val < 4 then 4267 else (if jt.2.val < 5 then 4269 else 4268)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4261 else (if jt.2.val < 2 then 4265 else 4266)) else (if jt.2.val < 4 then 4262 else (if jt.2.val < 5 then 4264 else 4263))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4748 else (if jt.2.val < 2 then 4754 else 4751)) else (if jt.2.val < 4 then 4752 else (if jt.2.val < 5 then 4753 else 4746)))))

checked_coverage fastCoverage0833 pairing0833 template0833 witness0833

theorem coverage0833 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0833) (maskBits m))
    cores template0833 witness0833 := by
  rw [← coresFast_eq]
  exact fastCoverage0833

theorem coverageSize0833 : ∀ q : Pattern,
    (cores (witness0833 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0833 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0833
#print axioms coverageSize0833

noncomputable def pairing0834 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0834 : List (Fin 4935) := templateData0834

noncomputable def witness0834 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3258 else 2974) else if t 2 = 1 then (if t 3 = 0 then 3254 else if t 3 = 1 then 3250 else 2972) else (if t 3 = 0 then 4537 else if t 3 = 1 then 4064 else 4198)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3256 else 965) else if t 2 = 1 then (if t 3 = 0 then 3252 else if t 3 = 1 then 3248 else 961) else (if t 3 = 0 then 1879 else if t 3 = 1 then 1877 else 978)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 144 else 1496) else if t 2 = 1 then (if t 3 = 0 then 143 else if t 3 = 1 then 142 else 172) else (if t 3 = 0 then 1538 else if t 3 = 1 then 158 else 179))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3257 else 1043) else if t 2 = 1 then (if t 3 = 0 then 3253 else if t 3 = 1 then 3249 else 1039) else (if t 3 = 0 then 1720 else if t 3 = 1 then 1718 else 1055)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3255 else 3278) else if t 2 = 1 then (if t 3 = 0 then 3251 else if t 3 = 1 then 3247 else 3276) else (if t 3 = 0 then 3269 else if t 3 = 1 then 3267 else 3279)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 3091 else 3095) else if t 2 = 1 then (if t 3 = 0 then 2623 else if t 3 = 1 then 3291 else 3293) else (if t 3 = 0 then 2627 else if t 3 = 1 then 3292 else 3294))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 775 else 1550) else if t 2 = 1 then (if t 3 = 0 then 774 else if t 3 = 1 then 773 else 787) else (if t 3 = 0 then 1499 else if t 3 = 1 then 781 else 791)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 3165 else 3167) else if t 2 = 1 then (if t 3 = 0 then 2717 else if t 3 = 1 then 3295 else 3297) else (if t 3 = 0 then 2719 else if t 3 = 1 then 3296 else 3298)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 3500 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2904 else if t 3 = 1 then 3299 else 3301) else (if t 3 = 0 then 2905 else if t 3 = 1 then 3300 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4845 else (if jt.2.val < 2 then 4847 else 4850)) else (if jt.2.val < 4 then 4846 else (if jt.2.val < 5 then 4849 else 4848))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3555 else (if jt.2.val < 2 then 3565 else 3566)) else (if jt.2.val < 4 then 3562 else (if jt.2.val < 5 then 3564 else 3563)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4578 else (if jt.2.val < 2 then 4589 else 4581)) else (if jt.2.val < 4 then 4587 else (if jt.2.val < 5 then 4588 else 4576))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3556 else (if jt.2.val < 2 then 3560 else 3561)) else (if jt.2.val < 4 then 3557 else (if jt.2.val < 5 then 3559 else 3558)))))

checked_coverage fastCoverage0834 pairing0834 template0834 witness0834

theorem coverage0834 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0834) (maskBits m))
    cores template0834 witness0834 := by
  rw [← coresFast_eq]
  exact fastCoverage0834

theorem coverageSize0834 : ∀ q : Pattern,
    (cores (witness0834 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0834 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0834
#print axioms coverageSize0834

noncomputable def pairing0835 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0835 : List (Fin 4935) := templateData0835

noncomputable def witness0835 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2817 else 3340) else if t 2 = 1 then (if t 3 = 0 then 2813 else if t 3 = 1 then 2809 else 3338) else (if t 3 = 0 then 4203 else if t 3 = 1 then 4054 else 4532)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2815 else 964) else if t 2 = 1 then (if t 3 = 0 then 2811 else if t 3 = 1 then 2807 else 960) else (if t 3 = 0 then 1171 else if t 3 = 1 then 1169 else 1801)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1416 else 374) else if t 2 = 1 then (if t 3 = 0 then 1415 else if t 3 = 1 then 1414 else 992) else (if t 3 = 0 then 569 else if t 3 = 1 then 1202 else 1433))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2816 else 1042) else if t 2 = 1 then (if t 3 = 0 then 2812 else if t 3 = 1 then 2808 else 1038) else (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 1817)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2814 else 2838) else if t 2 = 1 then (if t 3 = 0 then 2810 else if t 3 = 1 then 2806 else 2835) else (if t 3 = 0 then 2828 else if t 3 = 1 then 2826 else 2840)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2484 else 2489) else if t 2 = 1 then (if t 3 = 0 then 2632 else if t 3 = 1 then 2854 else 2857) else (if t 3 = 0 then 2635 else if t 3 = 1 then 2856 else 2858))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1687 else 599) else if t 2 = 1 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1685 else 1082) else (if t 3 = 0 then 404 else if t 3 = 1 then 866 else 1691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2576 else 2579) else if t 2 = 1 then (if t 3 = 0 then 2721 else if t 3 = 1 then 2859 else 2862) else (if t 3 = 0 then 2723 else if t 3 = 1 then 2861 else 2863)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3506 else 4197) else if t 2 = 1 then (if t 3 = 0 then 3321 else if t 3 = 1 then 2864 else 2866) else (if t 3 = 0 then 3322 else if t 3 = 1 then 2865 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4857 else (if jt.2.val < 2 then 4859 else 4862)) else (if jt.2.val < 4 then 4858 else (if jt.2.val < 5 then 4861 else 4860))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3575 else (if jt.2.val < 2 then 3580 else 3581)) else (if jt.2.val < 4 then 3577 else (if jt.2.val < 5 then 3579 else 3578)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4263 else (if jt.2.val < 2 then 4274 else 4266)) else (if jt.2.val < 4 then 4272 else (if jt.2.val < 5 then 4273 else 4261))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3558 else (if jt.2.val < 2 then 3576 else 3561)) else (if jt.2.val < 4 then 3573 else (if jt.2.val < 5 then 3574 else 3556)))))

checked_coverage fastCoverage0835 pairing0835 template0835 witness0835

theorem coverage0835 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0835) (maskBits m))
    cores template0835 witness0835 := by
  rw [← coresFast_eq]
  exact fastCoverage0835

theorem coverageSize0835 : ∀ q : Pattern,
    (cores (witness0835 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0835 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0835
#print axioms coverageSize0835

noncomputable def pairing0836 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0836 : List (Fin 4935) := templateData0836

noncomputable def witness0836 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1316 else 452) else if t 2 = 1 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1314 else 1342) else (if t 3 = 0 then 258 else if t 3 = 1 then 1353 else 1359)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1312 else if t 3 = 1 then 1308 else 448) else if t 2 = 1 then (if t 3 = 0 then 1310 else if t 3 = 1 then 1306 else 1339) else (if t 3 = 0 then 254 else if t 3 = 1 then 1350 else 1357)) else (if t 2 = 0 then (if t 3 = 0 then 4530 else if t 3 = 1 then 3963 else 4205) else if t 2 = 1 then (if t 3 = 0 then 3234 else if t 3 = 1 then 3232 else 2689) else (if t 3 = 0 then 3342 else if t 3 = 1 then 2545 else 2882))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1315 else 451) else if t 2 = 1 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1313 else 1341) else (if t 3 = 0 then 257 else if t 3 = 1 then 1352 else 1358)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1311 else if t 3 = 1 then 1307 else 447) else if t 2 = 1 then (if t 3 = 0 then 1309 else if t 3 = 1 then 1305 else 1338) else (if t 3 = 0 then 253 else if t 3 = 1 then 1349 else 1356)) else (if t 2 = 0 then (if t 3 = 0 then 1329 else if t 3 = 1 then 1327 else 454) else if t 2 = 1 then (if t 3 = 0 then 1328 else if t 3 = 1 then 1325 else 1343) else (if t 3 = 0 then 260 else if t 3 = 1 then 1354 else 1360))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1221 else 3343) else if t 2 = 1 then (if t 3 = 0 then 1011 else if t 3 = 1 then 1776 else 1779) else (if t 3 = 0 then 4206 else if t 3 = 1 then 2118 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1374 else if t 3 = 1 then 1208 else 500) else if t 2 = 1 then (if t 3 = 0 then 998 else if t 3 = 1 then 1362 else 1364) else (if t 3 = 0 then 302 else if t 3 = 1 then 1366 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 1375 else if t 3 = 1 then 1209 else 501) else if t 2 = 1 then (if t 3 = 0 then 999 else if t 3 = 1 then 1363 else 1365) else (if t 3 = 0 then 303 else if t 3 = 1 then 1367 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4857 else (if jt.2.val < 2 then 4873 else 4862)) else (if jt.2.val < 4 then 4872 else (if jt.2.val < 5 then 4874 else 4860))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4583 else (if jt.2.val < 2 then 4592 else 4586)) else (if jt.2.val < 4 then 4590 else (if jt.2.val < 5 then 4591 else 4575)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1971 else (if jt.2.val < 2 then 1981 else 1982)) else (if jt.2.val < 4 then 1978 else (if jt.2.val < 5 then 1980 else 1979))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1972 else (if jt.2.val < 2 then 1976 else 1977)) else (if jt.2.val < 4 then 1973 else (if jt.2.val < 5 then 1975 else 1974)))))

checked_coverage fastCoverage0836 pairing0836 template0836 witness0836

theorem coverage0836 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0836) (maskBits m))
    cores template0836 witness0836 := by
  rw [← coresFast_eq]
  exact fastCoverage0836

theorem coverageSize0836 : ∀ q : Pattern,
    (cores (witness0836 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0836 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0836
#print axioms coverageSize0836

noncomputable def pairing0837 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0837 : List (Fin 4935) := templateData0837

noncomputable def witness0837 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 20 else 1510) else if t 2 = 1 then (if t 3 = 0 then 22 else if t 3 = 1 then 18 else 48) else (if t 3 = 0 then 1471 else if t 3 = 1 then 65 else 75)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 16 else if t 3 = 1 then 12 else 1507) else if t 2 = 1 then (if t 3 = 0 then 14 else if t 3 = 1 then 10 else 43) else (if t 3 = 0 then 916 else if t 3 = 1 then 60 else 73)) else (if t 2 = 0 then (if t 3 = 0 then 4196 else if t 3 = 1 then 3939 else 4539) else if t 2 = 1 then (if t 3 = 0 then 2787 else if t 3 = 1 then 2785 else 3191) else (if t 3 = 0 then 2983 else if t 3 = 1 then 2794 else 3312))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 19 else 1509) else if t 2 = 1 then (if t 3 = 0 then 21 else if t 3 = 1 then 17 else 47) else (if t 3 = 0 then 1470 else if t 3 = 1 then 64 else 74)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 15 else if t 3 = 1 then 11 else 1506) else if t 2 = 1 then (if t 3 = 0 then 13 else if t 3 = 1 then 9 else 42) else (if t 3 = 0 then 915 else if t 3 = 1 then 59 else 72)) else (if t 2 = 0 then (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 1511) else if t 2 = 1 then (if t 3 = 0 then 32 else if t 3 = 1 then 29 else 51) else (if t 3 = 0 then 919 else if t 3 = 1 then 68 else 76))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 899 else 2986) else if t 2 = 1 then (if t 3 = 0 then 1806 else if t 3 = 1 then 897 else 903) else (if t 3 = 0 then 4540 else if t 3 = 1 then 2127 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 102 else if t 3 = 1 then 90 else 1521) else if t 2 = 1 then (if t 3 = 0 then 96 else if t 3 = 1 then 78 else 80) else (if t 3 = 0 then 1476 else if t 3 = 1 then 82 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 103 else if t 3 = 1 then 91 else 1522) else if t 2 = 1 then (if t 3 = 0 then 97 else if t 3 = 1 then 79 else 81) else (if t 3 = 0 then 1477 else if t 3 = 1 then 83 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4845 else (if jt.2.val < 2 then 4879 else 4850)) else (if jt.2.val < 4 then 4878 else (if jt.2.val < 5 then 4880 else 4848))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4268 else (if jt.2.val < 2 then 4277 else 4271)) else (if jt.2.val < 4 then 4275 else (if jt.2.val < 5 then 4276 else 4260)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1997 else (if jt.2.val < 2 then 2002 else 2003)) else (if jt.2.val < 4 then 1999 else (if jt.2.val < 5 then 2001 else 2000))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1974 else (if jt.2.val < 2 then 1998 else 1977)) else (if jt.2.val < 4 then 1995 else (if jt.2.val < 5 then 1996 else 1972)))))

checked_coverage fastCoverage0837 pairing0837 template0837 witness0837

theorem coverage0837 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0837) (maskBits m))
    cores template0837 witness0837 := by
  rw [← coresFast_eq]
  exact fastCoverage0837

theorem coverageSize0837 : ∀ q : Pattern,
    (cores (witness0837 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0837 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0837
#print axioms coverageSize0837

noncomputable def pairing0838 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 3)))) (by decide +kernel)

noncomputable def template0838 : List (Fin 4935) := templateData0838

noncomputable def witness0838 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 626 else 1519) else if t 2 = 1 then (if t 3 = 0 then 624 else if t 3 = 1 then 622 else 659) else (if t 3 = 0 then 1462 else if t 3 = 1 then 646 else 669)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 620 else if t 3 = 1 then 618 else 1132) else if t 2 = 1 then (if t 3 = 0 then 616 else if t 3 = 1 then 614 else 654) else (if t 3 = 0 then 1459 else if t 3 = 1 then 641 else 667)) else (if t 2 = 0 then (if t 3 = 0 then 3320 else if t 3 = 1 then 2768 else 2987) else if t 2 = 1 then (if t 3 = 0 then 3172 else if t 3 = 1 then 2766 else 2775) else (if t 3 = 0 then 4541 else if t 3 = 1 then 3945 else 4190))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 625 else 1518) else if t 2 = 1 then (if t 3 = 0 then 623 else if t 3 = 1 then 621 else 658) else (if t 3 = 0 then 1461 else if t 3 = 1 then 645 else 668)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 619 else if t 3 = 1 then 617 else 1131) else if t 2 = 1 then (if t 3 = 0 then 615 else if t 3 = 1 then 613 else 653) else (if t 3 = 0 then 1458 else if t 3 = 1 then 640 else 666)) else (if t 2 = 0 then (if t 3 = 0 then 635 else if t 3 = 1 then 634 else 1135) else if t 2 = 1 then (if t 3 = 0 then 633 else if t 3 = 1 then 632 else 662) else (if t 3 = 0 then 1463 else if t 3 = 1 then 649 else 670))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 2160 else 4542) else if t 2 = 1 then (if t 3 = 0 then 1146 else if t 3 = 1 then 1140 else 1824) else (if t 3 = 0 then 2990 else if t 3 = 1 then 1142 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 696 else if t 3 = 1 then 690 else 1524) else if t 2 = 1 then (if t 3 = 0 then 684 else if t 3 = 1 then 672 else 676) else (if t 3 = 0 then 1473 else if t 3 = 1 then 674 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 697 else if t 3 = 1 then 691 else 1525) else if t 2 = 1 then (if t 3 = 0 then 685 else if t 3 = 1 then 673 else 677) else (if t 3 = 0 then 1474 else if t 3 = 1 then 675 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4917 else (if jt.2.val < 2 then 4924 else 4922)) else (if jt.2.val < 4 then 4923 else (if jt.2.val < 5 then 4925 else 4920))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3563 else (if jt.2.val < 2 then 3590 else 3566)) else (if jt.2.val < 4 then 3588 else (if jt.2.val < 5 then 3589 else 3555)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1979 else (if jt.2.val < 2 then 2016 else 1982)) else (if jt.2.val < 4 then 2013 else (if jt.2.val < 5 then 2014 else 1971))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2015 else (if jt.2.val < 2 then 2020 else 2021)) else (if jt.2.val < 4 then 2017 else (if jt.2.val < 5 then 2019 else 2018)))))

checked_coverage fastCoverage0838 pairing0838 template0838 witness0838

theorem coverage0838 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0838) (maskBits m))
    cores template0838 witness0838 := by
  rw [← coresFast_eq]
  exact fastCoverage0838

theorem coverageSize0838 : ∀ q : Pattern,
    (cores (witness0838 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0838 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0838
#print axioms coverageSize0838

noncomputable def pairing0839 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 4)))) (by decide +kernel)

noncomputable def template0839 : List (Fin 4935) := templateData0839

noncomputable def witness0839 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1574 else 469) else if t 2 = 1 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1570 else 1071) else (if t 3 = 0 then 271 else if t 3 = 1 then 855 else 1599)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1566 else 464) else if t 2 = 1 then (if t 3 = 0 then 1564 else if t 3 = 1 then 1562 else 1593) else (if t 3 = 0 then 266 else if t 3 = 1 then 1589 else 1597)) else (if t 2 = 0 then (if t 3 = 0 then 2898 else if t 3 = 1 then 2482 else 3344) else if t 2 = 1 then (if t 3 = 0 then 2630 else if t 3 = 1 then 3219 else 3225) else (if t 3 = 0 then 4207 else if t 3 = 1 then 3953 else 4525))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1573 else 468) else if t 2 = 1 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1569 else 1070) else (if t 3 = 0 then 270 else if t 3 = 1 then 854 else 1598)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1565 else 463) else if t 2 = 1 then (if t 3 = 0 then 1563 else if t 3 = 1 then 1561 else 1592) else (if t 3 = 0 then 265 else if t 3 = 1 then 1588 else 1596)) else (if t 2 = 0 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1582 else 471) else if t 2 = 1 then (if t 3 = 0 then 1581 else if t 3 = 1 then 1580 else 1595) else (if t 3 = 0 then 273 else if t 3 = 1 then 1591 else 1600))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 2172 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1854 else if t 3 = 1 then 1851 else 1092) else (if t 3 = 0 then 3345 else if t 3 = 1 then 876 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1620 else if t 3 = 1 then 1617 else 494) else if t 2 = 1 then (if t 3 = 0 then 1614 else if t 3 = 1 then 1602 else 1606) else (if t 3 = 0 then 296 else if t 3 = 1 then 1604 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 1621 else if t 3 = 1 then 1618 else 495) else if t 2 = 1 then (if t 3 = 0 then 1615 else if t 3 = 1 then 1603 else 1607) else (if t 3 = 0 then 297 else if t 3 = 1 then 1605 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4926 else (if jt.2.val < 2 then 4933 else 4931)) else (if jt.2.val < 4 then 4932 else (if jt.2.val < 5 then 4934 else 4929))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3578 else (if jt.2.val < 2 then 3596 else 3581)) else (if jt.2.val < 4 then 3594 else (if jt.2.val < 5 then 3595 else 3575)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2000 else (if jt.2.val < 2 then 2035 else 2003)) else (if jt.2.val < 4 then 2031 else (if jt.2.val < 5 then 2032 else 1997))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2018 else (if jt.2.val < 2 then 2036 else 2021)) else (if jt.2.val < 4 then 2033 else (if jt.2.val < 5 then 2034 else 2015)))))

checked_coverage fastCoverage0839 pairing0839 template0839 witness0839

theorem coverage0839 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0839) (maskBits m))
    cores template0839 witness0839 := by
  rw [← coresFast_eq]
  exact fastCoverage0839

theorem coverageSize0839 : ∀ q : Pattern,
    (cores (witness0839 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0839 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0839
#print axioms coverageSize0839

end Crown.CertificateData
