import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0012

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0480 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0480 : List (Fin 4935) := templateData0480

noncomputable def witness0480 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3106) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 3003) else (if t 3 = 0 then 2732 else if t 3 = 1 then 2730 else 2743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 868) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 862) else (if t 3 = 0 then 344 else if t 3 = 1 then 340 else 400)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1648 else 1690) else if t 2 = 1 then (if t 3 = 0 then 1650 else if t 3 = 1 then 1646 else 864) else (if t 3 = 0 then 359 else if t 3 = 1 then 357 else 402))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 1213) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 1207) else (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 499)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2956) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3098) else (if t 3 = 0 then 3082 else if t 3 = 1 then 3080 else 3100)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2957) else if t 2 = 1 then (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3099) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3083 else 3101))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 635 else 697) else if t 2 = 1 then (if t 3 = 0 then 638 else if t 3 = 1 then 634 else 691) else (if t 3 = 0 then 1520 else if t 3 = 1 then 1135 else 1525)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2622 else 2652) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3089 else 3102) else (if t 3 = 0 then 3095 else if t 3 = 1 then 3094 else 3104)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2626 else 2653) else if t 2 = 1 then (if t 3 = 0 then 3093 else if t 3 = 1 then 3092 else 3103) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3096 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4611 else (if jt.2.val < 2 then 4615 else 4616)) else (if jt.2.val < 4 then 4612 else (if jt.2.val < 5 then 4614 else 4613))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4315 else (if jt.2.val < 2 then 4319 else 4320)) else (if jt.2.val < 4 then 4316 else (if jt.2.val < 5 then 4318 else 4317)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3385 else (if jt.2.val < 2 then 3389 else 3390)) else (if jt.2.val < 4 then 3386 else (if jt.2.val < 5 then 3388 else 3387))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3042 else (if jt.2.val < 2 then 3044 else 3047)) else (if jt.2.val < 4 then 3043 else (if jt.2.val < 5 then 3046 else 3045)))))

checked_coverage fastCoverage0480 pairing0480 template0480 witness0480

theorem coverage0480 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0480) (maskBits m))
    cores template0480 witness0480 := by
  rw [← coresFast_eq]
  exact fastCoverage0480

theorem coverageSize0480 : ∀ q : Pattern,
    (cores (witness0480 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0480 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0480
#print axioms coverageSize0480

noncomputable def pairing0481 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0481 : List (Fin 4935) := templateData0481

noncomputable def witness0481 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3152) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 3002) else (if t 3 = 0 then 2760 else if t 3 = 1 then 2756 else 2757)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 859) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 853) else (if t 3 = 0 then 292 else if t 3 = 1 then 264 else 269)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1597 else 1599) else if t 2 = 1 then (if t 3 = 0 then 1611 else if t 3 = 1 then 1589 else 855) else (if t 3 = 0 then 299 else if t 3 = 1 then 266 else 271))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 1204) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 1198) else (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 563)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2949) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3130) else (if t 3 = 0 then 3163 else if t 3 = 1 then 3123 else 3132)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2950) else if t 2 = 1 then (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3131) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3124 else 3133))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 760 else 762) else if t 2 = 1 then (if t 3 = 0 then 775 else if t 3 = 1 then 748 else 752) else (if t 3 = 0 then 1550 else if t 3 = 1 then 1105 else 1543)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2697 else 2701) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3126 else 3134) else (if t 3 = 0 then 3167 else if t 3 = 1 then 3128 else 3136)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2698 else 2702) else if t 2 = 1 then (if t 3 = 0 then 3166 else if t 3 = 1 then 3127 else 3135) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3129 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4617 else (if jt.2.val < 2 then 4619 else 4622)) else (if jt.2.val < 4 then 4618 else (if jt.2.val < 5 then 4621 else 4620))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4329 else (if jt.2.val < 2 then 4331 else 4337)) else (if jt.2.val < 4 then 4330 else (if jt.2.val < 5 then 4336 else 4332)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3399 else (if jt.2.val < 2 then 3401 else 3407)) else (if jt.2.val < 4 then 3400 else (if jt.2.val < 5 then 3406 else 3402))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3045 else (if jt.2.val < 2 then 3109 else 3047)) else (if jt.2.val < 4 then 3107 else (if jt.2.val < 5 then 3108 else 3042)))))

checked_coverage fastCoverage0481 pairing0481 template0481 witness0481

theorem coverage0481 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0481) (maskBits m))
    cores template0481 witness0481 := by
  rw [← coresFast_eq]
  exact fastCoverage0481

theorem coverageSize0481 : ∀ q : Pattern,
    (cores (witness0481 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0481 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0481
#print axioms coverageSize0481

noncomputable def pairing0482 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0482 : List (Fin 4935) := templateData0482

noncomputable def witness0482 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2446 else 2506) else if t 2 = 1 then (if t 3 = 0 then 2450 else if t 3 = 1 then 2442 else 2500) else (if t 3 = 0 then 3205 else if t 3 = 1 then 3203 else 3207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2444 else 1756) else if t 2 = 1 then (if t 3 = 0 then 2448 else if t 3 = 1 then 2440 else 1753) else (if t 3 = 0 then 343 else if t 3 = 1 then 339 else 394)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 724 else 790) else if t 2 = 1 then (if t 3 = 0 then 726 else if t 3 = 1 then 722 else 778) else (if t 3 = 0 then 1490 else if t 3 = 1 then 1489 else 1498))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2445 else 1909) else if t 2 = 1 then (if t 3 = 0 then 2449 else if t 3 = 1 then 2441 else 1906) else (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 493)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2443 else 2502) else if t 2 = 1 then (if t 3 = 0 then 2447 else if t 3 = 1 then 2439 else 2492) else (if t 3 = 0 then 2471 else if t 3 = 1 then 2468 else 2494)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2503) else if t 2 = 1 then (if t 3 = 0 then 2462 else if t 3 = 1 then 2459 else 2493) else (if t 3 = 0 then 2475 else if t 3 = 1 then 2473 else 2495))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1583 else 1621) else if t 2 = 1 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1582 else 1618) else (if t 3 = 0 then 473 else if t 3 = 1 then 471 else 495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2897 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2484 else if t 3 = 1 then 2481 else 2496) else (if t 3 = 0 then 2489 else if t 3 = 1 then 2488 else 2498)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2899 else 3184) else if t 2 = 1 then (if t 3 = 0 then 2487 else if t 3 = 1 then 2486 else 2497) else (if t 3 = 0 then 2491 else if t 3 = 1 then 2490 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4623 else (if jt.2.val < 2 then 4627 else 4628)) else (if jt.2.val < 4 then 4624 else (if jt.2.val < 5 then 4626 else 4625))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3691 else (if jt.2.val < 2 then 3695 else 3696)) else (if jt.2.val < 4 then 3692 else (if jt.2.val < 5 then 3694 else 3693)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3387 else (if jt.2.val < 2 then 3411 else 3390)) else (if jt.2.val < 4 then 3408 else (if jt.2.val < 5 then 3409 else 3385))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2430 else (if jt.2.val < 2 then 2432 else 2435)) else (if jt.2.val < 4 then 2431 else (if jt.2.val < 5 then 2434 else 2433)))))

checked_coverage fastCoverage0482 pairing0482 template0482 witness0482

theorem coverage0482 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0482) (maskBits m))
    cores template0482 witness0482 := by
  rw [← coresFast_eq]
  exact fastCoverage0482

theorem coverageSize0482 : ∀ q : Pattern,
    (cores (witness0482 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0482 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0482
#print axioms coverageSize0482

noncomputable def pairing0483 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0483 : List (Fin 4935) := templateData0483

noncomputable def witness0483 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2560 else 2561) else if t 2 = 1 then (if t 3 = 0 then 2565 else if t 3 = 1 then 2544 else 2546) else (if t 3 = 0 then 3215 else if t 3 = 1 then 3209 else 3210)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2558 else 1750) else if t 2 = 1 then (if t 3 = 0 then 2563 else if t 3 = 1 then 2538 else 1747) else (if t 3 = 0 then 291 else if t 3 = 1 then 251 else 256)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 667 else 669) else if t 2 = 1 then (if t 3 = 0 then 681 else if t 3 = 1 then 641 else 646) else (if t 3 = 0 then 1475 else if t 3 = 1 then 1459 else 1462))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2559 else 1903) else if t 2 = 1 then (if t 3 = 0 then 2564 else if t 3 = 1 then 2541 else 1900) else (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 549)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2548 else 2554) else if t 2 = 1 then (if t 3 = 0 then 2562 else if t 3 = 1 then 2519 else 2530) else (if t 3 = 0 then 2572 else if t 3 = 1 then 2523 else 2532)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2555) else if t 2 = 1 then (if t 3 = 0 then 2570 else if t 3 = 1 then 2521 else 2531) else (if t 3 = 0 then 2574 else if t 3 = 1 then 2524 else 2533))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1672 else 1674) else if t 2 = 1 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1666 else 1668) else (if t 3 = 0 then 599 else if t 3 = 1 then 547 else 551)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2878 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2576 else if t 3 = 1 then 2526 else 2534) else (if t 3 = 0 then 2579 else if t 3 = 1 then 2528 else 2536)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2879 else 3197) else if t 2 = 1 then (if t 3 = 0 then 2578 else if t 3 = 1 then 2527 else 2535) else (if t 3 = 0 then 2580 else if t 3 = 1 then 2529 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4629 else (if jt.2.val < 2 then 4631 else 4634)) else (if jt.2.val < 4 then 4630 else (if jt.2.val < 5 then 4633 else 4632))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3705 else (if jt.2.val < 2 then 3707 else 3713)) else (if jt.2.val < 4 then 3706 else (if jt.2.val < 5 then 3712 else 3708)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3402 else (if jt.2.val < 2 then 3424 else 3407)) else (if jt.2.val < 4 then 3423 else (if jt.2.val < 5 then 3425 else 3399))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2433 else (if jt.2.val < 2 then 2509 else 2435)) else (if jt.2.val < 4 then 2507 else (if jt.2.val < 5 then 2508 else 2430)))))

checked_coverage fastCoverage0483 pairing0483 template0483 witness0483

theorem coverage0483 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0483) (maskBits m))
    cores template0483 witness0483 := by
  rw [← coresFast_eq]
  exact fastCoverage0483

theorem coverageSize0483 : ∀ q : Pattern,
    (cores (witness0483 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0483 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0483
#print axioms coverageSize0483

noncomputable def pairing0484 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0484 : List (Fin 4935) := templateData0484

noncomputable def witness0484 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 1376) else if t 2 = 1 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 1211) else (if t 3 = 0 then 452 else if t 3 = 1 then 448 else 503)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 1001) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1370) else (if t 3 = 0 then 1342 else if t 3 = 1 then 1339 else 1371)) else (if t 2 = 0 then (if t 3 = 0 then 3236 else if t 3 = 1 then 3234 else 3242) else if t 2 = 1 then (if t 3 = 0 then 3235 else if t 3 = 1 then 3232 else 2860) else (if t 3 = 0 then 2691 else if t 3 = 1 then 2689 else 2722))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 1374) else if t 2 = 1 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 1208) else (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 500)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 998) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1362) else (if t 3 = 0 then 1341 else if t 3 = 1 then 1338 else 1364)) else (if t 2 = 0 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 999) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1363) else (if t 3 = 0 then 1344 else if t 3 = 1 then 1343 else 1365))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1785 else 2782) else if t 2 = 1 then (if t 3 = 0 then 647 else if t 3 = 1 then 643 else 692) else (if t 3 = 0 then 3206 else if t 3 = 1 then 1137 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 257 else if t 3 = 1 then 253 else 302) else if t 2 = 1 then (if t 3 = 0 then 1352 else if t 3 = 1 then 1349 else 1366) else (if t 3 = 0 then 1358 else if t 3 = 1 then 1356 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 262 else if t 3 = 1 then 260 else 303) else if t 2 = 1 then (if t 3 = 0 then 1355 else if t 3 = 1 then 1354 else 1367) else (if t 3 = 0 then 1361 else if t 3 = 1 then 1360 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4629 else (if jt.2.val < 2 then 4637 else 4634)) else (if jt.2.val < 4 then 4635 else (if jt.2.val < 5 then 4636 else 4632))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4317 else (if jt.2.val < 2 then 4352 else 4320)) else (if jt.2.val < 4 then 4350 else (if jt.2.val < 5 then 4351 else 4315)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1972 else (if jt.2.val < 2 then 1976 else 1977)) else (if jt.2.val < 4 then 1973 else (if jt.2.val < 5 then 1975 else 1974))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1296 else (if jt.2.val < 2 then 1298 else 1301)) else (if jt.2.val < 4 then 1297 else (if jt.2.val < 5 then 1300 else 1299)))))

checked_coverage fastCoverage0484 pairing0484 template0484 witness0484

theorem coverage0484 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0484) (maskBits m))
    cores template0484 witness0484 := by
  rw [← coresFast_eq]
  exact fastCoverage0484

theorem coverageSize0484 : ∀ q : Pattern,
    (cores (witness0484 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0484 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0484
#print axioms coverageSize0484

noncomputable def pairing0485 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0485 : List (Fin 4935) := templateData0485

noncomputable def witness0485 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 1433) else if t 2 = 1 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 1202) else (if t 3 = 0 then 591 else if t 3 = 1 then 567 else 569)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 992) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1414) else (if t 3 = 0 then 1447 else if t 3 = 1 then 1411 else 1415)) else (if t 2 = 0 then (if t 3 = 0 then 3228 else if t 3 = 1 then 3225 else 3226) else if t 2 = 1 then (if t 3 = 0 then 3227 else if t 3 = 1 then 3219 else 2855) else (if t 3 = 0 then 2649 else if t 3 = 1 then 2630 else 2633))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 1430) else if t 2 = 1 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 1199) else (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 564)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 989) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1400) else (if t 3 = 0 then 1446 else if t 3 = 1 then 1393 else 1402)) else (if t 2 = 0 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 990) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1401) else (if t 3 = 0 then 1448 else if t 3 = 1 then 1394 else 1403))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1773 else 2796) else if t 2 = 1 then (if t 3 = 0 then 779 else if t 3 = 1 then 749 else 753) else (if t 3 = 0 then 3216 else if t 3 = 1 then 1106 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 395 else if t 3 = 1 then 365 else 369) else if t 2 = 1 then (if t 3 = 0 then 1449 else if t 3 = 1 then 1396 else 1404) else (if t 3 = 0 then 1452 else if t 3 = 1 then 1398 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 398 else if t 3 = 1 then 366 else 370) else if t 2 = 1 then (if t 3 = 0 then 1451 else if t 3 = 1 then 1397 else 1405) else (if t 3 = 0 then 1454 else if t 3 = 1 then 1399 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4623 else (if jt.2.val < 2 then 4639 else 4628)) else (if jt.2.val < 4 then 4638 else (if jt.2.val < 5 then 4640 else 4625))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4332 else (if jt.2.val < 2 then 4360 else 4337)) else (if jt.2.val < 4 then 4359 else (if jt.2.val < 5 then 4361 else 4329)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1986 else (if jt.2.val < 2 then 1988 else 1994)) else (if jt.2.val < 4 then 1987 else (if jt.2.val < 5 then 1993 else 1989))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1299 else (if jt.2.val < 2 then 1379 else 1301)) else (if jt.2.val < 4 then 1377 else (if jt.2.val < 5 then 1378 else 1296)))))

checked_coverage fastCoverage0485 pairing0485 template0485 witness0485

theorem coverage0485 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0485) (maskBits m))
    cores template0485 witness0485 := by
  rw [← coresFast_eq]
  exact fastCoverage0485

theorem coverageSize0485 : ∀ q : Pattern,
    (cores (witness0485 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0485 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0485
#print axioms coverageSize0485

noncomputable def pairing0486 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0486 : List (Fin 4935) := templateData0486

noncomputable def witness0486 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 16 else 104) else if t 2 = 1 then (if t 3 = 0 then 20 else if t 3 = 1 then 12 else 94) else (if t 3 = 0 then 1510 else if t 3 = 1 then 1507 else 1523)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 22 else if t 3 = 1 then 14 else 100) else if t 2 = 1 then (if t 3 = 0 then 18 else if t 3 = 1 then 10 else 86) else (if t 3 = 0 then 48 else if t 3 = 1 then 43 else 87)) else (if t 2 = 0 then (if t 3 = 0 then 2789 else if t 3 = 1 then 2787 else 2800) else if t 2 = 1 then (if t 3 = 0 then 2788 else if t 3 = 1 then 2785 else 2797) else (if t 3 = 0 then 3192 else if t 3 = 1 then 3191 else 3198))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 15 else 102) else if t 2 = 1 then (if t 3 = 0 then 19 else if t 3 = 1 then 11 else 90) else (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 21 else if t 3 = 1 then 13 else 96) else if t 2 = 1 then (if t 3 = 0 then 17 else if t 3 = 1 then 9 else 78) else (if t 3 = 0 then 47 else if t 3 = 1 then 42 else 80)) else (if t 2 = 0 then (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 97) else if t 2 = 1 then (if t 3 = 0 then 34 else if t 3 = 1 then 29 else 79) else (if t 3 = 0 then 53 else if t 3 = 1 then 51 else 81))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 917 else 3229) else if t 2 = 1 then (if t 3 = 0 then 66 else if t 3 = 1 then 61 else 92) else (if t 3 = 0 then 2739 else if t 3 = 1 then 1848 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1470 else if t 3 = 1 then 915 else 1476) else if t 2 = 1 then (if t 3 = 0 then 64 else if t 3 = 1 then 59 else 82) else (if t 3 = 0 then 74 else if t 3 = 1 then 72 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 1472 else if t 3 = 1 then 919 else 1477) else if t 2 = 1 then (if t 3 = 0 then 70 else if t 3 = 1 then 68 else 83) else (if t 3 = 0 then 77 else if t 3 = 1 then 76 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4617 else (if jt.2.val < 2 then 4643 else 4622)) else (if jt.2.val < 4 then 4641 else (if jt.2.val < 5 then 4642 else 4620))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3693 else (if jt.2.val < 2 then 3740 else 3696)) else (if jt.2.val < 4 then 3738 else (if jt.2.val < 5 then 3739 else 3691)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1974 else (if jt.2.val < 2 then 1998 else 1977)) else (if jt.2.val < 4 then 1995 else (if jt.2.val < 5 then 1996 else 1972))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 0 else (if jt.2.val < 2 then 2 else 5)) else (if jt.2.val < 4 then 1 else (if jt.2.val < 5 then 4 else 3)))))

checked_coverage fastCoverage0486 pairing0486 template0486 witness0486

theorem coverage0486 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0486) (maskBits m))
    cores template0486 witness0486 := by
  rw [← coresFast_eq]
  exact fastCoverage0486

theorem coverageSize0486 : ∀ q : Pattern,
    (cores (witness0486 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0486 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0486
#print axioms coverageSize0486

noncomputable def pairing0487 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0487 : List (Fin 4935) := templateData0487

noncomputable def witness0487 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 178 else 179) else if t 2 = 1 then (if t 3 = 0 then 183 else if t 3 = 1 then 156 else 158) else (if t 3 = 0 then 1546 else if t 3 = 1 then 1537 else 1538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 185 else if t 3 = 1 then 170 else 172) else if t 2 = 1 then (if t 3 = 0 then 181 else if t 3 = 1 then 136 else 142) else (if t 3 = 0 then 193 else if t 3 = 1 then 139 else 143)) else (if t 2 = 0 then (if t 3 = 0 then 2779 else if t 3 = 1 then 2775 else 2776) else if t 2 = 1 then (if t 3 = 0 then 2778 else if t 3 = 1 then 2766 else 2769) else (if t 3 = 0 then 3182 else if t 3 = 1 then 3172 else 3174))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 174 else 176) else if t 2 = 1 then (if t 3 = 0 then 182 else if t 3 = 1 then 146 else 152) else (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1535)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 184 else if t 3 = 1 then 160 else 166) else if t 2 = 1 then (if t 3 = 0 then 180 else if t 3 = 1 then 117 else 128) else (if t 3 = 0 then 192 else if t 3 = 1 then 121 else 130)) else (if t 2 = 0 then (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 167) else if t 2 = 1 then (if t 3 = 0 then 188 else if t 3 = 1 then 119 else 129) else (if t 3 = 0 then 196 else if t 3 = 1 then 122 else 131))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 894 else 3240) else if t 2 = 1 then (if t 3 = 0 then 200 else if t 3 = 1 then 150 else 154) else (if t 3 = 0 then 2763 else if t 3 = 1 then 1833 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1500 else if t 3 = 1 then 888 else 1494) else if t 2 = 1 then (if t 3 = 0 then 198 else if t 3 = 1 then 124 else 132) else (if t 3 = 0 then 204 else if t 3 = 1 then 126 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 1502 else if t 3 = 1 then 889 else 1495) else if t 2 = 1 then (if t 3 = 0 then 202 else if t 3 = 1 then 125 else 133) else (if t 3 = 0 then 206 else if t 3 = 1 then 127 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4611 else (if jt.2.val < 2 then 4645 else 4616)) else (if jt.2.val < 4 then 4644 else (if jt.2.val < 5 then 4646 else 4613))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3708 else (if jt.2.val < 2 then 3748 else 3713)) else (if jt.2.val < 4 then 3747 else (if jt.2.val < 5 then 3749 else 3705)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1989 else (if jt.2.val < 2 then 2011 else 1994)) else (if jt.2.val < 4 then 2010 else (if jt.2.val < 5 then 2012 else 1986))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3 else (if jt.2.val < 2 then 107 else 5)) else (if jt.2.val < 4 then 105 else (if jt.2.val < 5 then 106 else 0)))))

checked_coverage fastCoverage0487 pairing0487 template0487 witness0487

theorem coverage0487 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0487) (maskBits m))
    cores template0487 witness0487 := by
  rw [← coresFast_eq]
  exact fastCoverage0487

theorem coverageSize0487 : ∀ q : Pattern,
    (cores (witness0487 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0487 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0487
#print axioms coverageSize0487

noncomputable def pairing0488 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0488 : List (Fin 4935) := templateData0488

noncomputable def witness0488 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3215) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2759) else (if t 3 = 0 then 2732 else if t 3 = 1 then 2731 else 2985)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 291) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 290) else (if t 3 = 0 then 344 else if t 3 = 1 then 342 else 928)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2197 else 1475) else if t 2 = 1 then (if t 3 = 0 then 2199 else if t 3 = 1 then 2195 else 298) else (if t 3 = 0 then 359 else if t 3 = 1 then 358 else 932))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 585) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 584) else (if t 3 = 0 then 442 else if t 3 = 1 then 440 else 1117)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2572) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3488) else (if t 3 = 0 then 3082 else if t 3 = 1 then 3479 else 3492)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2574) else if t 2 = 1 then (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3489) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3480 else 3493))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1042 else 599) else if t 2 = 1 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1041 else 598) else (if t 3 = 0 then 1520 else if t 3 = 1 then 472 else 2149)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2838 else 2579) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3472 else 3490) else (if t 3 = 0 then 3095 else if t 3 = 1 then 3486 else 3494)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2842 else 2580) else if t 2 = 1 then (if t 3 = 0 then 3280 else if t 3 = 1 then 3473 else 3491) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3487 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4647 else (if jt.2.val < 2 then 4657 else 4658)) else (if jt.2.val < 4 then 4654 else (if jt.2.val < 5 then 4656 else 4655))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4648 else (if jt.2.val < 2 then 4652 else 4653)) else (if jt.2.val < 4 then 4649 else (if jt.2.val < 5 then 4651 else 4650)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3439 else (if jt.2.val < 2 then 3477 else 3478)) else (if jt.2.val < 4 then 3474 else (if jt.2.val < 5 then 3476 else 3475))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3438 else (if jt.2.val < 2 then 3482 else 3485)) else (if jt.2.val < 4 then 3481 else (if jt.2.val < 5 then 3484 else 3483)))))

checked_coverage fastCoverage0488 pairing0488 template0488 witness0488

theorem coverage0488 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0488) (maskBits m))
    cores template0488 witness0488 := by
  rw [← coresFast_eq]
  exact fastCoverage0488

theorem coverageSize0488 : ∀ q : Pattern,
    (cores (witness0488 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0488 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0488
#print axioms coverageSize0488

noncomputable def pairing0489 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0489 : List (Fin 4935) := templateData0489

noncomputable def witness0489 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3499) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 2756) else (if t 3 = 0 then 3004 else if t 3 = 1 then 3002 else 2757)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 277) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 264) else (if t 3 = 0 then 874 else if t 3 = 1 then 853 else 269)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1597 else 2170) else if t 2 = 1 then (if t 3 = 0 then 1611 else if t 3 = 1 then 1589 else 266) else (if t 3 = 0 then 878 else if t 3 = 1 then 855 else 271))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 571) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 557) else (if t 3 = 0 then 1219 else if t 3 = 1 then 1198 else 563)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2550) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3123) else (if t 3 = 0 then 3313 else if t 3 = 1 then 3130 else 3132)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2551) else if t 2 = 1 then (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3124) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3131 else 3133))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 760 else 1111) else if t 2 = 1 then (if t 3 = 0 then 775 else if t 3 = 1 then 748 else 1105) else (if t 3 = 0 then 2162 else if t 3 = 1 then 752 else 1543)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2697 else 2880) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3126 else 3128) else (if t 3 = 0 then 3500 else if t 3 = 1 then 3134 else 3136)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2698 else 2881) else if t 2 = 1 then (if t 3 = 0 then 3166 else if t 3 = 1 then 3127 else 3129) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3135 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4617 else (if jt.2.val < 2 then 4619 else 4622)) else (if jt.2.val < 4 then 4618 else (if jt.2.val < 5 then 4621 else 4620))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4329 else (if jt.2.val < 2 then 4331 else 4337)) else (if jt.2.val < 4 then 4330 else (if jt.2.val < 5 then 4336 else 4332)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3305 else (if jt.2.val < 2 then 3307 else 3311)) else (if jt.2.val < 4 then 3306 else (if jt.2.val < 5 then 3310 else 3309))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3483 else (if jt.2.val < 2 then 3498 else 3485)) else (if jt.2.val < 4 then 3496 else (if jt.2.val < 5 then 3497 else 3438)))))

checked_coverage fastCoverage0489 pairing0489 template0489 witness0489

theorem coverage0489 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0489) (maskBits m))
    cores template0489 witness0489 := by
  rw [← coresFast_eq]
  exact fastCoverage0489

theorem coverageSize0489 : ∀ q : Pattern,
    (cores (witness0489 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0489 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0489
#print axioms coverageSize0489

noncomputable def pairing0490 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0490 : List (Fin 4935) := templateData0490

noncomputable def witness0490 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2450 else 2884) else if t 2 = 1 then (if t 3 = 0 then 2446 else if t 3 = 1 then 2442 else 2500) else (if t 3 = 0 then 3505 else if t 3 = 1 then 3203 else 3207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2448 else 1762) else if t 2 = 1 then (if t 3 = 0 then 2444 else if t 3 = 1 then 2440 else 1753) else (if t 3 = 0 then 341 else if t 3 = 1 then 339 else 394)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 726 else 1145) else if t 2 = 1 then (if t 3 = 0 then 724 else if t 3 = 1 then 722 else 778) else (if t 3 = 0 then 2159 else if t 3 = 1 then 1489 else 1498))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2449 else 1915) else if t 2 = 1 then (if t 3 = 0 then 2445 else if t 3 = 1 then 2441 else 1906) else (if t 3 = 0 then 439 else if t 3 = 1 then 437 else 493)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2447 else 2883) else if t 2 = 1 then (if t 3 = 0 then 2443 else if t 3 = 1 then 2439 else 2492) else (if t 3 = 0 then 2470 else if t 3 = 1 then 2468 else 2494)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2885) else if t 2 = 1 then (if t 3 = 0 then 2461 else if t 3 = 1 then 2459 else 2493) else (if t 3 = 0 then 2474 else if t 3 = 1 then 2473 else 2495))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1586 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1582 else 1618) else (if t 3 = 0 then 1136 else if t 3 = 1 then 471 else 495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2484 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2897 else if t 3 = 1 then 2481 else 2496) else (if t 3 = 0 then 2900 else if t 3 = 1 then 2488 else 2498)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2487 else 3507) else if t 2 = 1 then (if t 3 = 0 then 2899 else if t 3 = 1 then 2486 else 2497) else (if t 3 = 0 then 2901 else if t 3 = 1 then 2490 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4623 else (if jt.2.val < 2 then 4627 else 4628)) else (if jt.2.val < 4 then 4624 else (if jt.2.val < 5 then 4626 else 4625))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3691 else (if jt.2.val < 2 then 3695 else 3696)) else (if jt.2.val < 4 then 3692 else (if jt.2.val < 5 then 3694 else 3693)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3475 else (if jt.2.val < 2 then 3504 else 3478)) else (if jt.2.val < 4 then 3502 else (if jt.2.val < 5 then 3503 else 3439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3020 else (if jt.2.val < 2 then 3022 else 3025)) else (if jt.2.val < 4 then 3021 else (if jt.2.val < 5 then 3024 else 3023)))))

checked_coverage fastCoverage0490 pairing0490 template0490 witness0490

theorem coverage0490 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0490) (maskBits m))
    cores template0490 witness0490 := by
  rw [← coresFast_eq]
  exact fastCoverage0490

theorem coverageSize0490 : ∀ q : Pattern,
    (cores (witness0490 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0490 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0490
#print axioms coverageSize0490

noncomputable def pairing0491 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0491 : List (Fin 4935) := templateData0491

noncomputable def witness0491 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2953 else 2561) else if t 2 = 1 then (if t 3 = 0 then 2960 else if t 3 = 1 then 2937 else 2938) else (if t 3 = 0 then 3106 else if t 3 = 1 then 3329 else 3514)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2951 else 1750) else if t 2 = 1 then (if t 3 = 0 then 2958 else if t 3 = 1 then 2931 else 1730) else (if t 3 = 0 then 868 else if t 3 = 1 then 830 else 833)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1075 else 669) else if t 2 = 1 then (if t 3 = 0 then 1084 else if t 3 = 1 then 1046 else 1049) else (if t 3 = 0 then 1690 else if t 3 = 1 then 1813 else 2146))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2952 else 1903) else if t 2 = 1 then (if t 3 = 0 then 2959 else if t 3 = 1 then 2934 else 1888) else (if t 3 = 0 then 1213 else if t 3 = 1 then 1180 else 1182)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2947 else 2554) else if t 2 = 1 then (if t 3 = 0 then 2954 else if t 3 = 1 then 2913 else 2919) else (if t 3 = 0 then 2956 else if t 3 = 1 then 2917 else 2921)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2555) else if t 2 = 1 then (if t 3 = 0 then 2955 else if t 3 = 1 then 2915 else 2920) else (if t 3 = 0 then 2957 else if t 3 = 1 then 2918 else 2922))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2218 else 1674) else if t 2 = 1 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2206 else 1890) else (if t 3 = 0 then 697 else if t 3 = 1 then 1184 else 1186)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2699 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2650 else if t 3 = 1 then 2923 else 2927) else (if t 3 = 0 then 2652 else if t 3 = 1 then 2925 else 2929)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2700 else 3197) else if t 2 = 1 then (if t 3 = 0 then 2651 else if t 3 = 1 then 2924 else 2928) else (if t 3 = 0 then 2653 else if t 3 = 1 then 2926 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4659 else (if jt.2.val < 2 then 4661 else 4664)) else (if jt.2.val < 4 then 4660 else (if jt.2.val < 5 then 4663 else 4662))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3777 else (if jt.2.val < 2 then 3779 else 3785)) else (if jt.2.val < 4 then 3778 else (if jt.2.val < 5 then 3784 else 3780)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3309 else (if jt.2.val < 2 then 3332 else 3311)) else (if jt.2.val < 4 then 3331 else (if jt.2.val < 5 then 3333 else 3305))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3023 else (if jt.2.val < 2 then 3040 else 3025)) else (if jt.2.val < 4 then 3036 else (if jt.2.val < 5 then 3037 else 3020)))))

checked_coverage fastCoverage0491 pairing0491 template0491 witness0491

theorem coverage0491 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0491) (maskBits m))
    cores template0491 witness0491 := by
  rw [← coresFast_eq]
  exact fastCoverage0491

theorem coverageSize0491 : ∀ q : Pattern,
    (cores (witness0491 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0491 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0491
#print axioms coverageSize0491

noncomputable def pairing0492 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0492 : List (Fin 4935) := templateData0492

noncomputable def witness0492 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1546) else if t 2 = 1 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 589) else (if t 3 = 0 then 452 else if t 3 = 1 then 450 else 1120)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 193) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2101) else (if t 3 = 0 then 1342 else if t 3 = 1 then 2090 else 2107)) else (if t 2 = 0 then (if t 3 = 0 then 3532 else if t 3 = 1 then 3530 else 3182) else if t 2 = 1 then (if t 3 = 0 then 3531 else if t 3 = 1 then 3528 else 2648) else (if t 3 = 0 then 2691 else if t 3 = 1 then 2690 else 2906))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1545) else if t 2 = 1 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 588) else (if t 3 = 0 then 451 else if t 3 = 1 then 449 else 1119)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 192) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2100) else (if t 3 = 0 then 1341 else if t 3 = 1 then 2089 else 2106)) else (if t 2 = 0 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 196) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2102) else (if t 3 = 0 then 1344 else if t 3 = 1 then 2091 else 2108))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 1815 else 2763) else if t 2 = 1 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1050 else 600) else (if t 3 = 0 then 3206 else if t 3 = 1 then 476 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 836 else if t 3 = 1 then 834 else 204) else if t 2 = 1 then (if t 3 = 0 then 1732 else if t 3 = 1 then 2081 else 2103) else (if t 3 = 0 then 1358 else if t 3 = 1 then 2097 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 841 else if t 3 = 1 then 840 else 206) else if t 2 = 1 then (if t 3 = 0 then 1735 else if t 3 = 1 then 2083 else 2105) else (if t 3 = 0 then 1361 else if t 3 = 1 then 2099 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4659 else (if jt.2.val < 2 then 4670 else 4664)) else (if jt.2.val < 4 then 4668 else (if jt.2.val < 5 then 4669 else 4662))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4650 else (if jt.2.val < 2 then 4667 else 4653)) else (if jt.2.val < 4 then 4665 else (if jt.2.val < 5 then 4666 else 4648)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2044 else (if jt.2.val < 2 then 2087 else 2088)) else (if jt.2.val < 4 then 2084 else (if jt.2.val < 5 then 2086 else 2085))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2043 else (if jt.2.val < 2 then 2093 else 2096)) else (if jt.2.val < 4 then 2092 else (if jt.2.val < 5 then 2095 else 2094)))))

checked_coverage fastCoverage0492 pairing0492 template0492 witness0492

theorem coverage0492 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0492) (maskBits m))
    cores template0492 witness0492 := by
  rw [← coresFast_eq]
  exact fastCoverage0492

theorem coverageSize0492 : ∀ q : Pattern,
    (cores (witness0492 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0492 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0492
#print axioms coverageSize0492

noncomputable def pairing0493 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0493 : List (Fin 4935) := templateData0493

noncomputable def witness0493 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 2117) else if t 2 = 1 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 567) else (if t 3 = 0 then 1222 else if t 3 = 1 then 1202 else 569)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 171) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1411) else (if t 3 = 0 then 1777 else if t 3 = 1 then 1414 else 1415)) else (if t 2 = 0 then (if t 3 = 0 then 3228 else if t 3 = 1 then 3225 else 3524) else if t 2 = 1 then (if t 3 = 0 then 3227 else if t 3 = 1 then 3219 else 2630) else (if t 3 = 0 then 2868 else if t 3 = 1 then 2855 else 2633))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 2115) else if t 2 = 1 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 558) else (if t 3 = 0 then 1221 else if t 3 = 1 then 1199 else 564)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 162) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1393) else (if t 3 = 0 then 1776 else if t 3 = 1 then 1400 else 1402)) else (if t 2 = 0 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 163) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1394) else (if t 3 = 0 then 1778 else if t 3 = 1 then 1401 else 1403))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1773 else 2984) else if t 2 = 1 then (if t 3 = 0 then 779 else if t 3 = 1 then 749 else 1106) else (if t 3 = 0 then 3523 else if t 3 = 1 then 753 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 395 else if t 3 = 1 then 365 else 890) else if t 2 = 1 then (if t 3 = 0 then 1449 else if t 3 = 1 then 1396 else 1398) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1404 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 398 else if t 3 = 1 then 366 else 891) else if t 2 = 1 then (if t 3 = 0 then 1451 else if t 3 = 1 then 1397 else 1399) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1405 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4623 else (if jt.2.val < 2 then 4639 else 4628)) else (if jt.2.val < 4 then 4638 else (if jt.2.val < 5 then 4640 else 4625))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4332 else (if jt.2.val < 2 then 4360 else 4337)) else (if jt.2.val < 4 then 4359 else (if jt.2.val < 5 then 4361 else 4329)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1766 else (if jt.2.val < 2 then 1768 else 1772)) else (if jt.2.val < 4 then 1767 else (if jt.2.val < 5 then 1771 else 1770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2094 else (if jt.2.val < 2 then 2114 else 2096)) else (if jt.2.val < 4 then 2112 else (if jt.2.val < 5 then 2113 else 2043)))))

checked_coverage fastCoverage0493 pairing0493 template0493 witness0493

theorem coverage0493 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0493) (maskBits m))
    cores template0493 witness0493 := by
  rw [← coresFast_eq]
  exact fastCoverage0493

theorem coverageSize0493 : ∀ q : Pattern,
    (cores (witness0493 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0493 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0493
#print axioms coverageSize0493

noncomputable def pairing0494 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0494 : List (Fin 4935) := templateData0494

noncomputable def witness0494 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 20 else 900) else if t 2 = 1 then (if t 3 = 0 then 16 else if t 3 = 1 then 12 else 94) else (if t 3 = 0 then 2125 else if t 3 = 1 then 1507 else 1523)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 22 else if t 3 = 1 then 18 else 898) else if t 2 = 1 then (if t 3 = 0 then 14 else if t 3 = 1 then 10 else 86) else (if t 3 = 0 then 46 else if t 3 = 1 then 43 else 87)) else (if t 2 = 0 then (if t 3 = 0 then 2789 else if t 3 = 1 then 2788 else 2989) else if t 2 = 1 then (if t 3 = 0 then 2787 else if t 3 = 1 then 2785 else 2797) else (if t 3 = 0 then 3522 else if t 3 = 1 then 3191 else 3198))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 19 else 899) else if t 2 = 1 then (if t 3 = 0 then 15 else if t 3 = 1 then 11 else 90) else (if t 3 = 0 then 2124 else if t 3 = 1 then 1506 else 1521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 21 else if t 3 = 1 then 17 else 897) else if t 2 = 1 then (if t 3 = 0 then 13 else if t 3 = 1 then 9 else 78) else (if t 3 = 0 then 45 else if t 3 = 1 then 42 else 80)) else (if t 2 = 0 then (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 901) else if t 2 = 1 then (if t 3 = 0 then 32 else if t 3 = 1 then 29 else 79) else (if t 3 = 0 then 52 else if t 3 = 1 then 51 else 81))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 66 else 3525) else if t 2 = 1 then (if t 3 = 0 then 917 else if t 3 = 1 then 61 else 92) else (if t 3 = 0 then 2988 else if t 3 = 1 then 1848 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1470 else if t 3 = 1 then 64 else 2127) else if t 2 = 1 then (if t 3 = 0 then 915 else if t 3 = 1 then 59 else 82) else (if t 3 = 0 then 921 else if t 3 = 1 then 72 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 1472 else if t 3 = 1 then 70 else 2128) else if t 2 = 1 then (if t 3 = 0 then 919 else if t 3 = 1 then 68 else 83) else (if t 3 = 0 then 923 else if t 3 = 1 then 76 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4617 else (if jt.2.val < 2 then 4643 else 4622)) else (if jt.2.val < 4 then 4641 else (if jt.2.val < 5 then 4642 else 4620))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3693 else (if jt.2.val < 2 then 3740 else 3696)) else (if jt.2.val < 4 then 3738 else (if jt.2.val < 5 then 3739 else 3691)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2085 else (if jt.2.val < 2 then 2123 else 2088)) else (if jt.2.val < 4 then 2121 else (if jt.2.val < 5 then 2122 else 2044))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1238 else (if jt.2.val < 2 then 1240 else 1243)) else (if jt.2.val < 4 then 1239 else (if jt.2.val < 5 then 1242 else 1241)))))

checked_coverage fastCoverage0494 pairing0494 template0494 witness0494

theorem coverage0494 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0494) (maskBits m))
    cores template0494 witness0494 := by
  rw [← coresFast_eq]
  exact fastCoverage0494

theorem coverageSize0494 : ∀ q : Pattern,
    (cores (witness0494 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0494 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0494
#print axioms coverageSize0494

noncomputable def pairing0495 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0495 : List (Fin 4935) := templateData0495

noncomputable def witness0495 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 995 else 179) else if t 2 = 1 then (if t 3 = 0 then 1004 else if t 3 = 1 then 977 else 978) else (if t 3 = 0 then 1376 else if t 3 = 1 then 1801 else 2138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1006 else if t 3 = 1 then 991 else 172) else if t 2 = 1 then (if t 3 = 0 then 1000 else if t 3 = 1 then 957 else 961) else (if t 3 = 0 then 1001 else if t 3 = 1 then 960 else 962)) else (if t 2 = 0 then (if t 3 = 0 then 2981 else if t 3 = 1 then 2979 else 2776) else if t 2 = 1 then (if t 3 = 0 then 2980 else if t 3 = 1 then 2970 else 2972) else (if t 3 = 0 then 3242 else if t 3 = 1 then 3338 else 3520))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 993 else 176) else if t 2 = 1 then (if t 3 = 0 then 1002 else if t 3 = 1 then 967 else 971) else (if t 3 = 0 then 1374 else if t 3 = 1 then 1795 else 2136)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1005 else if t 3 = 1 then 987 else 166) else if t 2 = 1 then (if t 3 = 0 then 996 else if t 3 = 1 then 939 else 945) else (if t 3 = 0 then 998 else if t 3 = 1 then 943 else 947)) else (if t 2 = 0 then (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 167) else if t 2 = 1 then (if t 3 = 0 then 997 else if t 3 = 1 then 941 else 946) else (if t 3 = 0 then 999 else if t 3 = 1 then 944 else 948))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 377 else 3240) else if t 2 = 1 then (if t 3 = 0 then 306 else if t 3 = 1 then 973 else 975) else (if t 3 = 0 then 2782 else if t 3 = 1 then 1799 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2139 else if t 3 = 1 then 367 else 1494) else if t 2 = 1 then (if t 3 = 0 then 300 else if t 3 = 1 then 949 else 953) else (if t 3 = 0 then 302 else if t 3 = 1 then 951 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 2141 else if t 3 = 1 then 368 else 1495) else if t 2 = 1 then (if t 3 = 0 then 301 else if t 3 = 1 then 950 else 954) else (if t 3 = 0 then 303 else if t 3 = 1 then 952 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4647 else (if jt.2.val < 2 then 4672 else 4658)) else (if jt.2.val < 4 then 4671 else (if jt.2.val < 5 then 4673 else 4655))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3780 else (if jt.2.val < 2 then 3796 else 3785)) else (if jt.2.val < 4 then 3795 else (if jt.2.val < 5 then 3797 else 3777)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1770 else (if jt.2.val < 2 then 1804 else 1772)) else (if jt.2.val < 4 then 1803 else (if jt.2.val < 5 then 1805 else 1766))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1241 else (if jt.2.val < 2 then 1258 else 1243)) else (if jt.2.val < 4 then 1254 else (if jt.2.val < 5 then 1255 else 1238)))))

checked_coverage fastCoverage0495 pairing0495 template0495 witness0495

theorem coverage0495 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0495) (maskBits m))
    cores template0495 witness0495 := by
  rw [← coresFast_eq]
  exact fastCoverage0495

theorem coverageSize0495 : ∀ q : Pattern,
    (cores (witness0495 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0495 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0495
#print axioms coverageSize0495

noncomputable def pairing0496 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0496 : List (Fin 4935) := templateData0496

noncomputable def witness0496 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3205) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2731) else (if t 3 = 0 then 2760 else if t 3 = 1 then 2759 else 2985)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 343) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 342) else (if t 3 = 0 then 292 else if t 3 = 1 then 290 else 928)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2197 else 1490) else if t 2 = 1 then (if t 3 = 0 then 2199 else if t 3 = 1 then 2195 else 358) else (if t 3 = 0 then 299 else if t 3 = 1 then 298 else 932))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 441) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 440) else (if t 3 = 0 then 586 else if t 3 = 1 then 584 else 1117)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2471) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3479) else (if t 3 = 0 then 3163 else if t 3 = 1 then 3488 else 3492)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2475) else if t 2 = 1 then (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3480) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3489 else 3493))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1042 else 473) else if t 2 = 1 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1041 else 472) else (if t 3 = 0 then 1550 else if t 3 = 1 then 598 else 2149)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2838 else 2489) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3472 else 3486) else (if t 3 = 0 then 3167 else if t 3 = 1 then 3490 else 3494)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2842 else 2491) else if t 2 = 1 then (if t 3 = 0 then 3280 else if t 3 = 1 then 3473 else 3487) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3491 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4647 else (if jt.2.val < 2 then 4657 else 4658)) else (if jt.2.val < 4 then 4654 else (if jt.2.val < 5 then 4656 else 4655))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4648 else (if jt.2.val < 2 then 4652 else 4653)) else (if jt.2.val < 4 then 4649 else (if jt.2.val < 5 then 4651 else 4650)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3537 else (if jt.2.val < 2 then 3545 else 3548)) else (if jt.2.val < 4 then 3544 else (if jt.2.val < 5 then 3547 else 3546))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3538 else (if jt.2.val < 2 then 3542 else 3543)) else (if jt.2.val < 4 then 3539 else (if jt.2.val < 5 then 3541 else 3540)))))

checked_coverage fastCoverage0496 pairing0496 template0496 witness0496

theorem coverage0496 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0496) (maskBits m))
    cores template0496 witness0496 := by
  rw [← coresFast_eq]
  exact fastCoverage0496

theorem coverageSize0496 : ∀ q : Pattern,
    (cores (witness0496 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0496 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0496
#print axioms coverageSize0496

noncomputable def pairing0497 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0497 : List (Fin 4935) := templateData0497

noncomputable def witness0497 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3505) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 2730) else (if t 3 = 0 then 3004 else if t 3 = 1 then 3003 else 2743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 341) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 340) else (if t 3 = 0 then 874 else if t 3 = 1 then 862 else 400)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1648 else 2159) else if t 2 = 1 then (if t 3 = 0 then 1650 else if t 3 = 1 then 1646 else 357) else (if t 3 = 0 then 878 else if t 3 = 1 then 864 else 402))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 439) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 438) else (if t 3 = 0 then 1219 else if t 3 = 1 then 1207 else 499)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2470) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3080) else (if t 3 = 0 then 3313 else if t 3 = 1 then 3098 else 3100)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2474) else if t 2 = 1 then (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3083) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3099 else 3101))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 635 else 1136) else if t 2 = 1 then (if t 3 = 0 then 638 else if t 3 = 1 then 634 else 1135) else (if t 3 = 0 then 2162 else if t 3 = 1 then 691 else 1525)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2622 else 2900) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3089 else 3094) else (if t 3 = 0 then 3500 else if t 3 = 1 then 3102 else 3104)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2626 else 2901) else if t 2 = 1 then (if t 3 = 0 then 3093 else if t 3 = 1 then 3092 else 3096) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3103 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4611 else (if jt.2.val < 2 then 4615 else 4616)) else (if jt.2.val < 4 then 4612 else (if jt.2.val < 5 then 4614 else 4613))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4315 else (if jt.2.val < 2 then 4319 else 4320)) else (if jt.2.val < 4 then 4316 else (if jt.2.val < 5 then 4318 else 4317)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3371 else (if jt.2.val < 2 then 3373 else 3377)) else (if jt.2.val < 4 then 3372 else (if jt.2.val < 5 then 3376 else 3375))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3540 else (if jt.2.val < 2 then 3551 else 3543)) else (if jt.2.val < 4 then 3549 else (if jt.2.val < 5 then 3550 else 3538)))))

checked_coverage fastCoverage0497 pairing0497 template0497 witness0497

theorem coverage0497 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0497) (maskBits m))
    cores template0497 witness0497 := by
  rw [← coresFast_eq]
  exact fastCoverage0497

theorem coverageSize0497 : ∀ q : Pattern,
    (cores (witness0497 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0497 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0497
#print axioms coverageSize0497

noncomputable def pairing0498 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0498 : List (Fin 4935) := templateData0498

noncomputable def witness0498 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2565 else 2884) else if t 2 = 1 then (if t 3 = 0 then 2560 else if t 3 = 1 then 2544 else 2546) else (if t 3 = 0 then 3499 else if t 3 = 1 then 3209 else 3210)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2563 else 1762) else if t 2 = 1 then (if t 3 = 0 then 2558 else if t 3 = 1 then 2538 else 1747) else (if t 3 = 0 then 277 else if t 3 = 1 then 251 else 256)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 681 else 1145) else if t 2 = 1 then (if t 3 = 0 then 667 else if t 3 = 1 then 641 else 646) else (if t 3 = 0 then 2170 else if t 3 = 1 then 1459 else 1462))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2564 else 1915) else if t 2 = 1 then (if t 3 = 0 then 2559 else if t 3 = 1 then 2541 else 1900) else (if t 3 = 0 then 571 else if t 3 = 1 then 545 else 549)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2562 else 2883) else if t 2 = 1 then (if t 3 = 0 then 2548 else if t 3 = 1 then 2519 else 2530) else (if t 3 = 0 then 2550 else if t 3 = 1 then 2523 else 2532)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2885) else if t 2 = 1 then (if t 3 = 0 then 2549 else if t 3 = 1 then 2521 else 2531) else (if t 3 = 0 then 2551 else if t 3 = 1 then 2524 else 2533))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1687 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1666 else 1668) else (if t 3 = 0 then 1111 else if t 3 = 1 then 547 else 551)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2576 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2878 else if t 3 = 1 then 2526 else 2534) else (if t 3 = 0 then 2880 else if t 3 = 1 then 2528 else 2536)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2578 else 3507) else if t 2 = 1 then (if t 3 = 0 then 2879 else if t 3 = 1 then 2527 else 2535) else (if t 3 = 0 then 2881 else if t 3 = 1 then 2529 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4629 else (if jt.2.val < 2 then 4631 else 4634)) else (if jt.2.val < 4 then 4630 else (if jt.2.val < 5 then 4633 else 4632))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3705 else (if jt.2.val < 2 then 3707 else 3713)) else (if jt.2.val < 4 then 3706 else (if jt.2.val < 5 then 3712 else 3708)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3546 else (if jt.2.val < 2 then 3554 else 3548)) else (if jt.2.val < 4 then 3552 else (if jt.2.val < 5 then 3553 else 3537))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2871 else (if jt.2.val < 2 then 2873 else 2877)) else (if jt.2.val < 4 then 2872 else (if jt.2.val < 5 then 2876 else 2875)))))

checked_coverage fastCoverage0498 pairing0498 template0498 witness0498

theorem coverage0498 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0498) (maskBits m))
    cores template0498 witness0498 := by
  rw [← coresFast_eq]
  exact fastCoverage0498

theorem coverageSize0498 : ∀ q : Pattern,
    (cores (witness0498 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0498 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0498
#print axioms coverageSize0498

noncomputable def pairing0499 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0499 : List (Fin 4935) := templateData0499

noncomputable def witness0499 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2960 else 2506) else if t 2 = 1 then (if t 3 = 0 then 2953 else if t 3 = 1 then 2937 else 2938) else (if t 3 = 0 then 3152 else if t 3 = 1 then 3329 else 3514)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2958 else 1756) else if t 2 = 1 then (if t 3 = 0 then 2951 else if t 3 = 1 then 2931 else 1730) else (if t 3 = 0 then 859 else if t 3 = 1 then 830 else 833)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1084 else 790) else if t 2 = 1 then (if t 3 = 0 then 1075 else if t 3 = 1 then 1046 else 1049) else (if t 3 = 0 then 1599 else if t 3 = 1 then 1813 else 2146))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2959 else 1909) else if t 2 = 1 then (if t 3 = 0 then 2952 else if t 3 = 1 then 2934 else 1888) else (if t 3 = 0 then 1204 else if t 3 = 1 then 1180 else 1182)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2954 else 2502) else if t 2 = 1 then (if t 3 = 0 then 2947 else if t 3 = 1 then 2913 else 2919) else (if t 3 = 0 then 2949 else if t 3 = 1 then 2917 else 2921)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2503) else if t 2 = 1 then (if t 3 = 0 then 2948 else if t 3 = 1 then 2915 else 2920) else (if t 3 = 0 then 2950 else if t 3 = 1 then 2918 else 2922))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2224 else 1621) else if t 2 = 1 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2206 else 1890) else (if t 3 = 0 then 762 else if t 3 = 1 then 1184 else 1186)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2650 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2699 else if t 3 = 1 then 2923 else 2927) else (if t 3 = 0 then 2701 else if t 3 = 1 then 2925 else 2929)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2651 else 3184) else if t 2 = 1 then (if t 3 = 0 then 2700 else if t 3 = 1 then 2924 else 2928) else (if t 3 = 0 then 2702 else if t 3 = 1 then 2926 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4659 else (if jt.2.val < 2 then 4661 else 4664)) else (if jt.2.val < 4 then 4660 else (if jt.2.val < 5 then 4663 else 4662))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3777 else (if jt.2.val < 2 then 3779 else 3785)) else (if jt.2.val < 4 then 3778 else (if jt.2.val < 5 then 3784 else 3780)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3375 else (if jt.2.val < 2 then 3383 else 3377)) else (if jt.2.val < 4 then 3381 else (if jt.2.val < 5 then 3382 else 3371))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2875 else (if jt.2.val < 2 then 2945 else 2877)) else (if jt.2.val < 4 then 2944 else (if jt.2.val < 5 then 2946 else 2871)))))

checked_coverage fastCoverage0499 pairing0499 template0499 witness0499

theorem coverage0499 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0499) (maskBits m))
    cores template0499 witness0499 := by
  rw [← coresFast_eq]
  exact fastCoverage0499

theorem coverageSize0499 : ∀ q : Pattern,
    (cores (witness0499 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0499 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0499
#print axioms coverageSize0499

noncomputable def pairing0500 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0500 : List (Fin 4935) := templateData0500

noncomputable def witness0500 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1510) else if t 2 = 1 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 450) else (if t 3 = 0 then 591 else if t 3 = 1 then 589 else 1120)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 48) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2090) else (if t 3 = 0 then 1447 else if t 3 = 1 then 2101 else 2107)) else (if t 2 = 0 then (if t 3 = 0 then 3532 else if t 3 = 1 then 3530 else 3192) else if t 2 = 1 then (if t 3 = 0 then 3531 else if t 3 = 1 then 3528 else 2690) else (if t 3 = 0 then 2649 else if t 3 = 1 then 2648 else 2906))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1509) else if t 2 = 1 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 449) else (if t 3 = 0 then 590 else if t 3 = 1 then 588 else 1119)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 47) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2089) else (if t 3 = 0 then 1446 else if t 3 = 1 then 2100 else 2106)) else (if t 2 = 0 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 53) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2091) else (if t 3 = 0 then 1448 else if t 3 = 1 then 2102 else 2108))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 1815 else 2739) else if t 2 = 1 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1050 else 476) else (if t 3 = 0 then 3216 else if t 3 = 1 then 600 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 836 else if t 3 = 1 then 834 else 74) else if t 2 = 1 then (if t 3 = 0 then 1732 else if t 3 = 1 then 2081 else 2097) else (if t 3 = 0 then 1452 else if t 3 = 1 then 2103 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 841 else if t 3 = 1 then 840 else 77) else if t 2 = 1 then (if t 3 = 0 then 1735 else if t 3 = 1 then 2083 else 2099) else (if t 3 = 0 then 1454 else if t 3 = 1 then 2105 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4659 else (if jt.2.val < 2 then 4670 else 4664)) else (if jt.2.val < 4 then 4668 else (if jt.2.val < 5 then 4669 else 4662))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4650 else (if jt.2.val < 2 then 4667 else 4653)) else (if jt.2.val < 4 then 4665 else (if jt.2.val < 5 then 4666 else 4648)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2232 else (if jt.2.val < 2 then 2240 else 2243)) else (if jt.2.val < 4 then 2239 else (if jt.2.val < 5 then 2242 else 2241))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2233 else (if jt.2.val < 2 then 2237 else 2238)) else (if jt.2.val < 4 then 2234 else (if jt.2.val < 5 then 2236 else 2235)))))

checked_coverage fastCoverage0500 pairing0500 template0500 witness0500

theorem coverage0500 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0500) (maskBits m))
    cores template0500 witness0500 := by
  rw [← coresFast_eq]
  exact fastCoverage0500

theorem coverageSize0500 : ∀ q : Pattern,
    (cores (witness0500 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0500 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0500
#print axioms coverageSize0500

noncomputable def pairing0501 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0501 : List (Fin 4935) := templateData0501

noncomputable def witness0501 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 2125) else if t 2 = 1 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 448) else (if t 3 = 0 then 1222 else if t 3 = 1 then 1211 else 503)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 46) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1339) else (if t 3 = 0 then 1777 else if t 3 = 1 then 1370 else 1371)) else (if t 2 = 0 then (if t 3 = 0 then 3236 else if t 3 = 1 then 3234 else 3522) else if t 2 = 1 then (if t 3 = 0 then 3235 else if t 3 = 1 then 3232 else 2689) else (if t 3 = 0 then 2868 else if t 3 = 1 then 2860 else 2722))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 2124) else if t 2 = 1 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 447) else (if t 3 = 0 then 1221 else if t 3 = 1 then 1208 else 500)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 45) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1338) else (if t 3 = 0 then 1776 else if t 3 = 1 then 1362 else 1364)) else (if t 2 = 0 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 52) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1343) else (if t 3 = 0 then 1778 else if t 3 = 1 then 1363 else 1365))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1785 else 2988) else if t 2 = 1 then (if t 3 = 0 then 647 else if t 3 = 1 then 643 else 1137) else (if t 3 = 0 then 3523 else if t 3 = 1 then 692 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 257 else if t 3 = 1 then 253 else 921) else if t 2 = 1 then (if t 3 = 0 then 1352 else if t 3 = 1 then 1349 else 1356) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1366 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 262 else if t 3 = 1 then 260 else 923) else if t 2 = 1 then (if t 3 = 0 then 1355 else if t 3 = 1 then 1354 else 1360) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1367 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4629 else (if jt.2.val < 2 then 4637 else 4634)) else (if jt.2.val < 4 then 4635 else (if jt.2.val < 5 then 4636 else 4632))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4317 else (if jt.2.val < 2 then 4352 else 4320)) else (if jt.2.val < 4 then 4350 else (if jt.2.val < 5 then 4351 else 4315)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1931 else (if jt.2.val < 2 then 1933 else 1937)) else (if jt.2.val < 4 then 1932 else (if jt.2.val < 5 then 1936 else 1935))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2235 else (if jt.2.val < 2 then 2246 else 2238)) else (if jt.2.val < 4 then 2244 else (if jt.2.val < 5 then 2245 else 2233)))))

checked_coverage fastCoverage0501 pairing0501 template0501 witness0501

theorem coverage0501 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0501) (maskBits m))
    cores template0501 witness0501 := by
  rw [← coresFast_eq]
  exact fastCoverage0501

theorem coverageSize0501 : ∀ q : Pattern,
    (cores (witness0501 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0501 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0501
#print axioms coverageSize0501

noncomputable def pairing0502 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0502 : List (Fin 4935) := templateData0502

noncomputable def witness0502 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 183 else 900) else if t 2 = 1 then (if t 3 = 0 then 178 else if t 3 = 1 then 156 else 158) else (if t 3 = 0 then 2117 else if t 3 = 1 then 1537 else 1538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 185 else if t 3 = 1 then 181 else 898) else if t 2 = 1 then (if t 3 = 0 then 170 else if t 3 = 1 then 136 else 142) else (if t 3 = 0 then 171 else if t 3 = 1 then 139 else 143)) else (if t 2 = 0 then (if t 3 = 0 then 2779 else if t 3 = 1 then 2778 else 2989) else if t 2 = 1 then (if t 3 = 0 then 2775 else if t 3 = 1 then 2766 else 2769) else (if t 3 = 0 then 3524 else if t 3 = 1 then 3172 else 3174))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 182 else 899) else if t 2 = 1 then (if t 3 = 0 then 174 else if t 3 = 1 then 146 else 152) else (if t 3 = 0 then 2115 else if t 3 = 1 then 1531 else 1535)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 184 else if t 3 = 1 then 180 else 897) else if t 2 = 1 then (if t 3 = 0 then 160 else if t 3 = 1 then 117 else 128) else (if t 3 = 0 then 162 else if t 3 = 1 then 121 else 130)) else (if t 2 = 0 then (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 901) else if t 2 = 1 then (if t 3 = 0 then 161 else if t 3 = 1 then 119 else 129) else (if t 3 = 0 then 163 else if t 3 = 1 then 122 else 131))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 200 else 3525) else if t 2 = 1 then (if t 3 = 0 then 894 else if t 3 = 1 then 150 else 154) else (if t 3 = 0 then 2984 else if t 3 = 1 then 1833 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1500 else if t 3 = 1 then 198 else 2127) else if t 2 = 1 then (if t 3 = 0 then 888 else if t 3 = 1 then 124 else 132) else (if t 3 = 0 then 890 else if t 3 = 1 then 126 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 1502 else if t 3 = 1 then 202 else 2128) else if t 2 = 1 then (if t 3 = 0 then 889 else if t 3 = 1 then 125 else 133) else (if t 3 = 0 then 891 else if t 3 = 1 then 127 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4611 else (if jt.2.val < 2 then 4645 else 4616)) else (if jt.2.val < 4 then 4644 else (if jt.2.val < 5 then 4646 else 4613))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3708 else (if jt.2.val < 2 then 3748 else 3713)) else (if jt.2.val < 4 then 3747 else (if jt.2.val < 5 then 3749 else 3705)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2241 else (if jt.2.val < 2 then 2249 else 2243)) else (if jt.2.val < 4 then 2247 else (if jt.2.val < 5 then 2248 else 2232))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 881 else (if jt.2.val < 2 then 883 else 887)) else (if jt.2.val < 4 then 882 else (if jt.2.val < 5 then 886 else 885)))))

checked_coverage fastCoverage0502 pairing0502 template0502 witness0502

theorem coverage0502 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0502) (maskBits m))
    cores template0502 witness0502 := by
  rw [← coresFast_eq]
  exact fastCoverage0502

theorem coverageSize0502 : ∀ q : Pattern,
    (cores (witness0502 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0502 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0502
#print axioms coverageSize0502

noncomputable def pairing0503 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0503 : List (Fin 4935) := templateData0503

noncomputable def witness0503 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 1004 else 104) else if t 2 = 1 then (if t 3 = 0 then 995 else if t 3 = 1 then 977 else 978) else (if t 3 = 0 then 1433 else if t 3 = 1 then 1801 else 2138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1006 else if t 3 = 1 then 1000 else 100) else if t 2 = 1 then (if t 3 = 0 then 991 else if t 3 = 1 then 957 else 961) else (if t 3 = 0 then 992 else if t 3 = 1 then 960 else 962)) else (if t 2 = 0 then (if t 3 = 0 then 2981 else if t 3 = 1 then 2980 else 2800) else if t 2 = 1 then (if t 3 = 0 then 2979 else if t 3 = 1 then 2970 else 2972) else (if t 3 = 0 then 3226 else if t 3 = 1 then 3338 else 3520))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 1002 else 102) else if t 2 = 1 then (if t 3 = 0 then 993 else if t 3 = 1 then 967 else 971) else (if t 3 = 0 then 1430 else if t 3 = 1 then 1795 else 2136)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1005 else if t 3 = 1 then 996 else 96) else if t 2 = 1 then (if t 3 = 0 then 987 else if t 3 = 1 then 939 else 945) else (if t 3 = 0 then 989 else if t 3 = 1 then 943 else 947)) else (if t 2 = 0 then (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 97) else if t 2 = 1 then (if t 3 = 0 then 988 else if t 3 = 1 then 941 else 946) else (if t 3 = 0 then 990 else if t 3 = 1 then 944 else 948))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 306 else 3229) else if t 2 = 1 then (if t 3 = 0 then 377 else if t 3 = 1 then 973 else 975) else (if t 3 = 0 then 2796 else if t 3 = 1 then 1799 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2139 else if t 3 = 1 then 300 else 1476) else if t 2 = 1 then (if t 3 = 0 then 367 else if t 3 = 1 then 949 else 953) else (if t 3 = 0 then 369 else if t 3 = 1 then 951 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 2141 else if t 3 = 1 then 301 else 1477) else if t 2 = 1 then (if t 3 = 0 then 368 else if t 3 = 1 then 950 else 954) else (if t 3 = 0 then 370 else if t 3 = 1 then 952 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4647 else (if jt.2.val < 2 then 4672 else 4658)) else (if jt.2.val < 4 then 4671 else (if jt.2.val < 5 then 4673 else 4655))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3780 else (if jt.2.val < 2 then 3796 else 3785)) else (if jt.2.val < 4 then 3795 else (if jt.2.val < 5 then 3797 else 3777)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1935 else (if jt.2.val < 2 then 1943 else 1937)) else (if jt.2.val < 4 then 1941 else (if jt.2.val < 5 then 1942 else 1931))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 885 else (if jt.2.val < 2 then 985 else 887)) else (if jt.2.val < 4 then 984 else (if jt.2.val < 5 then 986 else 881)))))

checked_coverage fastCoverage0503 pairing0503 template0503 witness0503

theorem coverage0503 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0503) (maskBits m))
    cores template0503 witness0503 := by
  rw [← coresFast_eq]
  exact fastCoverage0503

theorem coverageSize0503 : ∀ q : Pattern,
    (cores (witness0503 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0503 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0503
#print axioms coverageSize0503

noncomputable def pairing0504 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0504 : List (Fin 4935) := templateData0504

noncomputable def witness0504 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 3860) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2980) else (if t 3 = 0 then 2789 else if t 3 = 1 then 2787 else 2800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 1084) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 1078) else (if t 3 = 0 then 727 else if t 3 = 1 then 723 else 784)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1648 else 1690) else if t 2 = 1 then (if t 3 = 0 then 1651 else if t 3 = 1 then 1647 else 1080) else (if t 3 = 0 then 743 else if t 3 = 1 then 741 else 786))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 1003) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 997) else (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 97)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2955) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3852) else (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3854)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2957) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3853) else (if t 3 = 0 then 3838 else if t 3 = 1 then 3837 else 3855))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 241 else 307) else if t 2 = 1 then (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 301) else (if t 3 = 0 then 1472 else if t 3 = 1 then 919 else 1477)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2651) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3856) else (if t 3 = 0 then 3849 else if t 3 = 1 then 3848 else 3858)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2626 else 2653) else if t 2 = 1 then (if t 3 = 0 then 3847 else if t 3 = 1 then 3846 else 3857) else (if t 3 = 0 then 3851 else if t 3 = 1 then 3850 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4674 else (if jt.2.val < 2 then 4678 else 4679)) else (if jt.2.val < 4 then 4675 else (if jt.2.val < 5 then 4677 else 4676))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4396 else (if jt.2.val < 2 then 4400 else 4401)) else (if jt.2.val < 4 then 4397 else (if jt.2.val < 5 then 4399 else 4398)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4096 else (if jt.2.val < 2 then 4100 else 4101)) else (if jt.2.val < 4 then 4097 else (if jt.2.val < 5 then 4099 else 4098))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3798 else (if jt.2.val < 2 then 3800 else 3803)) else (if jt.2.val < 4 then 3799 else (if jt.2.val < 5 then 3802 else 3801)))))

checked_coverage fastCoverage0504 pairing0504 template0504 witness0504

theorem coverage0504 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0504) (maskBits m))
    cores template0504 witness0504 := by
  rw [← coresFast_eq]
  exact fastCoverage0504

theorem coverageSize0504 : ∀ q : Pattern,
    (cores (witness0504 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0504 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0504
#print axioms coverageSize0504

noncomputable def pairing0505 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0505 : List (Fin 4935) := templateData0505

noncomputable def witness0505 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 3905) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2979) else (if t 3 = 0 then 2779 else if t 3 = 1 then 2775 else 2776)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 1075) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 1069) else (if t 3 = 0 then 682 else if t 3 = 1 then 654 else 659)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1597 else 1599) else if t 2 = 1 then (if t 3 = 0 then 1612 else if t 3 = 1 then 1593 else 1071) else (if t 3 = 0 then 689 else if t 3 = 1 then 656 else 661))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 994) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 988) else (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 167)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2948) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3884) else (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3886)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2950) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3885) else (if t 3 = 0 then 3916 else if t 3 = 1 then 3878 else 3887))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 376 else 378) else if t 2 = 1 then (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 368) else (if t 3 = 0 then 1502 else if t 3 = 1 then 889 else 1495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2700) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3888) else (if t 3 = 0 then 3919 else if t 3 = 1 then 3882 else 3890)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2698 else 2702) else if t 2 = 1 then (if t 3 = 0 then 3918 else if t 3 = 1 then 3881 else 3889) else (if t 3 = 0 then 3920 else if t 3 = 1 then 3883 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4680 else (if jt.2.val < 2 then 4682 else 4685)) else (if jt.2.val < 4 then 4681 else (if jt.2.val < 5 then 4684 else 4683))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4410 else (if jt.2.val < 2 then 4412 else 4418)) else (if jt.2.val < 4 then 4411 else (if jt.2.val < 5 then 4417 else 4413)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4110 else (if jt.2.val < 2 then 4112 else 4118)) else (if jt.2.val < 4 then 4111 else (if jt.2.val < 5 then 4117 else 4113))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3801 else (if jt.2.val < 2 then 3863 else 3803)) else (if jt.2.val < 4 then 3861 else (if jt.2.val < 5 then 3862 else 3798)))))

checked_coverage fastCoverage0505 pairing0505 template0505 witness0505

theorem coverage0505 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0505) (maskBits m))
    cores template0505 witness0505 := by
  rw [← coresFast_eq]
  exact fastCoverage0505

theorem coverageSize0505 : ∀ q : Pattern,
    (cores (witness0505 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0505 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0505
#print axioms coverageSize0505

noncomputable def pairing0506 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0506 : List (Fin 4935) := templateData0506

noncomputable def witness0506 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2446 else 2506) else if t 2 = 1 then (if t 3 = 0 then 2450 else if t 3 = 1 then 2442 else 2500) else (if t 3 = 0 then 3941 else if t 3 = 1 then 3939 else 3943)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2444 else 1756) else if t 2 = 1 then (if t 3 = 0 then 2448 else if t 3 = 1 then 2440 else 1753) else (if t 3 = 0 then 726 else if t 3 = 1 then 722 else 778)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 341 else 406) else if t 2 = 1 then (if t 3 = 0 then 343 else if t 3 = 1 then 339 else 394) else (if t 3 = 0 then 1490 else if t 3 = 1 then 1489 else 1498))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2445 else 1909) else if t 2 = 1 then (if t 3 = 0 then 2449 else if t 3 = 1 then 2441 else 1906) else (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 91)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2443 else 2502) else if t 2 = 1 then (if t 3 = 0 then 2447 else if t 3 = 1 then 2439 else 2492) else (if t 3 = 0 then 2462 else if t 3 = 1 then 2459 else 2493)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2504) else if t 2 = 1 then (if t 3 = 0 then 2471 else if t 3 = 1 then 2468 else 2494) else (if t 3 = 0 then 2475 else if t 3 = 1 then 2473 else 2495))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1583 else 1621) else if t 2 = 1 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1582 else 1618) else (if t 3 = 0 then 71 else if t 3 = 1 then 69 else 93)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2897 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2484 else if t 3 = 1 then 2481 else 2496) else (if t 3 = 0 then 2487 else if t 3 = 1 then 2486 else 2497)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2900 else 3928) else if t 2 = 1 then (if t 3 = 0 then 2489 else if t 3 = 1 then 2488 else 2498) else (if t 3 = 0 then 2491 else if t 3 = 1 then 2490 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4623 else (if jt.2.val < 2 then 4627 else 4628)) else (if jt.2.val < 4 then 4624 else (if jt.2.val < 5 then 4626 else 4625))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2437 else (if jt.2.val < 2 then 2467 else 2469)) else (if jt.2.val < 4 then 2464 else (if jt.2.val < 5 then 2466 else 2465)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4098 else (if jt.2.val < 2 then 4121 else 4101)) else (if jt.2.val < 4 then 4119 else (if jt.2.val < 5 then 4120 else 4096))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2430 else (if jt.2.val < 2 then 2432 else 2435)) else (if jt.2.val < 4 then 2431 else (if jt.2.val < 5 then 2434 else 2433)))))

checked_coverage fastCoverage0506 pairing0506 template0506 witness0506

theorem coverage0506 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0506) (maskBits m))
    cores template0506 witness0506 := by
  rw [← coresFast_eq]
  exact fastCoverage0506

theorem coverageSize0506 : ∀ q : Pattern,
    (cores (witness0506 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0506 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0506
#print axioms coverageSize0506

noncomputable def pairing0507 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0507 : List (Fin 4935) := templateData0507

noncomputable def witness0507 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2560 else 2561) else if t 2 = 1 then (if t 3 = 0 then 2565 else if t 3 = 1 then 2544 else 2546) else (if t 3 = 0 then 3951 else if t 3 = 1 then 3945 else 3946)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2558 else 1750) else if t 2 = 1 then (if t 3 = 0 then 2563 else if t 3 = 1 then 2538 else 1747) else (if t 3 = 0 then 681 else if t 3 = 1 then 641 else 646)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 277 else 279) else if t 2 = 1 then (if t 3 = 0 then 291 else if t 3 = 1 then 251 else 256) else (if t 3 = 0 then 1475 else if t 3 = 1 then 1459 else 1462))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2559 else 1903) else if t 2 = 1 then (if t 3 = 0 then 2564 else if t 3 = 1 then 2541 else 1900) else (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 153)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2548 else 2554) else if t 2 = 1 then (if t 3 = 0 then 2562 else if t 3 = 1 then 2519 else 2530) else (if t 3 = 0 then 2570 else if t 3 = 1 then 2521 else 2531)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2556) else if t 2 = 1 then (if t 3 = 0 then 2572 else if t 3 = 1 then 2523 else 2532) else (if t 3 = 0 then 2574 else if t 3 = 1 then 2524 else 2533))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1672 else 1674) else if t 2 = 1 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1666 else 1668) else (if t 3 = 0 then 203 else if t 3 = 1 then 151 else 155)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2878 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2576 else if t 3 = 1 then 2526 else 2534) else (if t 3 = 0 then 2578 else if t 3 = 1 then 2527 else 2535)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2880 else 3934) else if t 2 = 1 then (if t 3 = 0 then 2579 else if t 3 = 1 then 2528 else 2536) else (if t 3 = 0 then 2580 else if t 3 = 1 then 2529 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4629 else (if jt.2.val < 2 then 4631 else 4634)) else (if jt.2.val < 4 then 4630 else (if jt.2.val < 5 then 4633 else 4632))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2513 else (if jt.2.val < 2 then 2515 else 2543)) else (if jt.2.val < 4 then 2514 else (if jt.2.val < 5 then 2542 else 2522)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4113 else (if jt.2.val < 2 then 4123 else 4118)) else (if jt.2.val < 4 then 4122 else (if jt.2.val < 5 then 4124 else 4110))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2433 else (if jt.2.val < 2 then 2509 else 2435)) else (if jt.2.val < 4 then 2507 else (if jt.2.val < 5 then 2508 else 2430)))))

checked_coverage fastCoverage0507 pairing0507 template0507 witness0507

theorem coverage0507 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0507) (maskBits m))
    cores template0507 witness0507 := by
  rw [← coresFast_eq]
  exact fastCoverage0507

theorem coverageSize0507 : ∀ q : Pattern,
    (cores (witness0507 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0507 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0507
#print axioms coverageSize0507

noncomputable def pairing0508 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0508 : List (Fin 4935) := templateData0508

noncomputable def witness0508 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 1376) else if t 2 = 1 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 1001) else (if t 3 = 0 then 50 else if t 3 = 1 then 46 else 101)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 1211) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1370) else (if t 3 = 0 then 1342 else if t 3 = 1 then 1339 else 1371)) else (if t 2 = 0 then (if t 3 = 0 then 3965 else if t 3 = 1 then 3963 else 3967) else if t 2 = 1 then (if t 3 = 0 then 3235 else if t 3 = 1 then 3232 else 2860) else (if t 3 = 0 then 2691 else if t 3 = 1 then 2689 else 2722))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 1374) else if t 2 = 1 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 998) else (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 98)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 1208) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1362) else (if t 3 = 0 then 1341 else if t 3 = 1 then 1338 else 1364)) else (if t 2 = 0 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 1209) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1363) else (if t 3 = 0 then 1344 else if t 3 = 1 then 1343 else 1365))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1785 else 2782) else if t 2 = 1 then (if t 3 = 0 then 257 else if t 3 = 1 then 253 else 302) else (if t 3 = 0 then 3942 else if t 3 = 1 then 921 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 647 else if t 3 = 1 then 643 else 692) else if t 2 = 1 then (if t 3 = 0 then 1352 else if t 3 = 1 then 1349 else 1366) else (if t 3 = 0 then 1358 else if t 3 = 1 then 1356 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 652 else if t 3 = 1 then 650 else 693) else if t 2 = 1 then (if t 3 = 0 then 1355 else if t 3 = 1 then 1354 else 1367) else (if t 3 = 0 then 1361 else if t 3 = 1 then 1360 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4629 else (if jt.2.val < 2 then 4637 else 4634)) else (if jt.2.val < 4 then 4635 else (if jt.2.val < 5 then 4636 else 4632))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4398 else (if jt.2.val < 2 then 4421 else 4401)) else (if jt.2.val < 4 then 4419 else (if jt.2.val < 5 then 4420 else 4396)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1303 else (if jt.2.val < 2 then 1337 else 1340)) else (if jt.2.val < 4 then 1334 else (if jt.2.val < 5 then 1336 else 1335))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1296 else (if jt.2.val < 2 then 1298 else 1301)) else (if jt.2.val < 4 then 1297 else (if jt.2.val < 5 then 1300 else 1299)))))

checked_coverage fastCoverage0508 pairing0508 template0508 witness0508

theorem coverage0508 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0508) (maskBits m))
    cores template0508 witness0508 := by
  rw [← coresFast_eq]
  exact fastCoverage0508

theorem coverageSize0508 : ∀ q : Pattern,
    (cores (witness0508 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0508 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0508
#print axioms coverageSize0508

noncomputable def pairing0509 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0509 : List (Fin 4935) := templateData0509

noncomputable def witness0509 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 1433) else if t 2 = 1 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 992) else (if t 3 = 0 then 195 else if t 3 = 1 then 171 else 173)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 1202) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1414) else (if t 3 = 0 then 1447 else if t 3 = 1 then 1411 else 1415)) else (if t 2 = 0 then (if t 3 = 0 then 3959 else if t 3 = 1 then 3953 else 3954) else if t 2 = 1 then (if t 3 = 0 then 3227 else if t 3 = 1 then 3219 else 2855) else (if t 3 = 0 then 2649 else if t 3 = 1 then 2630 else 2633))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 1430) else if t 2 = 1 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 989) else (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 168)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 1199) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1400) else (if t 3 = 0 then 1446 else if t 3 = 1 then 1393 else 1402)) else (if t 2 = 0 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 1200) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1401) else (if t 3 = 0 then 1448 else if t 3 = 1 then 1394 else 1403))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1773 else 2796) else if t 2 = 1 then (if t 3 = 0 then 395 else if t 3 = 1 then 365 else 369) else (if t 3 = 0 then 3952 else if t 3 = 1 then 890 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 779 else if t 3 = 1 then 749 else 753) else if t 2 = 1 then (if t 3 = 0 then 1449 else if t 3 = 1 then 1396 else 1404) else (if t 3 = 0 then 1452 else if t 3 = 1 then 1398 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 782 else if t 3 = 1 then 750 else 754) else if t 2 = 1 then (if t 3 = 0 then 1451 else if t 3 = 1 then 1397 else 1405) else (if t 3 = 0 then 1454 else if t 3 = 1 then 1399 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4623 else (if jt.2.val < 2 then 4639 else 4628)) else (if jt.2.val < 4 then 4638 else (if jt.2.val < 5 then 4640 else 4625))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4413 else (if jt.2.val < 2 then 4423 else 4418)) else (if jt.2.val < 4 then 4422 else (if jt.2.val < 5 then 4424 else 4410)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1383 else (if jt.2.val < 2 then 1385 else 1421)) else (if jt.2.val < 4 then 1384 else (if jt.2.val < 5 then 1420 else 1392))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1299 else (if jt.2.val < 2 then 1379 else 1301)) else (if jt.2.val < 4 then 1377 else (if jt.2.val < 5 then 1378 else 1296)))))

checked_coverage fastCoverage0509 pairing0509 template0509 witness0509

theorem coverage0509 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0509) (maskBits m))
    cores template0509 witness0509 := by
  rw [← coresFast_eq]
  exact fastCoverage0509

theorem coverageSize0509 : ∀ q : Pattern,
    (cores (witness0509 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0509 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0509
#print axioms coverageSize0509

noncomputable def pairing0510 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0510 : List (Fin 4935) := templateData0510

noncomputable def witness0510 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 424 else 506) else if t 2 = 1 then (if t 3 = 0 then 428 else if t 3 = 1 then 420 else 496) else (if t 3 = 0 then 1510 else if t 3 = 1 then 1507 else 1523)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 430 else if t 3 = 1 then 422 else 502) else if t 2 = 1 then (if t 3 = 0 then 426 else if t 3 = 1 then 418 else 488) else (if t 3 = 0 then 450 else if t 3 = 1 then 445 else 489)) else (if t 2 = 0 then (if t 3 = 0 then 2732 else if t 3 = 1 then 2730 else 2743) else if t 2 = 1 then (if t 3 = 0 then 2731 else if t 3 = 1 then 2728 else 2740) else (if t 3 = 0 then 3930 else if t 3 = 1 then 3929 else 3935))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 423 else 504) else if t 2 = 1 then (if t 3 = 0 then 427 else if t 3 = 1 then 419 else 492) else (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 429 else if t 3 = 1 then 421 else 498) else if t 2 = 1 then (if t 3 = 0 then 425 else if t 3 = 1 then 417 else 480) else (if t 3 = 0 then 449 else if t 3 = 1 then 444 else 482)) else (if t 2 = 0 then (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 499) else if t 2 = 1 then (if t 3 = 0 then 440 else if t 3 = 1 then 436 else 481) else (if t 3 = 0 then 455 else if t 3 = 1 then 453 else 483))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 1133 else 3960) else if t 2 = 1 then (if t 3 = 0 then 468 else if t 3 = 1 then 463 else 494) else (if t 3 = 0 then 2739 else if t 3 = 1 then 1848 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1518 else if t 3 = 1 then 1131 else 1524) else if t 2 = 1 then (if t 3 = 0 then 466 else if t 3 = 1 then 461 else 484) else (if t 3 = 0 then 476 else if t 3 = 1 then 474 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 1520 else if t 3 = 1 then 1135 else 1525) else if t 2 = 1 then (if t 3 = 0 then 472 else if t 3 = 1 then 470 else 485) else (if t 3 = 0 then 479 else if t 3 = 1 then 478 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4680 else (if jt.2.val < 2 then 4688 else 4685)) else (if jt.2.val < 4 then 4686 else (if jt.2.val < 5 then 4687 else 4683))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2465 else (if jt.2.val < 2 then 2729 else 2469)) else (if jt.2.val < 4 then 2726 else (if jt.2.val < 5 then 2727 else 2437)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1335 else (if jt.2.val < 2 then 1508 else 1340)) else (if jt.2.val < 4 then 1503 else (if jt.2.val < 5 then 1504 else 1303))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 408 else (if jt.2.val < 2 then 410 else 413)) else (if jt.2.val < 4 then 409 else (if jt.2.val < 5 then 412 else 411)))))

checked_coverage fastCoverage0510 pairing0510 template0510 witness0510

theorem coverage0510 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0510) (maskBits m))
    cores template0510 witness0510 := by
  rw [← coresFast_eq]
  exact fastCoverage0510

theorem coverageSize0510 : ∀ q : Pattern,
    (cores (witness0510 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0510 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0510
#print axioms coverageSize0510

noncomputable def pairing0511 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0511 : List (Fin 4935) := templateData0511

noncomputable def witness0511 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 574 else 575) else if t 2 = 1 then (if t 3 = 0 then 579 else if t 3 = 1 then 552 else 554) else (if t 3 = 0 then 1546 else if t 3 = 1 then 1537 else 1538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 581 else if t 3 = 1 then 566 else 568) else if t 2 = 1 then (if t 3 = 0 then 577 else if t 3 = 1 then 532 else 537) else (if t 3 = 0 then 589 else if t 3 = 1 then 534 else 538)) else (if t 2 = 0 then (if t 3 = 0 then 2760 else if t 3 = 1 then 2756 else 2757) else if t 2 = 1 then (if t 3 = 0 then 2759 else if t 3 = 1 then 2747 else 2750) else (if t 3 = 0 then 3927 else if t 3 = 1 then 3923 else 3925))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 570 else 572) else if t 2 = 1 then (if t 3 = 0 then 578 else if t 3 = 1 then 544 else 548) else (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1535)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 580 else if t 3 = 1 then 556 else 562) else if t 2 = 1 then (if t 3 = 0 then 576 else if t 3 = 1 then 515 else 524) else (if t 3 = 0 then 588 else if t 3 = 1 then 517 else 526)) else (if t 2 = 0 then (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 563) else if t 2 = 1 then (if t 3 = 0 then 584 else if t 3 = 1 then 516 else 525) else (if t 3 = 0 then 592 else if t 3 = 1 then 518 else 527))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 1110 else 3966) else if t 2 = 1 then (if t 3 = 0 then 596 else if t 3 = 1 then 546 else 550) else (if t 3 = 0 then 2763 else if t 3 = 1 then 1833 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1548 else if t 3 = 1 then 1104 else 1542) else if t 2 = 1 then (if t 3 = 0 then 594 else if t 3 = 1 then 520 else 528) else (if t 3 = 0 then 600 else if t 3 = 1 then 522 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 1550 else if t 3 = 1 then 1105 else 1543) else if t 2 = 1 then (if t 3 = 0 then 598 else if t 3 = 1 then 521 else 529) else (if t 3 = 0 then 602 else if t 3 = 1 then 523 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4674 else (if jt.2.val < 2 then 4690 else 4679)) else (if jt.2.val < 4 then 4689 else (if jt.2.val < 5 then 4691 else 4676))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2522 else (if jt.2.val < 2 then 2753 else 2543)) else (if jt.2.val < 4 then 2752 else (if jt.2.val < 5 then 2754 else 2513)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1392 else (if jt.2.val < 2 then 1540 else 1421)) else (if jt.2.val < 4 then 1539 else (if jt.2.val < 5 then 1541 else 1383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 411 else (if jt.2.val < 2 then 509 else 413)) else (if jt.2.val < 4 then 507 else (if jt.2.val < 5 then 508 else 408)))))

checked_coverage fastCoverage0511 pairing0511 template0511 witness0511

theorem coverage0511 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0511) (maskBits m))
    cores template0511 witness0511 := by
  rw [← coresFast_eq]
  exact fastCoverage0511

theorem coverageSize0511 : ∀ q : Pattern,
    (cores (witness0511 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0511 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0511
#print axioms coverageSize0511

noncomputable def pairing0512 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0512 : List (Fin 4935) := templateData0512

noncomputable def witness0512 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 3951) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2778) else (if t 3 = 0 then 2789 else if t 3 = 1 then 2788 else 2989)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 681) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 680) else (if t 3 = 0 then 727 else if t 3 = 1 then 725 else 1144)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2197 else 1475) else if t 2 = 1 then (if t 3 = 0 then 2200 else if t 3 = 1 then 2196 else 688) else (if t 3 = 0 then 743 else if t 3 = 1 then 742 else 1148))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 189) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 188) else (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 901)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2570) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4179) else (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4183)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2574) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4180) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4171 else 4184))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 822 else 203) else if t 2 = 1 then (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 202) else (if t 3 = 0 then 1472 else if t 3 = 1 then 70 else 2128)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2578) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4181) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4177 else 4185)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2842 else 2580) else if t 2 = 1 then (if t 3 = 0 then 4004 else if t 3 = 1 then 4164 else 4182) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4178 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4692 else (if jt.2.val < 2 then 4702 else 4703)) else (if jt.2.val < 4 then 4699 else (if jt.2.val < 5 then 4701 else 4700))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4693 else (if jt.2.val < 2 then 4697 else 4698)) else (if jt.2.val < 4 then 4694 else (if jt.2.val < 5 then 4696 else 4695)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4132 else (if jt.2.val < 2 then 4168 else 4169)) else (if jt.2.val < 4 then 4165 else (if jt.2.val < 5 then 4167 else 4166))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4131 else (if jt.2.val < 2 then 4173 else 4176)) else (if jt.2.val < 4 then 4172 else (if jt.2.val < 5 then 4175 else 4174)))))

checked_coverage fastCoverage0512 pairing0512 template0512 witness0512

theorem coverage0512 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0512) (maskBits m))
    cores template0512 witness0512 := by
  rw [← coresFast_eq]
  exact fastCoverage0512

theorem coverageSize0512 : ∀ q : Pattern,
    (cores (witness0512 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0512 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0512
#print axioms coverageSize0512

noncomputable def pairing0513 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0513 : List (Fin 4935) := templateData0513

noncomputable def witness0513 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4190) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2775) else (if t 3 = 0 then 2981 else if t 3 = 1 then 2979 else 2776)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 667) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 654) else (if t 3 = 0 then 1090 else if t 3 = 1 then 1069 else 659)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1597 else 2170) else if t 2 = 1 then (if t 3 = 0 then 1612 else if t 3 = 1 then 1593 else 656) else (if t 3 = 0 then 1094 else if t 3 = 1 then 1071 else 661))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 175) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 161) else (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 167)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2549) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3877) else (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3886)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2551) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3878) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3885 else 3887))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 376 else 895) else if t 2 = 1 then (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 889) else (if t 3 = 0 then 2141 else if t 3 = 1 then 368 else 1495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2879) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3882) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3888 else 3890)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2698 else 2881) else if t 2 = 1 then (if t 3 = 0 then 3918 else if t 3 = 1 then 3881 else 3883) else (if t 3 = 0 then 4192 else if t 3 = 1 then 3889 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4680 else (if jt.2.val < 2 then 4682 else 4685)) else (if jt.2.val < 4 then 4681 else (if jt.2.val < 5 then 4684 else 4683))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4410 else (if jt.2.val < 2 then 4412 else 4418)) else (if jt.2.val < 4 then 4411 else (if jt.2.val < 5 then 4417 else 4413)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4029 else (if jt.2.val < 2 then 4031 else 4035)) else (if jt.2.val < 4 then 4030 else (if jt.2.val < 5 then 4034 else 4033))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4174 else (if jt.2.val < 2 then 4189 else 4176)) else (if jt.2.val < 4 then 4187 else (if jt.2.val < 5 then 4188 else 4131)))))

checked_coverage fastCoverage0513 pairing0513 template0513 witness0513

theorem coverage0513 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0513) (maskBits m))
    cores template0513 witness0513 := by
  rw [← coresFast_eq]
  exact fastCoverage0513

theorem coverageSize0513 : ∀ q : Pattern,
    (cores (witness0513 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0513 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0513
#print axioms coverageSize0513

noncomputable def pairing0514 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0514 : List (Fin 4935) := templateData0514

noncomputable def witness0514 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2450 else 2884) else if t 2 = 1 then (if t 3 = 0 then 2446 else if t 3 = 1 then 2442 else 2500) else (if t 3 = 0 then 4196 else if t 3 = 1 then 3939 else 3943)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2448 else 1762) else if t 2 = 1 then (if t 3 = 0 then 2444 else if t 3 = 1 then 2440 else 1753) else (if t 3 = 0 then 724 else if t 3 = 1 then 722 else 778)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 343 else 929) else if t 2 = 1 then (if t 3 = 0 then 341 else if t 3 = 1 then 339 else 394) else (if t 3 = 0 then 2159 else if t 3 = 1 then 1489 else 1498))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2449 else 1915) else if t 2 = 1 then (if t 3 = 0 then 2445 else if t 3 = 1 then 2441 else 1906) else (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 91)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2447 else 2883) else if t 2 = 1 then (if t 3 = 0 then 2443 else if t 3 = 1 then 2439 else 2492) else (if t 3 = 0 then 2461 else if t 3 = 1 then 2459 else 2493)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2471 else 2886) else if t 2 = 1 then (if t 3 = 0 then 2470 else if t 3 = 1 then 2468 else 2494) else (if t 3 = 0 then 2474 else if t 3 = 1 then 2473 else 2495))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1586 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1582 else 1618) else (if t 3 = 0 then 920 else if t 3 = 1 then 69 else 93)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2484 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2897 else if t 3 = 1 then 2481 else 2496) else (if t 3 = 0 then 2899 else if t 3 = 1 then 2486 else 2497)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2489 else 4197) else if t 2 = 1 then (if t 3 = 0 then 2900 else if t 3 = 1 then 2488 else 2498) else (if t 3 = 0 then 2901 else if t 3 = 1 then 2490 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4623 else (if jt.2.val < 2 then 4627 else 4628)) else (if jt.2.val < 4 then 4624 else (if jt.2.val < 5 then 4626 else 4625))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2437 else (if jt.2.val < 2 then 2467 else 2469)) else (if jt.2.val < 4 then 2464 else (if jt.2.val < 5 then 2466 else 2465)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4166 else (if jt.2.val < 2 then 4195 else 4169)) else (if jt.2.val < 4 then 4193 else (if jt.2.val < 5 then 4194 else 4132))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3020 else (if jt.2.val < 2 then 3022 else 3025)) else (if jt.2.val < 4 then 3021 else (if jt.2.val < 5 then 3024 else 3023)))))

checked_coverage fastCoverage0514 pairing0514 template0514 witness0514

theorem coverage0514 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0514) (maskBits m))
    cores template0514 witness0514 := by
  rw [← coresFast_eq]
  exact fastCoverage0514

theorem coverageSize0514 : ∀ q : Pattern,
    (cores (witness0514 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0514 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0514
#print axioms coverageSize0514

noncomputable def pairing0515 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0515 : List (Fin 4935) := templateData0515

noncomputable def witness0515 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2953 else 2561) else if t 2 = 1 then (if t 3 = 0 then 2960 else if t 3 = 1 then 2937 else 2938) else (if t 3 = 0 then 3860 else if t 3 = 1 then 4046 else 4198)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2951 else 1750) else if t 2 = 1 then (if t 3 = 0 then 2958 else if t 3 = 1 then 2931 else 1730) else (if t 3 = 0 then 1084 else if t 3 = 1 then 1046 else 1049)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 859 else 279) else if t 2 = 1 then (if t 3 = 0 then 868 else if t 3 = 1 then 830 else 833) else (if t 3 = 0 then 1690 else if t 3 = 1 then 1813 else 2146))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2952 else 1903) else if t 2 = 1 then (if t 3 = 0 then 2959 else if t 3 = 1 then 2934 else 1888) else (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 972)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2947 else 2554) else if t 2 = 1 then (if t 3 = 0 then 2954 else if t 3 = 1 then 2913 else 2919) else (if t 3 = 0 then 2955 else if t 3 = 1 then 2915 else 2920)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2949 else 2556) else if t 2 = 1 then (if t 3 = 0 then 2956 else if t 3 = 1 then 2917 else 2921) else (if t 3 = 0 then 2957 else if t 3 = 1 then 2918 else 2922))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2218 else 1674) else if t 2 = 1 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2206 else 1890) else (if t 3 = 0 then 307 else if t 3 = 1 then 974 else 976)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2699 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2650 else if t 3 = 1 then 2923 else 2927) else (if t 3 = 0 then 2651 else if t 3 = 1 then 2924 else 2928)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2701 else 3934) else if t 2 = 1 then (if t 3 = 0 then 2652 else if t 3 = 1 then 2925 else 2929) else (if t 3 = 0 then 2653 else if t 3 = 1 then 2926 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4659 else (if jt.2.val < 2 then 4661 else 4664)) else (if jt.2.val < 4 then 4660 else (if jt.2.val < 5 then 4663 else 4662))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2907 else (if jt.2.val < 2 then 2909 else 2936)) else (if jt.2.val < 4 then 2908 else (if jt.2.val < 5 then 2935 else 2916)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4033 else (if jt.2.val < 2 then 4049 else 4035)) else (if jt.2.val < 4 then 4048 else (if jt.2.val < 5 then 4050 else 4029))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3023 else (if jt.2.val < 2 then 3040 else 3025)) else (if jt.2.val < 4 then 3036 else (if jt.2.val < 5 then 3037 else 3020)))))

checked_coverage fastCoverage0515 pairing0515 template0515 witness0515

theorem coverage0515 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0515) (maskBits m))
    cores template0515 witness0515 := by
  rw [← coresFast_eq]
  exact fastCoverage0515

theorem coverageSize0515 : ∀ q : Pattern,
    (cores (witness0515 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0515 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0515
#print axioms coverageSize0515

noncomputable def pairing0516 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0516 : List (Fin 4935) := templateData0516

noncomputable def witness0516 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1546) else if t 2 = 1 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 193) else (if t 3 = 0 then 50 else if t 3 = 1 then 48 else 904)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 589) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2101) else (if t 3 = 0 then 1342 else if t 3 = 1 then 2090 else 2107)) else (if t 2 = 0 then (if t 3 = 0 then 4213 else if t 3 = 1 then 4211 else 3927) else if t 2 = 1 then (if t 3 = 0 then 3531 else if t 3 = 1 then 3528 else 2648) else (if t 3 = 0 then 2691 else if t 3 = 1 then 2690 else 2906))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1545) else if t 2 = 1 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 192) else (if t 3 = 0 then 49 else if t 3 = 1 then 47 else 903)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 588) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2100) else (if t 3 = 0 then 1341 else if t 3 = 1 then 2089 else 2106)) else (if t 2 = 0 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 592) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2102) else (if t 3 = 0 then 1344 else if t 3 = 1 then 2091 else 2108))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 1815 else 2763) else if t 2 = 1 then (if t 3 = 0 then 836 else if t 3 = 1 then 834 else 204) else (if t 3 = 0 then 3942 else if t 3 = 1 then 74 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1050 else 600) else if t 2 = 1 then (if t 3 = 0 then 1732 else if t 3 = 1 then 2081 else 2103) else (if t 3 = 0 then 1358 else if t 3 = 1 then 2097 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 1057 else if t 3 = 1 then 1056 else 602) else if t 2 = 1 then (if t 3 = 0 then 1735 else if t 3 = 1 then 2083 else 2105) else (if t 3 = 0 then 1361 else if t 3 = 1 then 2099 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4659 else (if jt.2.val < 2 then 4670 else 4664)) else (if jt.2.val < 4 then 4668 else (if jt.2.val < 5 then 4669 else 4662))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4695 else (if jt.2.val < 2 then 4706 else 4698)) else (if jt.2.val < 4 then 4704 else (if jt.2.val < 5 then 4705 else 4693)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2322 else (if jt.2.val < 2 then 2332 else 2333)) else (if jt.2.val < 4 then 2329 else (if jt.2.val < 5 then 2331 else 2330))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2043 else (if jt.2.val < 2 then 2093 else 2096)) else (if jt.2.val < 4 then 2092 else (if jt.2.val < 5 then 2095 else 2094)))))

checked_coverage fastCoverage0516 pairing0516 template0516 witness0516

theorem coverage0516 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0516) (maskBits m))
    cores template0516 witness0516 := by
  rw [← coresFast_eq]
  exact fastCoverage0516

theorem coverageSize0516 : ∀ q : Pattern,
    (cores (witness0516 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0516 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0516
#print axioms coverageSize0516

noncomputable def pairing0517 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0517 : List (Fin 4935) := templateData0517

noncomputable def witness0517 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 2117) else if t 2 = 1 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 171) else (if t 3 = 0 then 1012 else if t 3 = 1 then 992 else 173)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 567) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1411) else (if t 3 = 0 then 1777 else if t 3 = 1 then 1414 else 1415)) else (if t 2 = 0 then (if t 3 = 0 then 3959 else if t 3 = 1 then 3953 else 4207) else if t 2 = 1 then (if t 3 = 0 then 3227 else if t 3 = 1 then 3219 else 2630) else (if t 3 = 0 then 2868 else if t 3 = 1 then 2855 else 2633))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 2115) else if t 2 = 1 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 162) else (if t 3 = 0 then 1011 else if t 3 = 1 then 989 else 168)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 558) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1393) else (if t 3 = 0 then 1776 else if t 3 = 1 then 1400 else 1402)) else (if t 2 = 0 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 559) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1394) else (if t 3 = 0 then 1778 else if t 3 = 1 then 1401 else 1403))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1773 else 2984) else if t 2 = 1 then (if t 3 = 0 then 395 else if t 3 = 1 then 365 else 890) else (if t 3 = 0 then 4206 else if t 3 = 1 then 369 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 779 else if t 3 = 1 then 749 else 1106) else if t 2 = 1 then (if t 3 = 0 then 1449 else if t 3 = 1 then 1396 else 1398) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1404 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 782 else if t 3 = 1 then 750 else 1107) else if t 2 = 1 then (if t 3 = 0 then 1451 else if t 3 = 1 then 1397 else 1399) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1405 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4623 else (if jt.2.val < 2 then 4639 else 4628)) else (if jt.2.val < 4 then 4638 else (if jt.2.val < 5 then 4640 else 4625))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4413 else (if jt.2.val < 2 then 4423 else 4418)) else (if jt.2.val < 4 then 4422 else (if jt.2.val < 5 then 4424 else 4410)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2280 else (if jt.2.val < 2 then 2282 else 2285)) else (if jt.2.val < 4 then 2281 else (if jt.2.val < 5 then 2284 else 2283))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2094 else (if jt.2.val < 2 then 2114 else 2096)) else (if jt.2.val < 4 then 2112 else (if jt.2.val < 5 then 2113 else 2043)))))

checked_coverage fastCoverage0517 pairing0517 template0517 witness0517

theorem coverage0517 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0517) (maskBits m))
    cores template0517 witness0517 := by
  rw [← coresFast_eq]
  exact fastCoverage0517

theorem coverageSize0517 : ∀ q : Pattern,
    (cores (witness0517 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0517 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0517
#print axioms coverageSize0517

noncomputable def pairing0518 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0518 : List (Fin 4935) := templateData0518

noncomputable def witness0518 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 428 else 1116) else if t 2 = 1 then (if t 3 = 0 then 424 else if t 3 = 1 then 420 else 496) else (if t 3 = 0 then 2125 else if t 3 = 1 then 1507 else 1523)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 430 else if t 3 = 1 then 426 else 1114) else if t 2 = 1 then (if t 3 = 0 then 422 else if t 3 = 1 then 418 else 488) else (if t 3 = 0 then 448 else if t 3 = 1 then 445 else 489)) else (if t 2 = 0 then (if t 3 = 0 then 2732 else if t 3 = 1 then 2731 else 2985) else if t 2 = 1 then (if t 3 = 0 then 2730 else if t 3 = 1 then 2728 else 2740) else (if t 3 = 0 then 4205 else if t 3 = 1 then 3929 else 3935))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 427 else 1115) else if t 2 = 1 then (if t 3 = 0 then 423 else if t 3 = 1 then 419 else 492) else (if t 3 = 0 then 2124 else if t 3 = 1 then 1506 else 1521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 429 else if t 3 = 1 then 425 else 1113) else if t 2 = 1 then (if t 3 = 0 then 421 else if t 3 = 1 then 417 else 480) else (if t 3 = 0 then 447 else if t 3 = 1 then 444 else 482)) else (if t 2 = 0 then (if t 3 = 0 then 442 else if t 3 = 1 then 440 else 1117) else if t 2 = 1 then (if t 3 = 0 then 438 else if t 3 = 1 then 436 else 481) else (if t 3 = 0 then 454 else if t 3 = 1 then 453 else 483))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 468 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1133 else if t 3 = 1 then 463 else 494) else (if t 3 = 0 then 2988 else if t 3 = 1 then 1848 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1518 else if t 3 = 1 then 466 else 2148) else if t 2 = 1 then (if t 3 = 0 then 1131 else if t 3 = 1 then 461 else 484) else (if t 3 = 0 then 1137 else if t 3 = 1 then 474 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 1520 else if t 3 = 1 then 472 else 2149) else if t 2 = 1 then (if t 3 = 0 then 1135 else if t 3 = 1 then 470 else 485) else (if t 3 = 0 then 1139 else if t 3 = 1 then 478 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4680 else (if jt.2.val < 2 then 4688 else 4685)) else (if jt.2.val < 4 then 4686 else (if jt.2.val < 5 then 4687 else 4683))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2465 else (if jt.2.val < 2 then 2729 else 2469)) else (if jt.2.val < 4 then 2726 else (if jt.2.val < 5 then 2727 else 2437)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2330 else (if jt.2.val < 2 then 2345 else 2333)) else (if jt.2.val < 4 then 2343 else (if jt.2.val < 5 then 2344 else 2322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1272 else (if jt.2.val < 2 then 1274 else 1279)) else (if jt.2.val < 4 then 1273 else (if jt.2.val < 5 then 1278 else 1277)))))

checked_coverage fastCoverage0518 pairing0518 template0518 witness0518

theorem coverage0518 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0518) (maskBits m))
    cores template0518 witness0518 := by
  rw [← coresFast_eq]
  exact fastCoverage0518

theorem coverageSize0518 : ∀ q : Pattern,
    (cores (witness0518 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0518 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0518
#print axioms coverageSize0518

noncomputable def pairing0519 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0519 : List (Fin 4935) := templateData0519

noncomputable def witness0519 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1205 else 575) else if t 2 = 1 then (if t 3 = 0 then 1214 else if t 3 = 1 then 1187 else 1188) else (if t 3 = 0 then 1376 else if t 3 = 1 then 1801 else 2138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1201 else 568) else if t 2 = 1 then (if t 3 = 0 then 1210 else if t 3 = 1 then 1167 else 1170) else (if t 3 = 0 then 1211 else if t 3 = 1 then 1169 else 1171)) else (if t 2 = 0 then (if t 3 = 0 then 3004 else if t 3 = 1 then 3002 else 2757) else if t 2 = 1 then (if t 3 = 0 then 3003 else if t 3 = 1 then 2993 else 2995) else (if t 3 = 0 then 3967 else if t 3 = 1 then 4054 else 4203))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1203 else 572) else if t 2 = 1 then (if t 3 = 0 then 1212 else if t 3 = 1 then 1179 else 1181) else (if t 3 = 0 then 1374 else if t 3 = 1 then 1795 else 2136)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1197 else 562) else if t 2 = 1 then (if t 3 = 0 then 1206 else if t 3 = 1 then 1151 else 1155) else (if t 3 = 0 then 1208 else if t 3 = 1 then 1153 else 1157)) else (if t 2 = 0 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1198 else 563) else if t 2 = 1 then (if t 3 = 0 then 1207 else if t 3 = 1 then 1152 else 1156) else (if t 3 = 0 then 1209 else if t 3 = 1 then 1154 else 1158))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 761 else 3966) else if t 2 = 1 then (if t 3 = 0 then 696 else if t 3 = 1 then 1183 else 1185) else (if t 3 = 0 then 2782 else if t 3 = 1 then 1799 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2160 else if t 3 = 1 then 751 else 1542) else if t 2 = 1 then (if t 3 = 0 then 690 else if t 3 = 1 then 1159 else 1163) else (if t 3 = 0 then 692 else if t 3 = 1 then 1161 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 2162 else if t 3 = 1 then 752 else 1543) else if t 2 = 1 then (if t 3 = 0 then 691 else if t 3 = 1 then 1160 else 1164) else (if t 3 = 0 then 693 else if t 3 = 1 then 1162 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4692 else (if jt.2.val < 2 then 4708 else 4703)) else (if jt.2.val < 4 then 4707 else (if jt.2.val < 5 then 4709 else 4700))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2916 else (if jt.2.val < 2 then 2999 else 2936)) else (if jt.2.val < 4 then 2998 else (if jt.2.val < 5 then 3000 else 2907)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2283 else (if jt.2.val < 2 then 2311 else 2285)) else (if jt.2.val < 4 then 2310 else (if jt.2.val < 5 then 2312 else 2280))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1277 else (if jt.2.val < 2 then 1294 else 1279)) else (if jt.2.val < 4 then 1292 else (if jt.2.val < 5 then 1293 else 1272)))))

checked_coverage fastCoverage0519 pairing0519 template0519 witness0519

theorem coverage0519 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0519) (maskBits m))
    cores template0519 witness0519 := by
  rw [← coresFast_eq]
  exact fastCoverage0519

theorem coverageSize0519 : ∀ q : Pattern,
    (cores (witness0519 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0519 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0519
#print axioms coverageSize0519

end Crown.CertificateData
