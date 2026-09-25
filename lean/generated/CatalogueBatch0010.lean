import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0009

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0360 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0360 : List (Fin 4935) := templateData0360

noncomputable def witness0360 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3106) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 3003) else (if t 3 = 0 then 2770 else if t 3 = 1 then 2768 else 2781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 868) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 862) else (if t 3 = 0 then 144 else if t 3 = 1 then 140 else 199)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1648 else 1690) else if t 2 = 1 then (if t 3 = 0 then 1650 else if t 3 = 1 then 1646 else 864) else (if t 3 = 0 then 159 else if t 3 = 1 then 157 else 201))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 1213) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 1207) else (if t 3 = 0 then 638 else if t 3 = 1 then 634 else 691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2956) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3098) else (if t 3 = 0 then 3091 else if t 3 = 1 then 3089 else 3102)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2957) else if t 2 = 1 then (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3099) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3092 else 3103))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 439 else 505) else if t 2 = 1 then (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 499) else (if t 3 = 0 then 1520 else if t 3 = 1 then 1135 else 1525)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2504) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3080 else 3100) else (if t 3 = 0 then 3095 else if t 3 = 1 then 3094 else 3104)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2474 else 2505) else if t 2 = 1 then (if t 3 = 0 then 3084 else if t 3 = 1 then 3083 else 3101) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3096 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4314 else (if jt.2.val < 2 then 4324 else 4325)) else (if jt.2.val < 4 then 4321 else (if jt.2.val < 5 then 4323 else 4322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4315 else (if jt.2.val < 2 then 4319 else 4320)) else (if jt.2.val < 4 then 4316 else (if jt.2.val < 5 then 4318 else 4317)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3048 else (if jt.2.val < 2 then 3088 else 3090)) else (if jt.2.val < 4 then 3085 else (if jt.2.val < 5 then 3087 else 3086))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3042 else (if jt.2.val < 2 then 3044 else 3047)) else (if jt.2.val < 4 then 3043 else (if jt.2.val < 5 then 3046 else 3045)))))

checked_coverage fastCoverage0360 pairing0360 template0360 witness0360

theorem coverage0360 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0360) (maskBits m))
    cores template0360 witness0360 := by
  rw [← coresFast_eq]
  exact fastCoverage0360

theorem coverageSize0360 : ∀ q : Pattern,
    (cores (witness0360 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0360 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0360
#print axioms coverageSize0360

noncomputable def pairing0361 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0361 : List (Fin 4935) := templateData0361

noncomputable def witness0361 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3152) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 3002) else (if t 3 = 0 then 2798 else if t 3 = 1 then 2794 else 2795)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 859) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 853) else (if t 3 = 0 then 88 else if t 3 = 1 then 60 else 65)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1597 else 1599) else if t 2 = 1 then (if t 3 = 0 then 1611 else if t 3 = 1 then 1589 else 855) else (if t 3 = 0 then 95 else if t 3 = 1 then 62 else 67))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 1204) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 1198) else (if t 3 = 0 then 775 else if t 3 = 1 then 748 else 752)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2949) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3130) else (if t 3 = 0 then 3165 else if t 3 = 1 then 3126 else 3134)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2950) else if t 2 = 1 then (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3131) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3127 else 3135))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 571 else 573) else if t 2 = 1 then (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 563) else (if t 3 = 0 then 1550 else if t 3 = 1 then 1105 else 1543)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2556) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3123 else 3132) else (if t 3 = 0 then 3167 else if t 3 = 1 then 3128 else 3136)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2551 else 2557) else if t 2 = 1 then (if t 3 = 0 then 3164 else if t 3 = 1 then 3124 else 3133) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3129 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4326 else (if jt.2.val < 2 then 4328 else 4335)) else (if jt.2.val < 4 then 4327 else (if jt.2.val < 5 then 4334 else 4333))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4329 else (if jt.2.val < 2 then 4331 else 4337)) else (if jt.2.val < 4 then 4330 else (if jt.2.val < 5 then 4336 else 4332)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3110 else (if jt.2.val < 2 then 3112 else 3148)) else (if jt.2.val < 4 then 3111 else (if jt.2.val < 5 then 3147 else 3125))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3045 else (if jt.2.val < 2 then 3109 else 3047)) else (if jt.2.val < 4 then 3107 else (if jt.2.val < 5 then 3108 else 3042)))))

checked_coverage fastCoverage0361 pairing0361 template0361 witness0361

theorem coverage0361 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0361) (maskBits m))
    cores template0361 witness0361 := by
  rw [← coresFast_eq]
  exact fastCoverage0361

theorem coverageSize0361 : ∀ q : Pattern,
    (cores (witness0361 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0361 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0361
#print axioms coverageSize0361

noncomputable def pairing0362 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0362 : List (Fin 4935) := templateData0362

noncomputable def witness0362 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2598 else 2654) else if t 2 = 1 then (if t 3 = 0 then 2602 else if t 3 = 1 then 2594 else 2648) else (if t 3 = 0 then 3174 else if t 3 = 1 then 3172 else 3182)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2596 else 2104) else if t 2 = 1 then (if t 3 = 0 then 2600 else if t 3 = 1 then 2592 else 2101) else (if t 3 = 0 then 143 else if t 3 = 1 then 139 else 193)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 536 else 601) else if t 2 = 1 then (if t 3 = 0 then 538 else if t 3 = 1 then 534 else 589) else (if t 3 = 0 then 1538 else if t 3 = 1 then 1537 else 1546))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2597 else 2224) else if t 2 = 1 then (if t 3 = 0 then 2601 else if t 3 = 1 then 2593 else 2221) else (if t 3 = 0 then 637 else if t 3 = 1 then 633 else 685)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2595 else 2650) else if t 2 = 1 then (if t 3 = 0 then 2599 else if t 3 = 1 then 2591 else 2640) else (if t 3 = 0 then 2623 else if t 3 = 1 then 2620 else 2642)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2651) else if t 2 = 1 then (if t 3 = 0 then 2614 else if t 3 = 1 then 2611 else 2641) else (if t 3 = 0 then 2627 else if t 3 = 1 then 2625 else 2643))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1583 else 1621) else if t 2 = 1 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1581 else 1615) else (if t 3 = 0 then 665 else if t 3 = 1 then 663 else 687)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2897 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2632 else if t 3 = 1 then 2629 else 2644) else (if t 3 = 0 then 2637 else if t 3 = 1 then 2636 else 2646)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2899 else 3184) else if t 2 = 1 then (if t 3 = 0 then 2635 else if t 3 = 1 then 2634 else 2645) else (if t 3 = 0 then 2639 else if t 3 = 1 then 2638 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4338 else (if jt.2.val < 2 then 4342 else 4343)) else (if jt.2.val < 4 then 4339 else (if jt.2.val < 5 then 4341 else 4340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3715 else (if jt.2.val < 2 then 3719 else 3720)) else (if jt.2.val < 4 then 3716 else (if jt.2.val < 5 then 3718 else 3717)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3086 else (if jt.2.val < 2 then 3173 else 3090)) else (if jt.2.val < 4 then 3169 else (if jt.2.val < 5 then 3170 else 3048))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2581 else (if jt.2.val < 2 then 2583 else 2586)) else (if jt.2.val < 4 then 2582 else (if jt.2.val < 5 then 2585 else 2584)))))

checked_coverage fastCoverage0362 pairing0362 template0362 witness0362

theorem coverage0362 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0362) (maskBits m))
    cores template0362 witness0362 := by
  rw [← coresFast_eq]
  exact fastCoverage0362

theorem coverageSize0362 : ∀ q : Pattern,
    (cores (witness0362 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0362 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0362
#print axioms coverageSize0362

noncomputable def pairing0363 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0363 : List (Fin 4935) := templateData0363

noncomputable def witness0363 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2705 else 2706) else if t 2 = 1 then (if t 3 = 0 then 2710 else if t 3 = 1 then 2688 else 2690) else (if t 3 = 0 then 3198 else if t 3 = 1 then 3191 else 3192)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2703 else 2098) else if t 2 = 1 then (if t 3 = 0 then 2708 else if t 3 = 1 then 2682 else 2090) else (if t 3 = 0 then 87 else if t 3 = 1 then 43 else 48)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 475 else 477) else if t 2 = 1 then (if t 3 = 0 then 489 else if t 3 = 1 then 445 else 450) else (if t 3 = 0 then 1523 else if t 3 = 1 then 1507 else 1510))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2704 else 2218) else if t 2 = 1 then (if t 3 = 0 then 2709 else if t 3 = 1 then 2685 else 2212) else (if t 3 = 0 then 774 else if t 3 = 1 then 733 else 737)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2695 else 2699) else if t 2 = 1 then (if t 3 = 0 then 2707 else if t 3 = 1 then 2664 else 2674) else (if t 3 = 0 then 2717 else if t 3 = 1 then 2668 else 2676)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2700) else if t 2 = 1 then (if t 3 = 0 then 2715 else if t 3 = 1 then 2666 else 2675) else (if t 3 = 0 then 2719 else if t 3 = 1 then 2669 else 2677))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1672 else 1674) else if t 2 = 1 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1657 else 1659) else (if t 3 = 0 then 788 else if t 3 = 1 then 735 else 739)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2878 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2721 else if t 3 = 1 then 2670 else 2678) else (if t 3 = 0 then 2724 else if t 3 = 1 then 2672 else 2680)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2879 else 3197) else if t 2 = 1 then (if t 3 = 0 then 2723 else if t 3 = 1 then 2671 else 2679) else (if t 3 = 0 then 2725 else if t 3 = 1 then 2673 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4344 else (if jt.2.val < 2 then 4346 else 4349)) else (if jt.2.val < 4 then 4345 else (if jt.2.val < 5 then 4348 else 4347))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3729 else (if jt.2.val < 2 then 3731 else 3737)) else (if jt.2.val < 4 then 3730 else (if jt.2.val < 5 then 3736 else 3732)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3125 else (if jt.2.val < 2 then 3194 else 3148)) else (if jt.2.val < 4 then 3193 else (if jt.2.val < 5 then 3195 else 3110))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2584 else (if jt.2.val < 2 then 2657 else 2586)) else (if jt.2.val < 4 then 2655 else (if jt.2.val < 5 then 2656 else 2581)))))

checked_coverage fastCoverage0363 pairing0363 template0363 witness0363

theorem coverage0363 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0363) (maskBits m))
    cores template0363 witness0363 := by
  rw [← coresFast_eq]
  exact fastCoverage0363

theorem coverageSize0363 : ∀ q : Pattern,
    (cores (witness0363 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0363 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0363
#print axioms coverageSize0363

noncomputable def pairing0364 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0364 : List (Fin 4935) := templateData0364

noncomputable def witness0364 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 1376) else if t 2 = 1 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 1211) else (if t 3 = 0 then 648 else if t 3 = 1 then 644 else 695)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 1001) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1370) else (if t 3 = 0 then 1353 else if t 3 = 1 then 1350 else 1372)) else (if t 2 = 0 then (if t 3 = 0 then 3236 else if t 3 = 1 then 3234 else 3242) else if t 2 = 1 then (if t 3 = 0 then 3235 else if t 3 = 1 then 3232 else 2860) else (if t 3 = 0 then 2547 else if t 3 = 1 then 2545 else 2577))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 1374) else if t 2 = 1 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 1208) else (if t 3 = 0 then 647 else if t 3 = 1 then 643 else 692)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 998) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1362) else (if t 3 = 0 then 1352 else if t 3 = 1 then 1349 else 1366)) else (if t 2 = 0 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 999) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1363) else (if t 3 = 0 then 1355 else if t 3 = 1 then 1354 else 1367))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 2124 else 2744) else if t 2 = 1 then (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 500) else (if t 3 = 0 then 3206 else if t 3 = 1 then 1137 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 98) else if t 2 = 1 then (if t 3 = 0 then 1341 else if t 3 = 1 then 1338 else 1364) else (if t 3 = 0 then 1358 else if t 3 = 1 then 1356 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 54 else if t 3 = 1 then 52 else 99) else if t 2 = 1 then (if t 3 = 0 then 1344 else if t 3 = 1 then 1343 else 1365) else (if t 3 = 0 then 1361 else if t 3 = 1 then 1360 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4344 else (if jt.2.val < 2 then 4355 else 4349)) else (if jt.2.val < 4 then 4353 else (if jt.2.val < 5 then 4354 else 4347))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4317 else (if jt.2.val < 2 then 4352 else 4320)) else (if jt.2.val < 4 then 4350 else (if jt.2.val < 5 then 4351 else 4315)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1302 else (if jt.2.val < 2 then 1348 else 1351)) else (if jt.2.val < 4 then 1345 else (if jt.2.val < 5 then 1347 else 1346))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1296 else (if jt.2.val < 2 then 1298 else 1301)) else (if jt.2.val < 4 then 1297 else (if jt.2.val < 5 then 1300 else 1299)))))

checked_coverage fastCoverage0364 pairing0364 template0364 witness0364

theorem coverage0364 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0364) (maskBits m))
    cores template0364 witness0364 := by
  rw [← coresFast_eq]
  exact fastCoverage0364

theorem coverageSize0364 : ∀ q : Pattern,
    (cores (witness0364 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0364 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0364
#print axioms coverageSize0364

noncomputable def pairing0365 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0365 : List (Fin 4935) := templateData0365

noncomputable def witness0365 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 1433) else if t 2 = 1 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 1202) else (if t 3 = 0 then 780 else if t 3 = 1 then 756 else 758)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 992) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1414) else (if t 3 = 0 then 1450 else if t 3 = 1 then 1412 else 1416)) else (if t 2 = 0 then (if t 3 = 0 then 3228 else if t 3 = 1 then 3225 else 3226) else if t 2 = 1 then (if t 3 = 0 then 3227 else if t 3 = 1 then 3219 else 2855) else (if t 3 = 0 then 2501 else if t 3 = 1 then 2482 else 2485))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 1430) else if t 2 = 1 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 1199) else (if t 3 = 0 then 779 else if t 3 = 1 then 749 else 753)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 989) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1400) else (if t 3 = 0 then 1449 else if t 3 = 1 then 1396 else 1404)) else (if t 2 = 0 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 990) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1401) else (if t 3 = 0 then 1451 else if t 3 = 1 then 1397 else 1405))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 2115 else 2758) else if t 2 = 1 then (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 564) else (if t 3 = 0 then 3216 else if t 3 = 1 then 1106 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 168) else if t 2 = 1 then (if t 3 = 0 then 1446 else if t 3 = 1 then 1393 else 1402) else (if t 3 = 0 then 1452 else if t 3 = 1 then 1398 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 197 else if t 3 = 1 then 163 else 169) else if t 2 = 1 then (if t 3 = 0 then 1448 else if t 3 = 1 then 1394 else 1403) else (if t 3 = 0 then 1454 else if t 3 = 1 then 1399 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4338 else (if jt.2.val < 2 then 4357 else 4343)) else (if jt.2.val < 4 then 4356 else (if jt.2.val < 5 then 4358 else 4340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4332 else (if jt.2.val < 2 then 4360 else 4337)) else (if jt.2.val < 4 then 4359 else (if jt.2.val < 5 then 4361 else 4329)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1380 else (if jt.2.val < 2 then 1382 else 1426)) else (if jt.2.val < 4 then 1381 else (if jt.2.val < 5 then 1425 else 1395))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1299 else (if jt.2.val < 2 then 1379 else 1301)) else (if jt.2.val < 4 then 1377 else (if jt.2.val < 5 then 1378 else 1296)))))

checked_coverage fastCoverage0365 pairing0365 template0365 witness0365

theorem coverage0365 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0365) (maskBits m))
    cores template0365 witness0365 := by
  rw [← coresFast_eq]
  exact fastCoverage0365

theorem coverageSize0365 : ∀ q : Pattern,
    (cores (witness0365 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0365 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0365
#print axioms coverageSize0365

noncomputable def pairing0366 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0366 : List (Fin 4935) := templateData0366

noncomputable def witness0366 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 224 else 308) else if t 2 = 1 then (if t 3 = 0 then 228 else if t 3 = 1 then 220 else 298) else (if t 3 = 0 then 1462 else if t 3 = 1 then 1459 else 1475)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 230 else if t 3 = 1 then 222 else 304) else if t 2 = 1 then (if t 3 = 0 then 226 else if t 3 = 1 then 218 else 290) else (if t 3 = 0 then 256 else if t 3 = 1 then 251 else 291)) else (if t 2 = 0 then (if t 3 = 0 then 2751 else if t 3 = 1 then 2749 else 2762) else if t 2 = 1 then (if t 3 = 0 then 2750 else if t 3 = 1 then 2747 else 2759) else (if t 3 = 0 then 3210 else if t 3 = 1 then 3209 else 3215))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 223 else 306) else if t 2 = 1 then (if t 3 = 0 then 227 else if t 3 = 1 then 219 else 294) else (if t 3 = 0 then 1461 else if t 3 = 1 then 1458 else 1473)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 229 else if t 3 = 1 then 221 else 300) else if t 2 = 1 then (if t 3 = 0 then 225 else if t 3 = 1 then 217 else 282) else (if t 3 = 0 then 255 else if t 3 = 1 then 250 else 284)) else (if t 2 = 0 then (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 301) else if t 2 = 1 then (if t 3 = 0 then 242 else if t 3 = 1 then 237 else 283) else (if t 3 = 0 then 261 else if t 3 = 1 then 259 else 285))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 917 else 3229) else if t 2 = 1 then (if t 3 = 0 then 270 else if t 3 = 1 then 265 else 296) else (if t 3 = 0 then 2777 else if t 3 = 1 then 2169 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1470 else if t 3 = 1 then 915 else 1476) else if t 2 = 1 then (if t 3 = 0 then 268 else if t 3 = 1 then 263 else 286) else (if t 3 = 0 then 278 else if t 3 = 1 then 276 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 1472 else if t 3 = 1 then 919 else 1477) else if t 2 = 1 then (if t 3 = 0 then 274 else if t 3 = 1 then 272 else 287) else (if t 3 = 0 then 281 else if t 3 = 1 then 280 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4326 else (if jt.2.val < 2 then 4364 else 4335)) else (if jt.2.val < 4 then 4362 else (if jt.2.val < 5 then 4363 else 4333))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3717 else (if jt.2.val < 2 then 3752 else 3720)) else (if jt.2.val < 4 then 3750 else (if jt.2.val < 5 then 3751 else 3715)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1346 else (if jt.2.val < 2 then 1460 else 1351)) else (if jt.2.val < 4 then 1455 else (if jt.2.val < 5 then 1456 else 1302))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 207 else (if jt.2.val < 2 then 209 else 212)) else (if jt.2.val < 4 then 208 else (if jt.2.val < 5 then 211 else 210)))))

checked_coverage fastCoverage0366 pairing0366 template0366 witness0366

theorem coverage0366 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0366) (maskBits m))
    cores template0366 witness0366 := by
  rw [← coresFast_eq]
  exact fastCoverage0366

theorem coverageSize0366 : ∀ q : Pattern,
    (cores (witness0366 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0366 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0366
#print axioms coverageSize0366

noncomputable def pairing0367 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0367 : List (Fin 4935) := templateData0367

noncomputable def witness0367 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 379 else 380) else if t 2 = 1 then (if t 3 = 0 then 384 else if t 3 = 1 then 356 else 358) else (if t 3 = 0 then 1498 else if t 3 = 1 then 1489 else 1490)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 386 else if t 3 = 1 then 371 else 373) else if t 2 = 1 then (if t 3 = 0 then 382 else if t 3 = 1 then 336 else 342) else (if t 3 = 0 then 394 else if t 3 = 1 then 339 else 343)) else (if t 2 = 0 then (if t 3 = 0 then 2741 else if t 3 = 1 then 2737 else 2738) else if t 2 = 1 then (if t 3 = 0 then 2740 else if t 3 = 1 then 2728 else 2731) else (if t 3 = 0 then 3207 else if t 3 = 1 then 3203 else 3205))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 375 else 377) else if t 2 = 1 then (if t 3 = 0 then 383 else if t 3 = 1 then 346 else 352) else (if t 3 = 0 then 1497 else if t 3 = 1 then 1483 else 1487)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 385 else if t 3 = 1 then 363 else 367) else if t 2 = 1 then (if t 3 = 0 then 381 else if t 3 = 1 then 318 else 328) else (if t 3 = 0 then 393 else if t 3 = 1 then 322 else 330)) else (if t 2 = 0 then (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 368) else if t 2 = 1 then (if t 3 = 0 then 389 else if t 3 = 1 then 320 else 329) else (if t 3 = 0 then 397 else if t 3 = 1 then 323 else 331))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 894 else 3240) else if t 2 = 1 then (if t 3 = 0 then 401 else if t 3 = 1 then 350 else 354) else (if t 3 = 0 then 2801 else if t 3 = 1 then 2157 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1500 else if t 3 = 1 then 888 else 1494) else if t 2 = 1 then (if t 3 = 0 then 399 else if t 3 = 1 then 324 else 332) else (if t 3 = 0 then 405 else if t 3 = 1 then 326 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 1502 else if t 3 = 1 then 889 else 1495) else if t 2 = 1 then (if t 3 = 0 then 403 else if t 3 = 1 then 325 else 333) else (if t 3 = 0 then 407 else if t 3 = 1 then 327 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4314 else (if jt.2.val < 2 then 4366 else 4325)) else (if jt.2.val < 4 then 4365 else (if jt.2.val < 5 then 4367 else 4322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3732 else (if jt.2.val < 2 then 3760 else 3737)) else (if jt.2.val < 4 then 3759 else (if jt.2.val < 5 then 3761 else 3729)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1395 else (if jt.2.val < 2 then 1492 else 1426)) else (if jt.2.val < 4 then 1491 else (if jt.2.val < 5 then 1493 else 1380))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 210 else (if jt.2.val < 2 then 311 else 212)) else (if jt.2.val < 4 then 309 else (if jt.2.val < 5 then 310 else 207)))))

checked_coverage fastCoverage0367 pairing0367 template0367 witness0367

theorem coverage0367 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0367) (maskBits m))
    cores template0367 witness0367 := by
  rw [← coresFast_eq]
  exact fastCoverage0367

theorem coverageSize0367 : ∀ q : Pattern,
    (cores (witness0367 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0367 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0367
#print axioms coverageSize0367

noncomputable def pairing0368 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0368 : List (Fin 4935) := templateData0368

noncomputable def witness0368 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3198) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2797) else (if t 3 = 0 then 2770 else if t 3 = 1 then 2769 else 2989)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 87) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 86) else (if t 3 = 0 then 144 else if t 3 = 1 then 142 else 898)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1879 else 1523) else if t 2 = 1 then (if t 3 = 0 then 1881 else if t 3 = 1 then 1877 else 94) else (if t 3 = 0 then 159 else if t 3 = 1 then 158 else 900))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 774) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 773) else (if t 3 = 0 then 638 else if t 3 = 1 then 636 else 1141)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2717) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3295) else (if t 3 = 0 then 3091 else if t 3 = 1 then 3291 else 3299)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2719) else if t 2 = 1 then (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3296) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3292 else 3300))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1040 else 788) else if t 2 = 1 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 787) else (if t 3 = 0 then 1520 else if t 3 = 1 then 664 else 1825)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2724) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3276 else 3297) else (if t 3 = 0 then 3095 else if t 3 = 1 then 3293 else 3301)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2841 else 2725) else if t 2 = 1 then (if t 3 = 0 then 3280 else if t 3 = 1 then 3279 else 3298) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3294 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4368 else (if jt.2.val < 2 then 4378 else 4379)) else (if jt.2.val < 4 then 4375 else (if jt.2.val < 5 then 4377 else 4376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4369 else (if jt.2.val < 2 then 4373 else 4374)) else (if jt.2.val < 4 then 4370 else (if jt.2.val < 5 then 4372 else 4371)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3244 else (if jt.2.val < 2 then 3289 else 3290)) else (if jt.2.val < 4 then 3286 else (if jt.2.val < 5 then 3288 else 3287))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3243 else (if jt.2.val < 2 then 3282 else 3285)) else (if jt.2.val < 4 then 3281 else (if jt.2.val < 5 then 3284 else 3283)))))

checked_coverage fastCoverage0368 pairing0368 template0368 witness0368

theorem coverage0368 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0368) (maskBits m))
    cores template0368 witness0368 := by
  rw [← coresFast_eq]
  exact fastCoverage0368

theorem coverageSize0368 : ∀ q : Pattern,
    (cores (witness0368 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0368 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0368
#print axioms coverageSize0368

noncomputable def pairing0369 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0369 : List (Fin 4935) := templateData0369

noncomputable def witness0369 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3312) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 2794) else (if t 3 = 0 then 3004 else if t 3 = 1 then 3002 else 2795)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 73) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 60) else (if t 3 = 0 then 874 else if t 3 = 1 then 853 else 65)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1597 else 1849) else if t 2 = 1 then (if t 3 = 0 then 1611 else if t 3 = 1 then 1589 else 62) else (if t 3 = 0 then 878 else if t 3 = 1 then 855 else 67))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 760) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 748) else (if t 3 = 0 then 1219 else if t 3 = 1 then 1198 else 752)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2697) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3126) else (if t 3 = 0 then 3313 else if t 3 = 1 then 3130 else 3134)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2698) else if t 2 = 1 then (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3127) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3131 else 3135))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 571 else 1111) else if t 2 = 1 then (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 1105) else (if t 3 = 0 then 1838 else if t 3 = 1 then 563 else 1543)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2880) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3123 else 3128) else (if t 3 = 0 then 3315 else if t 3 = 1 then 3132 else 3136)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2551 else 2881) else if t 2 = 1 then (if t 3 = 0 then 3164 else if t 3 = 1 then 3124 else 3129) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3133 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4326 else (if jt.2.val < 2 then 4328 else 4335)) else (if jt.2.val < 4 then 4327 else (if jt.2.val < 5 then 4334 else 4333))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4329 else (if jt.2.val < 2 then 4331 else 4337)) else (if jt.2.val < 4 then 4330 else (if jt.2.val < 5 then 4336 else 4332)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3305 else (if jt.2.val < 2 then 3307 else 3311)) else (if jt.2.val < 4 then 3306 else (if jt.2.val < 5 then 3310 else 3309))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3283 else (if jt.2.val < 2 then 3308 else 3285)) else (if jt.2.val < 4 then 3303 else (if jt.2.val < 5 then 3304 else 3243)))))

checked_coverage fastCoverage0369 pairing0369 template0369 witness0369

theorem coverage0369 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0369) (maskBits m))
    cores template0369 witness0369 := by
  rw [← coresFast_eq]
  exact fastCoverage0369

theorem coverageSize0369 : ∀ q : Pattern,
    (cores (witness0369 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0369 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0369
#print axioms coverageSize0369

noncomputable def pairing0370 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0370 : List (Fin 4935) := templateData0370

noncomputable def witness0370 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2602 else 2906) else if t 2 = 1 then (if t 3 = 0 then 2598 else if t 3 = 1 then 2594 else 2648) else (if t 3 = 0 then 3320 else if t 3 = 1 then 3172 else 3182)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2600 else 2107) else if t 2 = 1 then (if t 3 = 0 then 2596 else if t 3 = 1 then 2592 else 2101) else (if t 3 = 0 then 141 else if t 3 = 1 then 139 else 193)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 538 else 1120) else if t 2 = 1 then (if t 3 = 0 then 536 else if t 3 = 1 then 534 else 589) else (if t 3 = 0 then 1835 else if t 3 = 1 then 1537 else 1546))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2601 else 2227) else if t 2 = 1 then (if t 3 = 0 then 2597 else if t 3 = 1 then 2593 else 2221) else (if t 3 = 0 then 635 else if t 3 = 1 then 633 else 685)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2599 else 2902) else if t 2 = 1 then (if t 3 = 0 then 2595 else if t 3 = 1 then 2591 else 2640) else (if t 3 = 0 then 2622 else if t 3 = 1 then 2620 else 2642)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2903) else if t 2 = 1 then (if t 3 = 0 then 2613 else if t 3 = 1 then 2611 else 2641) else (if t 3 = 0 then 2626 else if t 3 = 1 then 2625 else 2643))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1585 else 1855) else if t 2 = 1 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1581 else 1615) else (if t 3 = 0 then 1136 else if t 3 = 1 then 663 else 687)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2632 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2897 else if t 3 = 1 then 2629 else 2644) else (if t 3 = 0 then 2900 else if t 3 = 1 then 2636 else 2646)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2635 else 3322) else if t 2 = 1 then (if t 3 = 0 then 2899 else if t 3 = 1 then 2634 else 2645) else (if t 3 = 0 then 2901 else if t 3 = 1 then 2638 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4338 else (if jt.2.val < 2 then 4342 else 4343)) else (if jt.2.val < 4 then 4339 else (if jt.2.val < 5 then 4341 else 4340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3715 else (if jt.2.val < 2 then 3719 else 3720)) else (if jt.2.val < 4 then 3716 else (if jt.2.val < 5 then 3718 else 3717)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3287 else (if jt.2.val < 2 then 3319 else 3290)) else (if jt.2.val < 4 then 3317 else (if jt.2.val < 5 then 3318 else 3244))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2890 else (if jt.2.val < 2 then 2892 else 2895)) else (if jt.2.val < 4 then 2891 else (if jt.2.val < 5 then 2894 else 2893)))))

checked_coverage fastCoverage0370 pairing0370 template0370 witness0370

theorem coverage0370 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0370) (maskBits m))
    cores template0370 witness0370 := by
  rw [← coresFast_eq]
  exact fastCoverage0370

theorem coverageSize0370 : ∀ q : Pattern,
    (cores (witness0370 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0370 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0370
#print axioms coverageSize0370

noncomputable def pairing0371 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0371 : List (Fin 4935) := templateData0371

noncomputable def witness0371 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2953 else 2706) else if t 2 = 1 then (if t 3 = 0 then 2960 else if t 3 = 1 then 2937 else 2939) else (if t 3 = 0 then 3106 else if t 3 = 1 then 3329 else 3330)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2951 else 2098) else if t 2 = 1 then (if t 3 = 0 then 2958 else if t 3 = 1 then 2931 else 2082) else (if t 3 = 0 then 868 else if t 3 = 1 then 830 else 835)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1075 else 477) else if t 2 = 1 then (if t 3 = 0 then 1084 else if t 3 = 1 then 1046 else 1051) else (if t 3 = 0 then 1690 else if t 3 = 1 then 1813 else 1816))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2952 else 2218) else if t 2 = 1 then (if t 3 = 0 then 2959 else if t 3 = 1 then 2934 else 2206) else (if t 3 = 0 then 1213 else if t 3 = 1 then 1180 else 1184)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2947 else 2699) else if t 2 = 1 then (if t 3 = 0 then 2954 else if t 3 = 1 then 2913 else 2923) else (if t 3 = 0 then 2956 else if t 3 = 1 then 2917 else 2925)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2700) else if t 2 = 1 then (if t 3 = 0 then 2955 else if t 3 = 1 then 2915 else 2924) else (if t 3 = 0 then 2957 else if t 3 = 1 then 2918 else 2926))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1903 else 1674) else if t 2 = 1 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1888 else 1890) else (if t 3 = 0 then 505 else if t 3 = 1 then 1182 else 1186)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2554 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2502 else if t 3 = 1 then 2919 else 2927) else (if t 3 = 0 then 2504 else if t 3 = 1 then 2921 else 2929)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2555 else 3197) else if t 2 = 1 then (if t 3 = 0 then 2503 else if t 3 = 1 then 2920 else 2928) else (if t 3 = 0 then 2505 else if t 3 = 1 then 2922 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4380 else (if jt.2.val < 2 then 4382 else 4385)) else (if jt.2.val < 4 then 4381 else (if jt.2.val < 5 then 4384 else 4383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3777 else (if jt.2.val < 2 then 3779 else 3785)) else (if jt.2.val < 4 then 3778 else (if jt.2.val < 5 then 3784 else 3780)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3309 else (if jt.2.val < 2 then 3332 else 3311)) else (if jt.2.val < 4 then 3331 else (if jt.2.val < 5 then 3333 else 3305))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2893 else (if jt.2.val < 2 then 2943 else 2895)) else (if jt.2.val < 4 then 2941 else (if jt.2.val < 5 then 2942 else 2890)))))

checked_coverage fastCoverage0371 pairing0371 template0371 witness0371

theorem coverage0371 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0371) (maskBits m))
    cores template0371 witness0371 := by
  rw [← coresFast_eq]
  exact fastCoverage0371

theorem coverageSize0371 : ∀ q : Pattern,
    (cores (witness0371 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0371 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0371
#print axioms coverageSize0371

noncomputable def pairing0372 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0372 : List (Fin 4935) := templateData0372

noncomputable def witness0372 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 1498) else if t 2 = 1 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 778) else (if t 3 = 0 then 648 else if t 3 = 1 then 646 else 1145)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 394) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1753) else (if t 3 = 0 then 1353 else if t 3 = 1 then 1747 else 1762)) else (if t 2 = 0 then (if t 3 = 0 then 3352 else if t 3 = 1 then 3350 else 3207) else if t 2 = 1 then (if t 3 = 0 then 3351 else if t 3 = 1 then 3348 else 2500) else (if t 3 = 0 then 2547 else if t 3 = 1 then 2546 else 2884))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 1497) else if t 2 = 1 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 777) else (if t 3 = 0 then 647 else if t 3 = 1 then 645 else 1142)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 393) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1752) else (if t 3 = 0 then 1352 else if t 3 = 1 then 1746 else 1758)) else (if t 2 = 0 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 397) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1754) else (if t 3 = 0 then 1355 else if t 3 = 1 then 1748 else 1759))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 2145 else 2801) else if t 2 = 1 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 789) else (if t 3 = 0 then 3206 else if t 3 = 1 then 668 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 405) else if t 2 = 1 then (if t 3 = 0 then 1732 else if t 3 = 1 then 1729 else 1755) else (if t 3 = 0 then 1358 else if t 3 = 1 then 1749 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 841 else if t 3 = 1 then 839 else 407) else if t 2 = 1 then (if t 3 = 0 then 1735 else if t 3 = 1 then 1734 else 1757) else (if t 3 = 0 then 1361 else if t 3 = 1 then 1751 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4380 else (if jt.2.val < 2 then 4391 else 4385)) else (if jt.2.val < 4 then 4389 else (if jt.2.val < 5 then 4390 else 4383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4371 else (if jt.2.val < 2 then 4388 else 4374)) else (if jt.2.val < 4 then 4386 else (if jt.2.val < 5 then 4387 else 4369)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1693 else (if jt.2.val < 2 then 1744 else 1745)) else (if jt.2.val < 4 then 1741 else (if jt.2.val < 5 then 1743 else 1742))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1692 else (if jt.2.val < 2 then 1737 else 1740)) else (if jt.2.val < 4 then 1736 else (if jt.2.val < 5 then 1739 else 1738)))))

checked_coverage fastCoverage0372 pairing0372 template0372 witness0372

theorem coverage0372 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0372) (maskBits m))
    cores template0372 witness0372 := by
  rw [← coresFast_eq]
  exact fastCoverage0372

theorem coverageSize0372 : ∀ q : Pattern,
    (cores (witness0372 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0372 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0372
#print axioms coverageSize0372

noncomputable def pairing0373 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0373 : List (Fin 4935) := templateData0373

noncomputable def witness0373 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 1775) else if t 2 = 1 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 756) else (if t 3 = 0 then 1222 else if t 3 = 1 then 1202 else 758)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 372) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1412) else (if t 3 = 0 then 1777 else if t 3 = 1 then 1414 else 1416)) else (if t 2 = 0 then (if t 3 = 0 then 3228 else if t 3 = 1 then 3225 else 3344) else if t 2 = 1 then (if t 3 = 0 then 3227 else if t 3 = 1 then 3219 else 2482) else (if t 3 = 0 then 2868 else if t 3 = 1 then 2855 else 2485))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 1773) else if t 2 = 1 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 749) else (if t 3 = 0 then 1221 else if t 3 = 1 then 1199 else 753)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 365) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1396) else (if t 3 = 0 then 1776 else if t 3 = 1 then 1400 else 1404)) else (if t 2 = 0 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 366) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1397) else (if t 3 = 0 then 1778 else if t 3 = 1 then 1401 else 1405))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 2115 else 2984) else if t 2 = 1 then (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 1106) else (if t 3 = 0 then 3343 else if t 3 = 1 then 564 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 890) else if t 2 = 1 then (if t 3 = 0 then 1446 else if t 3 = 1 then 1393 else 1398) else (if t 3 = 0 then 1779 else if t 3 = 1 then 1402 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 197 else if t 3 = 1 then 163 else 891) else if t 2 = 1 then (if t 3 = 0 then 1448 else if t 3 = 1 then 1394 else 1399) else (if t 3 = 0 then 1781 else if t 3 = 1 then 1403 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4338 else (if jt.2.val < 2 then 4357 else 4343)) else (if jt.2.val < 4 then 4356 else (if jt.2.val < 5 then 4358 else 4340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4332 else (if jt.2.val < 2 then 4360 else 4337)) else (if jt.2.val < 4 then 4359 else (if jt.2.val < 5 then 4361 else 4329)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1766 else (if jt.2.val < 2 then 1768 else 1772)) else (if jt.2.val < 4 then 1767 else (if jt.2.val < 5 then 1771 else 1770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1738 else (if jt.2.val < 2 then 1769 else 1740)) else (if jt.2.val < 4 then 1764 else (if jt.2.val < 5 then 1765 else 1692)))))

checked_coverage fastCoverage0373 pairing0373 template0373 witness0373

theorem coverage0373 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0373) (maskBits m))
    cores template0373 witness0373 := by
  rw [← coresFast_eq]
  exact fastCoverage0373

theorem coverageSize0373 : ∀ q : Pattern,
    (cores (witness0373 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0373 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0373
#print axioms coverageSize0373

noncomputable def pairing0374 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0374 : List (Fin 4935) := templateData0374

noncomputable def witness0374 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 228 else 932) else if t 2 = 1 then (if t 3 = 0 then 224 else if t 3 = 1 then 220 else 298) else (if t 3 = 0 then 1786 else if t 3 = 1 then 1459 else 1475)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 230 else if t 3 = 1 then 226 else 928) else if t 2 = 1 then (if t 3 = 0 then 222 else if t 3 = 1 then 218 else 290) else (if t 3 = 0 then 254 else if t 3 = 1 then 251 else 291)) else (if t 2 = 0 then (if t 3 = 0 then 2751 else if t 3 = 1 then 2750 else 2985) else if t 2 = 1 then (if t 3 = 0 then 2749 else if t 3 = 1 then 2747 else 2759) else (if t 3 = 0 then 3342 else if t 3 = 1 then 3209 else 3215))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 227 else 930) else if t 2 = 1 then (if t 3 = 0 then 223 else if t 3 = 1 then 219 else 294) else (if t 3 = 0 then 1785 else if t 3 = 1 then 1458 else 1473)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 229 else if t 3 = 1 then 225 else 924) else if t 2 = 1 then (if t 3 = 0 then 221 else if t 3 = 1 then 217 else 282) else (if t 3 = 0 then 253 else if t 3 = 1 then 250 else 284)) else (if t 2 = 0 then (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 925) else if t 2 = 1 then (if t 3 = 0 then 240 else if t 3 = 1 then 237 else 283) else (if t 3 = 0 then 260 else if t 3 = 1 then 259 else 285))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 270 else 3345) else if t 2 = 1 then (if t 3 = 0 then 917 else if t 3 = 1 then 265 else 296) else (if t 3 = 0 then 2988 else if t 3 = 1 then 2169 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1470 else if t 3 = 1 then 268 else 1788) else if t 2 = 1 then (if t 3 = 0 then 915 else if t 3 = 1 then 263 else 286) else (if t 3 = 0 then 921 else if t 3 = 1 then 276 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 1472 else if t 3 = 1 then 274 else 1789) else if t 2 = 1 then (if t 3 = 0 then 919 else if t 3 = 1 then 272 else 287) else (if t 3 = 0 then 923 else if t 3 = 1 then 280 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4326 else (if jt.2.val < 2 then 4364 else 4335)) else (if jt.2.val < 4 then 4362 else (if jt.2.val < 5 then 4363 else 4333))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3717 else (if jt.2.val < 2 then 3752 else 3720)) else (if jt.2.val < 4 then 3750 else (if jt.2.val < 5 then 3751 else 3715)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1742 else (if jt.2.val < 2 then 1784 else 1745)) else (if jt.2.val < 4 then 1782 else (if jt.2.val < 5 then 1783 else 1693))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 908 else (if jt.2.val < 2 then 910 else 913)) else (if jt.2.val < 4 then 909 else (if jt.2.val < 5 then 912 else 911)))))

checked_coverage fastCoverage0374 pairing0374 template0374 witness0374

theorem coverage0374 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0374) (maskBits m))
    cores template0374 witness0374 := by
  rw [← coresFast_eq]
  exact fastCoverage0374

theorem coverageSize0374 : ∀ q : Pattern,
    (cores (witness0374 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0374 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0374
#print axioms coverageSize0374

noncomputable def pairing0375 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0375 : List (Fin 4935) := templateData0375

noncomputable def witness0375 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 995 else 380) else if t 2 = 1 then (if t 3 = 0 then 1004 else if t 3 = 1 then 977 else 979) else (if t 3 = 0 then 1376 else if t 3 = 1 then 1801 else 1802)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1006 else if t 3 = 1 then 991 else 373) else if t 2 = 1 then (if t 3 = 0 then 1000 else if t 3 = 1 then 957 else 963) else (if t 3 = 0 then 1001 else if t 3 = 1 then 960 else 964)) else (if t 2 = 0 then (if t 3 = 0 then 2981 else if t 3 = 1 then 2979 else 2738) else if t 2 = 1 then (if t 3 = 0 then 2980 else if t 3 = 1 then 2970 else 2973) else (if t 3 = 0 then 3242 else if t 3 = 1 then 3338 else 3340))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 993 else 377) else if t 2 = 1 then (if t 3 = 0 then 1002 else if t 3 = 1 then 967 else 973) else (if t 3 = 0 then 1374 else if t 3 = 1 then 1795 else 1799)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1005 else if t 3 = 1 then 987 else 367) else if t 2 = 1 then (if t 3 = 0 then 996 else if t 3 = 1 then 939 else 949) else (if t 3 = 0 then 998 else if t 3 = 1 then 943 else 951)) else (if t 2 = 0 then (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 368) else if t 2 = 1 then (if t 3 = 0 then 997 else if t 3 = 1 then 941 else 950) else (if t 3 = 0 then 999 else if t 3 = 1 then 944 else 952))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 176 else 3240) else if t 2 = 1 then (if t 3 = 0 then 102 else if t 3 = 1 then 971 else 975) else (if t 3 = 0 then 2744 else if t 3 = 1 then 2136 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1806 else if t 3 = 1 then 166 else 1494) else if t 2 = 1 then (if t 3 = 0 then 96 else if t 3 = 1 then 945 else 953) else (if t 3 = 0 then 98 else if t 3 = 1 then 947 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 1808 else if t 3 = 1 then 167 else 1495) else if t 2 = 1 then (if t 3 = 0 then 97 else if t 3 = 1 then 946 else 954) else (if t 3 = 0 then 99 else if t 3 = 1 then 948 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4368 else (if jt.2.val < 2 then 4393 else 4379)) else (if jt.2.val < 4 then 4392 else (if jt.2.val < 5 then 4394 else 4376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3780 else (if jt.2.val < 2 then 3796 else 3785)) else (if jt.2.val < 4 then 3795 else (if jt.2.val < 5 then 3797 else 3777)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1770 else (if jt.2.val < 2 then 1804 else 1772)) else (if jt.2.val < 4 then 1803 else (if jt.2.val < 5 then 1805 else 1766))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 911 else (if jt.2.val < 2 then 983 else 913)) else (if jt.2.val < 4 then 981 else (if jt.2.val < 5 then 982 else 908)))))

checked_coverage fastCoverage0375 pairing0375 template0375 witness0375

theorem coverage0375 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0375) (maskBits m))
    cores template0375 witness0375 := by
  rw [← coresFast_eq]
  exact fastCoverage0375

theorem coverageSize0375 : ∀ q : Pattern,
    (cores (witness0375 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0375 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0375
#print axioms coverageSize0375

noncomputable def pairing0376 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0376 : List (Fin 4935) := templateData0376

noncomputable def witness0376 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3174) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2769) else (if t 3 = 0 then 2798 else if t 3 = 1 then 2797 else 2989)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 143) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 142) else (if t 3 = 0 then 88 else if t 3 = 1 then 86 else 898)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1879 else 1538) else if t 2 = 1 then (if t 3 = 0 then 1881 else if t 3 = 1 then 1877 else 158) else (if t 3 = 0 then 95 else if t 3 = 1 then 94 else 900))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 637) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 636) else (if t 3 = 0 then 775 else if t 3 = 1 then 773 else 1141)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2623) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3291) else (if t 3 = 0 then 3165 else if t 3 = 1 then 3295 else 3299)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2627) else if t 2 = 1 then (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3292) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3296 else 3300))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1040 else 665) else if t 2 = 1 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 664) else (if t 3 = 0 then 1550 else if t 3 = 1 then 787 else 1825)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2637) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3276 else 3293) else (if t 3 = 0 then 3167 else if t 3 = 1 then 3297 else 3301)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2841 else 2639) else if t 2 = 1 then (if t 3 = 0 then 3280 else if t 3 = 1 then 3279 else 3294) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3298 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4368 else (if jt.2.val < 2 then 4378 else 4379)) else (if jt.2.val < 4 then 4375 else (if jt.2.val < 5 then 4377 else 4376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4369 else (if jt.2.val < 2 then 4373 else 4374)) else (if jt.2.val < 4 then 4370 else (if jt.2.val < 5 then 4372 else 4371)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3357 else (if jt.2.val < 2 then 3363 else 3368)) else (if jt.2.val < 4 then 3362 else (if jt.2.val < 5 then 3367 else 3366))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3358 else (if jt.2.val < 2 then 3364 else 3365)) else (if jt.2.val < 4 then 3359 else (if jt.2.val < 5 then 3361 else 3360)))))

checked_coverage fastCoverage0376 pairing0376 template0376 witness0376

theorem coverage0376 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0376) (maskBits m))
    cores template0376 witness0376 := by
  rw [← coresFast_eq]
  exact fastCoverage0376

theorem coverageSize0376 : ∀ q : Pattern,
    (cores (witness0376 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0376 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0376
#print axioms coverageSize0376

noncomputable def pairing0377 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0377 : List (Fin 4935) := templateData0377

noncomputable def witness0377 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3320) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 2768) else (if t 3 = 0 then 3004 else if t 3 = 1 then 3003 else 2781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 141) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 140) else (if t 3 = 0 then 874 else if t 3 = 1 then 862 else 199)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1648 else 1835) else if t 2 = 1 then (if t 3 = 0 then 1650 else if t 3 = 1 then 1646 else 157) else (if t 3 = 0 then 878 else if t 3 = 1 then 864 else 201))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 635) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 634) else (if t 3 = 0 then 1219 else if t 3 = 1 then 1207 else 691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2622) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3089) else (if t 3 = 0 then 3313 else if t 3 = 1 then 3098 else 3102)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2626) else if t 2 = 1 then (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3092) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3099 else 3103))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 439 else 1136) else if t 2 = 1 then (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 1135) else (if t 3 = 0 then 1838 else if t 3 = 1 then 499 else 1525)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2900) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3080 else 3094) else (if t 3 = 0 then 3315 else if t 3 = 1 then 3100 else 3104)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2474 else 2901) else if t 2 = 1 then (if t 3 = 0 then 3084 else if t 3 = 1 then 3083 else 3096) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3101 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4314 else (if jt.2.val < 2 then 4324 else 4325)) else (if jt.2.val < 4 then 4321 else (if jt.2.val < 5 then 4323 else 4322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4315 else (if jt.2.val < 2 then 4319 else 4320)) else (if jt.2.val < 4 then 4316 else (if jt.2.val < 5 then 4318 else 4317)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3371 else (if jt.2.val < 2 then 3373 else 3377)) else (if jt.2.val < 4 then 3372 else (if jt.2.val < 5 then 3376 else 3375))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3360 else (if jt.2.val < 2 then 3374 else 3365)) else (if jt.2.val < 4 then 3369 else (if jt.2.val < 5 then 3370 else 3358)))))

checked_coverage fastCoverage0377 pairing0377 template0377 witness0377

theorem coverage0377 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0377) (maskBits m))
    cores template0377 witness0377 := by
  rw [← coresFast_eq]
  exact fastCoverage0377

theorem coverageSize0377 : ∀ q : Pattern,
    (cores (witness0377 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0377 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0377
#print axioms coverageSize0377

noncomputable def pairing0378 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0378 : List (Fin 4935) := templateData0378

noncomputable def witness0378 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2710 else 2906) else if t 2 = 1 then (if t 3 = 0 then 2705 else if t 3 = 1 then 2688 else 2690) else (if t 3 = 0 then 3312 else if t 3 = 1 then 3191 else 3192)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2708 else 2107) else if t 2 = 1 then (if t 3 = 0 then 2703 else if t 3 = 1 then 2682 else 2090) else (if t 3 = 0 then 73 else if t 3 = 1 then 43 else 48)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 489 else 1120) else if t 2 = 1 then (if t 3 = 0 then 475 else if t 3 = 1 then 445 else 450) else (if t 3 = 0 then 1849 else if t 3 = 1 then 1507 else 1510))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2709 else 2227) else if t 2 = 1 then (if t 3 = 0 then 2704 else if t 3 = 1 then 2685 else 2212) else (if t 3 = 0 then 760 else if t 3 = 1 then 733 else 737)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2707 else 2902) else if t 2 = 1 then (if t 3 = 0 then 2695 else if t 3 = 1 then 2664 else 2674) else (if t 3 = 0 then 2697 else if t 3 = 1 then 2668 else 2676)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2903) else if t 2 = 1 then (if t 3 = 0 then 2696 else if t 3 = 1 then 2666 else 2675) else (if t 3 = 0 then 2698 else if t 3 = 1 then 2669 else 2677))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1686 else 1855) else if t 2 = 1 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1657 else 1659) else (if t 3 = 0 then 1111 else if t 3 = 1 then 735 else 739)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2721 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2878 else if t 3 = 1 then 2670 else 2678) else (if t 3 = 0 then 2880 else if t 3 = 1 then 2672 else 2680)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2723 else 3322) else if t 2 = 1 then (if t 3 = 0 then 2879 else if t 3 = 1 then 2671 else 2679) else (if t 3 = 0 then 2881 else if t 3 = 1 then 2673 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4344 else (if jt.2.val < 2 then 4346 else 4349)) else (if jt.2.val < 4 then 4345 else (if jt.2.val < 5 then 4348 else 4347))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3729 else (if jt.2.val < 2 then 3731 else 3737)) else (if jt.2.val < 4 then 3730 else (if jt.2.val < 5 then 3736 else 3732)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3366 else (if jt.2.val < 2 then 3380 else 3368)) else (if jt.2.val < 4 then 3378 else (if jt.2.val < 5 then 3379 else 3357))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3029 else (if jt.2.val < 2 then 3031 else 3035)) else (if jt.2.val < 4 then 3030 else (if jt.2.val < 5 then 3034 else 3032)))))

checked_coverage fastCoverage0378 pairing0378 template0378 witness0378

theorem coverage0378 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0378) (maskBits m))
    cores template0378 witness0378 := by
  rw [← coresFast_eq]
  exact fastCoverage0378

theorem coverageSize0378 : ∀ q : Pattern,
    (cores (witness0378 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0378 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0378
#print axioms coverageSize0378

noncomputable def pairing0379 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0379 : List (Fin 4935) := templateData0379

noncomputable def witness0379 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2960 else 2654) else if t 2 = 1 then (if t 3 = 0 then 2953 else if t 3 = 1 then 2937 else 2939) else (if t 3 = 0 then 3152 else if t 3 = 1 then 3329 else 3330)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2958 else 2104) else if t 2 = 1 then (if t 3 = 0 then 2951 else if t 3 = 1 then 2931 else 2082) else (if t 3 = 0 then 859 else if t 3 = 1 then 830 else 835)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1084 else 601) else if t 2 = 1 then (if t 3 = 0 then 1075 else if t 3 = 1 then 1046 else 1051) else (if t 3 = 0 then 1599 else if t 3 = 1 then 1813 else 1816))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2959 else 2224) else if t 2 = 1 then (if t 3 = 0 then 2952 else if t 3 = 1 then 2934 else 2206) else (if t 3 = 0 then 1204 else if t 3 = 1 then 1180 else 1184)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2954 else 2650) else if t 2 = 1 then (if t 3 = 0 then 2947 else if t 3 = 1 then 2913 else 2923) else (if t 3 = 0 then 2949 else if t 3 = 1 then 2917 else 2925)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2651) else if t 2 = 1 then (if t 3 = 0 then 2948 else if t 3 = 1 then 2915 else 2924) else (if t 3 = 0 then 2950 else if t 3 = 1 then 2918 else 2926))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1909 else 1621) else if t 2 = 1 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1888 else 1890) else (if t 3 = 0 then 573 else if t 3 = 1 then 1182 else 1186)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2502 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2554 else if t 3 = 1 then 2919 else 2927) else (if t 3 = 0 then 2556 else if t 3 = 1 then 2921 else 2929)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2503 else 3184) else if t 2 = 1 then (if t 3 = 0 then 2555 else if t 3 = 1 then 2920 else 2928) else (if t 3 = 0 then 2557 else if t 3 = 1 then 2922 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4380 else (if jt.2.val < 2 then 4382 else 4385)) else (if jt.2.val < 4 then 4381 else (if jt.2.val < 5 then 4384 else 4383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3777 else (if jt.2.val < 2 then 3779 else 3785)) else (if jt.2.val < 4 then 3778 else (if jt.2.val < 5 then 3784 else 3780)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3375 else (if jt.2.val < 2 then 3383 else 3377)) else (if jt.2.val < 4 then 3381 else (if jt.2.val < 5 then 3382 else 3371))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3032 else (if jt.2.val < 2 then 3039 else 3035)) else (if jt.2.val < 4 then 3038 else (if jt.2.val < 5 then 3041 else 3029)))))

checked_coverage fastCoverage0379 pairing0379 template0379 witness0379

theorem coverage0379 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0379) (maskBits m))
    cores template0379 witness0379 := by
  rw [← coresFast_eq]
  exact fastCoverage0379

theorem coverageSize0379 : ∀ q : Pattern,
    (cores (witness0379 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0379 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0379
#print axioms coverageSize0379

noncomputable def pairing0380 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0380 : List (Fin 4935) := templateData0380

noncomputable def witness0380 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 1462) else if t 2 = 1 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 646) else (if t 3 = 0 then 780 else if t 3 = 1 then 778 else 1145)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 256) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1747) else (if t 3 = 0 then 1450 else if t 3 = 1 then 1753 else 1762)) else (if t 2 = 0 then (if t 3 = 0 then 3352 else if t 3 = 1 then 3350 else 3210) else if t 2 = 1 then (if t 3 = 0 then 3351 else if t 3 = 1 then 3348 else 2546) else (if t 3 = 0 then 2501 else if t 3 = 1 then 2500 else 2884))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 1461) else if t 2 = 1 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 645) else (if t 3 = 0 then 779 else if t 3 = 1 then 777 else 1142)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 255) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1746) else (if t 3 = 0 then 1449 else if t 3 = 1 then 1752 else 1758)) else (if t 2 = 0 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 261) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1748) else (if t 3 = 0 then 1451 else if t 3 = 1 then 1754 else 1759))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 2145 else 2777) else if t 2 = 1 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 668) else (if t 3 = 0 then 3216 else if t 3 = 1 then 789 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 278) else if t 2 = 1 then (if t 3 = 0 then 1732 else if t 3 = 1 then 1729 else 1749) else (if t 3 = 0 then 1452 else if t 3 = 1 then 1755 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 841 else if t 3 = 1 then 839 else 281) else if t 2 = 1 then (if t 3 = 0 then 1735 else if t 3 = 1 then 1734 else 1751) else (if t 3 = 0 then 1454 else if t 3 = 1 then 1757 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4380 else (if jt.2.val < 2 then 4391 else 4385)) else (if jt.2.val < 4 then 4389 else (if jt.2.val < 5 then 4390 else 4383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4371 else (if jt.2.val < 2 then 4388 else 4374)) else (if jt.2.val < 4 then 4386 else (if jt.2.val < 5 then 4387 else 4369)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1917 else (if jt.2.val < 2 then 1923 else 1928)) else (if jt.2.val < 4 then 1922 else (if jt.2.val < 5 then 1927 else 1926))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1918 else (if jt.2.val < 2 then 1924 else 1925)) else (if jt.2.val < 4 then 1919 else (if jt.2.val < 5 then 1921 else 1920)))))

checked_coverage fastCoverage0380 pairing0380 template0380 witness0380

theorem coverage0380 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0380) (maskBits m))
    cores template0380 witness0380 := by
  rw [← coresFast_eq]
  exact fastCoverage0380

theorem coverageSize0380 : ∀ q : Pattern,
    (cores (witness0380 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0380 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0380
#print axioms coverageSize0380

noncomputable def pairing0381 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0381 : List (Fin 4935) := templateData0381

noncomputable def witness0381 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 1786) else if t 2 = 1 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 644) else (if t 3 = 0 then 1222 else if t 3 = 1 then 1211 else 695)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 254) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1350) else (if t 3 = 0 then 1777 else if t 3 = 1 then 1370 else 1372)) else (if t 2 = 0 then (if t 3 = 0 then 3236 else if t 3 = 1 then 3234 else 3342) else if t 2 = 1 then (if t 3 = 0 then 3235 else if t 3 = 1 then 3232 else 2545) else (if t 3 = 0 then 2868 else if t 3 = 1 then 2860 else 2577))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 1785) else if t 2 = 1 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 643) else (if t 3 = 0 then 1221 else if t 3 = 1 then 1208 else 692)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 253) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1349) else (if t 3 = 0 then 1776 else if t 3 = 1 then 1362 else 1366)) else (if t 2 = 0 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 260) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1354) else (if t 3 = 0 then 1778 else if t 3 = 1 then 1363 else 1367))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 2124 else 2988) else if t 2 = 1 then (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 1137) else (if t 3 = 0 then 3343 else if t 3 = 1 then 500 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 921) else if t 2 = 1 then (if t 3 = 0 then 1341 else if t 3 = 1 then 1338 else 1356) else (if t 3 = 0 then 1779 else if t 3 = 1 then 1364 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 54 else if t 3 = 1 then 52 else 923) else if t 2 = 1 then (if t 3 = 0 then 1344 else if t 3 = 1 then 1343 else 1360) else (if t 3 = 0 then 1781 else if t 3 = 1 then 1365 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4344 else (if jt.2.val < 2 then 4355 else 4349)) else (if jt.2.val < 4 then 4353 else (if jt.2.val < 5 then 4354 else 4347))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4317 else (if jt.2.val < 2 then 4352 else 4320)) else (if jt.2.val < 4 then 4350 else (if jt.2.val < 5 then 4351 else 4315)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1931 else (if jt.2.val < 2 then 1933 else 1937)) else (if jt.2.val < 4 then 1932 else (if jt.2.val < 5 then 1936 else 1935))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1920 else (if jt.2.val < 2 then 1934 else 1925)) else (if jt.2.val < 4 then 1929 else (if jt.2.val < 5 then 1930 else 1918)))))

checked_coverage fastCoverage0381 pairing0381 template0381 witness0381

theorem coverage0381 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0381) (maskBits m))
    cores template0381 witness0381 := by
  rw [← coresFast_eq]
  exact fastCoverage0381

theorem coverageSize0381 : ∀ q : Pattern,
    (cores (witness0381 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0381 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0381
#print axioms coverageSize0381

noncomputable def pairing0382 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0382 : List (Fin 4935) := templateData0382

noncomputable def witness0382 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 384 else 932) else if t 2 = 1 then (if t 3 = 0 then 379 else if t 3 = 1 then 356 else 358) else (if t 3 = 0 then 1775 else if t 3 = 1 then 1489 else 1490)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 386 else if t 3 = 1 then 382 else 928) else if t 2 = 1 then (if t 3 = 0 then 371 else if t 3 = 1 then 336 else 342) else (if t 3 = 0 then 372 else if t 3 = 1 then 339 else 343)) else (if t 2 = 0 then (if t 3 = 0 then 2741 else if t 3 = 1 then 2740 else 2985) else if t 2 = 1 then (if t 3 = 0 then 2737 else if t 3 = 1 then 2728 else 2731) else (if t 3 = 0 then 3344 else if t 3 = 1 then 3203 else 3205))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 383 else 930) else if t 2 = 1 then (if t 3 = 0 then 375 else if t 3 = 1 then 346 else 352) else (if t 3 = 0 then 1773 else if t 3 = 1 then 1483 else 1487)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 385 else if t 3 = 1 then 381 else 924) else if t 2 = 1 then (if t 3 = 0 then 363 else if t 3 = 1 then 318 else 328) else (if t 3 = 0 then 365 else if t 3 = 1 then 322 else 330)) else (if t 2 = 0 then (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 925) else if t 2 = 1 then (if t 3 = 0 then 364 else if t 3 = 1 then 320 else 329) else (if t 3 = 0 then 366 else if t 3 = 1 then 323 else 331))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 401 else 3345) else if t 2 = 1 then (if t 3 = 0 then 894 else if t 3 = 1 then 350 else 354) else (if t 3 = 0 then 2984 else if t 3 = 1 then 2157 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1500 else if t 3 = 1 then 399 else 1788) else if t 2 = 1 then (if t 3 = 0 then 888 else if t 3 = 1 then 324 else 332) else (if t 3 = 0 then 890 else if t 3 = 1 then 326 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 1502 else if t 3 = 1 then 403 else 1789) else if t 2 = 1 then (if t 3 = 0 then 889 else if t 3 = 1 then 325 else 333) else (if t 3 = 0 then 891 else if t 3 = 1 then 327 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4314 else (if jt.2.val < 2 then 4366 else 4325)) else (if jt.2.val < 4 then 4365 else (if jt.2.val < 5 then 4367 else 4322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3732 else (if jt.2.val < 2 then 3760 else 3737)) else (if jt.2.val < 4 then 3759 else (if jt.2.val < 5 then 3761 else 3729)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1926 else (if jt.2.val < 2 then 1940 else 1928)) else (if jt.2.val < 4 then 1938 else (if jt.2.val < 5 then 1939 else 1917))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1247 else (if jt.2.val < 2 then 1249 else 1253)) else (if jt.2.val < 4 then 1248 else (if jt.2.val < 5 then 1252 else 1250)))))

checked_coverage fastCoverage0382 pairing0382 template0382 witness0382

theorem coverage0382 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0382) (maskBits m))
    cores template0382 witness0382 := by
  rw [← coresFast_eq]
  exact fastCoverage0382

theorem coverageSize0382 : ∀ q : Pattern,
    (cores (witness0382 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0382 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0382
#print axioms coverageSize0382

noncomputable def pairing0383 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0383 : List (Fin 4935) := templateData0383

noncomputable def witness0383 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 1004 else 308) else if t 2 = 1 then (if t 3 = 0 then 995 else if t 3 = 1 then 977 else 979) else (if t 3 = 0 then 1433 else if t 3 = 1 then 1801 else 1802)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1006 else if t 3 = 1 then 1000 else 304) else if t 2 = 1 then (if t 3 = 0 then 991 else if t 3 = 1 then 957 else 963) else (if t 3 = 0 then 992 else if t 3 = 1 then 960 else 964)) else (if t 2 = 0 then (if t 3 = 0 then 2981 else if t 3 = 1 then 2980 else 2762) else if t 2 = 1 then (if t 3 = 0 then 2979 else if t 3 = 1 then 2970 else 2973) else (if t 3 = 0 then 3226 else if t 3 = 1 then 3338 else 3340))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 1002 else 306) else if t 2 = 1 then (if t 3 = 0 then 993 else if t 3 = 1 then 967 else 973) else (if t 3 = 0 then 1430 else if t 3 = 1 then 1795 else 1799)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1005 else if t 3 = 1 then 996 else 300) else if t 2 = 1 then (if t 3 = 0 then 987 else if t 3 = 1 then 939 else 949) else (if t 3 = 0 then 989 else if t 3 = 1 then 943 else 951)) else (if t 2 = 0 then (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 301) else if t 2 = 1 then (if t 3 = 0 then 988 else if t 3 = 1 then 941 else 950) else (if t 3 = 0 then 990 else if t 3 = 1 then 944 else 952))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 102 else 3229) else if t 2 = 1 then (if t 3 = 0 then 176 else if t 3 = 1 then 971 else 975) else (if t 3 = 0 then 2758 else if t 3 = 1 then 2136 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1806 else if t 3 = 1 then 96 else 1476) else if t 2 = 1 then (if t 3 = 0 then 166 else if t 3 = 1 then 945 else 953) else (if t 3 = 0 then 168 else if t 3 = 1 then 947 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 1808 else if t 3 = 1 then 97 else 1477) else if t 2 = 1 then (if t 3 = 0 then 167 else if t 3 = 1 then 946 else 954) else (if t 3 = 0 then 169 else if t 3 = 1 then 948 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4368 else (if jt.2.val < 2 then 4393 else 4379)) else (if jt.2.val < 4 then 4392 else (if jt.2.val < 5 then 4394 else 4376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3780 else (if jt.2.val < 2 then 3796 else 3785)) else (if jt.2.val < 4 then 3795 else (if jt.2.val < 5 then 3797 else 3777)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1935 else (if jt.2.val < 2 then 1943 else 1937)) else (if jt.2.val < 4 then 1941 else (if jt.2.val < 5 then 1942 else 1931))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1250 else (if jt.2.val < 2 then 1257 else 1253)) else (if jt.2.val < 4 then 1256 else (if jt.2.val < 5 then 1259 else 1247)))))

checked_coverage fastCoverage0383 pairing0383 template0383 witness0383

theorem coverage0383 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0383) (maskBits m))
    cores template0383 witness0383 := by
  rw [← coresFast_eq]
  exact fastCoverage0383

theorem coverageSize0383 : ∀ q : Pattern,
    (cores (witness0383 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0383 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0383
#print axioms coverageSize0383

noncomputable def pairing0384 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0384 : List (Fin 4935) := templateData0384

noncomputable def witness0384 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 3860) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2980) else (if t 3 = 0 then 2751 else if t 3 = 1 then 2749 else 2762)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 1084) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 1078) else (if t 3 = 0 then 539 else if t 3 = 1 then 535 else 595)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1648 else 1690) else if t 2 = 1 then (if t 3 = 0 then 1651 else if t 3 = 1 then 1647 else 1080) else (if t 3 = 0 then 555 else if t 3 = 1 then 553 else 597))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 1003) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 997) else (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 301)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2955) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3852) else (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3856)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2957) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3853) else (if t 3 = 0 then 3847 else if t 3 = 1 then 3846 else 3857))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 33 else 103) else if t 2 = 1 then (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 97) else (if t 3 = 0 then 1472 else if t 3 = 1 then 919 else 1477)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2503) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3854) else (if t 3 = 0 then 3849 else if t 3 = 1 then 3848 else 3858)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2474 else 2505) else if t 2 = 1 then (if t 3 = 0 then 3838 else if t 3 = 1 then 3837 else 3855) else (if t 3 = 0 then 3851 else if t 3 = 1 then 3850 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4395 else (if jt.2.val < 2 then 4405 else 4406)) else (if jt.2.val < 4 then 4402 else (if jt.2.val < 5 then 4404 else 4403))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4396 else (if jt.2.val < 2 then 4400 else 4401)) else (if jt.2.val < 4 then 4397 else (if jt.2.val < 5 then 4399 else 4398)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3804 else (if jt.2.val < 2 then 3842 else 3844)) else (if jt.2.val < 4 then 3839 else (if jt.2.val < 5 then 3841 else 3840))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3798 else (if jt.2.val < 2 then 3800 else 3803)) else (if jt.2.val < 4 then 3799 else (if jt.2.val < 5 then 3802 else 3801)))))

checked_coverage fastCoverage0384 pairing0384 template0384 witness0384

theorem coverage0384 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0384) (maskBits m))
    cores template0384 witness0384 := by
  rw [← coresFast_eq]
  exact fastCoverage0384

theorem coverageSize0384 : ∀ q : Pattern,
    (cores (witness0384 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0384 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0384
#print axioms coverageSize0384

noncomputable def pairing0385 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0385 : List (Fin 4935) := templateData0385

noncomputable def witness0385 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 3905) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2979) else (if t 3 = 0 then 2741 else if t 3 = 1 then 2737 else 2738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 1075) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 1069) else (if t 3 = 0 then 490 else if t 3 = 1 then 462 else 467)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1597 else 1599) else if t 2 = 1 then (if t 3 = 0 then 1612 else if t 3 = 1 then 1593 else 1071) else (if t 3 = 0 then 497 else if t 3 = 1 then 464 else 469))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 994) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 988) else (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 368)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2948) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3884) else (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3888)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2950) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3885) else (if t 3 = 0 then 3918 else if t 3 = 1 then 3881 else 3889))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 175 else 177) else if t 2 = 1 then (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 167) else (if t 3 = 0 then 1502 else if t 3 = 1 then 889 else 1495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2555) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3886) else (if t 3 = 0 then 3919 else if t 3 = 1 then 3882 else 3890)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2551 else 2557) else if t 2 = 1 then (if t 3 = 0 then 3916 else if t 3 = 1 then 3878 else 3887) else (if t 3 = 0 then 3920 else if t 3 = 1 then 3883 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4407 else (if jt.2.val < 2 then 4409 else 4416)) else (if jt.2.val < 4 then 4408 else (if jt.2.val < 5 then 4415 else 4414))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4410 else (if jt.2.val < 2 then 4412 else 4418)) else (if jt.2.val < 4 then 4411 else (if jt.2.val < 5 then 4417 else 4413)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3864 else (if jt.2.val < 2 then 3866 else 3901)) else (if jt.2.val < 4 then 3865 else (if jt.2.val < 5 then 3900 else 3879))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3801 else (if jt.2.val < 2 then 3863 else 3803)) else (if jt.2.val < 4 then 3861 else (if jt.2.val < 5 then 3862 else 3798)))))

checked_coverage fastCoverage0385 pairing0385 template0385 witness0385

theorem coverage0385 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0385) (maskBits m))
    cores template0385 witness0385 := by
  rw [← coresFast_eq]
  exact fastCoverage0385

theorem coverageSize0385 : ∀ q : Pattern,
    (cores (witness0385 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0385 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0385
#print axioms coverageSize0385

noncomputable def pairing0386 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0386 : List (Fin 4935) := templateData0386

noncomputable def witness0386 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2598 else 2654) else if t 2 = 1 then (if t 3 = 0 then 2602 else if t 3 = 1 then 2594 else 2648) else (if t 3 = 0 then 3925 else if t 3 = 1 then 3923 else 3927)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2596 else 2104) else if t 2 = 1 then (if t 3 = 0 then 2600 else if t 3 = 1 then 2592 else 2101) else (if t 3 = 0 then 538 else if t 3 = 1 then 534 else 589)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 141 else 205) else if t 2 = 1 then (if t 3 = 0 then 143 else if t 3 = 1 then 139 else 193) else (if t 3 = 0 then 1538 else if t 3 = 1 then 1537 else 1546))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2597 else 2224) else if t 2 = 1 then (if t 3 = 0 then 2601 else if t 3 = 1 then 2593 else 2221) else (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 295)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2595 else 2650) else if t 2 = 1 then (if t 3 = 0 then 2599 else if t 3 = 1 then 2591 else 2640) else (if t 3 = 0 then 2614 else if t 3 = 1 then 2611 else 2641)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2622 else 2652) else if t 2 = 1 then (if t 3 = 0 then 2623 else if t 3 = 1 then 2620 else 2642) else (if t 3 = 0 then 2627 else if t 3 = 1 then 2625 else 2643))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1583 else 1621) else if t 2 = 1 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1581 else 1615) else (if t 3 = 0 then 275 else if t 3 = 1 then 273 else 297)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2897 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2632 else if t 3 = 1 then 2629 else 2644) else (if t 3 = 0 then 2635 else if t 3 = 1 then 2634 else 2645)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2900 else 3928) else if t 2 = 1 then (if t 3 = 0 then 2637 else if t 3 = 1 then 2636 else 2646) else (if t 3 = 0 then 2639 else if t 3 = 1 then 2638 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4338 else (if jt.2.val < 2 then 4342 else 4343)) else (if jt.2.val < 4 then 4339 else (if jt.2.val < 5 then 4341 else 4340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2589 else (if jt.2.val < 2 then 2619 else 2621)) else (if jt.2.val < 4 then 2616 else (if jt.2.val < 5 then 2618 else 2617)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3840 else (if jt.2.val < 2 then 3924 else 3844)) else (if jt.2.val < 4 then 3921 else (if jt.2.val < 5 then 3922 else 3804))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2581 else (if jt.2.val < 2 then 2583 else 2586)) else (if jt.2.val < 4 then 2582 else (if jt.2.val < 5 then 2585 else 2584)))))

checked_coverage fastCoverage0386 pairing0386 template0386 witness0386

theorem coverage0386 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0386) (maskBits m))
    cores template0386 witness0386 := by
  rw [← coresFast_eq]
  exact fastCoverage0386

theorem coverageSize0386 : ∀ q : Pattern,
    (cores (witness0386 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0386 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0386
#print axioms coverageSize0386

noncomputable def pairing0387 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0387 : List (Fin 4935) := templateData0387

noncomputable def witness0387 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2705 else 2706) else if t 2 = 1 then (if t 3 = 0 then 2710 else if t 3 = 1 then 2688 else 2690) else (if t 3 = 0 then 3935 else if t 3 = 1 then 3929 else 3930)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2703 else 2098) else if t 2 = 1 then (if t 3 = 0 then 2708 else if t 3 = 1 then 2682 else 2090) else (if t 3 = 0 then 489 else if t 3 = 1 then 445 else 450)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 73 else 75) else if t 2 = 1 then (if t 3 = 0 then 87 else if t 3 = 1 then 43 else 48) else (if t 3 = 0 then 1523 else if t 3 = 1 then 1507 else 1510))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2704 else 2218) else if t 2 = 1 then (if t 3 = 0 then 2709 else if t 3 = 1 then 2685 else 2212) else (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 353)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2695 else 2699) else if t 2 = 1 then (if t 3 = 0 then 2707 else if t 3 = 1 then 2664 else 2674) else (if t 3 = 0 then 2715 else if t 3 = 1 then 2666 else 2675)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2697 else 2701) else if t 2 = 1 then (if t 3 = 0 then 2717 else if t 3 = 1 then 2668 else 2676) else (if t 3 = 0 then 2719 else if t 3 = 1 then 2669 else 2677))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1672 else 1674) else if t 2 = 1 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1657 else 1659) else (if t 3 = 0 then 404 else if t 3 = 1 then 351 else 355)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2878 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2721 else if t 3 = 1 then 2670 else 2678) else (if t 3 = 0 then 2723 else if t 3 = 1 then 2671 else 2679)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2880 else 3934) else if t 2 = 1 then (if t 3 = 0 then 2724 else if t 3 = 1 then 2672 else 2680) else (if t 3 = 0 then 2725 else if t 3 = 1 then 2673 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4344 else (if jt.2.val < 2 then 4346 else 4349)) else (if jt.2.val < 4 then 4345 else (if jt.2.val < 5 then 4348 else 4347))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2658 else (if jt.2.val < 2 then 2660 else 2687)) else (if jt.2.val < 4 then 2659 else (if jt.2.val < 5 then 2686 else 2667)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3879 else (if jt.2.val < 2 then 3932 else 3901)) else (if jt.2.val < 4 then 3931 else (if jt.2.val < 5 then 3933 else 3864))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2584 else (if jt.2.val < 2 then 2657 else 2586)) else (if jt.2.val < 4 then 2655 else (if jt.2.val < 5 then 2656 else 2581)))))

checked_coverage fastCoverage0387 pairing0387 template0387 witness0387

theorem coverage0387 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0387) (maskBits m))
    cores template0387 witness0387 := by
  rw [← coresFast_eq]
  exact fastCoverage0387

theorem coverageSize0387 : ∀ q : Pattern,
    (cores (witness0387 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0387 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0387
#print axioms coverageSize0387

noncomputable def pairing0388 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0388 : List (Fin 4935) := templateData0388

noncomputable def witness0388 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 1376) else if t 2 = 1 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 1001) else (if t 3 = 0 then 258 else if t 3 = 1 then 254 else 305)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 1211) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1370) else (if t 3 = 0 then 1353 else if t 3 = 1 then 1350 else 1372)) else (if t 2 = 0 then (if t 3 = 0 then 3965 else if t 3 = 1 then 3963 else 3967) else if t 2 = 1 then (if t 3 = 0 then 3235 else if t 3 = 1 then 3232 else 2860) else (if t 3 = 0 then 2547 else if t 3 = 1 then 2545 else 2577))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 1374) else if t 2 = 1 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 998) else (if t 3 = 0 then 257 else if t 3 = 1 then 253 else 302)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 1208) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1362) else (if t 3 = 0 then 1352 else if t 3 = 1 then 1349 else 1366)) else (if t 2 = 0 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 1209) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1363) else (if t 3 = 0 then 1355 else if t 3 = 1 then 1354 else 1367))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 2124 else 2744) else if t 2 = 1 then (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 98) else (if t 3 = 0 then 3942 else if t 3 = 1 then 921 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 500) else if t 2 = 1 then (if t 3 = 0 then 1341 else if t 3 = 1 then 1338 else 1364) else (if t 3 = 0 then 1358 else if t 3 = 1 then 1356 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 456 else if t 3 = 1 then 454 else 501) else if t 2 = 1 then (if t 3 = 0 then 1344 else if t 3 = 1 then 1343 else 1365) else (if t 3 = 0 then 1361 else if t 3 = 1 then 1360 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4344 else (if jt.2.val < 2 then 4355 else 4349)) else (if jt.2.val < 4 then 4353 else (if jt.2.val < 5 then 4354 else 4347))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4398 else (if jt.2.val < 2 then 4421 else 4401)) else (if jt.2.val < 4 then 4419 else (if jt.2.val < 5 then 4420 else 4396)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1971 else (if jt.2.val < 2 then 1981 else 1982)) else (if jt.2.val < 4 then 1978 else (if jt.2.val < 5 then 1980 else 1979))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1296 else (if jt.2.val < 2 then 1298 else 1301)) else (if jt.2.val < 4 then 1297 else (if jt.2.val < 5 then 1300 else 1299)))))

checked_coverage fastCoverage0388 pairing0388 template0388 witness0388

theorem coverage0388 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0388) (maskBits m))
    cores template0388 witness0388 := by
  rw [← coresFast_eq]
  exact fastCoverage0388

theorem coverageSize0388 : ∀ q : Pattern,
    (cores (witness0388 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0388 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0388
#print axioms coverageSize0388

noncomputable def pairing0389 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0389 : List (Fin 4935) := templateData0389

noncomputable def witness0389 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 1433) else if t 2 = 1 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 992) else (if t 3 = 0 then 396 else if t 3 = 1 then 372 else 374)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 1202) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1414) else (if t 3 = 0 then 1450 else if t 3 = 1 then 1412 else 1416)) else (if t 2 = 0 then (if t 3 = 0 then 3959 else if t 3 = 1 then 3953 else 3954) else if t 2 = 1 then (if t 3 = 0 then 3227 else if t 3 = 1 then 3219 else 2855) else (if t 3 = 0 then 2501 else if t 3 = 1 then 2482 else 2485))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 1430) else if t 2 = 1 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 989) else (if t 3 = 0 then 395 else if t 3 = 1 then 365 else 369)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 1199) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1400) else (if t 3 = 0 then 1449 else if t 3 = 1 then 1396 else 1404)) else (if t 2 = 0 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 1200) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1401) else (if t 3 = 0 then 1451 else if t 3 = 1 then 1397 else 1405))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 2115 else 2758) else if t 2 = 1 then (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 168) else (if t 3 = 0 then 3952 else if t 3 = 1 then 890 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 564) else if t 2 = 1 then (if t 3 = 0 then 1446 else if t 3 = 1 then 1393 else 1402) else (if t 3 = 0 then 1452 else if t 3 = 1 then 1398 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 593 else if t 3 = 1 then 559 else 565) else if t 2 = 1 then (if t 3 = 0 then 1448 else if t 3 = 1 then 1394 else 1403) else (if t 3 = 0 then 1454 else if t 3 = 1 then 1399 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4338 else (if jt.2.val < 2 then 4357 else 4343)) else (if jt.2.val < 4 then 4356 else (if jt.2.val < 5 then 4358 else 4340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4413 else (if jt.2.val < 2 then 4423 else 4418)) else (if jt.2.val < 4 then 4422 else (if jt.2.val < 5 then 4424 else 4410)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1983 else (if jt.2.val < 2 then 1985 else 1992)) else (if jt.2.val < 4 then 1984 else (if jt.2.val < 5 then 1991 else 1990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1299 else (if jt.2.val < 2 then 1379 else 1301)) else (if jt.2.val < 4 then 1377 else (if jt.2.val < 5 then 1378 else 1296)))))

checked_coverage fastCoverage0389 pairing0389 template0389 witness0389

theorem coverage0389 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0389) (maskBits m))
    cores template0389 witness0389 := by
  rw [← coresFast_eq]
  exact fastCoverage0389

theorem coverageSize0389 : ∀ q : Pattern,
    (cores (witness0389 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0389 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0389
#print axioms coverageSize0389

noncomputable def pairing0390 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0390 : List (Fin 4935) := templateData0390

noncomputable def witness0390 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 620 else 698) else if t 2 = 1 then (if t 3 = 0 then 624 else if t 3 = 1 then 616 else 688) else (if t 3 = 0 then 1462 else if t 3 = 1 then 1459 else 1475)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 626 else if t 3 = 1 then 618 else 694) else if t 2 = 1 then (if t 3 = 0 then 622 else if t 3 = 1 then 614 else 680) else (if t 3 = 0 then 646 else if t 3 = 1 then 641 else 681)) else (if t 2 = 0 then (if t 3 = 0 then 2770 else if t 3 = 1 then 2768 else 2781) else if t 2 = 1 then (if t 3 = 0 then 2769 else if t 3 = 1 then 2766 else 2778) else (if t 3 = 0 then 3946 else if t 3 = 1 then 3945 else 3951))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 619 else 696) else if t 2 = 1 then (if t 3 = 0 then 623 else if t 3 = 1 then 615 else 684) else (if t 3 = 0 then 1461 else if t 3 = 1 then 1458 else 1473)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 625 else if t 3 = 1 then 617 else 690) else if t 2 = 1 then (if t 3 = 0 then 621 else if t 3 = 1 then 613 else 672) else (if t 3 = 0 then 645 else if t 3 = 1 then 640 else 674)) else (if t 2 = 0 then (if t 3 = 0 then 638 else if t 3 = 1 then 634 else 691) else if t 2 = 1 then (if t 3 = 0 then 636 else if t 3 = 1 then 632 else 673) else (if t 3 = 0 then 651 else if t 3 = 1 then 649 else 675))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 1133 else 3960) else if t 2 = 1 then (if t 3 = 0 then 660 else if t 3 = 1 then 655 else 686) else (if t 3 = 0 then 2777 else if t 3 = 1 then 2169 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1518 else if t 3 = 1 then 1131 else 1524) else if t 2 = 1 then (if t 3 = 0 then 658 else if t 3 = 1 then 653 else 676) else (if t 3 = 0 then 668 else if t 3 = 1 then 666 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 1520 else if t 3 = 1 then 1135 else 1525) else if t 2 = 1 then (if t 3 = 0 then 664 else if t 3 = 1 then 662 else 677) else (if t 3 = 0 then 671 else if t 3 = 1 then 670 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4407 else (if jt.2.val < 2 then 4427 else 4416)) else (if jt.2.val < 4 then 4425 else (if jt.2.val < 5 then 4426 else 4414))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2617 else (if jt.2.val < 2 then 2767 else 2621)) else (if jt.2.val < 4 then 2764 else (if jt.2.val < 5 then 2765 else 2589)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1979 else (if jt.2.val < 2 then 2016 else 1982)) else (if jt.2.val < 4 then 2013 else (if jt.2.val < 5 then 2014 else 1971))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 603 else (if jt.2.val < 2 then 605 else 608)) else (if jt.2.val < 4 then 604 else (if jt.2.val < 5 then 607 else 606)))))

checked_coverage fastCoverage0390 pairing0390 template0390 witness0390

theorem coverage0390 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0390) (maskBits m))
    cores template0390 witness0390 := by
  rw [← coresFast_eq]
  exact fastCoverage0390

theorem coverageSize0390 : ∀ q : Pattern,
    (cores (witness0390 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0390 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0390
#print axioms coverageSize0390

noncomputable def pairing0391 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0391 : List (Fin 4935) := templateData0391

noncomputable def witness0391 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 763 else 764) else if t 2 = 1 then (if t 3 = 0 then 768 else if t 3 = 1 then 740 else 742) else (if t 3 = 0 then 1498 else if t 3 = 1 then 1489 else 1490)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 770 else if t 3 = 1 then 755 else 757) else if t 2 = 1 then (if t 3 = 0 then 766 else if t 3 = 1 then 720 else 725) else (if t 3 = 0 then 778 else if t 3 = 1 then 722 else 726)) else (if t 2 = 0 then (if t 3 = 0 then 2798 else if t 3 = 1 then 2794 else 2795) else if t 2 = 1 then (if t 3 = 0 then 2797 else if t 3 = 1 then 2785 else 2788) else (if t 3 = 0 then 3943 else if t 3 = 1 then 3939 else 3941))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 759 else 761) else if t 2 = 1 then (if t 3 = 0 then 767 else if t 3 = 1 then 732 else 736) else (if t 3 = 0 then 1497 else if t 3 = 1 then 1483 else 1487)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 769 else if t 3 = 1 then 747 else 751) else if t 2 = 1 then (if t 3 = 0 then 765 else if t 3 = 1 then 704 else 712) else (if t 3 = 0 then 777 else if t 3 = 1 then 706 else 714)) else (if t 2 = 0 then (if t 3 = 0 then 775 else if t 3 = 1 then 748 else 752) else if t 2 = 1 then (if t 3 = 0 then 773 else if t 3 = 1 then 705 else 713) else (if t 3 = 0 then 781 else if t 3 = 1 then 707 else 715))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 1110 else 3966) else if t 2 = 1 then (if t 3 = 0 then 785 else if t 3 = 1 then 734 else 738) else (if t 3 = 0 then 2801 else if t 3 = 1 then 2157 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1548 else if t 3 = 1 then 1104 else 1542) else if t 2 = 1 then (if t 3 = 0 then 783 else if t 3 = 1 then 708 else 716) else (if t 3 = 0 then 789 else if t 3 = 1 then 710 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 1550 else if t 3 = 1 then 1105 else 1543) else if t 2 = 1 then (if t 3 = 0 then 787 else if t 3 = 1 then 709 else 717) else (if t 3 = 0 then 791 else if t 3 = 1 then 711 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4395 else (if jt.2.val < 2 then 4429 else 4406)) else (if jt.2.val < 4 then 4428 else (if jt.2.val < 5 then 4430 else 4403))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2667 else (if jt.2.val < 2 then 2791 else 2687)) else (if jt.2.val < 4 then 2790 else (if jt.2.val < 5 then 2792 else 2658)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1990 else (if jt.2.val < 2 then 2029 else 1992)) else (if jt.2.val < 4 then 2028 else (if jt.2.val < 5 then 2030 else 1983))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 606 else (if jt.2.val < 2 then 701 else 608)) else (if jt.2.val < 4 then 699 else (if jt.2.val < 5 then 700 else 603)))))

checked_coverage fastCoverage0391 pairing0391 template0391 witness0391

theorem coverage0391 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0391) (maskBits m))
    cores template0391 witness0391 := by
  rw [← coresFast_eq]
  exact fastCoverage0391

theorem coverageSize0391 : ∀ q : Pattern,
    (cores (witness0391 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0391 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0391
#print axioms coverageSize0391

noncomputable def pairing0392 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0392 : List (Fin 4935) := templateData0392

noncomputable def witness0392 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 3935) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2740) else (if t 3 = 0 then 2751 else if t 3 = 1 then 2750 else 2985)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 489) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 488) else (if t 3 = 0 then 539 else if t 3 = 1 then 537 else 1114)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1879 else 1523) else if t 2 = 1 then (if t 3 = 0 then 1882 else if t 3 = 1 then 1878 else 496) else (if t 3 = 0 then 555 else if t 3 = 1 then 554 else 1116))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 390) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 389) else (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 925)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2715) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4019) else (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4023)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2719) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4020) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4016 else 4024))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 820 else 404) else if t 2 = 1 then (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 403) else (if t 3 = 0 then 1472 else if t 3 = 1 then 274 else 1789)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2723) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4021) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4017 else 4025)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2841 else 2725) else if t 2 = 1 then (if t 3 = 0 then 4004 else if t 3 = 1 then 4003 else 4022) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4018 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4431 else (if jt.2.val < 2 then 4441 else 4442)) else (if jt.2.val < 4 then 4438 else (if jt.2.val < 5 then 4440 else 4439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4432 else (if jt.2.val < 2 then 4436 else 4437)) else (if jt.2.val < 4 then 4433 else (if jt.2.val < 5 then 4435 else 4434)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3970 else (if jt.2.val < 2 then 4013 else 4014)) else (if jt.2.val < 4 then 4010 else (if jt.2.val < 5 then 4012 else 4011))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3969 else (if jt.2.val < 2 then 4006 else 4009)) else (if jt.2.val < 4 then 4005 else (if jt.2.val < 5 then 4008 else 4007)))))

checked_coverage fastCoverage0392 pairing0392 template0392 witness0392

theorem coverage0392 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0392) (maskBits m))
    cores template0392 witness0392 := by
  rw [← coresFast_eq]
  exact fastCoverage0392

theorem coverageSize0392 : ∀ q : Pattern,
    (cores (witness0392 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0392 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0392
#print axioms coverageSize0392

noncomputable def pairing0393 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0393 : List (Fin 4935) := templateData0393

noncomputable def witness0393 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4036) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2737) else (if t 3 = 0 then 2981 else if t 3 = 1 then 2979 else 2738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 475) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 462) else (if t 3 = 0 then 1090 else if t 3 = 1 then 1069 else 467)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1597 else 1849) else if t 2 = 1 then (if t 3 = 0 then 1612 else if t 3 = 1 then 1593 else 464) else (if t 3 = 0 then 1094 else if t 3 = 1 then 1071 else 469))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 376) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 364) else (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 368)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2696) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3880) else (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3888)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2698) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3881) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3885 else 3889))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 175 else 895) else if t 2 = 1 then (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 889) else (if t 3 = 0 then 1808 else if t 3 = 1 then 167 else 1495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2879) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3882) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3886 else 3890)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2551 else 2881) else if t 2 = 1 then (if t 3 = 0 then 3916 else if t 3 = 1 then 3878 else 3883) else (if t 3 = 0 then 4040 else if t 3 = 1 then 3887 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4407 else (if jt.2.val < 2 then 4409 else 4416)) else (if jt.2.val < 4 then 4408 else (if jt.2.val < 5 then 4415 else 4414))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4410 else (if jt.2.val < 2 then 4412 else 4418)) else (if jt.2.val < 4 then 4411 else (if jt.2.val < 5 then 4417 else 4413)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4029 else (if jt.2.val < 2 then 4031 else 4035)) else (if jt.2.val < 4 then 4030 else (if jt.2.val < 5 then 4034 else 4033))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4007 else (if jt.2.val < 2 then 4032 else 4009)) else (if jt.2.val < 4 then 4027 else (if jt.2.val < 5 then 4028 else 3969)))))

checked_coverage fastCoverage0393 pairing0393 template0393 witness0393

theorem coverage0393 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0393) (maskBits m))
    cores template0393 witness0393 := by
  rw [← coresFast_eq]
  exact fastCoverage0393

theorem coverageSize0393 : ∀ q : Pattern,
    (cores (witness0393 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0393 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0393
#print axioms coverageSize0393

noncomputable def pairing0394 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0394 : List (Fin 4935) := templateData0394

noncomputable def witness0394 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2602 else 2906) else if t 2 = 1 then (if t 3 = 0 then 2598 else if t 3 = 1 then 2594 else 2648) else (if t 3 = 0 then 4044 else if t 3 = 1 then 3923 else 3927)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2600 else 2107) else if t 2 = 1 then (if t 3 = 0 then 2596 else if t 3 = 1 then 2592 else 2101) else (if t 3 = 0 then 536 else if t 3 = 1 then 534 else 589)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 143 else 904) else if t 2 = 1 then (if t 3 = 0 then 141 else if t 3 = 1 then 139 else 193) else (if t 3 = 0 then 1835 else if t 3 = 1 then 1537 else 1546))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2601 else 2227) else if t 2 = 1 then (if t 3 = 0 then 2597 else if t 3 = 1 then 2593 else 2221) else (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 295)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2599 else 2902) else if t 2 = 1 then (if t 3 = 0 then 2595 else if t 3 = 1 then 2591 else 2640) else (if t 3 = 0 then 2613 else if t 3 = 1 then 2611 else 2641)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2623 else 2904) else if t 2 = 1 then (if t 3 = 0 then 2622 else if t 3 = 1 then 2620 else 2642) else (if t 3 = 0 then 2626 else if t 3 = 1 then 2625 else 2643))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1585 else 1855) else if t 2 = 1 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1581 else 1615) else (if t 3 = 0 then 920 else if t 3 = 1 then 273 else 297)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2632 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2897 else if t 3 = 1 then 2629 else 2644) else (if t 3 = 0 then 2899 else if t 3 = 1 then 2634 else 2645)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2637 else 4045) else if t 2 = 1 then (if t 3 = 0 then 2900 else if t 3 = 1 then 2636 else 2646) else (if t 3 = 0 then 2901 else if t 3 = 1 then 2638 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4338 else (if jt.2.val < 2 then 4342 else 4343)) else (if jt.2.val < 4 then 4339 else (if jt.2.val < 5 then 4341 else 4340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2589 else (if jt.2.val < 2 then 2619 else 2621)) else (if jt.2.val < 4 then 2616 else (if jt.2.val < 5 then 2618 else 2617)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4011 else (if jt.2.val < 2 then 4043 else 4014)) else (if jt.2.val < 4 then 4041 else (if jt.2.val < 5 then 4042 else 3970))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2890 else (if jt.2.val < 2 then 2892 else 2895)) else (if jt.2.val < 4 then 2891 else (if jt.2.val < 5 then 2894 else 2893)))))

checked_coverage fastCoverage0394 pairing0394 template0394 witness0394

theorem coverage0394 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0394) (maskBits m))
    cores template0394 witness0394 := by
  rw [← coresFast_eq]
  exact fastCoverage0394

theorem coverageSize0394 : ∀ q : Pattern,
    (cores (witness0394 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0394 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0394
#print axioms coverageSize0394

noncomputable def pairing0395 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0395 : List (Fin 4935) := templateData0395

noncomputable def witness0395 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2953 else 2706) else if t 2 = 1 then (if t 3 = 0 then 2960 else if t 3 = 1 then 2937 else 2939) else (if t 3 = 0 then 3860 else if t 3 = 1 then 4046 else 4047)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2951 else 2098) else if t 2 = 1 then (if t 3 = 0 then 2958 else if t 3 = 1 then 2931 else 2082) else (if t 3 = 0 then 1084 else if t 3 = 1 then 1046 else 1051)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 859 else 75) else if t 2 = 1 then (if t 3 = 0 then 868 else if t 3 = 1 then 830 else 835) else (if t 3 = 0 then 1690 else if t 3 = 1 then 1813 else 1816))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2952 else 2218) else if t 2 = 1 then (if t 3 = 0 then 2959 else if t 3 = 1 then 2934 else 2206) else (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 974)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2947 else 2699) else if t 2 = 1 then (if t 3 = 0 then 2954 else if t 3 = 1 then 2913 else 2923) else (if t 3 = 0 then 2955 else if t 3 = 1 then 2915 else 2924)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2949 else 2701) else if t 2 = 1 then (if t 3 = 0 then 2956 else if t 3 = 1 then 2917 else 2925) else (if t 3 = 0 then 2957 else if t 3 = 1 then 2918 else 2926))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1903 else 1674) else if t 2 = 1 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1888 else 1890) else (if t 3 = 0 then 103 else if t 3 = 1 then 972 else 976)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2554 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2502 else if t 3 = 1 then 2919 else 2927) else (if t 3 = 0 then 2503 else if t 3 = 1 then 2920 else 2928)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2556 else 3934) else if t 2 = 1 then (if t 3 = 0 then 2504 else if t 3 = 1 then 2921 else 2929) else (if t 3 = 0 then 2505 else if t 3 = 1 then 2922 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4380 else (if jt.2.val < 2 then 4382 else 4385)) else (if jt.2.val < 4 then 4381 else (if jt.2.val < 5 then 4384 else 4383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2907 else (if jt.2.val < 2 then 2909 else 2936)) else (if jt.2.val < 4 then 2908 else (if jt.2.val < 5 then 2935 else 2916)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4033 else (if jt.2.val < 2 then 4049 else 4035)) else (if jt.2.val < 4 then 4048 else (if jt.2.val < 5 then 4050 else 4029))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2893 else (if jt.2.val < 2 then 2943 else 2895)) else (if jt.2.val < 4 then 2941 else (if jt.2.val < 5 then 2942 else 2890)))))

checked_coverage fastCoverage0395 pairing0395 template0395 witness0395

theorem coverage0395 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0395) (maskBits m))
    cores template0395 witness0395 := by
  rw [← coresFast_eq]
  exact fastCoverage0395

theorem coverageSize0395 : ∀ q : Pattern,
    (cores (witness0395 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0395 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0395
#print axioms coverageSize0395

noncomputable def pairing0396 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0396 : List (Fin 4935) := templateData0396

noncomputable def witness0396 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 1498) else if t 2 = 1 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 394) else (if t 3 = 0 then 258 else if t 3 = 1 then 256 else 929)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 778) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1753) else (if t 3 = 0 then 1353 else if t 3 = 1 then 1747 else 1762)) else (if t 2 = 0 then (if t 3 = 0 then 4066 else if t 3 = 1 then 4064 else 3943) else if t 2 = 1 then (if t 3 = 0 then 3351 else if t 3 = 1 then 3348 else 2500) else (if t 3 = 0 then 2547 else if t 3 = 1 then 2546 else 2884))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 1497) else if t 2 = 1 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 393) else (if t 3 = 0 then 257 else if t 3 = 1 then 255 else 926)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 777) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1752) else (if t 3 = 0 then 1352 else if t 3 = 1 then 1746 else 1758)) else (if t 2 = 0 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 781) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1754) else (if t 3 = 0 then 1355 else if t 3 = 1 then 1748 else 1759))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 2145 else 2801) else if t 2 = 1 then (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 405) else (if t 3 = 0 then 3942 else if t 3 = 1 then 278 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 789) else if t 2 = 1 then (if t 3 = 0 then 1732 else if t 3 = 1 then 1729 else 1755) else (if t 3 = 0 then 1358 else if t 3 = 1 then 1749 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 1057 else if t 3 = 1 then 1055 else 791) else if t 2 = 1 then (if t 3 = 0 then 1735 else if t 3 = 1 then 1734 else 1757) else (if t 3 = 0 then 1361 else if t 3 = 1 then 1751 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4380 else (if jt.2.val < 2 then 4391 else 4385)) else (if jt.2.val < 4 then 4389 else (if jt.2.val < 5 then 4390 else 4383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4434 else (if jt.2.val < 2 then 4445 else 4437)) else (if jt.2.val < 4 then 4443 else (if jt.2.val < 5 then 4444 else 4432)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2268 else (if jt.2.val < 2 then 2278 else 2279)) else (if jt.2.val < 4 then 2275 else (if jt.2.val < 5 then 2277 else 2276))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1692 else (if jt.2.val < 2 then 1737 else 1740)) else (if jt.2.val < 4 then 1736 else (if jt.2.val < 5 then 1739 else 1738)))))

checked_coverage fastCoverage0396 pairing0396 template0396 witness0396

theorem coverage0396 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0396) (maskBits m))
    cores template0396 witness0396 := by
  rw [← coresFast_eq]
  exact fastCoverage0396

theorem coverageSize0396 : ∀ q : Pattern,
    (cores (witness0396 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0396 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0396
#print axioms coverageSize0396

noncomputable def pairing0397 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0397 : List (Fin 4935) := templateData0397

noncomputable def witness0397 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 1775) else if t 2 = 1 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 372) else (if t 3 = 0 then 1012 else if t 3 = 1 then 992 else 374)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 756) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1412) else (if t 3 = 0 then 1777 else if t 3 = 1 then 1414 else 1416)) else (if t 2 = 0 then (if t 3 = 0 then 3959 else if t 3 = 1 then 3953 else 4060) else if t 2 = 1 then (if t 3 = 0 then 3227 else if t 3 = 1 then 3219 else 2482) else (if t 3 = 0 then 2868 else if t 3 = 1 then 2855 else 2485))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 1773) else if t 2 = 1 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 365) else (if t 3 = 0 then 1011 else if t 3 = 1 then 989 else 369)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 749) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1396) else (if t 3 = 0 then 1776 else if t 3 = 1 then 1400 else 1404)) else (if t 2 = 0 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 750) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1397) else (if t 3 = 0 then 1778 else if t 3 = 1 then 1401 else 1405))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 2115 else 2984) else if t 2 = 1 then (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 890) else (if t 3 = 0 then 4059 else if t 3 = 1 then 168 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 1106) else if t 2 = 1 then (if t 3 = 0 then 1446 else if t 3 = 1 then 1393 else 1398) else (if t 3 = 0 then 1779 else if t 3 = 1 then 1402 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 593 else if t 3 = 1 then 559 else 1107) else if t 2 = 1 then (if t 3 = 0 then 1448 else if t 3 = 1 then 1394 else 1399) else (if t 3 = 0 then 1781 else if t 3 = 1 then 1403 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4338 else (if jt.2.val < 2 then 4357 else 4343)) else (if jt.2.val < 4 then 4356 else (if jt.2.val < 5 then 4358 else 4340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4413 else (if jt.2.val < 2 then 4423 else 4418)) else (if jt.2.val < 4 then 4422 else (if jt.2.val < 5 then 4424 else 4410)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2280 else (if jt.2.val < 2 then 2282 else 2285)) else (if jt.2.val < 4 then 2281 else (if jt.2.val < 5 then 2284 else 2283))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1738 else (if jt.2.val < 2 then 1769 else 1740)) else (if jt.2.val < 4 then 1764 else (if jt.2.val < 5 then 1765 else 1692)))))

checked_coverage fastCoverage0397 pairing0397 template0397 witness0397

theorem coverage0397 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0397) (maskBits m))
    cores template0397 witness0397 := by
  rw [← coresFast_eq]
  exact fastCoverage0397

theorem coverageSize0397 : ∀ q : Pattern,
    (cores (witness0397 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0397 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0397
#print axioms coverageSize0397

noncomputable def pairing0398 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0398 : List (Fin 4935) := templateData0398

noncomputable def witness0398 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 624 else 1148) else if t 2 = 1 then (if t 3 = 0 then 620 else if t 3 = 1 then 616 else 688) else (if t 3 = 0 then 1786 else if t 3 = 1 then 1459 else 1475)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 626 else if t 3 = 1 then 622 else 1144) else if t 2 = 1 then (if t 3 = 0 then 618 else if t 3 = 1 then 614 else 680) else (if t 3 = 0 then 644 else if t 3 = 1 then 641 else 681)) else (if t 2 = 0 then (if t 3 = 0 then 2770 else if t 3 = 1 then 2769 else 2989) else if t 2 = 1 then (if t 3 = 0 then 2768 else if t 3 = 1 then 2766 else 2778) else (if t 3 = 0 then 4058 else if t 3 = 1 then 3945 else 3951))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 623 else 1146) else if t 2 = 1 then (if t 3 = 0 then 619 else if t 3 = 1 then 615 else 684) else (if t 3 = 0 then 1785 else if t 3 = 1 then 1458 else 1473)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 625 else if t 3 = 1 then 621 else 1140) else if t 2 = 1 then (if t 3 = 0 then 617 else if t 3 = 1 then 613 else 672) else (if t 3 = 0 then 643 else if t 3 = 1 then 640 else 674)) else (if t 2 = 0 then (if t 3 = 0 then 638 else if t 3 = 1 then 636 else 1141) else if t 2 = 1 then (if t 3 = 0 then 634 else if t 3 = 1 then 632 else 673) else (if t 3 = 0 then 650 else if t 3 = 1 then 649 else 675))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 660 else 4061) else if t 2 = 1 then (if t 3 = 0 then 1133 else if t 3 = 1 then 655 else 686) else (if t 3 = 0 then 2988 else if t 3 = 1 then 2169 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1518 else if t 3 = 1 then 658 else 1824) else if t 2 = 1 then (if t 3 = 0 then 1131 else if t 3 = 1 then 653 else 676) else (if t 3 = 0 then 1137 else if t 3 = 1 then 666 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 1520 else if t 3 = 1 then 664 else 1825) else if t 2 = 1 then (if t 3 = 0 then 1135 else if t 3 = 1 then 662 else 677) else (if t 3 = 0 then 1139 else if t 3 = 1 then 670 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4407 else (if jt.2.val < 2 then 4427 else 4416)) else (if jt.2.val < 4 then 4425 else (if jt.2.val < 5 then 4426 else 4414))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2617 else (if jt.2.val < 2 then 2767 else 2621)) else (if jt.2.val < 4 then 2764 else (if jt.2.val < 5 then 2765 else 2589)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2276 else (if jt.2.val < 2 then 2303 else 2279)) else (if jt.2.val < 4 then 2301 else (if jt.2.val < 5 then 2302 else 2268))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1122 else (if jt.2.val < 2 then 1124 else 1129)) else (if jt.2.val < 4 then 1123 else (if jt.2.val < 5 then 1128 else 1127)))))

checked_coverage fastCoverage0398 pairing0398 template0398 witness0398

theorem coverage0398 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0398) (maskBits m))
    cores template0398 witness0398 := by
  rw [← coresFast_eq]
  exact fastCoverage0398

theorem coverageSize0398 : ∀ q : Pattern,
    (cores (witness0398 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0398 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0398
#print axioms coverageSize0398

noncomputable def pairing0399 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0399 : List (Fin 4935) := templateData0399

noncomputable def witness0399 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1205 else 764) else if t 2 = 1 then (if t 3 = 0 then 1214 else if t 3 = 1 then 1187 else 1189) else (if t 3 = 0 then 1376 else if t 3 = 1 then 1801 else 1802)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1201 else 757) else if t 2 = 1 then (if t 3 = 0 then 1210 else if t 3 = 1 then 1167 else 1172) else (if t 3 = 0 then 1211 else if t 3 = 1 then 1169 else 1173)) else (if t 2 = 0 then (if t 3 = 0 then 3004 else if t 3 = 1 then 3002 else 2795) else if t 2 = 1 then (if t 3 = 0 then 3003 else if t 3 = 1 then 2993 else 2996) else (if t 3 = 0 then 3967 else if t 3 = 1 then 4054 else 4056))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1203 else 761) else if t 2 = 1 then (if t 3 = 0 then 1212 else if t 3 = 1 then 1179 else 1183) else (if t 3 = 0 then 1374 else if t 3 = 1 then 1795 else 1799)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1197 else 751) else if t 2 = 1 then (if t 3 = 0 then 1206 else if t 3 = 1 then 1151 else 1159) else (if t 3 = 0 then 1208 else if t 3 = 1 then 1153 else 1161)) else (if t 2 = 0 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1198 else 752) else if t 2 = 1 then (if t 3 = 0 then 1207 else if t 3 = 1 then 1152 else 1160) else (if t 3 = 0 then 1209 else if t 3 = 1 then 1154 else 1162))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 572 else 3966) else if t 2 = 1 then (if t 3 = 0 then 504 else if t 3 = 1 then 1181 else 1185) else (if t 3 = 0 then 2744 else if t 3 = 1 then 2136 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1836 else if t 3 = 1 then 562 else 1542) else if t 2 = 1 then (if t 3 = 0 then 498 else if t 3 = 1 then 1155 else 1163) else (if t 3 = 0 then 500 else if t 3 = 1 then 1157 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 1838 else if t 3 = 1 then 563 else 1543) else if t 2 = 1 then (if t 3 = 0 then 499 else if t 3 = 1 then 1156 else 1164) else (if t 3 = 0 then 501 else if t 3 = 1 then 1158 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4431 else (if jt.2.val < 2 then 4447 else 4442)) else (if jt.2.val < 4 then 4446 else (if jt.2.val < 5 then 4448 else 4439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2916 else (if jt.2.val < 2 then 2999 else 2936)) else (if jt.2.val < 4 then 2998 else (if jt.2.val < 5 then 3000 else 2907)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2283 else (if jt.2.val < 2 then 2311 else 2285)) else (if jt.2.val < 4 then 2310 else (if jt.2.val < 5 then 2312 else 2280))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1127 else (if jt.2.val < 2 then 1193 else 1129)) else (if jt.2.val < 4 then 1191 else (if jt.2.val < 5 then 1192 else 1122)))))

checked_coverage fastCoverage0399 pairing0399 template0399 witness0399

theorem coverage0399 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0399) (maskBits m))
    cores template0399 witness0399 := by
  rw [← coresFast_eq]
  exact fastCoverage0399

theorem coverageSize0399 : ∀ q : Pattern,
    (cores (witness0399 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0399 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0399
#print axioms coverageSize0399

end Crown.CertificateData
