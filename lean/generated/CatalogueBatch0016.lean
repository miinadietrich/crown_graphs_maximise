import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0015

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0600 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0600 : List (Fin 4935) := templateData0600

noncomputable def witness0600 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3198) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2797) else (if t 3 = 0 then 2974 else if t 3 = 1 then 2972 else 2800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 87) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 86) else (if t 3 = 0 then 965 else if t 3 = 1 then 961 else 100)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1879 else 1523) else if t 2 = 1 then (if t 3 = 0 then 1881 else if t 3 = 1 then 1877 else 94) else (if t 3 = 0 then 980 else if t 3 = 1 then 978 else 104))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 774) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 773) else (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 787)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2717) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3295) else (if t 3 = 0 then 3278 else if t 3 = 1 then 3276 else 3297)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2719) else if t 2 = 1 then (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3296) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3279 else 3298))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 637 else 1147) else if t 2 = 1 then (if t 3 = 0 then 638 else if t 3 = 1 then 636 else 1141) else (if t 3 = 0 then 1520 else if t 3 = 1 then 664 else 1825)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2623 else 2904) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3291 else 3299) else (if t 3 = 0 then 3095 else if t 3 = 1 then 3293 else 3301)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2627 else 2905) else if t 2 = 1 then (if t 3 = 0 then 3093 else if t 3 = 1 then 3292 else 3300) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3294 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4755 else (if jt.2.val < 2 then 4759 else 4760)) else (if jt.2.val < 4 then 4756 else (if jt.2.val < 5 then 4758 else 4757))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4369 else (if jt.2.val < 2 then 4373 else 4374)) else (if jt.2.val < 4 then 4370 else (if jt.2.val < 5 then 4372 else 4371)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3556 else (if jt.2.val < 2 then 3560 else 3561)) else (if jt.2.val < 4 then 3557 else (if jt.2.val < 5 then 3559 else 3558))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3243 else (if jt.2.val < 2 then 3282 else 3285)) else (if jt.2.val < 4 then 3281 else (if jt.2.val < 5 then 3284 else 3283)))))

checked_coverage fastCoverage0600 pairing0600 template0600 witness0600

theorem coverage0600 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0600) (maskBits m))
    cores template0600 witness0600 := by
  rw [← coresFast_eq]
  exact fastCoverage0600

theorem coverageSize0600 : ∀ q : Pattern,
    (cores (witness0600 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0600 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0600
#print axioms coverageSize0600

noncomputable def pairing0601 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0601 : List (Fin 4935) := templateData0601

noncomputable def witness0601 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3312) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 2794) else (if t 3 = 0 then 2760 else if t 3 = 1 then 2756 else 2983)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 73) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 60) else (if t 3 = 0 then 292 else if t 3 = 1 then 264 else 916)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1597 else 1849) else if t 2 = 1 then (if t 3 = 0 then 1611 else if t 3 = 1 then 1589 else 62) else (if t 3 = 0 then 299 else if t 3 = 1 then 266 else 918))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 760) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 748) else (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 1105)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2697) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3126) else (if t 3 = 0 then 3163 else if t 3 = 1 then 3123 else 3128)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2698) else if t 2 = 1 then (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3127) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3124 else 3129))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1204 else 762) else if t 2 = 1 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1198 else 752) else (if t 3 = 0 then 1838 else if t 3 = 1 then 563 else 1543)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2949 else 2701) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3130 else 3134) else (if t 3 = 0 then 3315 else if t 3 = 1 then 3132 else 3136)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2950 else 2702) else if t 2 = 1 then (if t 3 = 0 then 3314 else if t 3 = 1 then 3131 else 3135) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3133 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4761 else (if jt.2.val < 2 then 4763 else 4766)) else (if jt.2.val < 4 then 4762 else (if jt.2.val < 5 then 4765 else 4764))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4329 else (if jt.2.val < 2 then 4331 else 4337)) else (if jt.2.val < 4 then 4330 else (if jt.2.val < 5 then 4336 else 4332)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3399 else (if jt.2.val < 2 then 3401 else 3407)) else (if jt.2.val < 4 then 3400 else (if jt.2.val < 5 then 3406 else 3402))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3283 else (if jt.2.val < 2 then 3308 else 3285)) else (if jt.2.val < 4 then 3303 else (if jt.2.val < 5 then 3304 else 3243)))))

checked_coverage fastCoverage0601 pairing0601 template0601 witness0601

theorem coverage0601 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0601) (maskBits m))
    cores template0601 witness0601 := by
  rw [← coresFast_eq]
  exact fastCoverage0601

theorem coverageSize0601 : ∀ q : Pattern,
    (cores (witness0601 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0601 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0601
#print axioms coverageSize0601

noncomputable def pairing0602 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0602 : List (Fin 4935) := templateData0602

noncomputable def witness0602 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2813 else 2722) else if t 2 = 1 then (if t 3 = 0 then 2817 else if t 3 = 1 then 2809 else 2860) else (if t 3 = 0 then 3340 else if t 3 = 1 then 3338 else 3242)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2811 else 1371) else if t 2 = 1 then (if t 3 = 0 then 2815 else if t 3 = 1 then 2807 else 1370) else (if t 3 = 0 then 964 else if t 3 = 1 then 960 else 1001)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1171 else 503) else if t 2 = 1 then (if t 3 = 0 then 1173 else if t 3 = 1 then 1169 else 1211) else (if t 3 = 0 then 1802 else if t 3 = 1 then 1801 else 1376))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2812 else 1686) else if t 2 = 1 then (if t 3 = 0 then 2816 else if t 3 = 1 then 2808 else 1685) else (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1082)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2810 else 2721) else if t 2 = 1 then (if t 3 = 0 then 2814 else if t 3 = 1 then 2806 else 2859) else (if t 3 = 0 then 2838 else if t 3 = 1 then 2835 else 2862)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2723) else if t 2 = 1 then (if t 3 = 0 then 2829 else if t 3 = 1 then 2826 else 2861) else (if t 3 = 0 then 2842 else if t 3 = 1 then 2840 else 2863))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1585 else 1855) else if t 2 = 1 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1584 else 1852) else (if t 3 = 0 then 473 else if t 3 = 1 then 1073 else 1093)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2632 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2484 else if t 3 = 1 then 2854 else 2864) else (if t 3 = 0 then 2489 else if t 3 = 1 then 2857 else 2866)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2635 else 3322) else if t 2 = 1 then (if t 3 = 0 then 2487 else if t 3 = 1 then 2856 else 2865) else (if t 3 = 0 then 2491 else if t 3 = 1 then 2858 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4767 else (if jt.2.val < 2 then 4771 else 4772)) else (if jt.2.val < 4 then 4768 else (if jt.2.val < 5 then 4770 else 4769))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3763 else (if jt.2.val < 2 then 3767 else 3768)) else (if jt.2.val < 4 then 3764 else (if jt.2.val < 5 then 3766 else 3765)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3558 else (if jt.2.val < 2 then 3576 else 3561)) else (if jt.2.val < 4 then 3573 else (if jt.2.val < 5 then 3574 else 3556))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2802 else (if jt.2.val < 2 then 2845 else 2848)) else (if jt.2.val < 4 then 2844 else (if jt.2.val < 5 then 2847 else 2846)))))

checked_coverage fastCoverage0602 pairing0602 template0602 witness0602

theorem coverage0602 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0602) (maskBits m))
    cores template0602 witness0602 := by
  rw [← coresFast_eq]
  exact fastCoverage0602

theorem coverageSize0602 : ∀ q : Pattern,
    (cores (witness0602 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0602 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0602
#print axioms coverageSize0602

noncomputable def pairing0603 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0603 : List (Fin 4935) := templateData0603

noncomputable def witness0603 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2560 else 2882) else if t 2 = 1 then (if t 3 = 0 then 2565 else if t 3 = 1 then 2544 else 2545) else (if t 3 = 0 then 3215 else if t 3 = 1 then 3209 else 3342)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2558 else 1357) else if t 2 = 1 then (if t 3 = 0 then 2563 else if t 3 = 1 then 2538 else 1350) else (if t 3 = 0 then 291 else if t 3 = 1 then 251 else 254)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 667 else 1138) else if t 2 = 1 then (if t 3 = 0 then 681 else if t 3 = 1 then 641 else 644) else (if t 3 = 0 then 1475 else if t 3 = 1 then 1459 else 1786))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2559 else 1672) else if t 2 = 1 then (if t 3 = 0 then 2564 else if t 3 = 1 then 2541 else 1666) else (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 547)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2548 else 2878) else if t 2 = 1 then (if t 3 = 0 then 2562 else if t 3 = 1 then 2519 else 2526) else (if t 3 = 0 then 2572 else if t 3 = 1 then 2523 else 2528)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2879) else if t 2 = 1 then (if t 3 = 0 then 2570 else if t 3 = 1 then 2521 else 2527) else (if t 3 = 0 then 2574 else if t 3 = 1 then 2524 else 2529))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1903 else 1674) else if t 2 = 1 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1900 else 1668) else (if t 3 = 0 then 1118 else if t 3 = 1 then 549 else 551)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2554 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2883 else if t 3 = 1 then 2530 else 2534) else (if t 3 = 0 then 2886 else if t 3 = 1 then 2532 else 2536)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2555 else 3197) else if t 2 = 1 then (if t 3 = 0 then 2885 else if t 3 = 1 then 2531 else 2535) else (if t 3 = 0 then 2887 else if t 3 = 1 then 2533 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4773 else (if jt.2.val < 2 then 4775 else 4778)) else (if jt.2.val < 4 then 4774 else (if jt.2.val < 5 then 4777 else 4776))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3705 else (if jt.2.val < 2 then 3707 else 3713)) else (if jt.2.val < 4 then 3706 else (if jt.2.val < 5 then 3712 else 3708)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3402 else (if jt.2.val < 2 then 3424 else 3407)) else (if jt.2.val < 4 then 3423 else (if jt.2.val < 5 then 3425 else 3399))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2846 else (if jt.2.val < 2 then 2874 else 2848)) else (if jt.2.val < 4 then 2869 else (if jt.2.val < 5 then 2870 else 2802)))))

checked_coverage fastCoverage0603 pairing0603 template0603 witness0603

theorem coverage0603 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0603) (maskBits m))
    cores template0603 witness0603 := by
  rw [← coresFast_eq]
  exact fastCoverage0603

theorem coverageSize0603 : ∀ q : Pattern,
    (cores (witness0603 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0603 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0603
#print axioms coverageSize0603

noncomputable def pairing0604 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0604 : List (Fin 4935) := templateData0604

noncomputable def witness0604 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 1498) else if t 2 = 1 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 778) else (if t 3 = 0 then 1053 else if t 3 = 1 then 1049 else 790)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 394) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1753) else (if t 3 = 0 then 1733 else if t 3 = 1 then 1730 else 1756)) else (if t 2 = 0 then (if t 3 = 0 then 3352 else if t 3 = 1 then 3350 else 3207) else if t 2 = 1 then (if t 3 = 0 then 3351 else if t 3 = 1 then 3348 else 2500) else (if t 3 = 0 then 2940 else if t 3 = 1 then 2938 else 2506))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 1497) else if t 2 = 1 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 777) else (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 789)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 393) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1752) else (if t 3 = 0 then 1732 else if t 3 = 1 then 1729 else 1755)) else (if t 2 = 0 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 397) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1754) else (if t 3 = 0 then 1735 else if t 3 = 1 then 1734 else 1757))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1461 else 2990) else if t 2 = 1 then (if t 3 = 0 then 647 else if t 3 = 1 then 645 else 1142) else (if t 3 = 0 then 3206 else if t 3 = 1 then 668 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 257 else if t 3 = 1 then 255 else 926) else if t 2 = 1 then (if t 3 = 0 then 1352 else if t 3 = 1 then 1746 else 1758) else (if t 3 = 0 then 1358 else if t 3 = 1 then 1749 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 262 else if t 3 = 1 then 261 else 927) else if t 2 = 1 then (if t 3 = 0 then 1355 else if t 3 = 1 then 1748 else 1759) else (if t 3 = 0 then 1361 else if t 3 = 1 then 1751 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4773 else (if jt.2.val < 2 then 4781 else 4778)) else (if jt.2.val < 4 then 4779 else (if jt.2.val < 5 then 4780 else 4776))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4371 else (if jt.2.val < 2 then 4388 else 4374)) else (if jt.2.val < 4 then 4386 else (if jt.2.val < 5 then 4387 else 4369)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2269 else (if jt.2.val < 2 then 2273 else 2274)) else (if jt.2.val < 4 then 2270 else (if jt.2.val < 5 then 2272 else 2271))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1692 else (if jt.2.val < 2 then 1737 else 1740)) else (if jt.2.val < 4 then 1736 else (if jt.2.val < 5 then 1739 else 1738)))))

checked_coverage fastCoverage0604 pairing0604 template0604 witness0604

theorem coverage0604 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0604) (maskBits m))
    cores template0604 witness0604 := by
  rw [← coresFast_eq]
  exact fastCoverage0604

theorem coverageSize0604 : ∀ q : Pattern,
    (cores (witness0604 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0604 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0604
#print axioms coverageSize0604

noncomputable def pairing0605 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0605 : List (Fin 4935) := templateData0605

noncomputable def witness0605 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 1775) else if t 2 = 1 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 756) else (if t 3 = 0 then 591 else if t 3 = 1 then 567 else 1109)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 372) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1412) else (if t 3 = 0 then 1447 else if t 3 = 1 then 1411 else 1413)) else (if t 2 = 0 then (if t 3 = 0 then 3228 else if t 3 = 1 then 3225 else 3344) else if t 2 = 1 then (if t 3 = 0 then 3227 else if t 3 = 1 then 3219 else 2482) else (if t 3 = 0 then 2649 else if t 3 = 1 then 2630 else 2898))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 1773) else if t 2 = 1 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 749) else (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 1106)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 365) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1396) else (if t 3 = 0 then 1446 else if t 3 = 1 then 1393 else 1398)) else (if t 2 = 0 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 366) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1397) else (if t 3 = 0 then 1448 else if t 3 = 1 then 1394 else 1399))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1430 else 2796) else if t 2 = 1 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1199 else 753) else (if t 3 = 0 then 3343 else if t 3 = 1 then 564 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1011 else if t 3 = 1 then 989 else 369) else if t 2 = 1 then (if t 3 = 0 then 1776 else if t 3 = 1 then 1400 else 1404) else (if t 3 = 0 then 1779 else if t 3 = 1 then 1402 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 1013 else if t 3 = 1 then 990 else 370) else if t 2 = 1 then (if t 3 = 0 then 1778 else if t 3 = 1 then 1401 else 1405) else (if t 3 = 0 then 1781 else if t 3 = 1 then 1403 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4767 else (if jt.2.val < 2 then 4783 else 4772)) else (if jt.2.val < 4 then 4782 else (if jt.2.val < 5 then 4784 else 4769))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4332 else (if jt.2.val < 2 then 4360 else 4337)) else (if jt.2.val < 4 then 4359 else (if jt.2.val < 5 then 4361 else 4329)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1986 else (if jt.2.val < 2 then 1988 else 1994)) else (if jt.2.val < 4 then 1987 else (if jt.2.val < 5 then 1993 else 1989))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1738 else (if jt.2.val < 2 then 1769 else 1740)) else (if jt.2.val < 4 then 1764 else (if jt.2.val < 5 then 1765 else 1692)))))

checked_coverage fastCoverage0605 pairing0605 template0605 witness0605

theorem coverage0605 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0605) (maskBits m))
    cores template0605 witness0605 := by
  rw [← coresFast_eq]
  exact fastCoverage0605

theorem coverageSize0605 : ∀ q : Pattern,
    (cores (witness0605 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0605 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0605
#print axioms coverageSize0605

noncomputable def pairing0606 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0606 : List (Fin 4935) := templateData0606

noncomputable def witness0606 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 803 else 402) else if t 2 = 1 then (if t 3 = 0 then 807 else if t 3 = 1 then 799 else 864) else (if t 3 = 0 then 1816 else if t 3 = 1 then 1813 else 1690)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 809 else if t 3 = 1 then 801 else 400) else if t 2 = 1 then (if t 3 = 0 then 805 else if t 3 = 1 then 797 else 862) else (if t 3 = 0 then 835 else if t 3 = 1 then 830 else 868)) else (if t 2 = 0 then (if t 3 = 0 then 2997 else if t 3 = 1 then 2995 else 2743) else if t 2 = 1 then (if t 3 = 0 then 2996 else if t 3 = 1 then 2993 else 3003) else (if t 3 = 0 then 3330 else if t 3 = 1 then 3329 else 3106))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 802 else 401) else if t 2 = 1 then (if t 3 = 0 then 806 else if t 3 = 1 then 798 else 863) else (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 808 else if t 3 = 1 then 800 else 399) else if t 2 = 1 then (if t 3 = 0 then 804 else if t 3 = 1 then 796 else 861) else (if t 3 = 0 then 834 else if t 3 = 1 then 829 else 867)) else (if t 2 = 0 then (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 403) else if t 2 = 1 then (if t 3 = 0 then 821 else if t 3 = 1 then 816 else 865) else (if t 3 = 0 then 840 else if t 3 = 1 then 838 else 869))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 270 else 3345) else if t 2 = 1 then (if t 3 = 0 then 66 else if t 3 = 1 then 854 else 876) else (if t 3 = 0 then 2739 else if t 3 = 1 then 1598 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1470 else if t 3 = 1 then 268 else 1788) else if t 2 = 1 then (if t 3 = 0 then 64 else if t 3 = 1 then 852 else 870) else (if t 3 = 0 then 74 else if t 3 = 1 then 858 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 1472 else if t 3 = 1 then 274 else 1789) else if t 2 = 1 then (if t 3 = 0 then 70 else if t 3 = 1 then 856 else 871) else (if t 3 = 0 then 77 else if t 3 = 1 then 860 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4761 else (if jt.2.val < 2 then 4787 else 4766)) else (if jt.2.val < 4 then 4785 else (if jt.2.val < 5 then 4786 else 4764))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3765 else (if jt.2.val < 2 then 3788 else 3768)) else (if jt.2.val < 4 then 3786 else (if jt.2.val < 5 then 3787 else 3763)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2271 else (if jt.2.val < 2 then 2289 else 2274)) else (if jt.2.val < 4 then 2286 else (if jt.2.val < 5 then 2287 else 2269))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 792 else (if jt.2.val < 2 then 843 else 846)) else (if jt.2.val < 4 then 842 else (if jt.2.val < 5 then 845 else 844)))))

checked_coverage fastCoverage0606 pairing0606 template0606 witness0606

theorem coverage0606 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0606) (maskBits m))
    cores template0606 witness0606 := by
  rw [← coresFast_eq]
  exact fastCoverage0606

theorem coverageSize0606 : ∀ q : Pattern,
    (cores (witness0606 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0606 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0606
#print axioms coverageSize0606

noncomputable def pairing0607 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0607 : List (Fin 4935) := templateData0607

noncomputable def witness0607 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 178 else 896) else if t 2 = 1 then (if t 3 = 0 then 183 else if t 3 = 1 then 156 else 157) else (if t 3 = 0 then 1546 else if t 3 = 1 then 1537 else 1835)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 185 else if t 3 = 1 then 170 else 892) else if t 2 = 1 then (if t 3 = 0 then 181 else if t 3 = 1 then 136 else 140) else (if t 3 = 0 then 193 else if t 3 = 1 then 139 else 141)) else (if t 2 = 0 then (if t 3 = 0 then 2779 else if t 3 = 1 then 2775 else 2987) else if t 2 = 1 then (if t 3 = 0 then 2778 else if t 3 = 1 then 2766 else 2768) else (if t 3 = 0 then 3182 else if t 3 = 1 then 3172 else 3320))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 174 else 894) else if t 2 = 1 then (if t 3 = 0 then 182 else if t 3 = 1 then 146 else 150) else (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1833)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 184 else if t 3 = 1 then 160 else 888) else if t 2 = 1 then (if t 3 = 0 then 180 else if t 3 = 1 then 117 else 124) else (if t 3 = 0 then 192 else if t 3 = 1 then 121 else 126)) else (if t 2 = 0 then (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 889) else if t 2 = 1 then (if t 3 = 0 then 188 else if t 3 = 1 then 119 else 125) else (if t 3 = 0 then 196 else if t 3 = 1 then 122 else 127))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 176 else 3240) else if t 2 = 1 then (if t 3 = 0 then 899 else if t 3 = 1 then 152 else 154) else (if t 3 = 0 then 2986 else if t 3 = 1 then 1535 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1806 else if t 3 = 1 then 166 else 1494) else if t 2 = 1 then (if t 3 = 0 then 897 else if t 3 = 1 then 128 else 132) else (if t 3 = 0 then 903 else if t 3 = 1 then 130 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 1808 else if t 3 = 1 then 167 else 1495) else if t 2 = 1 then (if t 3 = 0 then 901 else if t 3 = 1 then 129 else 133) else (if t 3 = 0 then 905 else if t 3 = 1 then 131 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4755 else (if jt.2.val < 2 then 4789 else 4760)) else (if jt.2.val < 4 then 4788 else (if jt.2.val < 5 then 4790 else 4757))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3708 else (if jt.2.val < 2 then 3748 else 3713)) else (if jt.2.val < 4 then 3747 else (if jt.2.val < 5 then 3749 else 3705)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1989 else (if jt.2.val < 2 then 2011 else 1994)) else (if jt.2.val < 4 then 2010 else (if jt.2.val < 5 then 2012 else 1986))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 844 else (if jt.2.val < 2 then 884 else 846)) else (if jt.2.val < 4 then 879 else (if jt.2.val < 5 then 880 else 792)))))

checked_coverage fastCoverage0607 pairing0607 template0607 witness0607

theorem coverage0607 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0607) (maskBits m))
    cores template0607 witness0607 := by
  rw [← coresFast_eq]
  exact fastCoverage0607

theorem coverageSize0607 : ∀ q : Pattern,
    (cores (witness0607 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0607 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0607
#print axioms coverageSize0607

noncomputable def pairing0608 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0608 : List (Fin 4935) := templateData0608

noncomputable def witness0608 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3215) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2759) else (if t 3 = 0 then 2974 else if t 3 = 1 then 2973 else 2762)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 291) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 290) else (if t 3 = 0 then 965 else if t 3 = 1 then 963 else 304)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2197 else 1475) else if t 2 = 1 then (if t 3 = 0 then 2199 else if t 3 = 1 then 2195 else 298) else (if t 3 = 0 then 980 else if t 3 = 1 then 979 else 308))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 585) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 584) else (if t 3 = 0 then 1043 else if t 3 = 1 then 1041 else 598)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2572) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3488) else (if t 3 = 0 then 3278 else if t 3 = 1 then 3472 else 3490)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2574) else if t 2 = 1 then (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3489) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3473 else 3491))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 441 else 1118) else if t 2 = 1 then (if t 3 = 0 then 442 else if t 3 = 1 then 440 else 1117) else (if t 3 = 0 then 1520 else if t 3 = 1 then 472 else 2149)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2471 else 2886) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3479 else 3492) else (if t 3 = 0 then 3095 else if t 3 = 1 then 3486 else 3494)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2475 else 2887) else if t 2 = 1 then (if t 3 = 0 then 3084 else if t 3 = 1 then 3480 else 3493) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3487 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4791 else (if jt.2.val < 2 then 4795 else 4796)) else (if jt.2.val < 4 then 4792 else (if jt.2.val < 5 then 4794 else 4793))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4648 else (if jt.2.val < 2 then 4652 else 4653)) else (if jt.2.val < 4 then 4649 else (if jt.2.val < 5 then 4651 else 4650)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3601 else (if jt.2.val < 2 then 3605 else 3606)) else (if jt.2.val < 4 then 3602 else (if jt.2.val < 5 then 3604 else 3603))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3438 else (if jt.2.val < 2 then 3482 else 3485)) else (if jt.2.val < 4 then 3481 else (if jt.2.val < 5 then 3484 else 3483)))))

checked_coverage fastCoverage0608 pairing0608 template0608 witness0608

theorem coverage0608 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0608) (maskBits m))
    cores template0608 witness0608 := by
  rw [← coresFast_eq]
  exact fastCoverage0608

theorem coverageSize0608 : ∀ q : Pattern,
    (cores (witness0608 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0608 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0608
#print axioms coverageSize0608

noncomputable def pairing0609 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0609 : List (Fin 4935) := templateData0609

noncomputable def witness0609 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3499) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 2756) else (if t 3 = 0 then 2798 else if t 3 = 1 then 2794 else 2983)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 277) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 264) else (if t 3 = 0 then 88 else if t 3 = 1 then 60 else 916)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1597 else 2170) else if t 2 = 1 then (if t 3 = 0 then 1611 else if t 3 = 1 then 1589 else 266) else (if t 3 = 0 then 95 else if t 3 = 1 then 62 else 918))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 571) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 557) else (if t 3 = 0 then 775 else if t 3 = 1 then 748 else 1105)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2550) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3123) else (if t 3 = 0 then 3165 else if t 3 = 1 then 3126 else 3128)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2551) else if t 2 = 1 then (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3124) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3127 else 3129))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1204 else 573) else if t 2 = 1 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1198 else 563) else (if t 3 = 0 then 2162 else if t 3 = 1 then 752 else 1543)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2949 else 2556) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3130 else 3132) else (if t 3 = 0 then 3500 else if t 3 = 1 then 3134 else 3136)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2950 else 2557) else if t 2 = 1 then (if t 3 = 0 then 3314 else if t 3 = 1 then 3131 else 3133) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3135 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4761 else (if jt.2.val < 2 then 4763 else 4766)) else (if jt.2.val < 4 then 4762 else (if jt.2.val < 5 then 4765 else 4764))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4329 else (if jt.2.val < 2 then 4331 else 4337)) else (if jt.2.val < 4 then 4330 else (if jt.2.val < 5 then 4336 else 4332)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3110 else (if jt.2.val < 2 then 3112 else 3148)) else (if jt.2.val < 4 then 3111 else (if jt.2.val < 5 then 3147 else 3125))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3483 else (if jt.2.val < 2 then 3498 else 3485)) else (if jt.2.val < 4 then 3496 else (if jt.2.val < 5 then 3497 else 3438)))))

checked_coverage fastCoverage0609 pairing0609 template0609 witness0609

theorem coverage0609 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0609) (maskBits m))
    cores template0609 witness0609 := by
  rw [← coresFast_eq]
  exact fastCoverage0609

theorem coverageSize0609 : ∀ q : Pattern,
    (cores (witness0609 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0609 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0609
#print axioms coverageSize0609

noncomputable def pairing0610 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0610 : List (Fin 4935) := templateData0610

noncomputable def witness0610 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2817 else 2577) else if t 2 = 1 then (if t 3 = 0 then 2813 else if t 3 = 1 then 2809 else 2860) else (if t 3 = 0 then 3520 else if t 3 = 1 then 3338 else 3242)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2815 else 1372) else if t 2 = 1 then (if t 3 = 0 then 2811 else if t 3 = 1 then 2807 else 1370) else (if t 3 = 0 then 962 else if t 3 = 1 then 960 else 1001)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1173 else 695) else if t 2 = 1 then (if t 3 = 0 then 1171 else if t 3 = 1 then 1169 else 1211) else (if t 3 = 0 then 2138 else if t 3 = 1 then 1801 else 1376))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2816 else 1687) else if t 2 = 1 then (if t 3 = 0 then 2812 else if t 3 = 1 then 2808 else 1685) else (if t 3 = 0 then 1040 else if t 3 = 1 then 1038 else 1082)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2814 else 2576) else if t 2 = 1 then (if t 3 = 0 then 2810 else if t 3 = 1 then 2806 else 2859) else (if t 3 = 0 then 2837 else if t 3 = 1 then 2835 else 2862)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2578) else if t 2 = 1 then (if t 3 = 0 then 2828 else if t 3 = 1 then 2826 else 2861) else (if t 3 = 0 then 2841 else if t 3 = 1 then 2840 else 2863))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1586 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1584 else 1852) else (if t 3 = 0 then 665 else if t 3 = 1 then 1073 else 1093)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2484 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2632 else if t 3 = 1 then 2854 else 2864) else (if t 3 = 0 then 2637 else if t 3 = 1 then 2857 else 2866)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2487 else 3507) else if t 2 = 1 then (if t 3 = 0 then 2635 else if t 3 = 1 then 2856 else 2865) else (if t 3 = 0 then 2639 else if t 3 = 1 then 2858 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4767 else (if jt.2.val < 2 then 4771 else 4772)) else (if jt.2.val < 4 then 4768 else (if jt.2.val < 5 then 4770 else 4769))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3763 else (if jt.2.val < 2 then 3767 else 3768)) else (if jt.2.val < 4 then 3764 else (if jt.2.val < 5 then 3766 else 3765)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3603 else (if jt.2.val < 2 then 3614 else 3606)) else (if jt.2.val < 4 then 3612 else (if jt.2.val < 5 then 3613 else 3601))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3006 else (if jt.2.val < 2 then 3012 else 3015)) else (if jt.2.val < 4 then 3011 else (if jt.2.val < 5 then 3014 else 3013)))))

checked_coverage fastCoverage0610 pairing0610 template0610 witness0610

theorem coverage0610 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0610) (maskBits m))
    cores template0610 witness0610 := by
  rw [← coresFast_eq]
  exact fastCoverage0610

theorem coverageSize0610 : ∀ q : Pattern,
    (cores (witness0610 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0610 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0610
#print axioms coverageSize0610

noncomputable def pairing0611 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0611 : List (Fin 4935) := templateData0611

noncomputable def witness0611 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2705 else 2882) else if t 2 = 1 then (if t 3 = 0 then 2710 else if t 3 = 1 then 2688 else 2689) else (if t 3 = 0 then 3198 else if t 3 = 1 then 3191 else 3522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2703 else 1357) else if t 2 = 1 then (if t 3 = 0 then 2708 else if t 3 = 1 then 2682 else 1339) else (if t 3 = 0 then 87 else if t 3 = 1 then 43 else 46)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 475 else 1138) else if t 2 = 1 then (if t 3 = 0 then 489 else if t 3 = 1 then 445 else 448) else (if t 3 = 0 then 1523 else if t 3 = 1 then 1507 else 2125))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2704 else 1672) else if t 2 = 1 then (if t 3 = 0 then 2709 else if t 3 = 1 then 2685 else 1657) else (if t 3 = 0 then 774 else if t 3 = 1 then 733 else 735)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2695 else 2878) else if t 2 = 1 then (if t 3 = 0 then 2707 else if t 3 = 1 then 2664 else 2670) else (if t 3 = 0 then 2717 else if t 3 = 1 then 2668 else 2672)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2879) else if t 2 = 1 then (if t 3 = 0 then 2715 else if t 3 = 1 then 2666 else 2671) else (if t 3 = 0 then 2719 else if t 3 = 1 then 2669 else 2673))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2218 else 1674) else if t 2 = 1 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2212 else 1659) else (if t 3 = 0 then 1147 else if t 3 = 1 then 737 else 739)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2699 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2902 else if t 3 = 1 then 2674 else 2678) else (if t 3 = 0 then 2904 else if t 3 = 1 then 2676 else 2680)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2700 else 3197) else if t 2 = 1 then (if t 3 = 0 then 2903 else if t 3 = 1 then 2675 else 2679) else (if t 3 = 0 then 2905 else if t 3 = 1 then 2677 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4797 else (if jt.2.val < 2 then 4799 else 4802)) else (if jt.2.val < 4 then 4798 else (if jt.2.val < 5 then 4801 else 4800))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3729 else (if jt.2.val < 2 then 3731 else 3737)) else (if jt.2.val < 4 then 3730 else (if jt.2.val < 5 then 3736 else 3732)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3125 else (if jt.2.val < 2 then 3194 else 3148)) else (if jt.2.val < 4 then 3193 else (if jt.2.val < 5 then 3195 else 3110))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3013 else (if jt.2.val < 2 then 3033 else 3015)) else (if jt.2.val < 4 then 3027 else (if jt.2.val < 5 then 3028 else 3006)))))

checked_coverage fastCoverage0611 pairing0611 template0611 witness0611

theorem coverage0611 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0611) (maskBits m))
    cores template0611 witness0611 := by
  rw [← coresFast_eq]
  exact fastCoverage0611

theorem coverageSize0611 : ∀ q : Pattern,
    (cores (witness0611 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0611 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0611
#print axioms coverageSize0611

noncomputable def pairing0612 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0612 : List (Fin 4935) := templateData0612

noncomputable def witness0612 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1546) else if t 2 = 1 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 589) else (if t 3 = 0 then 1053 else if t 3 = 1 then 1051 else 601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 193) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2101) else (if t 3 = 0 then 1733 else if t 3 = 1 then 2082 else 2104)) else (if t 2 = 0 then (if t 3 = 0 then 3532 else if t 3 = 1 then 3530 else 3182) else if t 2 = 1 then (if t 3 = 0 then 3531 else if t 3 = 1 then 3528 else 2648) else (if t 3 = 0 then 2940 else if t 3 = 1 then 2939 else 2654))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1545) else if t 2 = 1 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 588) else (if t 3 = 0 then 1052 else if t 3 = 1 then 1050 else 600)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 192) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2100) else (if t 3 = 0 then 1732 else if t 3 = 1 then 2081 else 2103)) else (if t 2 = 0 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 196) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2102) else (if t 3 = 0 then 1735 else if t 3 = 1 then 2083 else 2105))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 1509 else 2986) else if t 2 = 1 then (if t 3 = 0 then 451 else if t 3 = 1 then 449 else 1119) else (if t 3 = 0 then 3206 else if t 3 = 1 then 476 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 49 else if t 3 = 1 then 47 else 903) else if t 2 = 1 then (if t 3 = 0 then 1341 else if t 3 = 1 then 2089 else 2106) else (if t 3 = 0 then 1358 else if t 3 = 1 then 2097 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 54 else if t 3 = 1 then 53 else 905) else if t 2 = 1 then (if t 3 = 0 then 1344 else if t 3 = 1 then 2091 else 2108) else (if t 3 = 0 then 1361 else if t 3 = 1 then 2099 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4797 else (if jt.2.val < 2 then 4805 else 4802)) else (if jt.2.val < 4 then 4803 else (if jt.2.val < 5 then 4804 else 4800))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4650 else (if jt.2.val < 2 then 4667 else 4653)) else (if jt.2.val < 4 then 4665 else (if jt.2.val < 5 then 4666 else 4648)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2323 else (if jt.2.val < 2 then 2327 else 2328)) else (if jt.2.val < 4 then 2324 else (if jt.2.val < 5 then 2326 else 2325))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2043 else (if jt.2.val < 2 then 2093 else 2096)) else (if jt.2.val < 4 then 2092 else (if jt.2.val < 5 then 2095 else 2094)))))

checked_coverage fastCoverage0612 pairing0612 template0612 witness0612

theorem coverage0612 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0612) (maskBits m))
    cores template0612 witness0612 := by
  rw [← coresFast_eq]
  exact fastCoverage0612

theorem coverageSize0612 : ∀ q : Pattern,
    (cores (witness0612 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0612 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0612
#print axioms coverageSize0612

noncomputable def pairing0613 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0613 : List (Fin 4935) := templateData0613

noncomputable def witness0613 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 2117) else if t 2 = 1 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 567) else (if t 3 = 0 then 780 else if t 3 = 1 then 756 else 1109)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 171) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1411) else (if t 3 = 0 then 1450 else if t 3 = 1 then 1412 else 1413)) else (if t 2 = 0 then (if t 3 = 0 then 3228 else if t 3 = 1 then 3225 else 3524) else if t 2 = 1 then (if t 3 = 0 then 3227 else if t 3 = 1 then 3219 else 2630) else (if t 3 = 0 then 2501 else if t 3 = 1 then 2482 else 2898))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 2115) else if t 2 = 1 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 558) else (if t 3 = 0 then 779 else if t 3 = 1 then 749 else 1106)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 162) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1393) else (if t 3 = 0 then 1449 else if t 3 = 1 then 1396 else 1398)) else (if t 2 = 0 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 163) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1394) else (if t 3 = 0 then 1451 else if t 3 = 1 then 1397 else 1399))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1430 else 2758) else if t 2 = 1 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1199 else 564) else (if t 3 = 0 then 3523 else if t 3 = 1 then 753 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1011 else if t 3 = 1 then 989 else 168) else if t 2 = 1 then (if t 3 = 0 then 1776 else if t 3 = 1 then 1400 else 1402) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1404 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 1013 else if t 3 = 1 then 990 else 169) else if t 2 = 1 then (if t 3 = 0 then 1778 else if t 3 = 1 then 1401 else 1403) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1405 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4767 else (if jt.2.val < 2 then 4783 else 4772)) else (if jt.2.val < 4 then 4782 else (if jt.2.val < 5 then 4784 else 4769))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4332 else (if jt.2.val < 2 then 4360 else 4337)) else (if jt.2.val < 4 then 4359 else (if jt.2.val < 5 then 4361 else 4329)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1380 else (if jt.2.val < 2 then 1382 else 1426)) else (if jt.2.val < 4 then 1381 else (if jt.2.val < 5 then 1425 else 1395))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2094 else (if jt.2.val < 2 then 2114 else 2096)) else (if jt.2.val < 4 then 2112 else (if jt.2.val < 5 then 2113 else 2043)))))

checked_coverage fastCoverage0613 pairing0613 template0613 witness0613

theorem coverage0613 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0613) (maskBits m))
    cores template0613 witness0613 := by
  rw [← coresFast_eq]
  exact fastCoverage0613

theorem coverageSize0613 : ∀ q : Pattern,
    (cores (witness0613 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0613 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0613
#print axioms coverageSize0613

noncomputable def pairing0614 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0614 : List (Fin 4935) := templateData0614

noncomputable def witness0614 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 807 else 201) else if t 2 = 1 then (if t 3 = 0 then 803 else if t 3 = 1 then 799 else 864) else (if t 3 = 0 then 2146 else if t 3 = 1 then 1813 else 1690)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 809 else if t 3 = 1 then 805 else 199) else if t 2 = 1 then (if t 3 = 0 then 801 else if t 3 = 1 then 797 else 862) else (if t 3 = 0 then 833 else if t 3 = 1 then 830 else 868)) else (if t 2 = 0 then (if t 3 = 0 then 2997 else if t 3 = 1 then 2996 else 2781) else if t 2 = 1 then (if t 3 = 0 then 2995 else if t 3 = 1 then 2993 else 3003) else (if t 3 = 0 then 3514 else if t 3 = 1 then 3329 else 3106))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 806 else 200) else if t 2 = 1 then (if t 3 = 0 then 802 else if t 3 = 1 then 798 else 863) else (if t 3 = 0 then 2145 else if t 3 = 1 then 1812 else 1689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 808 else if t 3 = 1 then 804 else 198) else if t 2 = 1 then (if t 3 = 0 then 800 else if t 3 = 1 then 796 else 861) else (if t 3 = 0 then 832 else if t 3 = 1 then 829 else 867)) else (if t 2 = 0 then (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 202) else if t 2 = 1 then (if t 3 = 0 then 819 else if t 3 = 1 then 816 else 865) else (if t 3 = 0 then 839 else if t 3 = 1 then 838 else 869))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 66 else 3525) else if t 2 = 1 then (if t 3 = 0 then 270 else if t 3 = 1 then 854 else 876) else (if t 3 = 0 then 2777 else if t 3 = 1 then 1598 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1470 else if t 3 = 1 then 64 else 2127) else if t 2 = 1 then (if t 3 = 0 then 268 else if t 3 = 1 then 852 else 870) else (if t 3 = 0 then 278 else if t 3 = 1 then 858 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 1472 else if t 3 = 1 then 70 else 2128) else if t 2 = 1 then (if t 3 = 0 then 274 else if t 3 = 1 then 856 else 871) else (if t 3 = 0 then 281 else if t 3 = 1 then 860 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4761 else (if jt.2.val < 2 then 4787 else 4766)) else (if jt.2.val < 4 then 4785 else (if jt.2.val < 5 then 4786 else 4764))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3765 else (if jt.2.val < 2 then 3788 else 3768)) else (if jt.2.val < 4 then 3786 else (if jt.2.val < 5 then 3787 else 3763)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2325 else (if jt.2.val < 2 then 2336 else 2328)) else (if jt.2.val < 4 then 2334 else (if jt.2.val < 5 then 2335 else 2323))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1224 else (if jt.2.val < 2 then 1230 else 1233)) else (if jt.2.val < 4 then 1229 else (if jt.2.val < 5 then 1232 else 1231)))))

checked_coverage fastCoverage0614 pairing0614 template0614 witness0614

theorem coverage0614 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0614) (maskBits m))
    cores template0614 witness0614 := by
  rw [← coresFast_eq]
  exact fastCoverage0614

theorem coverageSize0614 : ∀ q : Pattern,
    (cores (witness0614 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0614 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0614
#print axioms coverageSize0614

noncomputable def pairing0615 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0615 : List (Fin 4935) := templateData0615

noncomputable def witness0615 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 379 else 896) else if t 2 = 1 then (if t 3 = 0 then 384 else if t 3 = 1 then 356 else 357) else (if t 3 = 0 then 1498 else if t 3 = 1 then 1489 else 2159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 386 else if t 3 = 1 then 371 else 892) else if t 2 = 1 then (if t 3 = 0 then 382 else if t 3 = 1 then 336 else 340) else (if t 3 = 0 then 394 else if t 3 = 1 then 339 else 341)) else (if t 2 = 0 then (if t 3 = 0 then 2741 else if t 3 = 1 then 2737 else 2987) else if t 2 = 1 then (if t 3 = 0 then 2740 else if t 3 = 1 then 2728 else 2730) else (if t 3 = 0 then 3207 else if t 3 = 1 then 3203 else 3505))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 375 else 894) else if t 2 = 1 then (if t 3 = 0 then 383 else if t 3 = 1 then 346 else 350) else (if t 3 = 0 then 1497 else if t 3 = 1 then 1483 else 2157)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 385 else if t 3 = 1 then 363 else 888) else if t 2 = 1 then (if t 3 = 0 then 381 else if t 3 = 1 then 318 else 324) else (if t 3 = 0 then 393 else if t 3 = 1 then 322 else 326)) else (if t 2 = 0 then (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 889) else if t 2 = 1 then (if t 3 = 0 then 389 else if t 3 = 1 then 320 else 325) else (if t 3 = 0 then 397 else if t 3 = 1 then 323 else 327))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 377 else 3240) else if t 2 = 1 then (if t 3 = 0 then 930 else if t 3 = 1 then 352 else 354) else (if t 3 = 0 then 2990 else if t 3 = 1 then 1487 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2139 else if t 3 = 1 then 367 else 1494) else if t 2 = 1 then (if t 3 = 0 then 924 else if t 3 = 1 then 328 else 332) else (if t 3 = 0 then 926 else if t 3 = 1 then 330 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 2141 else if t 3 = 1 then 368 else 1495) else if t 2 = 1 then (if t 3 = 0 then 925 else if t 3 = 1 then 329 else 333) else (if t 3 = 0 then 927 else if t 3 = 1 then 331 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4791 else (if jt.2.val < 2 then 4807 else 4796)) else (if jt.2.val < 4 then 4806 else (if jt.2.val < 5 then 4808 else 4793))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3732 else (if jt.2.val < 2 then 3760 else 3737)) else (if jt.2.val < 4 then 3759 else (if jt.2.val < 5 then 3761 else 3729)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1395 else (if jt.2.val < 2 then 1492 else 1426)) else (if jt.2.val < 4 then 1491 else (if jt.2.val < 5 then 1493 else 1380))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1231 else (if jt.2.val < 2 then 1251 else 1233)) else (if jt.2.val < 4 then 1245 else (if jt.2.val < 5 then 1246 else 1224)))))

checked_coverage fastCoverage0615 pairing0615 template0615 witness0615

theorem coverage0615 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0615) (maskBits m))
    cores template0615 witness0615 := by
  rw [← coresFast_eq]
  exact fastCoverage0615

theorem coverageSize0615 : ∀ q : Pattern,
    (cores (witness0615 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0615 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0615
#print axioms coverageSize0615

noncomputable def pairing0616 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0616 : List (Fin 4935) := templateData0616

noncomputable def witness0616 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3340) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2973) else (if t 3 = 0 then 2760 else if t 3 = 1 then 2759 else 2762)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 964) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 963) else (if t 3 = 0 then 292 else if t 3 = 1 then 290 else 304)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2197 else 1802) else if t 2 = 1 then (if t 3 = 0 then 2199 else if t 3 = 1 then 2195 else 979) else (if t 3 = 0 then 299 else if t 3 = 1 then 298 else 308))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 1042) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 1041) else (if t 3 = 0 then 586 else if t 3 = 1 then 584 else 598)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2838) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3472) else (if t 3 = 0 then 3163 else if t 3 = 1 then 3488 else 3490)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2842) else if t 2 = 1 then (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3473) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3489 else 3491))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 441 else 473) else if t 2 = 1 then (if t 3 = 0 then 442 else if t 3 = 1 then 440 else 472) else (if t 3 = 0 then 1838 else if t 3 = 1 then 1117 else 2149)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2471 else 2489) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3479 else 3486) else (if t 3 = 0 then 3315 else if t 3 = 1 then 3492 else 3494)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2475 else 2491) else if t 2 = 1 then (if t 3 = 0 then 3084 else if t 3 = 1 then 3480 else 3487) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3493 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4791 else (if jt.2.val < 2 then 4795 else 4796)) else (if jt.2.val < 4 then 4792 else (if jt.2.val < 5 then 4794 else 4793))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4648 else (if jt.2.val < 2 then 4652 else 4653)) else (if jt.2.val < 4 then 4649 else (if jt.2.val < 5 then 4651 else 4650)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3537 else (if jt.2.val < 2 then 3545 else 3548)) else (if jt.2.val < 4 then 3544 else (if jt.2.val < 5 then 3547 else 3546))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3627 else (if jt.2.val < 2 then 3631 else 3632)) else (if jt.2.val < 4 then 3628 else (if jt.2.val < 5 then 3630 else 3629)))))

checked_coverage fastCoverage0616 pairing0616 template0616 witness0616

theorem coverage0616 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0616) (maskBits m))
    cores template0616 witness0616 := by
  rw [← coresFast_eq]
  exact fastCoverage0616

theorem coverageSize0616 : ∀ q : Pattern,
    (cores (witness0616 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0616 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0616
#print axioms coverageSize0616

noncomputable def pairing0617 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0617 : List (Fin 4935) := templateData0617

noncomputable def witness0617 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3520) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2972) else (if t 3 = 0 then 2798 else if t 3 = 1 then 2797 else 2800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 962) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 961) else (if t 3 = 0 then 88 else if t 3 = 1 then 86 else 100)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1879 else 2138) else if t 2 = 1 then (if t 3 = 0 then 1881 else if t 3 = 1 then 1877 else 978) else (if t 3 = 0 then 95 else if t 3 = 1 then 94 else 104))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 1040) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 1039) else (if t 3 = 0 then 775 else if t 3 = 1 then 773 else 787)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2837) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3276) else (if t 3 = 0 then 3165 else if t 3 = 1 then 3295 else 3297)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2841) else if t 2 = 1 then (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3279) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3296 else 3298))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 637 else 665) else if t 2 = 1 then (if t 3 = 0 then 638 else if t 3 = 1 then 636 else 664) else (if t 3 = 0 then 2162 else if t 3 = 1 then 1141 else 1825)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2623 else 2637) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3291 else 3293) else (if t 3 = 0 then 3500 else if t 3 = 1 then 3299 else 3301)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2627 else 2639) else if t 2 = 1 then (if t 3 = 0 then 3093 else if t 3 = 1 then 3292 else 3294) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3300 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4755 else (if jt.2.val < 2 then 4759 else 4760)) else (if jt.2.val < 4 then 4756 else (if jt.2.val < 5 then 4758 else 4757))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4369 else (if jt.2.val < 2 then 4373 else 4374)) else (if jt.2.val < 4 then 4370 else (if jt.2.val < 5 then 4372 else 4371)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3357 else (if jt.2.val < 2 then 3363 else 3368)) else (if jt.2.val < 4 then 3362 else (if jt.2.val < 5 then 3367 else 3366))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3629 else (if jt.2.val < 2 then 3635 else 3632)) else (if jt.2.val < 4 then 3633 else (if jt.2.val < 5 then 3634 else 3627)))))

checked_coverage fastCoverage0617 pairing0617 template0617 witness0617

theorem coverage0617 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0617) (maskBits m))
    cores template0617 witness0617 := by
  rw [← coresFast_eq]
  exact fastCoverage0617

theorem coverageSize0617 : ∀ q : Pattern,
    (cores (witness0617 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0617 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0617
#print axioms coverageSize0617

noncomputable def pairing0618 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0618 : List (Fin 4935) := templateData0618

noncomputable def witness0618 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2565 else 2577) else if t 2 = 1 then (if t 3 = 0 then 2560 else if t 3 = 1 then 2544 else 2545) else (if t 3 = 0 then 3499 else if t 3 = 1 then 3209 else 3342)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2563 else 1372) else if t 2 = 1 then (if t 3 = 0 then 2558 else if t 3 = 1 then 2538 else 1350) else (if t 3 = 0 then 277 else if t 3 = 1 then 251 else 254)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 681 else 695) else if t 2 = 1 then (if t 3 = 0 then 667 else if t 3 = 1 then 641 else 644) else (if t 3 = 0 then 2170 else if t 3 = 1 then 1459 else 1786))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2564 else 1687) else if t 2 = 1 then (if t 3 = 0 then 2559 else if t 3 = 1 then 2541 else 1666) else (if t 3 = 0 then 571 else if t 3 = 1 then 545 else 547)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2562 else 2576) else if t 2 = 1 then (if t 3 = 0 then 2548 else if t 3 = 1 then 2519 else 2526) else (if t 3 = 0 then 2550 else if t 3 = 1 then 2523 else 2528)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2578) else if t 2 = 1 then (if t 3 = 0 then 2549 else if t 3 = 1 then 2521 else 2527) else (if t 3 = 0 then 2551 else if t 3 = 1 then 2524 else 2529))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1915 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1900 else 1668) else (if t 3 = 0 then 573 else if t 3 = 1 then 549 else 551)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2883 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2554 else if t 3 = 1 then 2530 else 2534) else (if t 3 = 0 then 2556 else if t 3 = 1 then 2532 else 2536)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2885 else 3507) else if t 2 = 1 then (if t 3 = 0 then 2555 else if t 3 = 1 then 2531 else 2535) else (if t 3 = 0 then 2557 else if t 3 = 1 then 2533 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4773 else (if jt.2.val < 2 then 4775 else 4778)) else (if jt.2.val < 4 then 4774 else (if jt.2.val < 5 then 4777 else 4776))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3705 else (if jt.2.val < 2 then 3707 else 3713)) else (if jt.2.val < 4 then 3706 else (if jt.2.val < 5 then 3712 else 3708)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3546 else (if jt.2.val < 2 then 3554 else 3548)) else (if jt.2.val < 4 then 3552 else (if jt.2.val < 5 then 3553 else 3537))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2510 else (if jt.2.val < 2 then 2512 else 2553)) else (if jt.2.val < 4 then 2511 else (if jt.2.val < 5 then 2552 else 2525)))))

checked_coverage fastCoverage0618 pairing0618 template0618 witness0618

theorem coverage0618 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0618) (maskBits m))
    cores template0618 witness0618 := by
  rw [← coresFast_eq]
  exact fastCoverage0618

theorem coverageSize0618 : ∀ q : Pattern,
    (cores (witness0618 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0618 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0618
#print axioms coverageSize0618

noncomputable def pairing0619 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0619 : List (Fin 4935) := templateData0619

noncomputable def witness0619 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2710 else 2722) else if t 2 = 1 then (if t 3 = 0 then 2705 else if t 3 = 1 then 2688 else 2689) else (if t 3 = 0 then 3312 else if t 3 = 1 then 3191 else 3522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2708 else 1371) else if t 2 = 1 then (if t 3 = 0 then 2703 else if t 3 = 1 then 2682 else 1339) else (if t 3 = 0 then 73 else if t 3 = 1 then 43 else 46)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 489 else 503) else if t 2 = 1 then (if t 3 = 0 then 475 else if t 3 = 1 then 445 else 448) else (if t 3 = 0 then 1849 else if t 3 = 1 then 1507 else 2125))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2709 else 1686) else if t 2 = 1 then (if t 3 = 0 then 2704 else if t 3 = 1 then 2685 else 1657) else (if t 3 = 0 then 760 else if t 3 = 1 then 733 else 735)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2707 else 2721) else if t 2 = 1 then (if t 3 = 0 then 2695 else if t 3 = 1 then 2664 else 2670) else (if t 3 = 0 then 2697 else if t 3 = 1 then 2668 else 2672)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2723) else if t 2 = 1 then (if t 3 = 0 then 2696 else if t 3 = 1 then 2666 else 2671) else (if t 3 = 0 then 2698 else if t 3 = 1 then 2669 else 2673))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2227 else 1855) else if t 2 = 1 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2212 else 1659) else (if t 3 = 0 then 762 else if t 3 = 1 then 737 else 739)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2902 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2699 else if t 3 = 1 then 2674 else 2678) else (if t 3 = 0 then 2701 else if t 3 = 1 then 2676 else 2680)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2903 else 3322) else if t 2 = 1 then (if t 3 = 0 then 2700 else if t 3 = 1 then 2675 else 2679) else (if t 3 = 0 then 2702 else if t 3 = 1 then 2677 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4797 else (if jt.2.val < 2 then 4799 else 4802)) else (if jt.2.val < 4 then 4798 else (if jt.2.val < 5 then 4801 else 4800))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3729 else (if jt.2.val < 2 then 3731 else 3737)) else (if jt.2.val < 4 then 3730 else (if jt.2.val < 5 then 3736 else 3732)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3366 else (if jt.2.val < 2 then 3380 else 3368)) else (if jt.2.val < 4 then 3378 else (if jt.2.val < 5 then 3379 else 3357))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2525 else (if jt.2.val < 2 then 2693 else 2553)) else (if jt.2.val < 4 then 2692 else (if jt.2.val < 5 then 2694 else 2510)))))

checked_coverage fastCoverage0619 pairing0619 template0619 witness0619

theorem coverage0619 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0619) (maskBits m))
    cores template0619 witness0619 := by
  rw [← coresFast_eq]
  exact fastCoverage0619

theorem coverageSize0619 : ∀ q : Pattern,
    (cores (witness0619 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0619 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0619
#print axioms coverageSize0619

noncomputable def pairing0620 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0620 : List (Fin 4935) := templateData0620

noncomputable def witness0620 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1816) else if t 2 = 1 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 1051) else (if t 3 = 0 then 591 else if t 3 = 1 then 589 else 601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 835) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2082) else (if t 3 = 0 then 1447 else if t 3 = 1 then 2101 else 2104)) else (if t 2 = 0 then (if t 3 = 0 then 3532 else if t 3 = 1 then 3530 else 3330) else if t 2 = 1 then (if t 3 = 0 then 3531 else if t 3 = 1 then 3528 else 2939) else (if t 3 = 0 then 2649 else if t 3 = 1 then 2648 else 2654))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1815) else if t 2 = 1 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 1050) else (if t 3 = 0 then 590 else if t 3 = 1 then 588 else 600)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 834) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2081) else (if t 3 = 0 then 1446 else if t 3 = 1 then 2100 else 2103)) else (if t 2 = 0 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 840) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2083) else (if t 3 = 0 then 1448 else if t 3 = 1 then 2102 else 2105))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 1509 else 2739) else if t 2 = 1 then (if t 3 = 0 then 451 else if t 3 = 1 then 449 else 476) else (if t 3 = 0 then 3343 else if t 3 = 1 then 1119 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 49 else if t 3 = 1 then 47 else 74) else if t 2 = 1 then (if t 3 = 0 then 1341 else if t 3 = 1 then 2089 else 2097) else (if t 3 = 0 then 1779 else if t 3 = 1 then 2106 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 54 else if t 3 = 1 then 53 else 77) else if t 2 = 1 then (if t 3 = 0 then 1344 else if t 3 = 1 then 2091 else 2099) else (if t 3 = 0 then 1781 else if t 3 = 1 then 2108 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4797 else (if jt.2.val < 2 then 4805 else 4802)) else (if jt.2.val < 4 then 4803 else (if jt.2.val < 5 then 4804 else 4800))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4650 else (if jt.2.val < 2 then 4667 else 4653)) else (if jt.2.val < 4 then 4665 else (if jt.2.val < 5 then 4666 else 4648)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2232 else (if jt.2.val < 2 then 2240 else 2243)) else (if jt.2.val < 4 then 2239 else (if jt.2.val < 5 then 2242 else 2241))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2358 else (if jt.2.val < 2 then 2362 else 2363)) else (if jt.2.val < 4 then 2359 else (if jt.2.val < 5 then 2361 else 2360)))))

checked_coverage fastCoverage0620 pairing0620 template0620 witness0620

theorem coverage0620 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0620) (maskBits m))
    cores template0620 witness0620 := by
  rw [← coresFast_eq]
  exact fastCoverage0620

theorem coverageSize0620 : ∀ q : Pattern,
    (cores (witness0620 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0620 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0620
#print axioms coverageSize0620

noncomputable def pairing0621 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0621 : List (Fin 4935) := templateData0621

noncomputable def witness0621 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 2146) else if t 2 = 1 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 1049) else (if t 3 = 0 then 780 else if t 3 = 1 then 778 else 790)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 833) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1730) else (if t 3 = 0 then 1450 else if t 3 = 1 then 1753 else 1756)) else (if t 2 = 0 then (if t 3 = 0 then 3352 else if t 3 = 1 then 3350 else 3514) else if t 2 = 1 then (if t 3 = 0 then 3351 else if t 3 = 1 then 3348 else 2938) else (if t 3 = 0 then 2501 else if t 3 = 1 then 2500 else 2506))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 2145) else if t 2 = 1 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 1048) else (if t 3 = 0 then 779 else if t 3 = 1 then 777 else 789)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 832) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1729) else (if t 3 = 0 then 1449 else if t 3 = 1 then 1752 else 1755)) else (if t 2 = 0 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 839) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1734) else (if t 3 = 0 then 1451 else if t 3 = 1 then 1754 else 1757))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1461 else 2777) else if t 2 = 1 then (if t 3 = 0 then 647 else if t 3 = 1 then 645 else 668) else (if t 3 = 0 then 3523 else if t 3 = 1 then 1142 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 257 else if t 3 = 1 then 255 else 278) else if t 2 = 1 then (if t 3 = 0 then 1352 else if t 3 = 1 then 1746 else 1749) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1758 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 262 else if t 3 = 1 then 261 else 281) else if t 2 = 1 then (if t 3 = 0 then 1355 else if t 3 = 1 then 1748 else 1751) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1759 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4773 else (if jt.2.val < 2 then 4781 else 4778)) else (if jt.2.val < 4 then 4779 else (if jt.2.val < 5 then 4780 else 4776))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4371 else (if jt.2.val < 2 then 4388 else 4374)) else (if jt.2.val < 4 then 4386 else (if jt.2.val < 5 then 4387 else 4369)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1917 else (if jt.2.val < 2 then 1923 else 1928)) else (if jt.2.val < 4 then 1922 else (if jt.2.val < 5 then 1927 else 1926))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2360 else (if jt.2.val < 2 then 2366 else 2363)) else (if jt.2.val < 4 then 2364 else (if jt.2.val < 5 then 2365 else 2358)))))

checked_coverage fastCoverage0621 pairing0621 template0621 witness0621

theorem coverage0621 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0621) (maskBits m))
    cores template0621 witness0621 := by
  rw [← coresFast_eq]
  exact fastCoverage0621

theorem coverageSize0621 : ∀ q : Pattern,
    (cores (witness0621 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0621 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0621
#print axioms coverageSize0621

noncomputable def pairing0622 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0622 : List (Fin 4935) := templateData0622

noncomputable def witness0622 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 183 else 201) else if t 2 = 1 then (if t 3 = 0 then 178 else if t 3 = 1 then 156 else 157) else (if t 3 = 0 then 2117 else if t 3 = 1 then 1537 else 1835)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 185 else if t 3 = 1 then 181 else 199) else if t 2 = 1 then (if t 3 = 0 then 170 else if t 3 = 1 then 136 else 140) else (if t 3 = 0 then 171 else if t 3 = 1 then 139 else 141)) else (if t 2 = 0 then (if t 3 = 0 then 2779 else if t 3 = 1 then 2778 else 2781) else if t 2 = 1 then (if t 3 = 0 then 2775 else if t 3 = 1 then 2766 else 2768) else (if t 3 = 0 then 3524 else if t 3 = 1 then 3172 else 3320))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 182 else 200) else if t 2 = 1 then (if t 3 = 0 then 174 else if t 3 = 1 then 146 else 150) else (if t 3 = 0 then 2115 else if t 3 = 1 then 1531 else 1833)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 184 else if t 3 = 1 then 180 else 198) else if t 2 = 1 then (if t 3 = 0 then 160 else if t 3 = 1 then 117 else 124) else (if t 3 = 0 then 162 else if t 3 = 1 then 121 else 126)) else (if t 2 = 0 then (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 202) else if t 2 = 1 then (if t 3 = 0 then 161 else if t 3 = 1 then 119 else 125) else (if t 3 = 0 then 163 else if t 3 = 1 then 122 else 127))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 899 else 3525) else if t 2 = 1 then (if t 3 = 0 then 176 else if t 3 = 1 then 152 else 154) else (if t 3 = 0 then 2758 else if t 3 = 1 then 1535 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1806 else if t 3 = 1 then 897 else 2127) else if t 2 = 1 then (if t 3 = 0 then 166 else if t 3 = 1 then 128 else 132) else (if t 3 = 0 then 168 else if t 3 = 1 then 130 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 1808 else if t 3 = 1 then 901 else 2128) else if t 2 = 1 then (if t 3 = 0 then 167 else if t 3 = 1 then 129 else 133) else (if t 3 = 0 then 169 else if t 3 = 1 then 131 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4755 else (if jt.2.val < 2 then 4789 else 4760)) else (if jt.2.val < 4 then 4788 else (if jt.2.val < 5 then 4790 else 4757))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3708 else (if jt.2.val < 2 then 3748 else 3713)) else (if jt.2.val < 4 then 3747 else (if jt.2.val < 5 then 3749 else 3705)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2241 else (if jt.2.val < 2 then 2249 else 2243)) else (if jt.2.val < 4 then 2247 else (if jt.2.val < 5 then 2248 else 2232))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 108 else (if jt.2.val < 2 then 110 else 165)) else (if jt.2.val < 4 then 109 else (if jt.2.val < 5 then 164 else 123)))))

checked_coverage fastCoverage0622 pairing0622 template0622 witness0622

theorem coverage0622 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0622) (maskBits m))
    cores template0622 witness0622 := by
  rw [← coresFast_eq]
  exact fastCoverage0622

theorem coverageSize0622 : ∀ q : Pattern,
    (cores (witness0622 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0622 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0622
#print axioms coverageSize0622

noncomputable def pairing0623 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0623 : List (Fin 4935) := templateData0623

noncomputable def witness0623 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 384 else 402) else if t 2 = 1 then (if t 3 = 0 then 379 else if t 3 = 1 then 356 else 357) else (if t 3 = 0 then 1775 else if t 3 = 1 then 1489 else 2159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 386 else if t 3 = 1 then 382 else 400) else if t 2 = 1 then (if t 3 = 0 then 371 else if t 3 = 1 then 336 else 340) else (if t 3 = 0 then 372 else if t 3 = 1 then 339 else 341)) else (if t 2 = 0 then (if t 3 = 0 then 2741 else if t 3 = 1 then 2740 else 2743) else if t 2 = 1 then (if t 3 = 0 then 2737 else if t 3 = 1 then 2728 else 2730) else (if t 3 = 0 then 3344 else if t 3 = 1 then 3203 else 3505))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 383 else 401) else if t 2 = 1 then (if t 3 = 0 then 375 else if t 3 = 1 then 346 else 350) else (if t 3 = 0 then 1773 else if t 3 = 1 then 1483 else 2157)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 385 else if t 3 = 1 then 381 else 399) else if t 2 = 1 then (if t 3 = 0 then 363 else if t 3 = 1 then 318 else 324) else (if t 3 = 0 then 365 else if t 3 = 1 then 322 else 326)) else (if t 2 = 0 then (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 403) else if t 2 = 1 then (if t 3 = 0 then 364 else if t 3 = 1 then 320 else 325) else (if t 3 = 0 then 366 else if t 3 = 1 then 323 else 327))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 930 else 3345) else if t 2 = 1 then (if t 3 = 0 then 377 else if t 3 = 1 then 352 else 354) else (if t 3 = 0 then 2796 else if t 3 = 1 then 1487 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2139 else if t 3 = 1 then 924 else 1788) else if t 2 = 1 then (if t 3 = 0 then 367 else if t 3 = 1 then 328 else 332) else (if t 3 = 0 then 369 else if t 3 = 1 then 330 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 2141 else if t 3 = 1 then 925 else 1789) else if t 2 = 1 then (if t 3 = 0 then 368 else if t 3 = 1 then 329 else 333) else (if t 3 = 0 then 370 else if t 3 = 1 then 331 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4791 else (if jt.2.val < 2 then 4807 else 4796)) else (if jt.2.val < 4 then 4806 else (if jt.2.val < 5 then 4808 else 4793))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3732 else (if jt.2.val < 2 then 3760 else 3737)) else (if jt.2.val < 4 then 3759 else (if jt.2.val < 5 then 3761 else 3729)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1926 else (if jt.2.val < 2 then 1940 else 1928)) else (if jt.2.val < 4 then 1938 else (if jt.2.val < 5 then 1939 else 1917))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 123 else (if jt.2.val < 2 then 361 else 165)) else (if jt.2.val < 4 then 360 else (if jt.2.val < 5 then 362 else 108)))))

checked_coverage fastCoverage0623 pairing0623 template0623 witness0623

theorem coverage0623 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0623) (maskBits m))
    cores template0623 witness0623 := by
  rw [← coresFast_eq]
  exact fastCoverage0623

theorem coverageSize0623 : ∀ q : Pattern,
    (cores (witness0623 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0623 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0623
#print axioms coverageSize0623

noncomputable def pairing0624 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0624 : List (Fin 4935) := templateData0624

noncomputable def witness0624 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 3935) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2740) else (if t 3 = 0 then 2997 else if t 3 = 1 then 2995 else 2743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 489) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 488) else (if t 3 = 0 then 1174 else if t 3 = 1 then 1170 else 502)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1879 else 1523) else if t 2 = 1 then (if t 3 = 0 then 1882 else if t 3 = 1 then 1878 else 496) else (if t 3 = 0 then 1190 else if t 3 = 1 then 1188 else 506))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 390) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 389) else (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 403)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2715) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4019) else (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4021)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2719) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4020) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4003 else 4022))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 243 else 931) else if t 2 = 1 then (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 925) else (if t 3 = 0 then 1472 else if t 3 = 1 then 274 else 1789)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2903) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4023) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4017 else 4025)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2627 else 2905) else if t 2 = 1 then (if t 3 = 0 then 3847 else if t 3 = 1 then 4016 else 4024) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4018 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4809 else (if jt.2.val < 2 then 4813 else 4814)) else (if jt.2.val < 4 then 4810 else (if jt.2.val < 5 then 4812 else 4811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4432 else (if jt.2.val < 2 then 4436 else 4437)) else (if jt.2.val < 4 then 4433 else (if jt.2.val < 5 then 4435 else 4434)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4234 else (if jt.2.val < 2 then 4238 else 4239)) else (if jt.2.val < 4 then 4235 else (if jt.2.val < 5 then 4237 else 4236))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3969 else (if jt.2.val < 2 then 4006 else 4009)) else (if jt.2.val < 4 then 4005 else (if jt.2.val < 5 then 4008 else 4007)))))

checked_coverage fastCoverage0624 pairing0624 template0624 witness0624

theorem coverage0624 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0624) (maskBits m))
    cores template0624 witness0624 := by
  rw [← coresFast_eq]
  exact fastCoverage0624

theorem coverageSize0624 : ∀ q : Pattern,
    (cores (witness0624 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0624 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0624
#print axioms coverageSize0624

noncomputable def pairing0625 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0625 : List (Fin 4935) := templateData0625

noncomputable def witness0625 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4036) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2737) else (if t 3 = 0 then 2779 else if t 3 = 1 then 2775 else 2987)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 475) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 462) else (if t 3 = 0 then 682 else if t 3 = 1 then 654 else 1132)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1597 else 1849) else if t 2 = 1 then (if t 3 = 0 then 1612 else if t 3 = 1 then 1593 else 464) else (if t 3 = 0 then 689 else if t 3 = 1 then 656 else 1134))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 376) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 364) else (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 889)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2696) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3880) else (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3882)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2698) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3881) else (if t 3 = 0 then 3916 else if t 3 = 1 then 3878 else 3883))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 994 else 378) else if t 2 = 1 then (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 368) else (if t 3 = 0 then 1808 else if t 3 = 1 then 167 else 1495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2700) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3888) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3886 else 3890)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2950 else 2702) else if t 2 = 1 then (if t 3 = 0 then 4038 else if t 3 = 1 then 3885 else 3889) else (if t 3 = 0 then 4040 else if t 3 = 1 then 3887 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4815 else (if jt.2.val < 2 then 4817 else 4820)) else (if jt.2.val < 4 then 4816 else (if jt.2.val < 5 then 4819 else 4818))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4410 else (if jt.2.val < 2 then 4412 else 4418)) else (if jt.2.val < 4 then 4411 else (if jt.2.val < 5 then 4417 else 4413)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4110 else (if jt.2.val < 2 then 4112 else 4118)) else (if jt.2.val < 4 then 4111 else (if jt.2.val < 5 then 4117 else 4113))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4007 else (if jt.2.val < 2 then 4032 else 4009)) else (if jt.2.val < 4 then 4027 else (if jt.2.val < 5 then 4028 else 3969)))))

checked_coverage fastCoverage0625 pairing0625 template0625 witness0625

theorem coverage0625 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0625) (maskBits m))
    cores template0625 witness0625 := by
  rw [← coresFast_eq]
  exact fastCoverage0625

theorem coverageSize0625 : ∀ q : Pattern,
    (cores (witness0625 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0625 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0625
#print axioms coverageSize0625

noncomputable def pairing0626 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0626 : List (Fin 4935) := templateData0626

noncomputable def witness0626 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2813 else 2722) else if t 2 = 1 then (if t 3 = 0 then 2817 else if t 3 = 1 then 2809 else 2860) else (if t 3 = 0 then 4056 else if t 3 = 1 then 4054 else 3967)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2811 else 1371) else if t 2 = 1 then (if t 3 = 0 then 2815 else if t 3 = 1 then 2807 else 1370) else (if t 3 = 0 then 1173 else if t 3 = 1 then 1169 else 1211)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 962 else 101) else if t 2 = 1 then (if t 3 = 0 then 964 else if t 3 = 1 then 960 else 1001) else (if t 3 = 0 then 1802 else if t 3 = 1 then 1801 else 1376))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2812 else 1686) else if t 2 = 1 then (if t 3 = 0 then 2816 else if t 3 = 1 then 2808 else 1685) else (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 866)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2810 else 2721) else if t 2 = 1 then (if t 3 = 0 then 2814 else if t 3 = 1 then 2806 else 2859) else (if t 3 = 0 then 2829 else if t 3 = 1 then 2826 else 2861)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2724) else if t 2 = 1 then (if t 3 = 0 then 2838 else if t 3 = 1 then 2835 else 2862) else (if t 3 = 0 then 2842 else if t 3 = 1 then 2840 else 2863))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1585 else 1855) else if t 2 = 1 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1584 else 1852) else (if t 3 = 0 then 71 else if t 3 = 1 then 857 else 877)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2632 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2484 else if t 3 = 1 then 2854 else 2864) else (if t 3 = 0 then 2487 else if t 3 = 1 then 2856 else 2865)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2637 else 4045) else if t 2 = 1 then (if t 3 = 0 then 2489 else if t 3 = 1 then 2857 else 2866) else (if t 3 = 0 then 2491 else if t 3 = 1 then 2858 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4767 else (if jt.2.val < 2 then 4771 else 4772)) else (if jt.2.val < 4 then 4768 else (if jt.2.val < 5 then 4770 else 4769))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2804 else (if jt.2.val < 2 then 2834 else 2836)) else (if jt.2.val < 4 then 2831 else (if jt.2.val < 5 then 2833 else 2832)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4236 else (if jt.2.val < 2 then 4253 else 4239)) else (if jt.2.val < 4 then 4251 else (if jt.2.val < 5 then 4252 else 4234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2802 else (if jt.2.val < 2 then 2845 else 2848)) else (if jt.2.val < 4 then 2844 else (if jt.2.val < 5 then 2847 else 2846)))))

checked_coverage fastCoverage0626 pairing0626 template0626 witness0626

theorem coverage0626 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0626) (maskBits m))
    cores template0626 witness0626 := by
  rw [← coresFast_eq]
  exact fastCoverage0626

theorem coverageSize0626 : ∀ q : Pattern,
    (cores (witness0626 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0626 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0626
#print axioms coverageSize0626

noncomputable def pairing0627 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0627 : List (Fin 4935) := templateData0627

noncomputable def witness0627 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2560 else 2882) else if t 2 = 1 then (if t 3 = 0 then 2565 else if t 3 = 1 then 2544 else 2545) else (if t 3 = 0 then 3951 else if t 3 = 1 then 3945 else 4058)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2558 else 1357) else if t 2 = 1 then (if t 3 = 0 then 2563 else if t 3 = 1 then 2538 else 1350) else (if t 3 = 0 then 681 else if t 3 = 1 then 641 else 644)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 277 else 922) else if t 2 = 1 then (if t 3 = 0 then 291 else if t 3 = 1 then 251 else 254) else (if t 3 = 0 then 1475 else if t 3 = 1 then 1459 else 1786))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2559 else 1672) else if t 2 = 1 then (if t 3 = 0 then 2564 else if t 3 = 1 then 2541 else 1666) else (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 151)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2548 else 2878) else if t 2 = 1 then (if t 3 = 0 then 2562 else if t 3 = 1 then 2519 else 2526) else (if t 3 = 0 then 2570 else if t 3 = 1 then 2521 else 2527)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2880) else if t 2 = 1 then (if t 3 = 0 then 2572 else if t 3 = 1 then 2523 else 2528) else (if t 3 = 0 then 2574 else if t 3 = 1 then 2524 else 2529))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1903 else 1674) else if t 2 = 1 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1900 else 1668) else (if t 3 = 0 then 902 else if t 3 = 1 then 153 else 155)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2554 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2883 else if t 3 = 1 then 2530 else 2534) else (if t 3 = 0 then 2885 else if t 3 = 1 then 2531 else 2535)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2556 else 3934) else if t 2 = 1 then (if t 3 = 0 then 2886 else if t 3 = 1 then 2532 else 2536) else (if t 3 = 0 then 2887 else if t 3 = 1 then 2533 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4773 else (if jt.2.val < 2 then 4775 else 4778)) else (if jt.2.val < 4 then 4774 else (if jt.2.val < 5 then 4777 else 4776))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2513 else (if jt.2.val < 2 then 2515 else 2543)) else (if jt.2.val < 4 then 2514 else (if jt.2.val < 5 then 2542 else 2522)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4113 else (if jt.2.val < 2 then 4123 else 4118)) else (if jt.2.val < 4 then 4122 else (if jt.2.val < 5 then 4124 else 4110))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2846 else (if jt.2.val < 2 then 2874 else 2848)) else (if jt.2.val < 4 then 2869 else (if jt.2.val < 5 then 2870 else 2802)))))

checked_coverage fastCoverage0627 pairing0627 template0627 witness0627

theorem coverage0627 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0627) (maskBits m))
    cores template0627 witness0627 := by
  rw [← coresFast_eq]
  exact fastCoverage0627

theorem coverageSize0627 : ∀ q : Pattern,
    (cores (witness0627 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0627 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0627
#print axioms coverageSize0627

noncomputable def pairing0628 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0628 : List (Fin 4935) := templateData0628

noncomputable def witness0628 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 1498) else if t 2 = 1 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 394) else (if t 3 = 0 then 837 else if t 3 = 1 then 833 else 406)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 778) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1753) else (if t 3 = 0 then 1733 else if t 3 = 1 then 1730 else 1756)) else (if t 2 = 0 then (if t 3 = 0 then 4066 else if t 3 = 1 then 4064 else 3943) else if t 2 = 1 then (if t 3 = 0 then 3351 else if t 3 = 1 then 3348 else 2500) else (if t 3 = 0 then 2940 else if t 3 = 1 then 2938 else 2506))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 1497) else if t 2 = 1 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 393) else (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 405)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 777) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1752) else (if t 3 = 0 then 1732 else if t 3 = 1 then 1729 else 1755)) else (if t 2 = 0 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 781) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1754) else (if t 3 = 0 then 1735 else if t 3 = 1 then 1734 else 1757))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1461 else 2990) else if t 2 = 1 then (if t 3 = 0 then 257 else if t 3 = 1 then 255 else 926) else (if t 3 = 0 then 3942 else if t 3 = 1 then 278 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 647 else if t 3 = 1 then 645 else 1142) else if t 2 = 1 then (if t 3 = 0 then 1352 else if t 3 = 1 then 1746 else 1758) else (if t 3 = 0 then 1358 else if t 3 = 1 then 1749 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 652 else if t 3 = 1 then 651 else 1143) else if t 2 = 1 then (if t 3 = 0 then 1355 else if t 3 = 1 then 1748 else 1759) else (if t 3 = 0 then 1361 else if t 3 = 1 then 1751 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4773 else (if jt.2.val < 2 then 4781 else 4778)) else (if jt.2.val < 4 then 4779 else (if jt.2.val < 5 then 4780 else 4776))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4434 else (if jt.2.val < 2 then 4445 else 4437)) else (if jt.2.val < 4 then 4443 else (if jt.2.val < 5 then 4444 else 4432)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1694 else (if jt.2.val < 2 then 1728 else 1731)) else (if jt.2.val < 4 then 1725 else (if jt.2.val < 5 then 1727 else 1726))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1692 else (if jt.2.val < 2 then 1737 else 1740)) else (if jt.2.val < 4 then 1736 else (if jt.2.val < 5 then 1739 else 1738)))))

checked_coverage fastCoverage0628 pairing0628 template0628 witness0628

theorem coverage0628 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0628) (maskBits m))
    cores template0628 witness0628 := by
  rw [← coresFast_eq]
  exact fastCoverage0628

theorem coverageSize0628 : ∀ q : Pattern,
    (cores (witness0628 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0628 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0628
#print axioms coverageSize0628

noncomputable def pairing0629 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0629 : List (Fin 4935) := templateData0629

noncomputable def witness0629 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 1775) else if t 2 = 1 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 372) else (if t 3 = 0 then 195 else if t 3 = 1 then 171 else 893)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 756) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1412) else (if t 3 = 0 then 1447 else if t 3 = 1 then 1411 else 1413)) else (if t 2 = 0 then (if t 3 = 0 then 3959 else if t 3 = 1 then 3953 else 4060) else if t 2 = 1 then (if t 3 = 0 then 3227 else if t 3 = 1 then 3219 else 2482) else (if t 3 = 0 then 2649 else if t 3 = 1 then 2630 else 2898))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 1773) else if t 2 = 1 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 365) else (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 890)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 749) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1396) else (if t 3 = 0 then 1446 else if t 3 = 1 then 1393 else 1398)) else (if t 2 = 0 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 750) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1397) else (if t 3 = 0 then 1448 else if t 3 = 1 then 1394 else 1399))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1430 else 2796) else if t 2 = 1 then (if t 3 = 0 then 1011 else if t 3 = 1 then 989 else 369) else (if t 3 = 0 then 4059 else if t 3 = 1 then 168 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1199 else 753) else if t 2 = 1 then (if t 3 = 0 then 1776 else if t 3 = 1 then 1400 else 1404) else (if t 3 = 0 then 1779 else if t 3 = 1 then 1402 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 1223 else if t 3 = 1 then 1200 else 754) else if t 2 = 1 then (if t 3 = 0 then 1778 else if t 3 = 1 then 1401 else 1405) else (if t 3 = 0 then 1781 else if t 3 = 1 then 1403 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4767 else (if jt.2.val < 2 then 4783 else 4772)) else (if jt.2.val < 4 then 4782 else (if jt.2.val < 5 then 4784 else 4769))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4413 else (if jt.2.val < 2 then 4423 else 4418)) else (if jt.2.val < 4 then 4422 else (if jt.2.val < 5 then 4424 else 4410)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1383 else (if jt.2.val < 2 then 1385 else 1421)) else (if jt.2.val < 4 then 1384 else (if jt.2.val < 5 then 1420 else 1392))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1738 else (if jt.2.val < 2 then 1769 else 1740)) else (if jt.2.val < 4 then 1764 else (if jt.2.val < 5 then 1765 else 1692)))))

checked_coverage fastCoverage0629 pairing0629 template0629 witness0629

theorem coverage0629 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0629) (maskBits m))
    cores template0629 witness0629 := by
  rw [← coresFast_eq]
  exact fastCoverage0629

theorem coverageSize0629 : ∀ q : Pattern,
    (cores (witness0629 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0629 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0629
#print axioms coverageSize0629

noncomputable def pairing0630 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0630 : List (Fin 4935) := templateData0630

noncomputable def witness0630 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1025 else 786) else if t 2 = 1 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1021 else 1080) else (if t 3 = 0 then 1816 else if t 3 = 1 then 1813 else 1690)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1023 else 784) else if t 2 = 1 then (if t 3 = 0 then 1027 else if t 3 = 1 then 1019 else 1078) else (if t 3 = 0 then 1051 else if t 3 = 1 then 1046 else 1084)) else (if t 2 = 0 then (if t 3 = 0 then 2974 else if t 3 = 1 then 2972 else 2800) else if t 2 = 1 then (if t 3 = 0 then 2973 else if t 3 = 1 then 2970 else 2980) else (if t 3 = 0 then 4047 else if t 3 = 1 then 4046 else 3860))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1024 else 785) else if t 2 = 1 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1020 else 1079) else (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1022 else 783) else if t 2 = 1 then (if t 3 = 0 then 1026 else if t 3 = 1 then 1018 else 1077) else (if t 3 = 0 then 1050 else if t 3 = 1 then 1045 else 1083)) else (if t 2 = 0 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 787) else if t 2 = 1 then (if t 3 = 0 then 1041 else if t 3 = 1 then 1037 else 1081) else (if t 3 = 0 then 1056 else if t 3 = 1 then 1054 else 1085))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 660 else 4061) else if t 2 = 1 then (if t 3 = 0 then 468 else if t 3 = 1 then 1070 else 1092) else (if t 3 = 0 then 2739 else if t 3 = 1 then 1598 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1518 else if t 3 = 1 then 658 else 1824) else if t 2 = 1 then (if t 3 = 0 then 466 else if t 3 = 1 then 1068 else 1086) else (if t 3 = 0 then 476 else if t 3 = 1 then 1074 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 1520 else if t 3 = 1 then 664 else 1825) else if t 2 = 1 then (if t 3 = 0 then 472 else if t 3 = 1 then 1072 else 1087) else (if t 3 = 0 then 479 else if t 3 = 1 then 1076 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4815 else (if jt.2.val < 2 then 4823 else 4820)) else (if jt.2.val < 4 then 4821 else (if jt.2.val < 5 then 4822 else 4818))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2832 else (if jt.2.val < 2 then 2971 else 2836)) else (if jt.2.val < 4 then 2968 else (if jt.2.val < 5 then 2969 else 2804)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1726 else (if jt.2.val < 2 then 1814 else 1731)) else (if jt.2.val < 4 then 1809 else (if jt.2.val < 5 then 1810 else 1694))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1016 else (if jt.2.val < 2 then 1059 else 1062)) else (if jt.2.val < 4 then 1058 else (if jt.2.val < 5 then 1061 else 1060)))))

checked_coverage fastCoverage0630 pairing0630 template0630 witness0630

theorem coverage0630 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0630) (maskBits m))
    cores template0630 witness0630 := by
  rw [← coresFast_eq]
  exact fastCoverage0630

theorem coverageSize0630 : ∀ q : Pattern,
    (cores (witness0630 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0630 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0630
#print axioms coverageSize0630

noncomputable def pairing0631 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0631 : List (Fin 4935) := templateData0631

noncomputable def witness0631 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 574 else 1112) else if t 2 = 1 then (if t 3 = 0 then 579 else if t 3 = 1 then 552 else 553) else (if t 3 = 0 then 1546 else if t 3 = 1 then 1537 else 1835)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 581 else if t 3 = 1 then 566 else 1108) else if t 2 = 1 then (if t 3 = 0 then 577 else if t 3 = 1 then 532 else 535) else (if t 3 = 0 then 589 else if t 3 = 1 then 534 else 536)) else (if t 2 = 0 then (if t 3 = 0 then 2760 else if t 3 = 1 then 2756 else 2983) else if t 2 = 1 then (if t 3 = 0 then 2759 else if t 3 = 1 then 2747 else 2749) else (if t 3 = 0 then 3927 else if t 3 = 1 then 3923 else 4044))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 570 else 1110) else if t 2 = 1 then (if t 3 = 0 then 578 else if t 3 = 1 then 544 else 546) else (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1833)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 580 else if t 3 = 1 then 556 else 1104) else if t 2 = 1 then (if t 3 = 0 then 576 else if t 3 = 1 then 515 else 520) else (if t 3 = 0 then 588 else if t 3 = 1 then 517 else 522)) else (if t 2 = 0 then (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 1105) else if t 2 = 1 then (if t 3 = 0 then 584 else if t 3 = 1 then 516 else 521) else (if t 3 = 0 then 592 else if t 3 = 1 then 518 else 523))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 572 else 3966) else if t 2 = 1 then (if t 3 = 0 then 1115 else if t 3 = 1 then 548 else 550) else (if t 3 = 0 then 2986 else if t 3 = 1 then 1535 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1836 else if t 3 = 1 then 562 else 1542) else if t 2 = 1 then (if t 3 = 0 then 1113 else if t 3 = 1 then 524 else 528) else (if t 3 = 0 then 1119 else if t 3 = 1 then 526 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 1838 else if t 3 = 1 then 563 else 1543) else if t 2 = 1 then (if t 3 = 0 then 1117 else if t 3 = 1 then 525 else 529) else (if t 3 = 0 then 1121 else if t 3 = 1 then 527 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4809 else (if jt.2.val < 2 then 4825 else 4814)) else (if jt.2.val < 4 then 4824 else (if jt.2.val < 5 then 4826 else 4811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2522 else (if jt.2.val < 2 then 2753 else 2543)) else (if jt.2.val < 4 then 2752 else (if jt.2.val < 5 then 2754 else 2513)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1392 else (if jt.2.val < 2 then 1540 else 1421)) else (if jt.2.val < 4 then 1539 else (if jt.2.val < 5 then 1541 else 1383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1060 else (if jt.2.val < 2 then 1100 else 1062)) else (if jt.2.val < 4 then 1098 else (if jt.2.val < 5 then 1099 else 1016)))))

checked_coverage fastCoverage0631 pairing0631 template0631 witness0631

theorem coverage0631 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0631) (maskBits m))
    cores template0631 witness0631 := by
  rw [← coresFast_eq]
  exact fastCoverage0631

theorem coverageSize0631 : ∀ q : Pattern,
    (cores (witness0631 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0631 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0631
#print axioms coverageSize0631

noncomputable def pairing0632 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0632 : List (Fin 4935) := templateData0632

noncomputable def witness0632 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 3951) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2778) else (if t 3 = 0 then 2997 else if t 3 = 1 then 2996 else 2781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 681) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 680) else (if t 3 = 0 then 1174 else if t 3 = 1 then 1172 else 694)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2197 else 1475) else if t 2 = 1 then (if t 3 = 0 then 2200 else if t 3 = 1 then 2196 else 688) else (if t 3 = 0 then 1190 else if t 3 = 1 then 1189 else 698))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 189) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 188) else (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 202)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2570) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4179) else (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4181)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2574) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4180) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4164 else 4182))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 35 else 902) else if t 2 = 1 then (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 901) else (if t 3 = 0 then 1472 else if t 3 = 1 then 70 else 2128)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2885) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4183) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4177 else 4185)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2475 else 2887) else if t 2 = 1 then (if t 3 = 0 then 3838 else if t 3 = 1 then 4171 else 4184) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4178 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4827 else (if jt.2.val < 2 then 4831 else 4832)) else (if jt.2.val < 4 then 4828 else (if jt.2.val < 5 then 4830 else 4829))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4693 else (if jt.2.val < 2 then 4697 else 4698)) else (if jt.2.val < 4 then 4694 else (if jt.2.val < 5 then 4696 else 4695)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4261 else (if jt.2.val < 2 then 4265 else 4266)) else (if jt.2.val < 4 then 4262 else (if jt.2.val < 5 then 4264 else 4263))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4131 else (if jt.2.val < 2 then 4173 else 4176)) else (if jt.2.val < 4 then 4172 else (if jt.2.val < 5 then 4175 else 4174)))))

checked_coverage fastCoverage0632 pairing0632 template0632 witness0632

theorem coverage0632 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0632) (maskBits m))
    cores template0632 witness0632 := by
  rw [← coresFast_eq]
  exact fastCoverage0632

theorem coverageSize0632 : ∀ q : Pattern,
    (cores (witness0632 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0632 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0632
#print axioms coverageSize0632

noncomputable def pairing0633 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0633 : List (Fin 4935) := templateData0633

noncomputable def witness0633 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4190) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2775) else (if t 3 = 0 then 2741 else if t 3 = 1 then 2737 else 2987)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 667) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 654) else (if t 3 = 0 then 490 else if t 3 = 1 then 462 else 1132)) else (if t 2 = 0 then (if t 3 = 0 then 1613 else if t 3 = 1 then 1597 else 2170) else if t 2 = 1 then (if t 3 = 0 then 1612 else if t 3 = 1 then 1593 else 656) else (if t 3 = 0 then 497 else if t 3 = 1 then 464 else 1134))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 175) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 161) else (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 889)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2549) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3877) else (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3882)) else (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2551) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3878) else (if t 3 = 0 then 3918 else if t 3 = 1 then 3881 else 3883))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 994 else 177) else if t 2 = 1 then (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 167) else (if t 3 = 0 then 2141 else if t 3 = 1 then 368 else 1495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2555) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3886) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3888 else 3890)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2950 else 2557) else if t 2 = 1 then (if t 3 = 0 then 4038 else if t 3 = 1 then 3885 else 3887) else (if t 3 = 0 then 4192 else if t 3 = 1 then 3889 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4815 else (if jt.2.val < 2 then 4817 else 4820)) else (if jt.2.val < 4 then 4816 else (if jt.2.val < 5 then 4819 else 4818))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4410 else (if jt.2.val < 2 then 4412 else 4418)) else (if jt.2.val < 4 then 4411 else (if jt.2.val < 5 then 4417 else 4413)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3864 else (if jt.2.val < 2 then 3866 else 3901)) else (if jt.2.val < 4 then 3865 else (if jt.2.val < 5 then 3900 else 3879))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4174 else (if jt.2.val < 2 then 4189 else 4176)) else (if jt.2.val < 4 then 4187 else (if jt.2.val < 5 then 4188 else 4131)))))

checked_coverage fastCoverage0633 pairing0633 template0633 witness0633

theorem coverage0633 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0633) (maskBits m))
    cores template0633 witness0633 := by
  rw [← coresFast_eq]
  exact fastCoverage0633

theorem coverageSize0633 : ∀ q : Pattern,
    (cores (witness0633 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0633 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0633
#print axioms coverageSize0633

noncomputable def pairing0634 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0634 : List (Fin 4935) := templateData0634

noncomputable def witness0634 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2817 else 2577) else if t 2 = 1 then (if t 3 = 0 then 2813 else if t 3 = 1 then 2809 else 2860) else (if t 3 = 0 then 4203 else if t 3 = 1 then 4054 else 3967)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2815 else 1372) else if t 2 = 1 then (if t 3 = 0 then 2811 else if t 3 = 1 then 2807 else 1370) else (if t 3 = 0 then 1171 else if t 3 = 1 then 1169 else 1211)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 964 else 305) else if t 2 = 1 then (if t 3 = 0 then 962 else if t 3 = 1 then 960 else 1001) else (if t 3 = 0 then 2138 else if t 3 = 1 then 1801 else 1376))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2816 else 1687) else if t 2 = 1 then (if t 3 = 0 then 2812 else if t 3 = 1 then 2808 else 1685) else (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 866)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2814 else 2576) else if t 2 = 1 then (if t 3 = 0 then 2810 else if t 3 = 1 then 2806 else 2859) else (if t 3 = 0 then 2828 else if t 3 = 1 then 2826 else 2861)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2838 else 2579) else if t 2 = 1 then (if t 3 = 0 then 2837 else if t 3 = 1 then 2835 else 2862) else (if t 3 = 0 then 2841 else if t 3 = 1 then 2840 else 2863))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1586 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1584 else 1852) else (if t 3 = 0 then 275 else if t 3 = 1 then 857 else 877)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2484 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2632 else if t 3 = 1 then 2854 else 2864) else (if t 3 = 0 then 2635 else if t 3 = 1 then 2856 else 2865)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2489 else 4197) else if t 2 = 1 then (if t 3 = 0 then 2637 else if t 3 = 1 then 2857 else 2866) else (if t 3 = 0 then 2639 else if t 3 = 1 then 2858 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4767 else (if jt.2.val < 2 then 4771 else 4772)) else (if jt.2.val < 4 then 4768 else (if jt.2.val < 5 then 4770 else 4769))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2804 else (if jt.2.val < 2 then 2834 else 2836)) else (if jt.2.val < 4 then 2831 else (if jt.2.val < 5 then 2833 else 2832)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4263 else (if jt.2.val < 2 then 4274 else 4266)) else (if jt.2.val < 4 then 4272 else (if jt.2.val < 5 then 4273 else 4261))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3006 else (if jt.2.val < 2 then 3012 else 3015)) else (if jt.2.val < 4 then 3011 else (if jt.2.val < 5 then 3014 else 3013)))))

checked_coverage fastCoverage0634 pairing0634 template0634 witness0634

theorem coverage0634 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0634) (maskBits m))
    cores template0634 witness0634 := by
  rw [← coresFast_eq]
  exact fastCoverage0634

theorem coverageSize0634 : ∀ q : Pattern,
    (cores (witness0634 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0634 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0634
#print axioms coverageSize0634

noncomputable def pairing0635 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0635 : List (Fin 4935) := templateData0635

noncomputable def witness0635 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2705 else 2882) else if t 2 = 1 then (if t 3 = 0 then 2710 else if t 3 = 1 then 2688 else 2689) else (if t 3 = 0 then 3935 else if t 3 = 1 then 3929 else 4205)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2703 else 1357) else if t 2 = 1 then (if t 3 = 0 then 2708 else if t 3 = 1 then 2682 else 1339) else (if t 3 = 0 then 489 else if t 3 = 1 then 445 else 448)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 73 else 922) else if t 2 = 1 then (if t 3 = 0 then 87 else if t 3 = 1 then 43 else 46) else (if t 3 = 0 then 1523 else if t 3 = 1 then 1507 else 2125))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2704 else 1672) else if t 2 = 1 then (if t 3 = 0 then 2709 else if t 3 = 1 then 2685 else 1657) else (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 351)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2695 else 2878) else if t 2 = 1 then (if t 3 = 0 then 2707 else if t 3 = 1 then 2664 else 2670) else (if t 3 = 0 then 2715 else if t 3 = 1 then 2666 else 2671)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2697 else 2880) else if t 2 = 1 then (if t 3 = 0 then 2717 else if t 3 = 1 then 2668 else 2672) else (if t 3 = 0 then 2719 else if t 3 = 1 then 2669 else 2673))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2218 else 1674) else if t 2 = 1 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2212 else 1659) else (if t 3 = 0 then 931 else if t 3 = 1 then 353 else 355)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2699 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2902 else if t 3 = 1 then 2674 else 2678) else (if t 3 = 0 then 2903 else if t 3 = 1 then 2675 else 2679)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2701 else 3934) else if t 2 = 1 then (if t 3 = 0 then 2904 else if t 3 = 1 then 2676 else 2680) else (if t 3 = 0 then 2905 else if t 3 = 1 then 2677 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4797 else (if jt.2.val < 2 then 4799 else 4802)) else (if jt.2.val < 4 then 4798 else (if jt.2.val < 5 then 4801 else 4800))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2658 else (if jt.2.val < 2 then 2660 else 2687)) else (if jt.2.val < 4 then 2659 else (if jt.2.val < 5 then 2686 else 2667)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3879 else (if jt.2.val < 2 then 3932 else 3901)) else (if jt.2.val < 4 then 3931 else (if jt.2.val < 5 then 3933 else 3864))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3013 else (if jt.2.val < 2 then 3033 else 3015)) else (if jt.2.val < 4 then 3027 else (if jt.2.val < 5 then 3028 else 3006)))))

checked_coverage fastCoverage0635 pairing0635 template0635 witness0635

theorem coverage0635 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0635) (maskBits m))
    cores template0635 witness0635 := by
  rw [← coresFast_eq]
  exact fastCoverage0635

theorem coverageSize0635 : ∀ q : Pattern,
    (cores (witness0635 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0635 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0635
#print axioms coverageSize0635

noncomputable def pairing0636 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0636 : List (Fin 4935) := templateData0636

noncomputable def witness0636 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1546) else if t 2 = 1 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 193) else (if t 3 = 0 then 837 else if t 3 = 1 then 835 else 205)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 589) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2101) else (if t 3 = 0 then 1733 else if t 3 = 1 then 2082 else 2104)) else (if t 2 = 0 then (if t 3 = 0 then 4213 else if t 3 = 1 then 4211 else 3927) else if t 2 = 1 then (if t 3 = 0 then 3531 else if t 3 = 1 then 3528 else 2648) else (if t 3 = 0 then 2940 else if t 3 = 1 then 2939 else 2654))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1545) else if t 2 = 1 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 192) else (if t 3 = 0 then 836 else if t 3 = 1 then 834 else 204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 588) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2100) else (if t 3 = 0 then 1732 else if t 3 = 1 then 2081 else 2103)) else (if t 2 = 0 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 592) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2102) else (if t 3 = 0 then 1735 else if t 3 = 1 then 2083 else 2105))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 1509 else 2986) else if t 2 = 1 then (if t 3 = 0 then 49 else if t 3 = 1 then 47 else 903) else (if t 3 = 0 then 3942 else if t 3 = 1 then 74 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 451 else if t 3 = 1 then 449 else 1119) else if t 2 = 1 then (if t 3 = 0 then 1341 else if t 3 = 1 then 2089 else 2106) else (if t 3 = 0 then 1358 else if t 3 = 1 then 2097 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 456 else if t 3 = 1 then 455 else 1121) else if t 2 = 1 then (if t 3 = 0 then 1344 else if t 3 = 1 then 2091 else 2108) else (if t 3 = 0 then 1361 else if t 3 = 1 then 2099 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4797 else (if jt.2.val < 2 then 4805 else 4802)) else (if jt.2.val < 4 then 4803 else (if jt.2.val < 5 then 4804 else 4800))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4695 else (if jt.2.val < 2 then 4706 else 4698)) else (if jt.2.val < 4 then 4704 else (if jt.2.val < 5 then 4705 else 4693)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2045 else (if jt.2.val < 2 then 2079 else 2080)) else (if jt.2.val < 4 then 2076 else (if jt.2.val < 5 then 2078 else 2077))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2043 else (if jt.2.val < 2 then 2093 else 2096)) else (if jt.2.val < 4 then 2092 else (if jt.2.val < 5 then 2095 else 2094)))))

checked_coverage fastCoverage0636 pairing0636 template0636 witness0636

theorem coverage0636 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0636) (maskBits m))
    cores template0636 witness0636 := by
  rw [← coresFast_eq]
  exact fastCoverage0636

theorem coverageSize0636 : ∀ q : Pattern,
    (cores (witness0636 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0636 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0636
#print axioms coverageSize0636

noncomputable def pairing0637 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0637 : List (Fin 4935) := templateData0637

noncomputable def witness0637 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 2117) else if t 2 = 1 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 171) else (if t 3 = 0 then 396 else if t 3 = 1 then 372 else 893)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 567) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1411) else (if t 3 = 0 then 1450 else if t 3 = 1 then 1412 else 1413)) else (if t 2 = 0 then (if t 3 = 0 then 3959 else if t 3 = 1 then 3953 else 4207) else if t 2 = 1 then (if t 3 = 0 then 3227 else if t 3 = 1 then 3219 else 2630) else (if t 3 = 0 then 2501 else if t 3 = 1 then 2482 else 2898))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 2115) else if t 2 = 1 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 162) else (if t 3 = 0 then 395 else if t 3 = 1 then 365 else 890)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 558) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1393) else (if t 3 = 0 then 1449 else if t 3 = 1 then 1396 else 1398)) else (if t 2 = 0 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 559) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1394) else (if t 3 = 0 then 1451 else if t 3 = 1 then 1397 else 1399))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1430 else 2758) else if t 2 = 1 then (if t 3 = 0 then 1011 else if t 3 = 1 then 989 else 168) else (if t 3 = 0 then 4206 else if t 3 = 1 then 369 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1199 else 564) else if t 2 = 1 then (if t 3 = 0 then 1776 else if t 3 = 1 then 1400 else 1402) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1404 else 1406)) else (if t 2 = 0 then (if t 3 = 0 then 1223 else if t 3 = 1 then 1200 else 565) else if t 2 = 1 then (if t 3 = 0 then 1778 else if t 3 = 1 then 1401 else 1403) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1405 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4767 else (if jt.2.val < 2 then 4783 else 4772)) else (if jt.2.val < 4 then 4782 else (if jt.2.val < 5 then 4784 else 4769))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4413 else (if jt.2.val < 2 then 4423 else 4418)) else (if jt.2.val < 4 then 4422 else (if jt.2.val < 5 then 4424 else 4410)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1983 else (if jt.2.val < 2 then 1985 else 1992)) else (if jt.2.val < 4 then 1984 else (if jt.2.val < 5 then 1991 else 1990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2094 else (if jt.2.val < 2 then 2114 else 2096)) else (if jt.2.val < 4 then 2112 else (if jt.2.val < 5 then 2113 else 2043)))))

checked_coverage fastCoverage0637 pairing0637 template0637 witness0637

theorem coverage0637 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0637) (maskBits m))
    cores template0637 witness0637 := by
  rw [← coresFast_eq]
  exact fastCoverage0637

theorem coverageSize0637 : ∀ q : Pattern,
    (cores (witness0637 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0637 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0637
#print axioms coverageSize0637

noncomputable def pairing0638 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0638 : List (Fin 4935) := templateData0638

noncomputable def witness0638 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1029 else 597) else if t 2 = 1 then (if t 3 = 0 then 1025 else if t 3 = 1 then 1021 else 1080) else (if t 3 = 0 then 2146 else if t 3 = 1 then 1813 else 1690)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1027 else 595) else if t 2 = 1 then (if t 3 = 0 then 1023 else if t 3 = 1 then 1019 else 1078) else (if t 3 = 0 then 1049 else if t 3 = 1 then 1046 else 1084)) else (if t 2 = 0 then (if t 3 = 0 then 2974 else if t 3 = 1 then 2973 else 2762) else if t 2 = 1 then (if t 3 = 0 then 2972 else if t 3 = 1 then 2970 else 2980) else (if t 3 = 0 then 4198 else if t 3 = 1 then 4046 else 3860))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1028 else 596) else if t 2 = 1 then (if t 3 = 0 then 1024 else if t 3 = 1 then 1020 else 1079) else (if t 3 = 0 then 2145 else if t 3 = 1 then 1812 else 1689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1026 else 594) else if t 2 = 1 then (if t 3 = 0 then 1022 else if t 3 = 1 then 1018 else 1077) else (if t 3 = 0 then 1048 else if t 3 = 1 then 1045 else 1083)) else (if t 2 = 0 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1041 else 598) else if t 2 = 1 then (if t 3 = 0 then 1039 else if t 3 = 1 then 1037 else 1081) else (if t 3 = 0 then 1055 else if t 3 = 1 then 1054 else 1085))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 468 else 4208) else if t 2 = 1 then (if t 3 = 0 then 660 else if t 3 = 1 then 1070 else 1092) else (if t 3 = 0 then 2777 else if t 3 = 1 then 1598 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1518 else if t 3 = 1 then 466 else 2148) else if t 2 = 1 then (if t 3 = 0 then 658 else if t 3 = 1 then 1068 else 1086) else (if t 3 = 0 then 668 else if t 3 = 1 then 1074 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 1520 else if t 3 = 1 then 472 else 2149) else if t 2 = 1 then (if t 3 = 0 then 664 else if t 3 = 1 then 1072 else 1087) else (if t 3 = 0 then 671 else if t 3 = 1 then 1076 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4815 else (if jt.2.val < 2 then 4823 else 4820)) else (if jt.2.val < 4 then 4821 else (if jt.2.val < 5 then 4822 else 4818))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2832 else (if jt.2.val < 2 then 2971 else 2836)) else (if jt.2.val < 4 then 2968 else (if jt.2.val < 5 then 2969 else 2804)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2077 else (if jt.2.val < 2 then 2144 else 2080)) else (if jt.2.val < 4 then 2142 else (if jt.2.val < 5 then 2143 else 2045))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1260 else (if jt.2.val < 2 then 1263 else 1269)) else (if jt.2.val < 4 then 1262 else (if jt.2.val < 5 then 1268 else 1267)))))

checked_coverage fastCoverage0638 pairing0638 template0638 witness0638

theorem coverage0638 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0638) (maskBits m))
    cores template0638 witness0638 := by
  rw [← coresFast_eq]
  exact fastCoverage0638

theorem coverageSize0638 : ∀ q : Pattern,
    (cores (witness0638 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0638 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0638
#print axioms coverageSize0638

noncomputable def pairing0639 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0639 : List (Fin 4935) := templateData0639

noncomputable def witness0639 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 763 else 1112) else if t 2 = 1 then (if t 3 = 0 then 768 else if t 3 = 1 then 740 else 741) else (if t 3 = 0 then 1498 else if t 3 = 1 then 1489 else 2159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 770 else if t 3 = 1 then 755 else 1108) else if t 2 = 1 then (if t 3 = 0 then 766 else if t 3 = 1 then 720 else 723) else (if t 3 = 0 then 778 else if t 3 = 1 then 722 else 724)) else (if t 2 = 0 then (if t 3 = 0 then 2798 else if t 3 = 1 then 2794 else 2983) else if t 2 = 1 then (if t 3 = 0 then 2797 else if t 3 = 1 then 2785 else 2787) else (if t 3 = 0 then 3943 else if t 3 = 1 then 3939 else 4196))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 759 else 1110) else if t 2 = 1 then (if t 3 = 0 then 767 else if t 3 = 1 then 732 else 734) else (if t 3 = 0 then 1497 else if t 3 = 1 then 1483 else 2157)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 769 else if t 3 = 1 then 747 else 1104) else if t 2 = 1 then (if t 3 = 0 then 765 else if t 3 = 1 then 704 else 708) else (if t 3 = 0 then 777 else if t 3 = 1 then 706 else 710)) else (if t 2 = 0 then (if t 3 = 0 then 775 else if t 3 = 1 then 748 else 1105) else if t 2 = 1 then (if t 3 = 0 then 773 else if t 3 = 1 then 705 else 709) else (if t 3 = 0 then 781 else if t 3 = 1 then 707 else 711))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 761 else 3966) else if t 2 = 1 then (if t 3 = 0 then 1146 else if t 3 = 1 then 736 else 738) else (if t 3 = 0 then 2990 else if t 3 = 1 then 1487 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2160 else if t 3 = 1 then 751 else 1542) else if t 2 = 1 then (if t 3 = 0 then 1140 else if t 3 = 1 then 712 else 716) else (if t 3 = 0 then 1142 else if t 3 = 1 then 714 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 2162 else if t 3 = 1 then 752 else 1543) else if t 2 = 1 then (if t 3 = 0 then 1141 else if t 3 = 1 then 713 else 717) else (if t 3 = 0 then 1143 else if t 3 = 1 then 715 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4827 else (if jt.2.val < 2 then 4834 else 4832)) else (if jt.2.val < 4 then 4833 else (if jt.2.val < 5 then 4835 else 4829))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2667 else (if jt.2.val < 2 then 2791 else 2687)) else (if jt.2.val < 4 then 2790 else (if jt.2.val < 5 then 2792 else 2658)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1990 else (if jt.2.val < 2 then 2029 else 1992)) else (if jt.2.val < 4 then 2028 else (if jt.2.val < 5 then 2030 else 1983))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1267 else (if jt.2.val < 2 then 1287 else 1269)) else (if jt.2.val < 4 then 1284 else (if jt.2.val < 5 then 1285 else 1260)))))

checked_coverage fastCoverage0639 pairing0639 template0639 witness0639

theorem coverage0639 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0639) (maskBits m))
    cores template0639 witness0639 := by
  rw [← coresFast_eq]
  exact fastCoverage0639

theorem coverageSize0639 : ∀ q : Pattern,
    (cores (witness0639 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0639 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0639
#print axioms coverageSize0639

end Crown.CertificateData
