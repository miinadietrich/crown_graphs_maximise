import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0005

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0200 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0200 : List (Fin 4935) := templateData0200

noncomputable def witness0200 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3215) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2759) else (if t 3 = 0 then 2974 else if t 3 = 1 then 2973 else 2762)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 291) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 290) else (if t 3 = 0 then 965 else if t 3 = 1 then 963 else 304)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 343 else 929) else if t 2 = 1 then (if t 3 = 0 then 344 else if t 3 = 1 then 342 else 928) else (if t 3 = 0 then 1496 else if t 3 = 1 then 373 else 2140))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 585) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 584) else (if t 3 = 0 then 1043 else if t 3 = 1 then 1041 else 598)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2572) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3488) else (if t 3 = 0 then 3278 else if t 3 = 1 then 3472 else 3490)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2471 else 2886) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3479 else 3492) else (if t 3 = 0 then 3095 else if t 3 = 1 then 3486 else 3494))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1547) else if t 2 = 1 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 592) else (if t 3 = 0 then 1057 else if t 3 = 1 then 1056 else 602)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2574) else if t 2 = 1 then (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3489) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3473 else 3491)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2475 else 2887) else if t 2 = 1 then (if t 3 = 0 then 3084 else if t 3 = 1 then 3480 else 3493) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3487 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3441 else (if jt.2.val < 2 then 3461 else 3463)) else (if jt.2.val < 4 then 3458 else (if jt.2.val < 5 then 3460 else 3459))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3600 else (if jt.2.val < 2 then 3610 else 3611)) else (if jt.2.val < 4 then 3607 else (if jt.2.val < 5 then 3609 else 3608)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3601 else (if jt.2.val < 2 then 3605 else 3606)) else (if jt.2.val < 4 then 3602 else (if jt.2.val < 5 then 3604 else 3603))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3438 else (if jt.2.val < 2 then 3482 else 3485)) else (if jt.2.val < 4 then 3481 else (if jt.2.val < 5 then 3484 else 3483)))))

checked_coverage fastCoverage0200 pairing0200 template0200 witness0200

theorem coverage0200 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0200) (maskBits m))
    cores template0200 witness0200 := by
  rw [← coresFast_eq]
  exact fastCoverage0200

theorem coverageSize0200 : ∀ q : Pattern,
    (cores (witness0200 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0200 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0200
#print axioms coverageSize0200

noncomputable def pairing0201 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0201 : List (Fin 4935) := templateData0201

noncomputable def witness0201 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3499) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 2756) else (if t 3 = 0 then 2798 else if t 3 = 1 then 2794 else 2983)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 277) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 264) else (if t 3 = 0 then 88 else if t 3 = 1 then 60 else 916)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 859 else 279) else if t 2 = 1 then (if t 3 = 0 then 874 else if t 3 = 1 then 853 else 269) else (if t 3 = 0 then 2129 else if t 3 = 1 then 65 else 1471))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 571) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 557) else (if t 3 = 0 then 775 else if t 3 = 1 then 748 else 1105)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2550) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3123) else (if t 3 = 0 then 3165 else if t 3 = 1 then 3126 else 3128)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2949 else 2556) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3130 else 3132) else (if t 3 = 0 then 3500 else if t 3 = 1 then 3134 else 3136))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 2116) else if t 2 = 1 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 559) else (if t 3 = 0 then 782 else if t 3 = 1 then 750 else 1107)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2551) else if t 2 = 1 then (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3124) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3127 else 3129)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2950 else 2557) else if t 2 = 1 then (if t 3 = 0 then 3314 else if t 3 = 1 then 3131 else 3133) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3135 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3116 else (if jt.2.val < 2 then 3118 else 3140)) else (if jt.2.val < 4 then 3117 else (if jt.2.val < 5 then 3139 else 3120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3567 else (if jt.2.val < 2 then 3569 else 3572)) else (if jt.2.val < 4 then 3568 else (if jt.2.val < 5 then 3571 else 3570)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3110 else (if jt.2.val < 2 then 3112 else 3148)) else (if jt.2.val < 4 then 3111 else (if jt.2.val < 5 then 3147 else 3125))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3483 else (if jt.2.val < 2 then 3498 else 3485)) else (if jt.2.val < 4 then 3496 else (if jt.2.val < 5 then 3497 else 3438)))))

checked_coverage fastCoverage0201 pairing0201 template0201 witness0201

theorem coverage0201 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0201) (maskBits m))
    cores template0201 witness0201 := by
  rw [← coresFast_eq]
  exact fastCoverage0201

theorem coverageSize0201 : ∀ q : Pattern,
    (cores (witness0201 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0201 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0201
#print axioms coverageSize0201

noncomputable def pairing0202 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0202 : List (Fin 4935) := templateData0202

noncomputable def witness0202 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2817 else 2577) else if t 2 = 1 then (if t 3 = 0 then 2813 else if t 3 = 1 then 2809 else 2860) else (if t 3 = 0 then 3520 else if t 3 = 1 then 3338 else 3242)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2815 else 1372) else if t 2 = 1 then (if t 3 = 0 then 2811 else if t 3 = 1 then 2807 else 1370) else (if t 3 = 0 then 962 else if t 3 = 1 then 960 else 1001)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1416 else 2119) else if t 2 = 1 then (if t 3 = 0 then 1415 else if t 3 = 1 then 1414 else 1777) else (if t 3 = 0 then 173 else if t 3 = 1 then 992 else 1012))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2816 else 1687) else if t 2 = 1 then (if t 3 = 0 then 2812 else if t 3 = 1 then 2808 else 1685) else (if t 3 = 0 then 1040 else if t 3 = 1 then 1038 else 1082)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2814 else 2576) else if t 2 = 1 then (if t 3 = 0 then 2810 else if t 3 = 1 then 2806 else 2859) else (if t 3 = 0 then 2837 else if t 3 = 1 then 2835 else 2862)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2484 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2632 else if t 3 = 1 then 2854 else 2864) else (if t 3 = 0 then 2637 else if t 3 = 1 then 2857 else 2866))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 822 else 203) else if t 2 = 1 then (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 866) else (if t 3 = 0 then 2147 else if t 3 = 1 then 1817 else 1691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2578) else if t 2 = 1 then (if t 3 = 0 then 2828 else if t 3 = 1 then 2826 else 2861) else (if t 3 = 0 then 2841 else if t 3 = 1 then 2840 else 2863)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2487 else 3507) else if t 2 = 1 then (if t 3 = 0 then 2635 else if t 3 = 1 then 2856 else 2865) else (if t 3 = 0 then 2639 else if t 3 = 1 then 2858 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2805 else (if jt.2.val < 2 then 2825 else 2827)) else (if jt.2.val < 4 then 2822 else (if jt.2.val < 5 then 2824 else 2823))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3575 else (if jt.2.val < 2 then 3580 else 3581)) else (if jt.2.val < 4 then 3577 else (if jt.2.val < 5 then 3579 else 3578)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3603 else (if jt.2.val < 2 then 3614 else 3606)) else (if jt.2.val < 4 then 3612 else (if jt.2.val < 5 then 3613 else 3601))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3006 else (if jt.2.val < 2 then 3012 else 3015)) else (if jt.2.val < 4 then 3011 else (if jt.2.val < 5 then 3014 else 3013)))))

checked_coverage fastCoverage0202 pairing0202 template0202 witness0202

theorem coverage0202 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0202) (maskBits m))
    cores template0202 witness0202 := by
  rw [← coresFast_eq]
  exact fastCoverage0202

theorem coverageSize0202 : ∀ q : Pattern,
    (cores (witness0202 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0202 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0202
#print axioms coverageSize0202

noncomputable def pairing0203 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0203 : List (Fin 4935) := templateData0203

noncomputable def witness0203 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2705 else 2882) else if t 2 = 1 then (if t 3 = 0 then 2710 else if t 3 = 1 then 2688 else 2689) else (if t 3 = 0 then 3198 else if t 3 = 1 then 3191 else 3522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2703 else 1357) else if t 2 = 1 then (if t 3 = 0 then 2708 else if t 3 = 1 then 2682 else 1339) else (if t 3 = 0 then 87 else if t 3 = 1 then 43 else 46)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2098 else 1359) else if t 2 = 1 then (if t 3 = 0 then 2107 else if t 3 = 1 then 2090 else 1342) else (if t 3 = 0 then 904 else if t 3 = 1 then 48 else 50))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2704 else 1672) else if t 2 = 1 then (if t 3 = 0 then 2709 else if t 3 = 1 then 2685 else 1657) else (if t 3 = 0 then 774 else if t 3 = 1 then 733 else 735)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2695 else 2878) else if t 2 = 1 then (if t 3 = 0 then 2707 else if t 3 = 1 then 2664 else 2670) else (if t 3 = 0 then 2717 else if t 3 = 1 then 2668 else 2672)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2699 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2902 else if t 3 = 1 then 2674 else 2678) else (if t 3 = 0 then 2904 else if t 3 = 1 then 2676 else 2680))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 376 else 895) else if t 2 = 1 then (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 351) else (if t 3 = 0 then 1499 else if t 3 = 1 then 1484 else 2158)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2879) else if t 2 = 1 then (if t 3 = 0 then 2715 else if t 3 = 1 then 2666 else 2671) else (if t 3 = 0 then 2719 else if t 3 = 1 then 2669 else 2673)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2700 else 3197) else if t 2 = 1 then (if t 3 = 0 then 2903 else if t 3 = 1 then 2675 else 2679) else (if t 3 = 0 then 2905 else if t 3 = 1 then 2677 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2661 else (if jt.2.val < 2 then 2663 else 2684)) else (if jt.2.val < 4 then 2662 else (if jt.2.val < 5 then 2683 else 2665))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3615 else (if jt.2.val < 2 then 3617 else 3620)) else (if jt.2.val < 4 then 3616 else (if jt.2.val < 5 then 3619 else 3618)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3125 else (if jt.2.val < 2 then 3194 else 3148)) else (if jt.2.val < 4 then 3193 else (if jt.2.val < 5 then 3195 else 3110))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3013 else (if jt.2.val < 2 then 3033 else 3015)) else (if jt.2.val < 4 then 3027 else (if jt.2.val < 5 then 3028 else 3006)))))

checked_coverage fastCoverage0203 pairing0203 template0203 witness0203

theorem coverage0203 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0203) (maskBits m))
    cores template0203 witness0203 := by
  rw [← coresFast_eq]
  exact fastCoverage0203

theorem coverageSize0203 : ∀ q : Pattern,
    (cores (witness0203 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0203 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0203
#print axioms coverageSize0203

noncomputable def pairing0204 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0204 : List (Fin 4935) := templateData0204

noncomputable def witness0204 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 428 else 1116) else if t 2 = 1 then (if t 3 = 0 then 430 else if t 3 = 1 then 426 else 1114) else (if t 3 = 0 then 1519 else if t 3 = 1 then 467 else 2150)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 424 else if t 3 = 1 then 420 else 496) else if t 2 = 1 then (if t 3 = 0 then 422 else if t 3 = 1 then 418 else 488) else (if t 3 = 0 then 1132 else if t 3 = 1 then 462 else 490)) else (if t 2 = 0 then (if t 3 = 0 then 3505 else if t 3 = 1 then 3203 else 3207) else if t 2 = 1 then (if t 3 = 0 then 2730 else if t 3 = 1 then 2728 else 2740) else (if t 3 = 0 then 2987 else if t 3 = 1 then 2737 else 2741))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 427 else 1115) else if t 2 = 1 then (if t 3 = 0 then 429 else if t 3 = 1 then 425 else 1113) else (if t 3 = 0 then 1518 else if t 3 = 1 then 466 else 2148)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 423 else if t 3 = 1 then 419 else 492) else if t 2 = 1 then (if t 3 = 0 then 421 else if t 3 = 1 then 417 else 480) else (if t 3 = 0 then 1131 else if t 3 = 1 then 461 else 484)) else (if t 2 = 0 then (if t 3 = 0 then 439 else if t 3 = 1 then 437 else 493) else if t 2 = 1 then (if t 3 = 0 then 438 else if t 3 = 1 then 436 else 481) else (if t 3 = 0 then 1135 else if t 3 = 1 then 470 else 485))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 1509 else 2986) else if t 2 = 1 then (if t 3 = 0 then 451 else if t 3 = 1 then 449 else 1119) else (if t 3 = 0 then 3206 else if t 3 = 1 then 476 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2124 else if t 3 = 1 then 1506 else 1521) else if t 2 = 1 then (if t 3 = 0 then 447 else if t 3 = 1 then 444 else 482) else (if t 3 = 0 then 1137 else if t 3 = 1 then 474 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 2126 else if t 3 = 1 then 1511 else 1522) else if t 2 = 1 then (if t 3 = 0 then 454 else if t 3 = 1 then 453 else 483) else (if t 3 = 0 then 1139 else if t 3 = 1 then 478 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2661 else (if jt.2.val < 2 then 2735 else 2684)) else (if jt.2.val < 4 then 2733 else (if jt.2.val < 5 then 2734 else 2665))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3608 else (if jt.2.val < 2 then 3623 else 3611)) else (if jt.2.val < 4 then 3621 else (if jt.2.val < 5 then 3622 else 3600)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1505 else (if jt.2.val < 2 then 1516 else 1517)) else (if jt.2.val < 4 then 1513 else (if jt.2.val < 5 then 1515 else 1514))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1272 else (if jt.2.val < 2 then 1274 else 1279)) else (if jt.2.val < 4 then 1273 else (if jt.2.val < 5 then 1278 else 1277)))))

checked_coverage fastCoverage0204 pairing0204 template0204 witness0204

theorem coverage0204 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0204) (maskBits m))
    cores template0204 witness0204 := by
  rw [← coresFast_eq]
  exact fastCoverage0204

theorem coverageSize0204 : ∀ q : Pattern,
    (cores (witness0204 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0204 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0204
#print axioms coverageSize0204

noncomputable def pairing0205 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0205 : List (Fin 4935) := templateData0205

noncomputable def witness0205 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1205 else 575) else if t 2 = 1 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1201 else 568) else (if t 3 = 0 then 2161 else if t 3 = 1 then 757 else 1544)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1214 else if t 3 = 1 then 1187 else 1188) else if t 2 = 1 then (if t 3 = 0 then 1210 else if t 3 = 1 then 1167 else 1170) else (if t 3 = 0 then 694 else if t 3 = 1 then 1172 else 1174)) else (if t 2 = 0 then (if t 3 = 0 then 3106 else if t 3 = 1 then 3329 else 3514) else if t 2 = 1 then (if t 3 = 0 then 3003 else if t 3 = 1 then 2993 else 2995) else (if t 3 = 0 then 2781 else if t 3 = 1 then 2996 else 2997))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1203 else 572) else if t 2 = 1 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1197 else 562) else (if t 3 = 0 then 2160 else if t 3 = 1 then 751 else 1542)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1212 else if t 3 = 1 then 1179 else 1181) else if t 2 = 1 then (if t 3 = 0 then 1206 else if t 3 = 1 then 1151 else 1155) else (if t 3 = 0 then 690 else if t 3 = 1 then 1159 else 1163)) else (if t 2 = 0 then (if t 3 = 0 then 1213 else if t 3 = 1 then 1180 else 1182) else if t 2 = 1 then (if t 3 = 0 then 1207 else if t 3 = 1 then 1152 else 1156) else (if t 3 = 0 then 691 else if t 3 = 1 then 1160 else 1164))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1430 else 2758) else if t 2 = 1 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1199 else 564) else (if t 3 = 0 then 3523 else if t 3 = 1 then 753 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1374 else if t 3 = 1 then 1795 else 2136) else if t 2 = 1 then (if t 3 = 0 then 1208 else if t 3 = 1 then 1153 else 1157) else (if t 3 = 0 then 692 else if t 3 = 1 then 1161 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 1375 else if t 3 = 1 then 1796 else 2137) else if t 2 = 1 then (if t 3 = 0 then 1209 else if t 3 = 1 then 1154 else 1158) else (if t 3 = 0 then 693 else if t 3 = 1 then 1162 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2805 else (if jt.2.val < 2 then 2992 else 2827)) else (if jt.2.val < 4 then 2991 else (if jt.2.val < 5 then 2994 else 2823))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3570 else (if jt.2.val < 2 then 3592 else 3572)) else (if jt.2.val < 4 then 3591 else (if jt.2.val < 5 then 3593 else 3567)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2346 else (if jt.2.val < 2 then 2348 else 2351)) else (if jt.2.val < 4 then 2347 else (if jt.2.val < 5 then 2350 else 2349))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1277 else (if jt.2.val < 2 then 1294 else 1279)) else (if jt.2.val < 4 then 1292 else (if jt.2.val < 5 then 1293 else 1272)))))

checked_coverage fastCoverage0205 pairing0205 template0205 witness0205

theorem coverage0205 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0205) (maskBits m))
    cores template0205 witness0205 := by
  rw [← coresFast_eq]
  exact fastCoverage0205

theorem coverageSize0205 : ∀ q : Pattern,
    (cores (witness0205 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0205 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0205
#print axioms coverageSize0205

noncomputable def pairing0206 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0206 : List (Fin 4935) := templateData0206

noncomputable def witness0206 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1574 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1570 else 1853) else (if t 3 = 0 then 661 else if t 3 = 1 then 1071 else 1094)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1566 else 1619) else if t 2 = 1 then (if t 3 = 0 then 1564 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 656 else if t 3 = 1 then 1593 else 1612)) else (if t 2 = 0 then (if t 3 = 0 then 2898 else if t 3 = 1 then 2482 else 2501) else if t 2 = 1 then (if t 3 = 0 then 2630 else if t 3 = 1 then 3219 else 3227) else (if t 3 = 0 then 3524 else if t 3 = 1 then 3225 else 3228))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1573 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1569 else 1851) else (if t 3 = 0 then 660 else if t 3 = 1 then 1070 else 1092)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1565 else 1617) else if t 2 = 1 then (if t 3 = 0 then 1563 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 655 else if t 3 = 1 then 1592 else 1606)) else (if t 2 = 0 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1582 else 1618) else if t 2 = 1 then (if t 3 = 0 then 1581 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 663 else if t 3 = 1 then 1595 else 1607))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 66 else 3525) else if t 2 = 1 then (if t 3 = 0 then 270 else if t 3 = 1 then 854 else 876) else (if t 3 = 0 then 2777 else if t 3 = 1 then 1598 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 917 else if t 3 = 1 then 61 else 92) else if t 2 = 1 then (if t 3 = 0 then 265 else if t 3 = 1 then 1588 else 1604) else (if t 3 = 0 then 2169 else if t 3 = 1 then 1596 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 920 else if t 3 = 1 then 69 else 93) else if t 2 = 1 then (if t 3 = 0 then 273 else if t 3 = 1 then 1591 else 1605) else (if t 3 = 0 then 2171 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3116 else (if jt.2.val < 2 then 3223 else 3140)) else (if jt.2.val < 4 then 3221 else (if jt.2.val < 5 then 3222 else 3120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3578 else (if jt.2.val < 2 then 3596 else 3581)) else (if jt.2.val < 4 then 3594 else (if jt.2.val < 5 then 3595 else 3575)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1514 else (if jt.2.val < 2 then 1594 else 1517)) else (if jt.2.val < 4 then 1557 else (if jt.2.val < 5 then 1558 else 1505))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2163 else (if jt.2.val < 2 then 2165 else 2168)) else (if jt.2.val < 4 then 2164 else (if jt.2.val < 5 then 2167 else 2166)))))

checked_coverage fastCoverage0206 pairing0206 template0206 witness0206

theorem coverage0206 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0206) (maskBits m))
    cores template0206 witness0206 := by
  rw [← coresFast_eq]
  exact fastCoverage0206

theorem coverageSize0206 : ∀ q : Pattern,
    (cores (witness0206 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0206 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0206
#print axioms coverageSize0206

noncomputable def pairing0207 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0207 : List (Fin 4935) := templateData0207

noncomputable def witness0207 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2219 else 1676) else if t 2 = 1 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2213 else 1661) else (if t 3 = 0 then 1148 else if t 3 = 1 then 742 else 743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2207 else 1892) else if t 2 = 1 then (if t 3 = 0 then 2222 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 688 else if t 3 = 1 then 2196 else 2200)) else (if t 2 = 0 then (if t 3 = 0 then 2654 else if t 3 = 1 then 2939 else 2940) else if t 2 = 1 then (if t 3 = 0 then 2648 else if t 3 = 1 then 3528 else 3531) else (if t 3 = 0 then 3182 else if t 3 = 1 then 3530 else 3532))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2217 else 1673) else if t 2 = 1 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2211 else 1658) else (if t 3 = 0 then 1146 else if t 3 = 1 then 736 else 738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2205 else 1889) else if t 2 = 1 then (if t 3 = 0 then 2220 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 684 else if t 3 = 1 then 2181 else 2189)) else (if t 2 = 0 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2206 else 1890) else if t 2 = 1 then (if t 3 = 0 then 2221 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 685 else if t 3 = 1 then 2182 else 2190))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 377 else 3240) else if t 2 = 1 then (if t 3 = 0 then 930 else if t 3 = 1 then 352 else 354) else (if t 3 = 0 then 2990 else if t 3 = 1 then 1487 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 306 else if t 3 = 1 then 973 else 975) else if t 2 = 1 then (if t 3 = 0 then 294 else if t 3 = 1 then 2179 else 2187) else (if t 3 = 0 then 1473 else if t 3 = 1 then 2183 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 307 else if t 3 = 1 then 974 else 976) else if t 2 = 1 then (if t 3 = 0 then 295 else if t 3 = 1 then 2180 else 2188) else (if t 3 = 0 then 1474 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3441 else (if jt.2.val < 2 then 3527 else 3463)) else (if jt.2.val < 4 then 3526 else (if jt.2.val < 5 then 3529 else 3459))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3618 else (if jt.2.val < 2 then 3625 else 3620)) else (if jt.2.val < 4 then 3624 else (if jt.2.val < 5 then 3626 else 3615)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2349 else (if jt.2.val < 2 then 2353 else 2351)) else (if jt.2.val < 4 then 2352 else (if jt.2.val < 5 then 2354 else 2346))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2166 else (if jt.2.val < 2 then 2216 else 2168)) else (if jt.2.val < 4 then 2214 else (if jt.2.val < 5 then 2215 else 2163)))))

checked_coverage fastCoverage0207 pairing0207 template0207 witness0207

theorem coverage0207 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0207) (maskBits m))
    cores template0207 witness0207 := by
  rw [← coresFast_eq]
  exact fastCoverage0207

theorem coverageSize0207 : ∀ q : Pattern,
    (cores (witness0207 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0207 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0207
#print axioms coverageSize0207

noncomputable def pairing0208 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0208 : List (Fin 4935) := templateData0208

noncomputable def witness0208 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3340) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2973) else (if t 3 = 0 then 2760 else if t 3 = 1 then 2759 else 2762)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 964) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 963) else (if t 3 = 0 then 292 else if t 3 = 1 then 290 else 304)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 343 else 374) else if t 2 = 1 then (if t 3 = 0 then 344 else if t 3 = 1 then 342 else 373) else (if t 3 = 0 then 1790 else if t 3 = 1 then 928 else 2140))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 1042) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 1041) else (if t 3 = 0 then 586 else if t 3 = 1 then 584 else 598)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2838) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3472) else (if t 3 = 0 then 3163 else if t 3 = 1 then 3488 else 3490)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2471 else 2489) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3479 else 3486) else (if t 3 = 0 then 3315 else if t 3 = 1 then 3492 else 3494))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1818) else if t 2 = 1 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 1056) else (if t 3 = 0 then 593 else if t 3 = 1 then 592 else 602)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2842) else if t 2 = 1 then (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3473) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3489 else 3491)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2475 else 2491) else if t 2 = 1 then (if t 3 = 0 then 3084 else if t 3 = 1 then 3480 else 3487) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3493 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3441 else (if jt.2.val < 2 then 3461 else 3463)) else (if jt.2.val < 4 then 3458 else (if jt.2.val < 5 then 3460 else 3459))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3600 else (if jt.2.val < 2 then 3610 else 3611)) else (if jt.2.val < 4 then 3607 else (if jt.2.val < 5 then 3609 else 3608)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3537 else (if jt.2.val < 2 then 3545 else 3548)) else (if jt.2.val < 4 then 3544 else (if jt.2.val < 5 then 3547 else 3546))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3627 else (if jt.2.val < 2 then 3631 else 3632)) else (if jt.2.val < 4 then 3628 else (if jt.2.val < 5 then 3630 else 3629)))))

checked_coverage fastCoverage0208 pairing0208 template0208 witness0208

theorem coverage0208 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0208) (maskBits m))
    cores template0208 witness0208 := by
  rw [← coresFast_eq]
  exact fastCoverage0208

theorem coverageSize0208 : ∀ q : Pattern,
    (cores (witness0208 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0208 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0208
#print axioms coverageSize0208

noncomputable def pairing0209 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0209 : List (Fin 4935) := templateData0209

noncomputable def witness0209 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3520) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2972) else (if t 3 = 0 then 2798 else if t 3 = 1 then 2797 else 2800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 962) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 961) else (if t 3 = 0 then 88 else if t 3 = 1 then 86 else 100)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 143 else 173) else if t 2 = 1 then (if t 3 = 0 then 144 else if t 3 = 1 then 142 else 172) else (if t 3 = 0 then 2129 else if t 3 = 1 then 898 else 1807))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 1040) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 1039) else (if t 3 = 0 then 775 else if t 3 = 1 then 773 else 787)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2837) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3276) else (if t 3 = 0 then 3165 else if t 3 = 1 then 3295 else 3297)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2623 else 2637) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3291 else 3293) else (if t 3 = 0 then 3500 else if t 3 = 1 then 3299 else 3301))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 2147) else if t 2 = 1 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 1055) else (if t 3 = 0 then 782 else if t 3 = 1 then 781 else 791)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2841) else if t 2 = 1 then (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3279) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3296 else 3298)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2627 else 2639) else if t 2 = 1 then (if t 3 = 0 then 3093 else if t 3 = 1 then 3292 else 3294) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3300 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3246 else (if jt.2.val < 2 then 3266 else 3268)) else (if jt.2.val < 4 then 3263 else (if jt.2.val < 5 then 3265 else 3264))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3555 else (if jt.2.val < 2 then 3565 else 3566)) else (if jt.2.val < 4 then 3562 else (if jt.2.val < 5 then 3564 else 3563)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3357 else (if jt.2.val < 2 then 3363 else 3368)) else (if jt.2.val < 4 then 3362 else (if jt.2.val < 5 then 3367 else 3366))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3629 else (if jt.2.val < 2 then 3635 else 3632)) else (if jt.2.val < 4 then 3633 else (if jt.2.val < 5 then 3634 else 3627)))))

checked_coverage fastCoverage0209 pairing0209 template0209 witness0209

theorem coverage0209 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0209) (maskBits m))
    cores template0209 witness0209 := by
  rw [← coresFast_eq]
  exact fastCoverage0209

theorem coverageSize0209 : ∀ q : Pattern,
    (cores (witness0209 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0209 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0209
#print axioms coverageSize0209

noncomputable def pairing0210 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0210 : List (Fin 4935) := templateData0210

noncomputable def witness0210 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2565 else 2577) else if t 2 = 1 then (if t 3 = 0 then 2560 else if t 3 = 1 then 2544 else 2545) else (if t 3 = 0 then 3499 else if t 3 = 1 then 3209 else 3342)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2563 else 1372) else if t 2 = 1 then (if t 3 = 0 then 2558 else if t 3 = 1 then 2538 else 1350) else (if t 3 = 0 then 277 else if t 3 = 1 then 251 else 254)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1762 else 2119) else if t 2 = 1 then (if t 3 = 0 then 1750 else if t 3 = 1 then 1747 else 1353) else (if t 3 = 0 then 279 else if t 3 = 1 then 256 else 258))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2564 else 1687) else if t 2 = 1 then (if t 3 = 0 then 2559 else if t 3 = 1 then 2541 else 1666) else (if t 3 = 0 then 571 else if t 3 = 1 then 545 else 547)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2562 else 2576) else if t 2 = 1 then (if t 3 = 0 then 2548 else if t 3 = 1 then 2519 else 2526) else (if t 3 = 0 then 2550 else if t 3 = 1 then 2523 else 2528)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2883 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2554 else if t 3 = 1 then 2530 else 2534) else (if t 3 = 0 then 2556 else if t 3 = 1 then 2532 else 2536))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 189 else 203) else if t 2 = 1 then (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 151) else (if t 3 = 0 then 2116 else if t 3 = 1 then 1532 else 1834)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2578) else if t 2 = 1 then (if t 3 = 0 then 2549 else if t 3 = 1 then 2521 else 2527) else (if t 3 = 0 then 2551 else if t 3 = 1 then 2524 else 2529)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2885 else 3507) else if t 2 = 1 then (if t 3 = 0 then 2555 else if t 3 = 1 then 2531 else 2535) else (if t 3 = 0 then 2557 else if t 3 = 1 then 2533 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2516 else (if jt.2.val < 2 then 2518 else 2540)) else (if jt.2.val < 4 then 2517 else (if jt.2.val < 5 then 2539 else 2520))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3582 else (if jt.2.val < 2 then 3584 else 3587)) else (if jt.2.val < 4 then 3583 else (if jt.2.val < 5 then 3586 else 3585)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3546 else (if jt.2.val < 2 then 3554 else 3548)) else (if jt.2.val < 4 then 3552 else (if jt.2.val < 5 then 3553 else 3537))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2510 else (if jt.2.val < 2 then 2512 else 2553)) else (if jt.2.val < 4 then 2511 else (if jt.2.val < 5 then 2552 else 2525)))))

checked_coverage fastCoverage0210 pairing0210 template0210 witness0210

theorem coverage0210 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0210) (maskBits m))
    cores template0210 witness0210 := by
  rw [← coresFast_eq]
  exact fastCoverage0210

theorem coverageSize0210 : ∀ q : Pattern,
    (cores (witness0210 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0210 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0210
#print axioms coverageSize0210

noncomputable def pairing0211 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0211 : List (Fin 4935) := templateData0211

noncomputable def witness0211 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2710 else 2722) else if t 2 = 1 then (if t 3 = 0 then 2705 else if t 3 = 1 then 2688 else 2689) else (if t 3 = 0 then 3312 else if t 3 = 1 then 3191 else 3522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2708 else 1371) else if t 2 = 1 then (if t 3 = 0 then 2703 else if t 3 = 1 then 2682 else 1339) else (if t 3 = 0 then 73 else if t 3 = 1 then 43 else 46)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2107 else 1780) else if t 2 = 1 then (if t 3 = 0 then 2098 else if t 3 = 1 then 2090 else 1342) else (if t 3 = 0 then 75 else if t 3 = 1 then 48 else 50))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2709 else 1686) else if t 2 = 1 then (if t 3 = 0 then 2704 else if t 3 = 1 then 2685 else 1657) else (if t 3 = 0 then 760 else if t 3 = 1 then 733 else 735)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2707 else 2721) else if t 2 = 1 then (if t 3 = 0 then 2695 else if t 3 = 1 then 2664 else 2670) else (if t 3 = 0 then 2697 else if t 3 = 1 then 2668 else 2672)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2902 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2699 else if t 3 = 1 then 2674 else 2678) else (if t 3 = 0 then 2701 else if t 3 = 1 then 2676 else 2680))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 390 else 404) else if t 2 = 1 then (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 351) else (if t 3 = 0 then 1774 else if t 3 = 1 then 1484 else 2158)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2723) else if t 2 = 1 then (if t 3 = 0 then 2696 else if t 3 = 1 then 2666 else 2671) else (if t 3 = 0 then 2698 else if t 3 = 1 then 2669 else 2673)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2903 else 3322) else if t 2 = 1 then (if t 3 = 0 then 2700 else if t 3 = 1 then 2675 else 2679) else (if t 3 = 0 then 2702 else if t 3 = 1 then 2677 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2661 else (if jt.2.val < 2 then 2663 else 2684)) else (if jt.2.val < 4 then 2662 else (if jt.2.val < 5 then 2683 else 2665))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3615 else (if jt.2.val < 2 then 3617 else 3620)) else (if jt.2.val < 4 then 3616 else (if jt.2.val < 5 then 3619 else 3618)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3366 else (if jt.2.val < 2 then 3380 else 3368)) else (if jt.2.val < 4 then 3378 else (if jt.2.val < 5 then 3379 else 3357))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2525 else (if jt.2.val < 2 then 2693 else 2553)) else (if jt.2.val < 4 then 2692 else (if jt.2.val < 5 then 2694 else 2510)))))

checked_coverage fastCoverage0211 pairing0211 template0211 witness0211

theorem coverage0211 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0211) (maskBits m))
    cores template0211 witness0211 := by
  rw [← coresFast_eq]
  exact fastCoverage0211

theorem coverageSize0211 : ∀ q : Pattern,
    (cores (witness0211 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0211 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0211
#print axioms coverageSize0211

noncomputable def pairing0212 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0212 : List (Fin 4935) := templateData0212

noncomputable def witness0212 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 428 else 469) else if t 2 = 1 then (if t 3 = 0 then 430 else if t 3 = 1 then 426 else 467) else (if t 3 = 0 then 1837 else if t 3 = 1 then 1114 else 2150)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 424 else if t 3 = 1 then 420 else 464) else if t 2 = 1 then (if t 3 = 0 then 422 else if t 3 = 1 then 418 else 462) else (if t 3 = 0 then 502 else if t 3 = 1 then 488 else 490)) else (if t 2 = 0 then (if t 3 = 0 then 3505 else if t 3 = 1 then 3203 else 3344) else if t 2 = 1 then (if t 3 = 0 then 2730 else if t 3 = 1 then 2728 else 2737) else (if t 3 = 0 then 2743 else if t 3 = 1 then 2740 else 2741))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 427 else 468) else if t 2 = 1 then (if t 3 = 0 then 429 else if t 3 = 1 then 425 else 466) else (if t 3 = 0 then 1836 else if t 3 = 1 then 1113 else 2148)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 423 else if t 3 = 1 then 419 else 463) else if t 2 = 1 then (if t 3 = 0 then 421 else if t 3 = 1 then 417 else 461) else (if t 3 = 0 then 498 else if t 3 = 1 then 480 else 484)) else (if t 2 = 0 then (if t 3 = 0 then 439 else if t 3 = 1 then 437 else 471) else if t 2 = 1 then (if t 3 = 0 then 438 else if t 3 = 1 then 436 else 470) else (if t 3 = 0 then 499 else if t 3 = 1 then 481 else 485))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 1509 else 2739) else if t 2 = 1 then (if t 3 = 0 then 451 else if t 3 = 1 then 449 else 476) else (if t 3 = 0 then 3343 else if t 3 = 1 then 1119 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2124 else if t 3 = 1 then 1506 else 1848) else if t 2 = 1 then (if t 3 = 0 then 447 else if t 3 = 1 then 444 else 474) else (if t 3 = 0 then 500 else if t 3 = 1 then 482 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 2126 else if t 3 = 1 then 1511 else 1850) else if t 2 = 1 then (if t 3 = 0 then 454 else if t 3 = 1 then 453 else 478) else (if t 3 = 0 then 501 else if t 3 = 1 then 483 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2661 else (if jt.2.val < 2 then 2735 else 2684)) else (if jt.2.val < 4 then 2733 else (if jt.2.val < 5 then 2734 else 2665))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3608 else (if jt.2.val < 2 then 3623 else 3611)) else (if jt.2.val < 4 then 3621 else (if jt.2.val < 5 then 3622 else 3600)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1950 else (if jt.2.val < 2 then 1952 else 1955)) else (if jt.2.val < 4 then 1951 else (if jt.2.val < 5 then 1954 else 1953))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 416 else (if jt.2.val < 2 then 460 else 465)) else (if jt.2.val < 4 then 457 else (if jt.2.val < 5 then 459 else 458)))))

checked_coverage fastCoverage0212 pairing0212 template0212 witness0212

theorem coverage0212 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0212) (maskBits m))
    cores template0212 witness0212 := by
  rw [← coresFast_eq]
  exact fastCoverage0212

theorem coverageSize0212 : ∀ q : Pattern,
    (cores (witness0212 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0212 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0212
#print axioms coverageSize0212

noncomputable def pairing0213 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0213 : List (Fin 4935) := templateData0213

noncomputable def witness0213 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 624 else 661) else if t 2 = 1 then (if t 3 = 0 then 626 else if t 3 = 1 then 622 else 659) else (if t 3 = 0 then 2161 else if t 3 = 1 then 1144 else 1826)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 620 else if t 3 = 1 then 616 else 656) else if t 2 = 1 then (if t 3 = 0 then 618 else if t 3 = 1 then 614 else 654) else (if t 3 = 0 then 694 else if t 3 = 1 then 680 else 682)) else (if t 2 = 0 then (if t 3 = 0 then 3320 else if t 3 = 1 then 3172 else 3524) else if t 2 = 1 then (if t 3 = 0 then 2768 else if t 3 = 1 then 2766 else 2775) else (if t 3 = 0 then 2781 else if t 3 = 1 then 2778 else 2779))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 623 else 660) else if t 2 = 1 then (if t 3 = 0 then 625 else if t 3 = 1 then 621 else 658) else (if t 3 = 0 then 2160 else if t 3 = 1 then 1140 else 1824)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 619 else if t 3 = 1 then 615 else 655) else if t 2 = 1 then (if t 3 = 0 then 617 else if t 3 = 1 then 613 else 653) else (if t 3 = 0 then 690 else if t 3 = 1 then 672 else 676)) else (if t 2 = 0 then (if t 3 = 0 then 635 else if t 3 = 1 then 633 else 663) else if t 2 = 1 then (if t 3 = 0 then 634 else if t 3 = 1 then 632 else 662) else (if t 3 = 0 then 691 else if t 3 = 1 then 673 else 677))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1461 else 2777) else if t 2 = 1 then (if t 3 = 0 then 647 else if t 3 = 1 then 645 else 668) else (if t 3 = 0 then 3523 else if t 3 = 1 then 1142 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1785 else if t 3 = 1 then 1458 else 2169) else if t 2 = 1 then (if t 3 = 0 then 643 else if t 3 = 1 then 640 else 666) else (if t 3 = 0 then 692 else if t 3 = 1 then 674 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 1787 else if t 3 = 1 then 1463 else 2171) else if t 2 = 1 then (if t 3 = 0 then 650 else if t 3 = 1 then 649 else 670) else (if t 3 = 0 then 693 else if t 3 = 1 then 675 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2516 else (if jt.2.val < 2 then 2773 else 2540)) else (if jt.2.val < 4 then 2771 else (if jt.2.val < 5 then 2772 else 2520))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3563 else (if jt.2.val < 2 then 3590 else 3566)) else (if jt.2.val < 4 then 3588 else (if jt.2.val < 5 then 3589 else 3555)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2250 else (if jt.2.val < 2 then 2252 else 2255)) else (if jt.2.val < 4 then 2251 else (if jt.2.val < 5 then 2254 else 2253))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 458 else (if jt.2.val < 2 then 657 else 465)) else (if jt.2.val < 4 then 609 else (if jt.2.val < 5 then 610 else 416)))))

checked_coverage fastCoverage0213 pairing0213 template0213 witness0213

theorem coverage0213 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0213) (maskBits m))
    cores template0213 witness0213 := by
  rw [← coresFast_eq]
  exact fastCoverage0213

theorem coverageSize0213 : ∀ q : Pattern,
    (cores (witness0213 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0213 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0213
#print axioms coverageSize0213

noncomputable def pairing0214 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0214 : List (Fin 4935) := templateData0214

noncomputable def witness0214 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1912 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1901 else 1670) else (if t 3 = 0 then 575 else if t 3 = 1 then 554 else 555)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1907 else 1619) else if t 2 = 1 then (if t 3 = 0 then 1891 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 1188 else if t 3 = 1 then 1878 else 1882)) else (if t 2 = 0 then (if t 3 = 0 then 2506 else if t 3 = 1 then 2500 else 2501) else if t 2 = 1 then (if t 3 = 0 then 2938 else if t 3 = 1 then 3348 else 3351) else (if t 3 = 0 then 3514 else if t 3 = 1 then 3350 else 3352))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1911 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1899 else 1667) else (if t 3 = 0 then 572 else if t 3 = 1 then 548 else 550)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1905 else 1617) else if t 2 = 1 then (if t 3 = 0 then 1887 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 1181 else if t 3 = 1 then 1863 else 1871)) else (if t 2 = 0 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1906 else 1618) else if t 2 = 1 then (if t 3 = 0 then 1888 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 1182 else if t 3 = 1 then 1864 else 1872))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 899 else 3525) else if t 2 = 1 then (if t 3 = 0 then 176 else if t 3 = 1 then 152 else 154) else (if t 3 = 0 then 2758 else if t 3 = 1 then 1535 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 102 else if t 3 = 1 then 90 else 92) else if t 2 = 1 then (if t 3 = 0 then 971 else if t 3 = 1 then 1861 else 1869) else (if t 3 = 0 then 2136 else if t 3 = 1 then 1865 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 103 else if t 3 = 1 then 91 else 93) else if t 2 = 1 then (if t 3 = 0 then 972 else if t 3 = 1 then 1862 else 1870) else (if t 3 = 0 then 2137 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3246 else (if jt.2.val < 2 then 3347 else 3268)) else (if jt.2.val < 4 then 3346 else (if jt.2.val < 5 then 3349 else 3264))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3585 else (if jt.2.val < 2 then 3598 else 3587)) else (if jt.2.val < 4 then 3597 else (if jt.2.val < 5 then 3599 else 3582)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1953 else (if jt.2.val < 2 then 1970 else 1955)) else (if jt.2.val < 4 then 1967 else (if jt.2.val < 5 then 1968 else 1950))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2367 else (if jt.2.val < 2 then 2369 else 2372)) else (if jt.2.val < 4 then 2368 else (if jt.2.val < 5 then 2371 else 2370)))))

checked_coverage fastCoverage0214 pairing0214 template0214 witness0214

theorem coverage0214 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0214) (maskBits m))
    cores template0214 witness0214 := by
  rw [← coresFast_eq]
  exact fastCoverage0214

theorem coverageSize0214 : ∀ q : Pattern,
    (cores (witness0214 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0214 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0214
#print axioms coverageSize0214

noncomputable def pairing0215 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0215 : List (Fin 4935) := templateData0215

noncomputable def witness0215 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2228 else 1856) else if t 2 = 1 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2213 else 1661) else (if t 3 = 0 then 764 else if t 3 = 1 then 742 else 743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2222 else 1616) else if t 2 = 1 then (if t 3 = 0 then 2207 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 1189 else if t 3 = 1 then 2196 else 2200)) else (if t 2 = 0 then (if t 3 = 0 then 2654 else if t 3 = 1 then 2648 else 2649) else if t 2 = 1 then (if t 3 = 0 then 2939 else if t 3 = 1 then 3528 else 3531) else (if t 3 = 0 then 3330 else if t 3 = 1 then 3530 else 3532))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2226 else 1854) else if t 2 = 1 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2211 else 1658) else (if t 3 = 0 then 761 else if t 3 = 1 then 736 else 738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2220 else 1614) else if t 2 = 1 then (if t 3 = 0 then 2205 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 1183 else if t 3 = 1 then 2181 else 2189)) else (if t 2 = 0 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2221 else 1615) else if t 2 = 1 then (if t 3 = 0 then 2206 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 1184 else if t 3 = 1 then 2182 else 2190))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 930 else 3345) else if t 2 = 1 then (if t 3 = 0 then 377 else if t 3 = 1 then 352 else 354) else (if t 3 = 0 then 2796 else if t 3 = 1 then 1487 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 306 else if t 3 = 1 then 294 else 296) else if t 2 = 1 then (if t 3 = 0 then 973 else if t 3 = 1 then 2179 else 2187) else (if t 3 = 0 then 1799 else if t 3 = 1 then 2183 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 307 else if t 3 = 1 then 295 else 297) else if t 2 = 1 then (if t 3 = 0 then 974 else if t 3 = 1 then 2180 else 2188) else (if t 3 = 0 then 1800 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3441 else (if jt.2.val < 2 then 3527 else 3463)) else (if jt.2.val < 4 then 3526 else (if jt.2.val < 5 then 3529 else 3459))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3618 else (if jt.2.val < 2 then 3625 else 3620)) else (if jt.2.val < 4 then 3624 else (if jt.2.val < 5 then 3626 else 3615)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2253 else (if jt.2.val < 2 then 2267 else 2255)) else (if jt.2.val < 4 then 2265 else (if jt.2.val < 5 then 2266 else 2250))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2370 else (if jt.2.val < 2 then 2374 else 2372)) else (if jt.2.val < 4 then 2373 else (if jt.2.val < 5 then 2375 else 2367)))))

checked_coverage fastCoverage0215 pairing0215 template0215 witness0215

theorem coverage0215 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0215) (maskBits m))
    cores template0215 witness0215 := by
  rw [← coresFast_eq]
  exact fastCoverage0215

theorem coverageSize0215 : ∀ q : Pattern,
    (cores (witness0215 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0215 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0215
#print axioms coverageSize0215

noncomputable def pairing0216 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0216 : List (Fin 4935) := templateData0216

noncomputable def witness0216 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3174) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2769) else (if t 3 = 0 then 2974 else if t 3 = 1 then 2972 else 2776)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 143) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 142) else (if t 3 = 0 then 965 else if t 3 = 1 then 961 else 172)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 87 else 904) else if t 2 = 1 then (if t 3 = 0 then 88 else if t 3 = 1 then 86 else 898) else (if t 3 = 0 then 1478 else if t 3 = 1 then 100 else 1807))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 637) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 636) else (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 664)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2623) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3291) else (if t 3 = 0 then 3278 else if t 3 = 1 then 3276 else 3293)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2717 else 2904) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3295 else 3299) else (if t 3 = 0 then 3167 else if t 3 = 1 then 3297 else 3301))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 1464) else if t 2 = 1 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 651) else (if t 3 = 0 then 1057 else if t 3 = 1 then 1055 else 671)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2627) else if t 2 = 1 then (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3292) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3279 else 3294)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2719 else 2905) else if t 2 = 1 then (if t 3 = 0 then 3166 else if t 3 = 1 then 3296 else 3300) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3298 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3246 else (if jt.2.val < 2 then 3266 else 3268)) else (if jt.2.val < 4 then 3263 else (if jt.2.val < 5 then 3265 else 3264))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3636 else (if jt.2.val < 2 then 3638 else 3641)) else (if jt.2.val < 4 then 3637 else (if jt.2.val < 5 then 3640 else 3639)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3556 else (if jt.2.val < 2 then 3560 else 3561)) else (if jt.2.val < 4 then 3557 else (if jt.2.val < 5 then 3559 else 3558))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3358 else (if jt.2.val < 2 then 3364 else 3365)) else (if jt.2.val < 4 then 3359 else (if jt.2.val < 5 then 3361 else 3360)))))

checked_coverage fastCoverage0216 pairing0216 template0216 witness0216

theorem coverage0216 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0216) (maskBits m))
    cores template0216 witness0216 := by
  rw [← coresFast_eq]
  exact fastCoverage0216

theorem coverageSize0216 : ∀ q : Pattern,
    (cores (witness0216 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0216 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0216
#print axioms coverageSize0216

noncomputable def pairing0217 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0217 : List (Fin 4935) := templateData0217

noncomputable def witness0217 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3320) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 2768) else (if t 3 = 0 then 2732 else if t 3 = 1 then 2730 else 2987)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 141) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 140) else (if t 3 = 0 then 344 else if t 3 = 1 then 340 else 892)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 868 else 205) else if t 2 = 1 then (if t 3 = 0 then 874 else if t 3 = 1 then 862 else 199) else (if t 3 = 0 then 1790 else if t 3 = 1 then 400 else 1501))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 635) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 634) else (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 1135)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2622) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3089) else (if t 3 = 0 then 3082 else if t 3 = 1 then 3080 else 3094)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2956 else 2652) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3098 else 3102) else (if t 3 = 0 then 3315 else if t 3 = 1 then 3100 else 3104))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 1787) else if t 2 = 1 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 650) else (if t 3 = 0 then 456 else if t 3 = 1 then 454 else 1139)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2626) else if t 2 = 1 then (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3092) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3083 else 3096)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2957 else 2653) else if t 2 = 1 then (if t 3 = 0 then 3314 else if t 3 = 1 then 3099 else 3103) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3101 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3050 else (if jt.2.val < 2 then 3070 else 3072)) else (if jt.2.val < 4 then 3067 else (if jt.2.val < 5 then 3069 else 3068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3642 else (if jt.2.val < 2 then 3644 else 3647)) else (if jt.2.val < 4 then 3643 else (if jt.2.val < 5 then 3646 else 3645)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3385 else (if jt.2.val < 2 then 3389 else 3390)) else (if jt.2.val < 4 then 3386 else (if jt.2.val < 5 then 3388 else 3387))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3360 else (if jt.2.val < 2 then 3374 else 3365)) else (if jt.2.val < 4 then 3369 else (if jt.2.val < 5 then 3370 else 3358)))))

checked_coverage fastCoverage0217 pairing0217 template0217 witness0217

theorem coverage0217 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0217) (maskBits m))
    cores template0217 witness0217 := by
  rw [← coresFast_eq]
  exact fastCoverage0217

theorem coverageSize0217 : ∀ q : Pattern,
    (cores (witness0217 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0217 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0217
#print axioms coverageSize0217

noncomputable def pairing0218 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0218 : List (Fin 4935) := templateData0218

noncomputable def witness0218 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2813 else 2633) else if t 2 = 1 then (if t 3 = 0 then 2817 else if t 3 = 1 then 2809 else 2855) else (if t 3 = 0 then 3340 else if t 3 = 1 then 3338 else 3226)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2811 else 1415) else if t 2 = 1 then (if t 3 = 0 then 2815 else if t 3 = 1 then 2807 else 1414) else (if t 3 = 0 then 964 else if t 3 = 1 then 960 else 992)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1371 else 1780) else if t 2 = 1 then (if t 3 = 0 then 1372 else if t 3 = 1 then 1370 else 1777) else (if t 3 = 0 then 305 else if t 3 = 1 then 1001 else 1012))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2812 else 1585) else if t 2 = 1 then (if t 3 = 0 then 2816 else if t 3 = 1 then 2808 else 1584) else (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1073)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2810 else 2632) else if t 2 = 1 then (if t 3 = 0 then 2814 else if t 3 = 1 then 2806 else 2854) else (if t 3 = 0 then 2838 else if t 3 = 1 then 2835 else 2857)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2721 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2576 else if t 3 = 1 then 2859 else 2864) else (if t 3 = 0 then 2579 else if t 3 = 1 then 2862 else 2866))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 820 else 275) else if t 2 = 1 then (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 857) else (if t 3 = 0 then 1818 else if t 3 = 1 then 1817 else 1601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2635) else if t 2 = 1 then (if t 3 = 0 then 2829 else if t 3 = 1 then 2826 else 2856) else (if t 3 = 0 then 2842 else if t 3 = 1 then 2840 else 2858)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2723 else 3322) else if t 2 = 1 then (if t 3 = 0 then 2578 else if t 3 = 1 then 2861 else 2865) else (if t 3 = 0 then 2580 else if t 3 = 1 then 2863 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2805 else (if jt.2.val < 2 then 2825 else 2827)) else (if jt.2.val < 4 then 2822 else (if jt.2.val < 5 then 2824 else 2823))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3648 else (if jt.2.val < 2 then 3650 else 3653)) else (if jt.2.val < 4 then 3649 else (if jt.2.val < 5 then 3652 else 3651)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3558 else (if jt.2.val < 2 then 3576 else 3561)) else (if jt.2.val < 4 then 3573 else (if jt.2.val < 5 then 3574 else 3556))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3007 else (if jt.2.val < 2 then 3016 else 3017)) else (if jt.2.val < 4 then 3008 else (if jt.2.val < 5 then 3010 else 3009)))))

checked_coverage fastCoverage0218 pairing0218 template0218 witness0218

theorem coverage0218 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0218) (maskBits m))
    cores template0218 witness0218 := by
  rw [← coresFast_eq]
  exact fastCoverage0218

theorem coverageSize0218 : ∀ q : Pattern,
    (cores (witness0218 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0218 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0218
#print axioms coverageSize0218

noncomputable def pairing0219 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0219 : List (Fin 4935) := templateData0219

noncomputable def witness0219 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2446 else 2898) else if t 2 = 1 then (if t 3 = 0 then 2450 else if t 3 = 1 then 2442 else 2482) else (if t 3 = 0 then 3205 else if t 3 = 1 then 3203 else 3344)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2444 else 1413) else if t 2 = 1 then (if t 3 = 0 then 2448 else if t 3 = 1 then 2440 else 1412) else (if t 3 = 0 then 343 else if t 3 = 1 then 339 else 372)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1756 else 1453) else if t 2 = 1 then (if t 3 = 0 then 1762 else if t 3 = 1 then 1753 else 1450) else (if t 3 = 0 then 929 else if t 3 = 1 then 394 else 396))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2445 else 1583) else if t 2 = 1 then (if t 3 = 0 then 2449 else if t 3 = 1 then 2441 else 1582) else (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 471)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2443 else 2897) else if t 2 = 1 then (if t 3 = 0 then 2447 else if t 3 = 1 then 2439 else 2481) else (if t 3 = 0 then 2471 else if t 3 = 1 then 2468 else 2488)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2502 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2883 else if t 3 = 1 then 2492 else 2496) else (if t 3 = 0 then 2886 else if t 3 = 1 then 2494 else 2498))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 33 else 920) else if t 2 = 1 then (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 69) else (if t 3 = 0 then 1512 else if t 3 = 1 then 1511 else 1850)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2899) else if t 2 = 1 then (if t 3 = 0 then 2462 else if t 3 = 1 then 2459 else 2486) else (if t 3 = 0 then 2475 else if t 3 = 1 then 2473 else 2490)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2503 else 3184) else if t 2 = 1 then (if t 3 = 0 then 2885 else if t 3 = 1 then 2493 else 2497) else (if t 3 = 0 then 2887 else if t 3 = 1 then 2495 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2438 else (if jt.2.val < 2 then 2458 else 2460)) else (if jt.2.val < 4 then 2455 else (if jt.2.val < 5 then 2457 else 2456))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3654 else (if jt.2.val < 2 then 3656 else 3659)) else (if jt.2.val < 4 then 3655 else (if jt.2.val < 5 then 3658 else 3657)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3387 else (if jt.2.val < 2 then 3411 else 3390)) else (if jt.2.val < 4 then 3408 else (if jt.2.val < 5 then 3409 else 3385))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3009 else (if jt.2.val < 2 then 3026 else 3017)) else (if jt.2.val < 4 then 3018 else (if jt.2.val < 5 then 3019 else 3007)))))

checked_coverage fastCoverage0219 pairing0219 template0219 witness0219

theorem coverage0219 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0219) (maskBits m))
    cores template0219 witness0219 := by
  rw [← coresFast_eq]
  exact fastCoverage0219

theorem coverageSize0219 : ∀ q : Pattern,
    (cores (witness0219 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0219 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0219
#print axioms coverageSize0219

noncomputable def pairing0220 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0220 : List (Fin 4935) := templateData0220

noncomputable def witness0220 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 768 else 1148) else if t 2 = 1 then (if t 3 = 0 then 770 else if t 3 = 1 then 766 else 1144) else (if t 3 = 0 then 1549 else if t 3 = 1 then 784 else 1826)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 763 else if t 3 = 1 then 740 else 742) else if t 2 = 1 then (if t 3 = 0 then 755 else if t 3 = 1 then 720 else 725) else (if t 3 = 0 then 1108 else if t 3 = 1 then 723 else 727)) else (if t 2 = 0 then (if t 3 = 0 then 3312 else if t 3 = 1 then 3191 else 3192) else if t 2 = 1 then (if t 3 = 0 then 2794 else if t 3 = 1 then 2785 else 2788) else (if t 3 = 0 then 2983 else if t 3 = 1 then 2787 else 2789))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 767 else 1146) else if t 2 = 1 then (if t 3 = 0 then 769 else if t 3 = 1 then 765 else 1140) else (if t 3 = 0 then 1548 else if t 3 = 1 then 783 else 1824)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 759 else if t 3 = 1 then 732 else 736) else if t 2 = 1 then (if t 3 = 0 then 747 else if t 3 = 1 then 704 else 712) else (if t 3 = 0 then 1104 else if t 3 = 1 then 708 else 716)) else (if t 2 = 0 then (if t 3 = 0 then 760 else if t 3 = 1 then 733 else 737) else if t 2 = 1 then (if t 3 = 0 then 748 else if t 3 = 1 then 705 else 713) else (if t 3 = 0 then 1105 else if t 3 = 1 then 709 else 717))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1497 else 2990) else if t 2 = 1 then (if t 3 = 0 then 779 else if t 3 = 1 then 777 else 1142) else (if t 3 = 0 then 3216 else if t 3 = 1 then 789 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1773 else if t 3 = 1 then 1483 else 1487) else if t 2 = 1 then (if t 3 = 0 then 749 else if t 3 = 1 then 706 else 714) else (if t 3 = 0 then 1106 else if t 3 = 1 then 710 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 1774 else if t 3 = 1 then 1484 else 1488) else if t 2 = 1 then (if t 3 = 0 then 750 else if t 3 = 1 then 707 else 715) else (if t 3 = 0 then 1107 else if t 3 = 1 then 711 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2438 else (if jt.2.val < 2 then 2784 else 2460)) else (if jt.2.val < 4 then 2783 else (if jt.2.val < 5 then 2786 else 2456))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3639 else (if jt.2.val < 2 then 3662 else 3641)) else (if jt.2.val < 4 then 3660 else (if jt.2.val < 5 then 3661 else 3636)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2022 else (if jt.2.val < 2 then 2024 else 2027)) else (if jt.2.val < 4 then 2023 else (if jt.2.val < 5 then 2026 else 2025))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1281 else (if jt.2.val < 2 then 1283 else 1289)) else (if jt.2.val < 4 then 1282 else (if jt.2.val < 5 then 1288 else 1286)))))

checked_coverage fastCoverage0220 pairing0220 template0220 witness0220

theorem coverage0220 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0220) (maskBits m))
    cores template0220 witness0220 := by
  rw [← coresFast_eq]
  exact fastCoverage0220

theorem coverageSize0220 : ∀ q : Pattern,
    (cores (witness0220 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0220 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0220
#print axioms coverageSize0220

noncomputable def pairing0221 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0221 : List (Fin 4935) := templateData0221

noncomputable def witness0221 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1214 else 698) else if t 2 = 1 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1210 else 694) else (if t 3 = 0 then 1837 else if t 3 = 1 then 502 else 1526)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1205 else if t 3 = 1 then 1187 else 1189) else if t 2 = 1 then (if t 3 = 0 then 1201 else if t 3 = 1 then 1167 else 1172) else (if t 3 = 0 then 568 else if t 3 = 1 then 1170 else 1174)) else (if t 2 = 0 then (if t 3 = 0 then 3152 else if t 3 = 1 then 3329 else 3330) else if t 2 = 1 then (if t 3 = 0 then 3002 else if t 3 = 1 then 2993 else 2996) else (if t 3 = 0 then 2757 else if t 3 = 1 then 2995 else 2997))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1212 else 696) else if t 2 = 1 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1206 else 690) else (if t 3 = 0 then 1836 else if t 3 = 1 then 498 else 1524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1203 else if t 3 = 1 then 1179 else 1183) else if t 2 = 1 then (if t 3 = 0 then 1197 else if t 3 = 1 then 1151 else 1159) else (if t 3 = 0 then 562 else if t 3 = 1 then 1155 else 1163)) else (if t 2 = 0 then (if t 3 = 0 then 1204 else if t 3 = 1 then 1180 else 1184) else if t 2 = 1 then (if t 3 = 0 then 1198 else if t 3 = 1 then 1152 else 1160) else (if t 3 = 0 then 563 else if t 3 = 1 then 1156 else 1164))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1374 else 2782) else if t 2 = 1 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1208 else 692) else (if t 3 = 0 then 3343 else if t 3 = 1 then 500 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1430 else if t 3 = 1 then 1795 else 1799) else if t 2 = 1 then (if t 3 = 0 then 1199 else if t 3 = 1 then 1153 else 1161) else (if t 3 = 0 then 564 else if t 3 = 1 then 1157 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 1431 else if t 3 = 1 then 1796 else 1800) else if t 2 = 1 then (if t 3 = 0 then 1200 else if t 3 = 1 then 1154 else 1162) else (if t 3 = 0 then 565 else if t 3 = 1 then 1158 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2805 else (if jt.2.val < 2 then 2992 else 2827)) else (if jt.2.val < 4 then 2991 else (if jt.2.val < 5 then 2994 else 2823))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3645 else (if jt.2.val < 2 then 3665 else 3647)) else (if jt.2.val < 4 then 3663 else (if jt.2.val < 5 then 3664 else 3642)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2304 else (if jt.2.val < 2 then 2306 else 2309)) else (if jt.2.val < 4 then 2305 else (if jt.2.val < 5 then 2308 else 2307))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1286 else (if jt.2.val < 2 then 1291 else 1289)) else (if jt.2.val < 4 then 1290 else (if jt.2.val < 5 then 1295 else 1281)))))

checked_coverage fastCoverage0221 pairing0221 template0221 witness0221

theorem coverage0221 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0221) (maskBits m))
    cores template0221 witness0221 := by
  rw [← coresFast_eq]
  exact fastCoverage0221

theorem coverageSize0221 : ∀ q : Pattern,
    (cores (witness0221 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0221 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0221
#print axioms coverageSize0221

noncomputable def pairing0222 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0222 : List (Fin 4935) := templateData0222

noncomputable def witness0222 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1680 else 1856) else if t 2 = 1 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1678 else 1853) else (if t 3 = 0 then 597 else if t 3 = 1 then 1080 else 1094)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1660 else 1661) else if t 2 = 1 then (if t 3 = 0 then 1669 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 553 else if t 3 = 1 then 1647 else 1651)) else (if t 2 = 0 then (if t 3 = 0 then 2882 else if t 3 = 1 then 2689 else 2691) else if t 2 = 1 then (if t 3 = 0 then 2545 else if t 3 = 1 then 3232 else 3235) else (if t 3 = 0 then 3342 else if t 3 = 1 then 3234 else 3236))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1679 else 1854) else if t 2 = 1 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1677 else 1851) else (if t 3 = 0 then 596 else if t 3 = 1 then 1079 else 1092)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1656 else 1658) else if t 2 = 1 then (if t 3 = 0 then 1665 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 546 else if t 3 = 1 then 1632 else 1640)) else (if t 2 = 0 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1657 else 1659) else if t 2 = 1 then (if t 3 = 0 then 1666 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 547 else if t 3 = 1 then 1633 else 1641))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 401 else 3345) else if t 2 = 1 then (if t 3 = 0 then 200 else if t 3 = 1 then 863 else 876) else (if t 3 = 0 then 2763 else if t 3 = 1 then 1689 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 894 else if t 3 = 1 then 350 else 354) else if t 2 = 1 then (if t 3 = 0 then 150 else if t 3 = 1 then 1630 else 1638) else (if t 3 = 0 then 1833 else if t 3 = 1 then 1634 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 895 else if t 3 = 1 then 351 else 355) else if t 2 = 1 then (if t 3 = 0 then 151 else if t 3 = 1 then 1631 else 1639) else (if t 3 = 0 then 1834 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3050 else (if jt.2.val < 2 then 3231 else 3072)) else (if jt.2.val < 4 then 3230 else (if jt.2.val < 5 then 3233 else 3068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3651 else (if jt.2.val < 2 then 3668 else 3653)) else (if jt.2.val < 4 then 3666 else (if jt.2.val < 5 then 3667 else 3648)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2025 else (if jt.2.val < 2 then 2038 else 2027)) else (if jt.2.val < 4 then 2037 else (if jt.2.val < 5 then 2039 else 2022))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1956 else (if jt.2.val < 2 then 1958 else 1963)) else (if jt.2.val < 4 then 1957 else (if jt.2.val < 5 then 1962 else 1961)))))

checked_coverage fastCoverage0222 pairing0222 template0222 witness0222

theorem coverage0222 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0222) (maskBits m))
    cores template0222 witness0222 := by
  rw [← coresFast_eq]
  exact fastCoverage0222

theorem coverageSize0222 : ∀ q : Pattern,
    (cores (witness0222 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0222 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0222
#print axioms coverageSize0222

noncomputable def pairing0223 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0223 : List (Fin 4935) := templateData0223

noncomputable def witness0223 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1910 else 1622) else if t 2 = 1 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1907 else 1619) else (if t 3 = 0 then 1116 else if t 3 = 1 then 496 else 497)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1891 else 1892) else if t 2 = 1 then (if t 3 = 0 then 1901 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 554 else if t 3 = 1 then 1878 else 1882)) else (if t 2 = 0 then (if t 3 = 0 then 2561 else if t 3 = 1 then 2938 else 2940) else if t 2 = 1 then (if t 3 = 0 then 2546 else if t 3 = 1 then 3348 else 3351) else (if t 3 = 0 then 3210 else if t 3 = 1 then 3350 else 3352))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1908 else 1620) else if t 2 = 1 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1905 else 1617) else (if t 3 = 0 then 1115 else if t 3 = 1 then 492 else 494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1887 else 1889) else if t 2 = 1 then (if t 3 = 0 then 1899 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 548 else if t 3 = 1 then 1863 else 1871)) else (if t 2 = 0 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1888 else 1890) else if t 2 = 1 then (if t 3 = 0 then 1900 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 549 else if t 3 = 1 then 1864 else 1872))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 102 else 3229) else if t 2 = 1 then (if t 3 = 0 then 899 else if t 3 = 1 then 90 else 92) else (if t 3 = 0 then 2986 else if t 3 = 1 then 1521 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 176 else if t 3 = 1 then 971 else 975) else if t 2 = 1 then (if t 3 = 0 then 152 else if t 3 = 1 then 1861 else 1869) else (if t 3 = 0 then 1535 else if t 3 = 1 then 1865 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 177 else if t 3 = 1 then 972 else 976) else if t 2 = 1 then (if t 3 = 0 then 153 else if t 3 = 1 then 1862 else 1870) else (if t 3 = 0 then 1536 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3246 else (if jt.2.val < 2 then 3347 else 3268)) else (if jt.2.val < 4 then 3346 else (if jt.2.val < 5 then 3349 else 3264))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3657 else (if jt.2.val < 2 then 3671 else 3659)) else (if jt.2.val < 4 then 3669 else (if jt.2.val < 5 then 3670 else 3654)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2307 else (if jt.2.val < 2 then 2317 else 2309)) else (if jt.2.val < 4 then 2316 else (if jt.2.val < 5 then 2318 else 2304))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1961 else (if jt.2.val < 2 then 1966 else 1963)) else (if jt.2.val < 4 then 1965 else (if jt.2.val < 5 then 1969 else 1956)))))

checked_coverage fastCoverage0223 pairing0223 template0223 witness0223

theorem coverage0223 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0223) (maskBits m))
    cores template0223 witness0223 := by
  rw [← coresFast_eq]
  exact fastCoverage0223

theorem coverageSize0223 : ∀ q : Pattern,
    (cores (witness0223 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0223 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0223
#print axioms coverageSize0223

noncomputable def pairing0224 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0224 : List (Fin 4935) := templateData0224

noncomputable def witness0224 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3205) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2731) else (if t 3 = 0 then 2974 else if t 3 = 1 then 2973 else 2738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 343) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 342) else (if t 3 = 0 then 965 else if t 3 = 1 then 963 else 373)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 291 else 929) else if t 2 = 1 then (if t 3 = 0 then 292 else if t 3 = 1 then 290 else 928) else (if t 3 = 0 then 1478 else if t 3 = 1 then 304 else 2140))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 441) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 440) else (if t 3 = 0 then 1043 else if t 3 = 1 then 1041 else 472)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2471) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3479) else (if t 3 = 0 then 3278 else if t 3 = 1 then 3472 else 3486)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2572 else 2886) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3488 else 3492) else (if t 3 = 0 then 3167 else if t 3 = 1 then 3490 else 3494))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1512) else if t 2 = 1 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 455) else (if t 3 = 0 then 1057 else if t 3 = 1 then 1056 else 479)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2475) else if t 2 = 1 then (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3480) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3473 else 3487)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2574 else 2887) else if t 2 = 1 then (if t 3 = 0 then 3164 else if t 3 = 1 then 3489 else 3493) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3491 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3441 else (if jt.2.val < 2 then 3461 else 3463)) else (if jt.2.val < 4 then 3458 else (if jt.2.val < 5 then 3460 else 3459))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3672 else (if jt.2.val < 2 then 3674 else 3677)) else (if jt.2.val < 4 then 3673 else (if jt.2.val < 5 then 3676 else 3675)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3601 else (if jt.2.val < 2 then 3605 else 3606)) else (if jt.2.val < 4 then 3602 else (if jt.2.val < 5 then 3604 else 3603))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3538 else (if jt.2.val < 2 then 3542 else 3543)) else (if jt.2.val < 4 then 3539 else (if jt.2.val < 5 then 3541 else 3540)))))

checked_coverage fastCoverage0224 pairing0224 template0224 witness0224

theorem coverage0224 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0224) (maskBits m))
    cores template0224 witness0224 := by
  rw [← coresFast_eq]
  exact fastCoverage0224

theorem coverageSize0224 : ∀ q : Pattern,
    (cores (witness0224 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0224 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0224
#print axioms coverageSize0224

noncomputable def pairing0225 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0225 : List (Fin 4935) := templateData0225

noncomputable def witness0225 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3505) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 2730) else (if t 3 = 0 then 2770 else if t 3 = 1 then 2768 else 2987)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 341) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 340) else (if t 3 = 0 then 144 else if t 3 = 1 then 140 else 892)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 868 else 406) else if t 2 = 1 then (if t 3 = 0 then 874 else if t 3 = 1 then 862 else 400) else (if t 3 = 0 then 2129 else if t 3 = 1 then 199 else 1501))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 439) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 438) else (if t 3 = 0 then 638 else if t 3 = 1 then 634 else 1135)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2470) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3080) else (if t 3 = 0 then 3091 else if t 3 = 1 then 3089 else 3094)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2956 else 2504) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3098 else 3100) else (if t 3 = 0 then 3500 else if t 3 = 1 then 3102 else 3104))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 2126) else if t 2 = 1 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 454) else (if t 3 = 0 then 652 else if t 3 = 1 then 650 else 1139)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2474) else if t 2 = 1 then (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3083) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3092 else 3096)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2957 else 2505) else if t 2 = 1 then (if t 3 = 0 then 3314 else if t 3 = 1 then 3099 else 3101) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3103 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3050 else (if jt.2.val < 2 then 3070 else 3072)) else (if jt.2.val < 4 then 3067 else (if jt.2.val < 5 then 3069 else 3068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3642 else (if jt.2.val < 2 then 3644 else 3647)) else (if jt.2.val < 4 then 3643 else (if jt.2.val < 5 then 3646 else 3645)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3048 else (if jt.2.val < 2 then 3088 else 3090)) else (if jt.2.val < 4 then 3085 else (if jt.2.val < 5 then 3087 else 3086))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3540 else (if jt.2.val < 2 then 3551 else 3543)) else (if jt.2.val < 4 then 3549 else (if jt.2.val < 5 then 3550 else 3538)))))

checked_coverage fastCoverage0225 pairing0225 template0225 witness0225

theorem coverage0225 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0225) (maskBits m))
    cores template0225 witness0225 := by
  rw [← coresFast_eq]
  exact fastCoverage0225

theorem coverageSize0225 : ∀ q : Pattern,
    (cores (witness0225 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0225 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0225
#print axioms coverageSize0225

noncomputable def pairing0226 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0226 : List (Fin 4935) := templateData0226

noncomputable def witness0226 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2817 else 2485) else if t 2 = 1 then (if t 3 = 0 then 2813 else if t 3 = 1 then 2809 else 2855) else (if t 3 = 0 then 3520 else if t 3 = 1 then 3338 else 3226)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2815 else 1416) else if t 2 = 1 then (if t 3 = 0 then 2811 else if t 3 = 1 then 2807 else 1414) else (if t 3 = 0 then 962 else if t 3 = 1 then 960 else 992)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1372 else 2119) else if t 2 = 1 then (if t 3 = 0 then 1371 else if t 3 = 1 then 1370 else 1777) else (if t 3 = 0 then 101 else if t 3 = 1 then 1001 else 1012))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2816 else 1586) else if t 2 = 1 then (if t 3 = 0 then 2812 else if t 3 = 1 then 2808 else 1584) else (if t 3 = 0 then 1040 else if t 3 = 1 then 1038 else 1073)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2814 else 2484) else if t 2 = 1 then (if t 3 = 0 then 2810 else if t 3 = 1 then 2806 else 2854) else (if t 3 = 0 then 2837 else if t 3 = 1 then 2835 else 2857)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2576 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2721 else if t 3 = 1 then 2859 else 2864) else (if t 3 = 0 then 2724 else if t 3 = 1 then 2862 else 2866))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 822 else 71) else if t 2 = 1 then (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 857) else (if t 3 = 0 then 2147 else if t 3 = 1 then 1817 else 1601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2487) else if t 2 = 1 then (if t 3 = 0 then 2828 else if t 3 = 1 then 2826 else 2856) else (if t 3 = 0 then 2841 else if t 3 = 1 then 2840 else 2858)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2578 else 3507) else if t 2 = 1 then (if t 3 = 0 then 2723 else if t 3 = 1 then 2861 else 2865) else (if t 3 = 0 then 2725 else if t 3 = 1 then 2863 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2805 else (if jt.2.val < 2 then 2825 else 2827)) else (if jt.2.val < 4 then 2822 else (if jt.2.val < 5 then 2824 else 2823))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3648 else (if jt.2.val < 2 then 3650 else 3653)) else (if jt.2.val < 4 then 3649 else (if jt.2.val < 5 then 3652 else 3651)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3603 else (if jt.2.val < 2 then 3614 else 3606)) else (if jt.2.val < 4 then 3612 else (if jt.2.val < 5 then 3613 else 3601))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2803 else (if jt.2.val < 2 then 2852 else 2853)) else (if jt.2.val < 4 then 2849 else (if jt.2.val < 5 then 2851 else 2850)))))

checked_coverage fastCoverage0226 pairing0226 template0226 witness0226

theorem coverage0226 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0226) (maskBits m))
    cores template0226 witness0226 := by
  rw [← coresFast_eq]
  exact fastCoverage0226

theorem coverageSize0226 : ∀ q : Pattern,
    (cores (witness0226 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0226 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0226
#print axioms coverageSize0226

noncomputable def pairing0227 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0227 : List (Fin 4935) := templateData0227

noncomputable def witness0227 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2598 else 2898) else if t 2 = 1 then (if t 3 = 0 then 2602 else if t 3 = 1 then 2594 else 2630) else (if t 3 = 0 then 3174 else if t 3 = 1 then 3172 else 3524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2596 else 1413) else if t 2 = 1 then (if t 3 = 0 then 2600 else if t 3 = 1 then 2592 else 1411) else (if t 3 = 0 then 143 else if t 3 = 1 then 139 else 171)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2104 else 1453) else if t 2 = 1 then (if t 3 = 0 then 2107 else if t 3 = 1 then 2101 else 1447) else (if t 3 = 0 then 904 else if t 3 = 1 then 193 else 195))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2597 else 1583) else if t 2 = 1 then (if t 3 = 0 then 2601 else if t 3 = 1 then 2593 else 1581) else (if t 3 = 0 then 637 else if t 3 = 1 then 633 else 663)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2595 else 2897) else if t 2 = 1 then (if t 3 = 0 then 2599 else if t 3 = 1 then 2591 else 2629) else (if t 3 = 0 then 2623 else if t 3 = 1 then 2620 else 2636)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2650 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2902 else if t 3 = 1 then 2640 else 2644) else (if t 3 = 0 then 2904 else if t 3 = 1 then 2642 else 2646))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 241 else 920) else if t 2 = 1 then (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 273) else (if t 3 = 0 then 1464 else if t 3 = 1 then 1463 else 2171)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2899) else if t 2 = 1 then (if t 3 = 0 then 2614 else if t 3 = 1 then 2611 else 2634) else (if t 3 = 0 then 2627 else if t 3 = 1 then 2625 else 2638)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2651 else 3184) else if t 2 = 1 then (if t 3 = 0 then 2903 else if t 3 = 1 then 2641 else 2645) else (if t 3 = 0 then 2905 else if t 3 = 1 then 2643 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2590 else (if jt.2.val < 2 then 2610 else 2612)) else (if jt.2.val < 4 then 2607 else (if jt.2.val < 5 then 2609 else 2608))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3678 else (if jt.2.val < 2 then 3680 else 3683)) else (if jt.2.val < 4 then 3679 else (if jt.2.val < 5 then 3682 else 3681)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3086 else (if jt.2.val < 2 then 3173 else 3090)) else (if jt.2.val < 4 then 3169 else (if jt.2.val < 5 then 3170 else 3048))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2850 else (if jt.2.val < 2 then 2896 else 2853)) else (if jt.2.val < 4 then 2888 else (if jt.2.val < 5 then 2889 else 2803)))))

checked_coverage fastCoverage0227 pairing0227 template0227 witness0227

theorem coverage0227 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0227) (maskBits m))
    cores template0227 witness0227 := by
  rw [← coresFast_eq]
  exact fastCoverage0227

theorem coverageSize0227 : ∀ q : Pattern,
    (cores (witness0227 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0227 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0227
#print axioms coverageSize0227

noncomputable def pairing0228 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0228 : List (Fin 4935) := templateData0228

noncomputable def witness0228 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 579 else 1116) else if t 2 = 1 then (if t 3 = 0 then 581 else if t 3 = 1 then 577 else 1114) else (if t 3 = 0 then 1549 else if t 3 = 1 then 595 else 2150)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 574 else if t 3 = 1 then 552 else 554) else if t 2 = 1 then (if t 3 = 0 then 566 else if t 3 = 1 then 532 else 537) else (if t 3 = 0 then 1108 else if t 3 = 1 then 535 else 539)) else (if t 2 = 0 then (if t 3 = 0 then 3499 else if t 3 = 1 then 3209 else 3210) else if t 2 = 1 then (if t 3 = 0 then 2756 else if t 3 = 1 then 2747 else 2750) else (if t 3 = 0 then 2983 else if t 3 = 1 then 2749 else 2751))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 578 else 1115) else if t 2 = 1 then (if t 3 = 0 then 580 else if t 3 = 1 then 576 else 1113) else (if t 3 = 0 then 1548 else if t 3 = 1 then 594 else 2148)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 570 else if t 3 = 1 then 544 else 548) else if t 2 = 1 then (if t 3 = 0 then 556 else if t 3 = 1 then 515 else 524) else (if t 3 = 0 then 1104 else if t 3 = 1 then 520 else 528)) else (if t 2 = 0 then (if t 3 = 0 then 571 else if t 3 = 1 then 545 else 549) else if t 2 = 1 then (if t 3 = 0 then 557 else if t 3 = 1 then 516 else 525) else (if t 3 = 0 then 1105 else if t 3 = 1 then 521 else 529))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 1545 else 2986) else if t 2 = 1 then (if t 3 = 0 then 590 else if t 3 = 1 then 588 else 1119) else (if t 3 = 0 then 3216 else if t 3 = 1 then 600 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2115 else if t 3 = 1 then 1531 else 1535) else if t 2 = 1 then (if t 3 = 0 then 558 else if t 3 = 1 then 517 else 526) else (if t 3 = 0 then 1106 else if t 3 = 1 then 522 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 2116 else if t 3 = 1 then 1532 else 1536) else if t 2 = 1 then (if t 3 = 0 then 559 else if t 3 = 1 then 518 else 527) else (if t 3 = 0 then 1107 else if t 3 = 1 then 523 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2590 else (if jt.2.val < 2 then 2746 else 2612)) else (if jt.2.val < 4 then 2745 else (if jt.2.val < 5 then 2748 else 2608))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3675 else (if jt.2.val < 2 then 3686 else 3677)) else (if jt.2.val < 4 then 3684 else (if jt.2.val < 5 then 3685 else 3672)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1527 else (if jt.2.val < 2 then 1529 else 1534)) else (if jt.2.val < 4 then 1528 else (if jt.2.val < 5 then 1533 else 1530))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1095 else (if jt.2.val < 2 then 1097 else 1103)) else (if jt.2.val < 4 then 1096 else (if jt.2.val < 5 then 1102 else 1101)))))

checked_coverage fastCoverage0228 pairing0228 template0228 witness0228

theorem coverage0228 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0228) (maskBits m))
    cores template0228 witness0228 := by
  rw [← coresFast_eq]
  exact fastCoverage0228

theorem coverageSize0228 : ∀ q : Pattern,
    (cores (witness0228 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0228 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0228
#print axioms coverageSize0228

noncomputable def pairing0229 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0229 : List (Fin 4935) := templateData0229

noncomputable def witness0229 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1214 else 506) else if t 2 = 1 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1210 else 502) else (if t 3 = 0 then 2161 else if t 3 = 1 then 694 else 1526)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1205 else if t 3 = 1 then 1187 else 1188) else if t 2 = 1 then (if t 3 = 0 then 1201 else if t 3 = 1 then 1167 else 1170) else (if t 3 = 0 then 757 else if t 3 = 1 then 1172 else 1174)) else (if t 2 = 0 then (if t 3 = 0 then 3152 else if t 3 = 1 then 3329 else 3514) else if t 2 = 1 then (if t 3 = 0 then 3002 else if t 3 = 1 then 2993 else 2995) else (if t 3 = 0 then 2795 else if t 3 = 1 then 2996 else 2997))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1212 else 504) else if t 2 = 1 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1206 else 498) else (if t 3 = 0 then 2160 else if t 3 = 1 then 690 else 1524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1203 else if t 3 = 1 then 1179 else 1181) else if t 2 = 1 then (if t 3 = 0 then 1197 else if t 3 = 1 then 1151 else 1155) else (if t 3 = 0 then 751 else if t 3 = 1 then 1159 else 1163)) else (if t 2 = 0 then (if t 3 = 0 then 1204 else if t 3 = 1 then 1180 else 1182) else if t 2 = 1 then (if t 3 = 0 then 1198 else if t 3 = 1 then 1152 else 1156) else (if t 3 = 0 then 752 else if t 3 = 1 then 1160 else 1164))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1374 else 2744) else if t 2 = 1 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1208 else 500) else (if t 3 = 0 then 3523 else if t 3 = 1 then 692 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1430 else if t 3 = 1 then 1795 else 2136) else if t 2 = 1 then (if t 3 = 0 then 1199 else if t 3 = 1 then 1153 else 1157) else (if t 3 = 0 then 753 else if t 3 = 1 then 1161 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 1431 else if t 3 = 1 then 1796 else 2137) else if t 2 = 1 then (if t 3 = 0 then 1200 else if t 3 = 1 then 1154 else 1158) else (if t 3 = 0 then 754 else if t 3 = 1 then 1162 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2805 else (if jt.2.val < 2 then 2992 else 2827)) else (if jt.2.val < 4 then 2991 else (if jt.2.val < 5 then 2994 else 2823))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3645 else (if jt.2.val < 2 then 3665 else 3647)) else (if jt.2.val < 4 then 3663 else (if jt.2.val < 5 then 3664 else 3642)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2346 else (if jt.2.val < 2 then 2348 else 2351)) else (if jt.2.val < 4 then 2347 else (if jt.2.val < 5 then 2350 else 2349))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1101 else (if jt.2.val < 2 then 1195 else 1103)) else (if jt.2.val < 4 then 1194 else (if jt.2.val < 5 then 1196 else 1095)))))

checked_coverage fastCoverage0229 pairing0229 template0229 witness0229

theorem coverage0229 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0229) (maskBits m))
    cores template0229 witness0229 := by
  rw [← coresFast_eq]
  exact fastCoverage0229

theorem coverageSize0229 : ∀ q : Pattern,
    (cores (witness0229 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0229 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0229
#print axioms coverageSize0229

noncomputable def pairing0230 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0230 : List (Fin 4935) := templateData0230

noncomputable def witness0230 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1682 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1678 else 1853) else (if t 3 = 0 then 786 else if t 3 = 1 then 1080 else 1094)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1669 else 1670) else if t 2 = 1 then (if t 3 = 0 then 1660 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 741 else if t 3 = 1 then 1647 else 1651)) else (if t 2 = 0 then (if t 3 = 0 then 2882 else if t 3 = 1 then 2545 else 2547) else if t 2 = 1 then (if t 3 = 0 then 2689 else if t 3 = 1 then 3232 else 3235) else (if t 3 = 0 then 3522 else if t 3 = 1 then 3234 else 3236))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1681 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1677 else 1851) else (if t 3 = 0 then 785 else if t 3 = 1 then 1079 else 1092)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1665 else 1667) else if t 2 = 1 then (if t 3 = 0 then 1656 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 734 else if t 3 = 1 then 1632 else 1640)) else (if t 2 = 0 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1666 else 1668) else if t 2 = 1 then (if t 3 = 0 then 1657 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 735 else if t 3 = 1 then 1633 else 1641))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 200 else 3525) else if t 2 = 1 then (if t 3 = 0 then 401 else if t 3 = 1 then 863 else 876) else (if t 3 = 0 then 2801 else if t 3 = 1 then 1689 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 894 else if t 3 = 1 then 150 else 154) else if t 2 = 1 then (if t 3 = 0 then 350 else if t 3 = 1 then 1630 else 1638) else (if t 3 = 0 then 2157 else if t 3 = 1 then 1634 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 895 else if t 3 = 1 then 151 else 155) else if t 2 = 1 then (if t 3 = 0 then 351 else if t 3 = 1 then 1631 else 1639) else (if t 3 = 0 then 2158 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3050 else (if jt.2.val < 2 then 3231 else 3072)) else (if jt.2.val < 4 then 3230 else (if jt.2.val < 5 then 3233 else 3068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3651 else (if jt.2.val < 2 then 3668 else 3653)) else (if jt.2.val < 4 then 3666 else (if jt.2.val < 5 then 3667 else 3648)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1530 else (if jt.2.val < 2 then 1663 else 1534)) else (if jt.2.val < 4 then 1662 else (if jt.2.val < 5 then 1664 else 1527))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2256 else (if jt.2.val < 2 then 2258 else 2261)) else (if jt.2.val < 4 then 2257 else (if jt.2.val < 5 then 2260 else 2259)))))

checked_coverage fastCoverage0230 pairing0230 template0230 witness0230

theorem coverage0230 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0230) (maskBits m))
    cores template0230 witness0230 := by
  rw [← coresFast_eq]
  exact fastCoverage0230

theorem coverageSize0230 : ∀ q : Pattern,
    (cores (witness0230 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0230 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0230
#print axioms coverageSize0230

noncomputable def pairing0231 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0231 : List (Fin 4935) := templateData0231

noncomputable def witness0231 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2225 else 1622) else if t 2 = 1 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2222 else 1616) else (if t 3 = 0 then 1148 else if t 3 = 1 then 688 else 689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2207 else 1892) else if t 2 = 1 then (if t 3 = 0 then 2213 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 742 else if t 3 = 1 then 2196 else 2200)) else (if t 2 = 0 then (if t 3 = 0 then 2706 else if t 3 = 1 then 2939 else 2940) else if t 2 = 1 then (if t 3 = 0 then 2690 else if t 3 = 1 then 3528 else 3531) else (if t 3 = 0 then 3192 else if t 3 = 1 then 3530 else 3532))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2223 else 1620) else if t 2 = 1 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2220 else 1614) else (if t 3 = 0 then 1146 else if t 3 = 1 then 684 else 686)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2205 else 1889) else if t 2 = 1 then (if t 3 = 0 then 2211 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 736 else if t 3 = 1 then 2181 else 2189)) else (if t 2 = 0 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2206 else 1890) else if t 2 = 1 then (if t 3 = 0 then 2212 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 737 else if t 3 = 1 then 2182 else 2190))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 306 else 3229) else if t 2 = 1 then (if t 3 = 0 then 930 else if t 3 = 1 then 294 else 296) else (if t 3 = 0 then 2990 else if t 3 = 1 then 1473 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 377 else if t 3 = 1 then 973 else 975) else if t 2 = 1 then (if t 3 = 0 then 352 else if t 3 = 1 then 2179 else 2187) else (if t 3 = 0 then 1487 else if t 3 = 1 then 2183 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 378 else if t 3 = 1 then 974 else 976) else if t 2 = 1 then (if t 3 = 0 then 353 else if t 3 = 1 then 2180 else 2188) else (if t 3 = 0 then 1488 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3441 else (if jt.2.val < 2 then 3527 else 3463)) else (if jt.2.val < 4 then 3526 else (if jt.2.val < 5 then 3529 else 3459))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3681 else (if jt.2.val < 2 then 3689 else 3683)) else (if jt.2.val < 4 then 3687 else (if jt.2.val < 5 then 3688 else 3678)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2349 else (if jt.2.val < 2 then 2353 else 2351)) else (if jt.2.val < 4 then 2352 else (if jt.2.val < 5 then 2354 else 2346))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2259 else (if jt.2.val < 2 then 2263 else 2261)) else (if jt.2.val < 4 then 2262 else (if jt.2.val < 5 then 2264 else 2256)))))

checked_coverage fastCoverage0231 pairing0231 template0231 witness0231

theorem coverage0231 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0231) (maskBits m))
    cores template0231 witness0231 := by
  rw [← coresFast_eq]
  exact fastCoverage0231

theorem coverageSize0231 : ∀ q : Pattern,
    (cores (witness0231 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0231 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0231
#print axioms coverageSize0231

noncomputable def pairing0232 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0232 : List (Fin 4935) := templateData0232

noncomputable def witness0232 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3340) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2973) else (if t 3 = 0 then 2732 else if t 3 = 1 then 2731 else 2738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 964) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 963) else (if t 3 = 0 then 344 else if t 3 = 1 then 342 else 373)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 291 else 305) else if t 2 = 1 then (if t 3 = 0 then 292 else if t 3 = 1 then 290 else 304) else (if t 3 = 0 then 1790 else if t 3 = 1 then 928 else 2140))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 1042) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 1041) else (if t 3 = 0 then 442 else if t 3 = 1 then 440 else 472)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2838) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3472) else (if t 3 = 0 then 3082 else if t 3 = 1 then 3479 else 3486)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2572 else 2579) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3488 else 3490) else (if t 3 = 0 then 3315 else if t 3 = 1 then 3492 else 3494))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1818) else if t 2 = 1 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 1056) else (if t 3 = 0 then 456 else if t 3 = 1 then 455 else 479)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2842) else if t 2 = 1 then (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3473) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3480 else 3487)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2574 else 2580) else if t 2 = 1 then (if t 3 = 0 then 3164 else if t 3 = 1 then 3489 else 3491) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3493 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3441 else (if jt.2.val < 2 then 3461 else 3463)) else (if jt.2.val < 4 then 3458 else (if jt.2.val < 5 then 3460 else 3459))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3672 else (if jt.2.val < 2 then 3674 else 3677)) else (if jt.2.val < 4 then 3673 else (if jt.2.val < 5 then 3676 else 3675)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3439 else (if jt.2.val < 2 then 3477 else 3478)) else (if jt.2.val < 4 then 3474 else (if jt.2.val < 5 then 3476 else 3475))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3627 else (if jt.2.val < 2 then 3631 else 3632)) else (if jt.2.val < 4 then 3628 else (if jt.2.val < 5 then 3630 else 3629)))))

checked_coverage fastCoverage0232 pairing0232 template0232 witness0232

theorem coverage0232 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0232) (maskBits m))
    cores template0232 witness0232 := by
  rw [← coresFast_eq]
  exact fastCoverage0232

theorem coverageSize0232 : ∀ q : Pattern,
    (cores (witness0232 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0232 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0232
#print axioms coverageSize0232

noncomputable def pairing0233 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0233 : List (Fin 4935) := templateData0233

noncomputable def witness0233 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3520) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2972) else (if t 3 = 0 then 2770 else if t 3 = 1 then 2769 else 2776)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 962) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 961) else (if t 3 = 0 then 144 else if t 3 = 1 then 142 else 172)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 87 else 101) else if t 2 = 1 then (if t 3 = 0 then 88 else if t 3 = 1 then 86 else 100) else (if t 3 = 0 then 2129 else if t 3 = 1 then 898 else 1807))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 1040) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 1039) else (if t 3 = 0 then 638 else if t 3 = 1 then 636 else 664)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2837) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3276) else (if t 3 = 0 then 3091 else if t 3 = 1 then 3291 else 3293)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2717 else 2724) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3295 else 3297) else (if t 3 = 0 then 3500 else if t 3 = 1 then 3299 else 3301))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 2147) else if t 2 = 1 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 1055) else (if t 3 = 0 then 652 else if t 3 = 1 then 651 else 671)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2841) else if t 2 = 1 then (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3279) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3292 else 3294)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2719 else 2725) else if t 2 = 1 then (if t 3 = 0 then 3166 else if t 3 = 1 then 3296 else 3298) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3300 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3246 else (if jt.2.val < 2 then 3266 else 3268)) else (if jt.2.val < 4 then 3263 else (if jt.2.val < 5 then 3265 else 3264))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3636 else (if jt.2.val < 2 then 3638 else 3641)) else (if jt.2.val < 4 then 3637 else (if jt.2.val < 5 then 3640 else 3639)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3244 else (if jt.2.val < 2 then 3289 else 3290)) else (if jt.2.val < 4 then 3286 else (if jt.2.val < 5 then 3288 else 3287))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3629 else (if jt.2.val < 2 then 3635 else 3632)) else (if jt.2.val < 4 then 3633 else (if jt.2.val < 5 then 3634 else 3627)))))

checked_coverage fastCoverage0233 pairing0233 template0233 witness0233

theorem coverage0233 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0233) (maskBits m))
    cores template0233 witness0233 := by
  rw [← coresFast_eq]
  exact fastCoverage0233

theorem coverageSize0233 : ∀ q : Pattern,
    (cores (witness0233 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0233 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0233
#print axioms coverageSize0233

noncomputable def pairing0234 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0234 : List (Fin 4935) := templateData0234

noncomputable def witness0234 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2450 else 2485) else if t 2 = 1 then (if t 3 = 0 then 2446 else if t 3 = 1 then 2442 else 2482) else (if t 3 = 0 then 3505 else if t 3 = 1 then 3203 else 3344)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2448 else 1416) else if t 2 = 1 then (if t 3 = 0 then 2444 else if t 3 = 1 then 2440 else 1412) else (if t 3 = 0 then 341 else if t 3 = 1 then 339 else 372)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1762 else 2119) else if t 2 = 1 then (if t 3 = 0 then 1756 else if t 3 = 1 then 1753 else 1450) else (if t 3 = 0 then 406 else if t 3 = 1 then 394 else 396))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2449 else 1586) else if t 2 = 1 then (if t 3 = 0 then 2445 else if t 3 = 1 then 2441 else 1582) else (if t 3 = 0 then 439 else if t 3 = 1 then 437 else 471)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2447 else 2484) else if t 2 = 1 then (if t 3 = 0 then 2443 else if t 3 = 1 then 2439 else 2481) else (if t 3 = 0 then 2470 else if t 3 = 1 then 2468 else 2488)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2883 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2502 else if t 3 = 1 then 2492 else 2496) else (if t 3 = 0 then 2504 else if t 3 = 1 then 2494 else 2498))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 35 else 71) else if t 2 = 1 then (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 69) else (if t 3 = 0 then 2126 else if t 3 = 1 then 1511 else 1850)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2487) else if t 2 = 1 then (if t 3 = 0 then 2461 else if t 3 = 1 then 2459 else 2486) else (if t 3 = 0 then 2474 else if t 3 = 1 then 2473 else 2490)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2885 else 3507) else if t 2 = 1 then (if t 3 = 0 then 2503 else if t 3 = 1 then 2493 else 2497) else (if t 3 = 0 then 2505 else if t 3 = 1 then 2495 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2438 else (if jt.2.val < 2 then 2458 else 2460)) else (if jt.2.val < 4 then 2455 else (if jt.2.val < 5 then 2457 else 2456))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3654 else (if jt.2.val < 2 then 3656 else 3659)) else (if jt.2.val < 4 then 3655 else (if jt.2.val < 5 then 3658 else 3657)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3475 else (if jt.2.val < 2 then 3504 else 3478)) else (if jt.2.val < 4 then 3502 else (if jt.2.val < 5 then 3503 else 3439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2436 else (if jt.2.val < 2 then 2480 else 2483)) else (if jt.2.val < 4 then 2477 else (if jt.2.val < 5 then 2479 else 2478)))))

checked_coverage fastCoverage0234 pairing0234 template0234 witness0234

theorem coverage0234 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0234) (maskBits m))
    cores template0234 witness0234 := by
  rw [← coresFast_eq]
  exact fastCoverage0234

theorem coverageSize0234 : ∀ q : Pattern,
    (cores (witness0234 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0234 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0234
#print axioms coverageSize0234

noncomputable def pairing0235 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0235 : List (Fin 4935) := templateData0235

noncomputable def witness0235 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2602 else 2633) else if t 2 = 1 then (if t 3 = 0 then 2598 else if t 3 = 1 then 2594 else 2630) else (if t 3 = 0 then 3320 else if t 3 = 1 then 3172 else 3524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2600 else 1415) else if t 2 = 1 then (if t 3 = 0 then 2596 else if t 3 = 1 then 2592 else 1411) else (if t 3 = 0 then 141 else if t 3 = 1 then 139 else 171)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2107 else 1780) else if t 2 = 1 then (if t 3 = 0 then 2104 else if t 3 = 1 then 2101 else 1447) else (if t 3 = 0 then 205 else if t 3 = 1 then 193 else 195))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2601 else 1585) else if t 2 = 1 then (if t 3 = 0 then 2597 else if t 3 = 1 then 2593 else 1581) else (if t 3 = 0 then 635 else if t 3 = 1 then 633 else 663)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2599 else 2632) else if t 2 = 1 then (if t 3 = 0 then 2595 else if t 3 = 1 then 2591 else 2629) else (if t 3 = 0 then 2622 else if t 3 = 1 then 2620 else 2636)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2902 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2650 else if t 3 = 1 then 2640 else 2644) else (if t 3 = 0 then 2652 else if t 3 = 1 then 2642 else 2646))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 243 else 275) else if t 2 = 1 then (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 273) else (if t 3 = 0 then 1787 else if t 3 = 1 then 1463 else 2171)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2635) else if t 2 = 1 then (if t 3 = 0 then 2613 else if t 3 = 1 then 2611 else 2634) else (if t 3 = 0 then 2626 else if t 3 = 1 then 2625 else 2638)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2903 else 3322) else if t 2 = 1 then (if t 3 = 0 then 2651 else if t 3 = 1 then 2641 else 2645) else (if t 3 = 0 then 2653 else if t 3 = 1 then 2643 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2590 else (if jt.2.val < 2 then 2610 else 2612)) else (if jt.2.val < 4 then 2607 else (if jt.2.val < 5 then 2609 else 2608))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3678 else (if jt.2.val < 2 then 3680 else 3683)) else (if jt.2.val < 4 then 3679 else (if jt.2.val < 5 then 3682 else 3681)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3287 else (if jt.2.val < 2 then 3319 else 3290)) else (if jt.2.val < 4 then 3317 else (if jt.2.val < 5 then 3318 else 3244))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2478 else (if jt.2.val < 2 then 2631 else 2483)) else (if jt.2.val < 4 then 2587 else (if jt.2.val < 5 then 2588 else 2436)))))

checked_coverage fastCoverage0235 pairing0235 template0235 witness0235

theorem coverage0235 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0235) (maskBits m))
    cores template0235 witness0235 := by
  rw [← coresFast_eq]
  exact fastCoverage0235

theorem coverageSize0235 : ∀ q : Pattern,
    (cores (witness0235 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0235 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0235
#print axioms coverageSize0235

noncomputable def pairing0236 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0236 : List (Fin 4935) := templateData0236

noncomputable def witness0236 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 579 else 597) else if t 2 = 1 then (if t 3 = 0 then 581 else if t 3 = 1 then 577 else 595) else (if t 3 = 0 then 1837 else if t 3 = 1 then 1114 else 2150)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 574 else if t 3 = 1 then 552 else 553) else if t 2 = 1 then (if t 3 = 0 then 566 else if t 3 = 1 then 532 else 535) else (if t 3 = 0 then 568 else if t 3 = 1 then 537 else 539)) else (if t 2 = 0 then (if t 3 = 0 then 3499 else if t 3 = 1 then 3209 else 3342) else if t 2 = 1 then (if t 3 = 0 then 2756 else if t 3 = 1 then 2747 else 2749) else (if t 3 = 0 then 2757 else if t 3 = 1 then 2750 else 2751))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 578 else 596) else if t 2 = 1 then (if t 3 = 0 then 580 else if t 3 = 1 then 576 else 594) else (if t 3 = 0 then 1836 else if t 3 = 1 then 1113 else 2148)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 570 else if t 3 = 1 then 544 else 546) else if t 2 = 1 then (if t 3 = 0 then 556 else if t 3 = 1 then 515 else 520) else (if t 3 = 0 then 562 else if t 3 = 1 then 524 else 528)) else (if t 2 = 0 then (if t 3 = 0 then 571 else if t 3 = 1 then 545 else 547) else if t 2 = 1 then (if t 3 = 0 then 557 else if t 3 = 1 then 516 else 521) else (if t 3 = 0 then 563 else if t 3 = 1 then 525 else 529))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 1545 else 2763) else if t 2 = 1 then (if t 3 = 0 then 590 else if t 3 = 1 then 588 else 600) else (if t 3 = 0 then 3343 else if t 3 = 1 then 1119 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2115 else if t 3 = 1 then 1531 else 1833) else if t 2 = 1 then (if t 3 = 0 then 558 else if t 3 = 1 then 517 else 522) else (if t 3 = 0 then 564 else if t 3 = 1 then 526 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 2116 else if t 3 = 1 then 1532 else 1834) else if t 2 = 1 then (if t 3 = 0 then 559 else if t 3 = 1 then 518 else 523) else (if t 3 = 0 then 565 else if t 3 = 1 then 527 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2590 else (if jt.2.val < 2 then 2746 else 2612)) else (if jt.2.val < 4 then 2745 else (if jt.2.val < 5 then 2748 else 2608))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3675 else (if jt.2.val < 2 then 3686 else 3677)) else (if jt.2.val < 4 then 3684 else (if jt.2.val < 5 then 3685 else 3672)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1827 else (if jt.2.val < 2 then 1829 else 1832)) else (if jt.2.val < 4 then 1828 else (if jt.2.val < 5 then 1831 else 1830))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 510 else (if jt.2.val < 2 then 512 else 561)) else (if jt.2.val < 4 then 511 else (if jt.2.val < 5 then 560 else 519)))))

checked_coverage fastCoverage0236 pairing0236 template0236 witness0236

theorem coverage0236 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0236) (maskBits m))
    cores template0236 witness0236 := by
  rw [← coresFast_eq]
  exact fastCoverage0236

theorem coverageSize0236 : ∀ q : Pattern,
    (cores (witness0236 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0236 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0236
#print axioms coverageSize0236

noncomputable def pairing0237 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0237 : List (Fin 4935) := templateData0237

noncomputable def witness0237 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 768 else 786) else if t 2 = 1 then (if t 3 = 0 then 770 else if t 3 = 1 then 766 else 784) else (if t 3 = 0 then 2161 else if t 3 = 1 then 1144 else 1826)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 763 else if t 3 = 1 then 740 else 741) else if t 2 = 1 then (if t 3 = 0 then 755 else if t 3 = 1 then 720 else 723) else (if t 3 = 0 then 757 else if t 3 = 1 then 725 else 727)) else (if t 2 = 0 then (if t 3 = 0 then 3312 else if t 3 = 1 then 3191 else 3522) else if t 2 = 1 then (if t 3 = 0 then 2794 else if t 3 = 1 then 2785 else 2787) else (if t 3 = 0 then 2795 else if t 3 = 1 then 2788 else 2789))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 767 else 785) else if t 2 = 1 then (if t 3 = 0 then 769 else if t 3 = 1 then 765 else 783) else (if t 3 = 0 then 2160 else if t 3 = 1 then 1140 else 1824)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 759 else if t 3 = 1 then 732 else 734) else if t 2 = 1 then (if t 3 = 0 then 747 else if t 3 = 1 then 704 else 708) else (if t 3 = 0 then 751 else if t 3 = 1 then 712 else 716)) else (if t 2 = 0 then (if t 3 = 0 then 760 else if t 3 = 1 then 733 else 735) else if t 2 = 1 then (if t 3 = 0 then 748 else if t 3 = 1 then 705 else 709) else (if t 3 = 0 then 752 else if t 3 = 1 then 713 else 717))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1497 else 2801) else if t 2 = 1 then (if t 3 = 0 then 779 else if t 3 = 1 then 777 else 789) else (if t 3 = 0 then 3523 else if t 3 = 1 then 1142 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1773 else if t 3 = 1 then 1483 else 2157) else if t 2 = 1 then (if t 3 = 0 then 749 else if t 3 = 1 then 706 else 710) else (if t 3 = 0 then 753 else if t 3 = 1 then 714 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 1774 else if t 3 = 1 then 1484 else 2158) else if t 2 = 1 then (if t 3 = 0 then 750 else if t 3 = 1 then 707 else 711) else (if t 3 = 0 then 754 else if t 3 = 1 then 715 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2438 else (if jt.2.val < 2 then 2784 else 2460)) else (if jt.2.val < 4 then 2783 else (if jt.2.val < 5 then 2786 else 2456))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3639 else (if jt.2.val < 2 then 3662 else 3641)) else (if jt.2.val < 4 then 3660 else (if jt.2.val < 5 then 3661 else 3636)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2151 else (if jt.2.val < 2 then 2153 else 2156)) else (if jt.2.val < 4 then 2152 else (if jt.2.val < 5 then 2155 else 2154))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 519 else (if jt.2.val < 2 then 745 else 561)) else (if jt.2.val < 4 then 744 else (if jt.2.val < 5 then 746 else 510)))))

checked_coverage fastCoverage0237 pairing0237 template0237 witness0237

theorem coverage0237 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0237) (maskBits m))
    cores template0237 witness0237 := by
  rw [← coresFast_eq]
  exact fastCoverage0237

theorem coverageSize0237 : ∀ q : Pattern,
    (cores (witness0237 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0237 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0237
#print axioms coverageSize0237

noncomputable def pairing0238 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0238 : List (Fin 4935) := templateData0238

noncomputable def witness0238 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1912 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1907 else 1619) else (if t 3 = 0 then 506 else if t 3 = 1 then 496 else 497)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1901 else 1670) else if t 2 = 1 then (if t 3 = 0 then 1891 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 1188 else if t 3 = 1 then 1878 else 1882)) else (if t 2 = 0 then (if t 3 = 0 then 2561 else if t 3 = 1 then 2546 else 2547) else if t 2 = 1 then (if t 3 = 0 then 2938 else if t 3 = 1 then 3348 else 3351) else (if t 3 = 0 then 3514 else if t 3 = 1 then 3350 else 3352))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1911 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1905 else 1617) else (if t 3 = 0 then 504 else if t 3 = 1 then 492 else 494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1899 else 1667) else if t 2 = 1 then (if t 3 = 0 then 1887 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 1181 else if t 3 = 1 then 1863 else 1871)) else (if t 2 = 0 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1900 else 1668) else if t 2 = 1 then (if t 3 = 0 then 1888 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 1182 else if t 3 = 1 then 1864 else 1872))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 899 else 3525) else if t 2 = 1 then (if t 3 = 0 then 102 else if t 3 = 1 then 90 else 92) else (if t 3 = 0 then 2744 else if t 3 = 1 then 1521 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 176 else if t 3 = 1 then 152 else 154) else if t 2 = 1 then (if t 3 = 0 then 971 else if t 3 = 1 then 1861 else 1869) else (if t 3 = 0 then 2136 else if t 3 = 1 then 1865 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 177 else if t 3 = 1 then 153 else 155) else if t 2 = 1 then (if t 3 = 0 then 972 else if t 3 = 1 then 1862 else 1870) else (if t 3 = 0 then 2137 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3246 else (if jt.2.val < 2 then 3347 else 3268)) else (if jt.2.val < 4 then 3346 else (if jt.2.val < 5 then 3349 else 3264))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3657 else (if jt.2.val < 2 then 3671 else 3659)) else (if jt.2.val < 4 then 3669 else (if jt.2.val < 5 then 3670 else 3654)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1830 else (if jt.2.val < 2 then 1897 else 1832)) else (if jt.2.val < 4 then 1896 else (if jt.2.val < 5 then 1898 else 1827))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2367 else (if jt.2.val < 2 then 2369 else 2372)) else (if jt.2.val < 4 then 2368 else (if jt.2.val < 5 then 2371 else 2370)))))

checked_coverage fastCoverage0238 pairing0238 template0238 witness0238

theorem coverage0238 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0238) (maskBits m))
    cores template0238 witness0238 := by
  rw [← coresFast_eq]
  exact fastCoverage0238

theorem coverageSize0238 : ∀ q : Pattern,
    (cores (witness0238 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0238 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0238
#print axioms coverageSize0238

noncomputable def pairing0239 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0239 : List (Fin 4935) := templateData0239

noncomputable def witness0239 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2228 else 1856) else if t 2 = 1 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2222 else 1616) else (if t 3 = 0 then 698 else if t 3 = 1 then 688 else 689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2213 else 1661) else if t 2 = 1 then (if t 3 = 0 then 2207 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 1189 else if t 3 = 1 then 2196 else 2200)) else (if t 2 = 0 then (if t 3 = 0 then 2706 else if t 3 = 1 then 2690 else 2691) else if t 2 = 1 then (if t 3 = 0 then 2939 else if t 3 = 1 then 3528 else 3531) else (if t 3 = 0 then 3330 else if t 3 = 1 then 3530 else 3532))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2226 else 1854) else if t 2 = 1 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2220 else 1614) else (if t 3 = 0 then 696 else if t 3 = 1 then 684 else 686)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2211 else 1658) else if t 2 = 1 then (if t 3 = 0 then 2205 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 1183 else if t 3 = 1 then 2181 else 2189)) else (if t 2 = 0 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2212 else 1659) else if t 2 = 1 then (if t 3 = 0 then 2206 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 1184 else if t 3 = 1 then 2182 else 2190))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 930 else 3345) else if t 2 = 1 then (if t 3 = 0 then 306 else if t 3 = 1 then 294 else 296) else (if t 3 = 0 then 2782 else if t 3 = 1 then 1473 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 377 else if t 3 = 1 then 352 else 354) else if t 2 = 1 then (if t 3 = 0 then 973 else if t 3 = 1 then 2179 else 2187) else (if t 3 = 0 then 1799 else if t 3 = 1 then 2183 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 378 else if t 3 = 1 then 353 else 355) else if t 2 = 1 then (if t 3 = 0 then 974 else if t 3 = 1 then 2180 else 2188) else (if t 3 = 0 then 1800 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3441 else (if jt.2.val < 2 then 3527 else 3463)) else (if jt.2.val < 4 then 3526 else (if jt.2.val < 5 then 3529 else 3459))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3681 else (if jt.2.val < 2 then 3689 else 3683)) else (if jt.2.val < 4 then 3687 else (if jt.2.val < 5 then 3688 else 3678)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2154 else (if jt.2.val < 2 then 2209 else 2156)) else (if jt.2.val < 4 then 2208 else (if jt.2.val < 5 then 2210 else 2151))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2370 else (if jt.2.val < 2 then 2374 else 2372)) else (if jt.2.val < 4 then 2373 else (if jt.2.val < 5 then 2375 else 2367)))))

checked_coverage fastCoverage0239 pairing0239 template0239 witness0239

theorem coverage0239 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0239) (maskBits m))
    cores template0239 witness0239 := by
  rw [← coresFast_eq]
  exact fastCoverage0239

theorem coverageSize0239 : ∀ q : Pattern,
    (cores (witness0239 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0239 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0239
#print axioms coverageSize0239

end Crown.CertificateData
