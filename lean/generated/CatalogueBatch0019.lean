import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0018

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0720 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0720 : List (Fin 4935) := templateData0720

noncomputable def witness0720 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3174) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2769) else (if t 3 = 0 then 2974 else if t 3 = 1 then 2972 else 2776)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 143) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 142) else (if t 3 = 0 then 965 else if t 3 = 1 then 961 else 172)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1879 else 1538) else if t 2 = 1 then (if t 3 = 0 then 1881 else if t 3 = 1 then 1877 else 158) else (if t 3 = 0 then 980 else if t 3 = 1 then 978 else 179))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 637) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 636) else (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 664)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2623) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3291) else (if t 3 = 0 then 3278 else if t 3 = 1 then 3276 else 3293)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2627) else if t 2 = 1 then (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3292) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3279 else 3294))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 774 else 1147) else if t 2 = 1 then (if t 3 = 0 then 775 else if t 3 = 1 then 773 else 1141) else (if t 3 = 0 then 1550 else if t 3 = 1 then 787 else 1825)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2717 else 2904) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3295 else 3299) else (if t 3 = 0 then 3167 else if t 3 = 1 then 3297 else 3301)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2719 else 2905) else if t 2 = 1 then (if t 3 = 0 then 3166 else if t 3 = 1 then 3296 else 3300) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3298 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4845 else (if jt.2.val < 2 then 4847 else 4850)) else (if jt.2.val < 4 then 4846 else (if jt.2.val < 5 then 4849 else 4848))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4369 else (if jt.2.val < 2 then 4373 else 4374)) else (if jt.2.val < 4 then 4370 else (if jt.2.val < 5 then 4372 else 4371)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3556 else (if jt.2.val < 2 then 3560 else 3561)) else (if jt.2.val < 4 then 3557 else (if jt.2.val < 5 then 3559 else 3558))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3358 else (if jt.2.val < 2 then 3364 else 3365)) else (if jt.2.val < 4 then 3359 else (if jt.2.val < 5 then 3361 else 3360)))))

checked_coverage fastCoverage0720 pairing0720 template0720 witness0720

theorem coverage0720 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0720) (maskBits m))
    cores template0720 witness0720 := by
  rw [← coresFast_eq]
  exact fastCoverage0720

theorem coverageSize0720 : ∀ q : Pattern,
    (cores (witness0720 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0720 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0720
#print axioms coverageSize0720

noncomputable def pairing0721 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0721 : List (Fin 4935) := templateData0721

noncomputable def witness0721 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3320) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 2768) else (if t 3 = 0 then 2732 else if t 3 = 1 then 2730 else 2987)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 141) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 140) else (if t 3 = 0 then 344 else if t 3 = 1 then 340 else 892)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1648 else 1835) else if t 2 = 1 then (if t 3 = 0 then 1650 else if t 3 = 1 then 1646 else 157) else (if t 3 = 0 then 359 else if t 3 = 1 then 357 else 896))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 635) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 634) else (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 1135)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2622) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3089) else (if t 3 = 0 then 3082 else if t 3 = 1 then 3080 else 3094)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2626) else if t 2 = 1 then (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3092) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3083 else 3096))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1213 else 697) else if t 2 = 1 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1207 else 691) else (if t 3 = 0 then 1838 else if t 3 = 1 then 499 else 1525)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2956 else 2652) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3098 else 3102) else (if t 3 = 0 then 3315 else if t 3 = 1 then 3100 else 3104)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2957 else 2653) else if t 2 = 1 then (if t 3 = 0 then 3314 else if t 3 = 1 then 3099 else 3103) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3101 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4851 else (if jt.2.val < 2 then 4853 else 4856)) else (if jt.2.val < 4 then 4852 else (if jt.2.val < 5 then 4855 else 4854))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4315 else (if jt.2.val < 2 then 4319 else 4320)) else (if jt.2.val < 4 then 4316 else (if jt.2.val < 5 then 4318 else 4317)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3385 else (if jt.2.val < 2 then 3389 else 3390)) else (if jt.2.val < 4 then 3386 else (if jt.2.val < 5 then 3388 else 3387))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3360 else (if jt.2.val < 2 then 3374 else 3365)) else (if jt.2.val < 4 then 3369 else (if jt.2.val < 5 then 3370 else 3358)))))

checked_coverage fastCoverage0721 pairing0721 template0721 witness0721

theorem coverage0721 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0721) (maskBits m))
    cores template0721 witness0721 := by
  rw [← coresFast_eq]
  exact fastCoverage0721

theorem coverageSize0721 : ∀ q : Pattern,
    (cores (witness0721 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0721 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0721
#print axioms coverageSize0721

noncomputable def pairing0722 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0722 : List (Fin 4935) := templateData0722

noncomputable def witness0722 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2813 else 2633) else if t 2 = 1 then (if t 3 = 0 then 2817 else if t 3 = 1 then 2809 else 2855) else (if t 3 = 0 then 3340 else if t 3 = 1 then 3338 else 3226)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2811 else 1415) else if t 2 = 1 then (if t 3 = 0 then 2815 else if t 3 = 1 then 2807 else 1414) else (if t 3 = 0 then 964 else if t 3 = 1 then 960 else 992)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1171 else 569) else if t 2 = 1 then (if t 3 = 0 then 1173 else if t 3 = 1 then 1169 else 1202) else (if t 3 = 0 then 1802 else if t 3 = 1 then 1801 else 1433))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2812 else 1585) else if t 2 = 1 then (if t 3 = 0 then 2816 else if t 3 = 1 then 2808 else 1584) else (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1073)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2810 else 2632) else if t 2 = 1 then (if t 3 = 0 then 2814 else if t 3 = 1 then 2806 else 2854) else (if t 3 = 0 then 2838 else if t 3 = 1 then 2835 else 2857)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2635) else if t 2 = 1 then (if t 3 = 0 then 2829 else if t 3 = 1 then 2826 else 2856) else (if t 3 = 0 then 2842 else if t 3 = 1 then 2840 else 2858))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1686 else 1855) else if t 2 = 1 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1685 else 1852) else (if t 3 = 0 then 599 else if t 3 = 1 then 1082 else 1093)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2721 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2576 else if t 3 = 1 then 2859 else 2864) else (if t 3 = 0 then 2579 else if t 3 = 1 then 2862 else 2866)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2723 else 3322) else if t 2 = 1 then (if t 3 = 0 then 2578 else if t 3 = 1 then 2861 else 2865) else (if t 3 = 0 then 2580 else if t 3 = 1 then 2863 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4857 else (if jt.2.val < 2 then 4859 else 4862)) else (if jt.2.val < 4 then 4858 else (if jt.2.val < 5 then 4861 else 4860))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3763 else (if jt.2.val < 2 then 3767 else 3768)) else (if jt.2.val < 4 then 3764 else (if jt.2.val < 5 then 3766 else 3765)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3558 else (if jt.2.val < 2 then 3576 else 3561)) else (if jt.2.val < 4 then 3573 else (if jt.2.val < 5 then 3574 else 3556))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3007 else (if jt.2.val < 2 then 3016 else 3017)) else (if jt.2.val < 4 then 3008 else (if jt.2.val < 5 then 3010 else 3009)))))

checked_coverage fastCoverage0722 pairing0722 template0722 witness0722

theorem coverage0722 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0722) (maskBits m))
    cores template0722 witness0722 := by
  rw [← coresFast_eq]
  exact fastCoverage0722

theorem coverageSize0722 : ∀ q : Pattern,
    (cores (witness0722 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0722 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0722
#print axioms coverageSize0722

noncomputable def pairing0723 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0723 : List (Fin 4935) := templateData0723

noncomputable def witness0723 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2446 else 2898) else if t 2 = 1 then (if t 3 = 0 then 2450 else if t 3 = 1 then 2442 else 2482) else (if t 3 = 0 then 3205 else if t 3 = 1 then 3203 else 3344)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2444 else 1413) else if t 2 = 1 then (if t 3 = 0 then 2448 else if t 3 = 1 then 2440 else 1412) else (if t 3 = 0 then 343 else if t 3 = 1 then 339 else 372)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 724 else 1109) else if t 2 = 1 then (if t 3 = 0 then 726 else if t 3 = 1 then 722 else 756) else (if t 3 = 0 then 1490 else if t 3 = 1 then 1489 else 1775))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2445 else 1583) else if t 2 = 1 then (if t 3 = 0 then 2449 else if t 3 = 1 then 2441 else 1582) else (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 471)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2443 else 2897) else if t 2 = 1 then (if t 3 = 0 then 2447 else if t 3 = 1 then 2439 else 2481) else (if t 3 = 0 then 2471 else if t 3 = 1 then 2468 else 2488)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2899) else if t 2 = 1 then (if t 3 = 0 then 2462 else if t 3 = 1 then 2459 else 2486) else (if t 3 = 0 then 2475 else if t 3 = 1 then 2473 else 2490))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1909 else 1621) else if t 2 = 1 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1906 else 1618) else (if t 3 = 0 then 1118 else if t 3 = 1 then 493 else 495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2502 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2883 else if t 3 = 1 then 2492 else 2496) else (if t 3 = 0 then 2886 else if t 3 = 1 then 2494 else 2498)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2503 else 3184) else if t 2 = 1 then (if t 3 = 0 then 2885 else if t 3 = 1 then 2493 else 2497) else (if t 3 = 0 then 2887 else if t 3 = 1 then 2495 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4863 else (if jt.2.val < 2 then 4865 else 4868)) else (if jt.2.val < 4 then 4864 else (if jt.2.val < 5 then 4867 else 4866))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3691 else (if jt.2.val < 2 then 3695 else 3696)) else (if jt.2.val < 4 then 3692 else (if jt.2.val < 5 then 3694 else 3693)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3387 else (if jt.2.val < 2 then 3411 else 3390)) else (if jt.2.val < 4 then 3408 else (if jt.2.val < 5 then 3409 else 3385))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3009 else (if jt.2.val < 2 then 3026 else 3017)) else (if jt.2.val < 4 then 3018 else (if jt.2.val < 5 then 3019 else 3007)))))

checked_coverage fastCoverage0723 pairing0723 template0723 witness0723

theorem coverage0723 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0723) (maskBits m))
    cores template0723 witness0723 := by
  rw [← coresFast_eq]
  exact fastCoverage0723

theorem coverageSize0723 : ∀ q : Pattern,
    (cores (witness0723 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0723 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0723
#print axioms coverageSize0723

noncomputable def pairing0724 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0724 : List (Fin 4935) := templateData0724

noncomputable def witness0724 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 1462) else if t 2 = 1 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 646) else (if t 3 = 0 then 1053 else if t 3 = 1 then 1049 else 669)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 256) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1747) else (if t 3 = 0 then 1733 else if t 3 = 1 then 1730 else 1750)) else (if t 2 = 0 then (if t 3 = 0 then 3352 else if t 3 = 1 then 3350 else 3210) else if t 2 = 1 then (if t 3 = 0 then 3351 else if t 3 = 1 then 3348 else 2546) else (if t 3 = 0 then 2940 else if t 3 = 1 then 2938 else 2561))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 1461) else if t 2 = 1 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 645) else (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 668)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 255) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1746) else (if t 3 = 0 then 1732 else if t 3 = 1 then 1729 else 1749)) else (if t 2 = 0 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 261) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1748) else (if t 3 = 0 then 1735 else if t 3 = 1 then 1734 else 1751))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1497 else 2990) else if t 2 = 1 then (if t 3 = 0 then 779 else if t 3 = 1 then 777 else 1142) else (if t 3 = 0 then 3216 else if t 3 = 1 then 789 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 395 else if t 3 = 1 then 393 else 926) else if t 2 = 1 then (if t 3 = 0 then 1449 else if t 3 = 1 then 1752 else 1758) else (if t 3 = 0 then 1452 else if t 3 = 1 then 1755 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 398 else if t 3 = 1 then 397 else 927) else if t 2 = 1 then (if t 3 = 0 then 1451 else if t 3 = 1 then 1754 else 1759) else (if t 3 = 0 then 1454 else if t 3 = 1 then 1757 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4863 else (if jt.2.val < 2 then 4870 else 4868)) else (if jt.2.val < 4 then 4869 else (if jt.2.val < 5 then 4871 else 4866))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4371 else (if jt.2.val < 2 then 4388 else 4374)) else (if jt.2.val < 4 then 4386 else (if jt.2.val < 5 then 4387 else 4369)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2269 else (if jt.2.val < 2 then 2273 else 2274)) else (if jt.2.val < 4 then 2270 else (if jt.2.val < 5 then 2272 else 2271))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1918 else (if jt.2.val < 2 then 1924 else 1925)) else (if jt.2.val < 4 then 1919 else (if jt.2.val < 5 then 1921 else 1920)))))

checked_coverage fastCoverage0724 pairing0724 template0724 witness0724

theorem coverage0724 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0724) (maskBits m))
    cores template0724 witness0724 := by
  rw [← coresFast_eq]
  exact fastCoverage0724

theorem coverageSize0724 : ∀ q : Pattern,
    (cores (witness0724 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0724 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0724
#print axioms coverageSize0724

noncomputable def pairing0725 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0725 : List (Fin 4935) := templateData0725

noncomputable def witness0725 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 1786) else if t 2 = 1 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 644) else (if t 3 = 0 then 452 else if t 3 = 1 then 448 else 1138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 254) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1350) else (if t 3 = 0 then 1342 else if t 3 = 1 then 1339 else 1357)) else (if t 2 = 0 then (if t 3 = 0 then 3236 else if t 3 = 1 then 3234 else 3342) else if t 2 = 1 then (if t 3 = 0 then 3235 else if t 3 = 1 then 3232 else 2545) else (if t 3 = 0 then 2691 else if t 3 = 1 then 2689 else 2882))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 1785) else if t 2 = 1 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 643) else (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 1137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 253) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1349) else (if t 3 = 0 then 1341 else if t 3 = 1 then 1338 else 1356)) else (if t 2 = 0 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 260) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1354) else (if t 3 = 0 then 1344 else if t 3 = 1 then 1343 else 1360))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1374 else 2782) else if t 2 = 1 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1208 else 692) else (if t 3 = 0 then 3343 else if t 3 = 1 then 500 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1011 else if t 3 = 1 then 998 else 302) else if t 2 = 1 then (if t 3 = 0 then 1776 else if t 3 = 1 then 1362 else 1366) else (if t 3 = 0 then 1779 else if t 3 = 1 then 1364 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 1013 else if t 3 = 1 then 999 else 303) else if t 2 = 1 then (if t 3 = 0 then 1778 else if t 3 = 1 then 1363 else 1367) else (if t 3 = 0 then 1781 else if t 3 = 1 then 1365 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4857 else (if jt.2.val < 2 then 4873 else 4862)) else (if jt.2.val < 4 then 4872 else (if jt.2.val < 5 then 4874 else 4860))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4317 else (if jt.2.val < 2 then 4352 else 4320)) else (if jt.2.val < 4 then 4350 else (if jt.2.val < 5 then 4351 else 4315)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1972 else (if jt.2.val < 2 then 1976 else 1977)) else (if jt.2.val < 4 then 1973 else (if jt.2.val < 5 then 1975 else 1974))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1920 else (if jt.2.val < 2 then 1934 else 1925)) else (if jt.2.val < 4 then 1929 else (if jt.2.val < 5 then 1930 else 1918)))))

checked_coverage fastCoverage0725 pairing0725 template0725 witness0725

theorem coverage0725 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0725) (maskBits m))
    cores template0725 witness0725 := by
  rw [← coresFast_eq]
  exact fastCoverage0725

theorem coverageSize0725 : ∀ q : Pattern,
    (cores (witness0725 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0725 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0725
#print axioms coverageSize0725

noncomputable def pairing0726 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0726 : List (Fin 4935) := templateData0726

noncomputable def witness0726 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 803 else 271) else if t 2 = 1 then (if t 3 = 0 then 807 else if t 3 = 1 then 799 else 855) else (if t 3 = 0 then 1816 else if t 3 = 1 then 1813 else 1599)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 809 else if t 3 = 1 then 801 else 269) else if t 2 = 1 then (if t 3 = 0 then 805 else if t 3 = 1 then 797 else 853) else (if t 3 = 0 then 835 else if t 3 = 1 then 830 else 859)) else (if t 2 = 0 then (if t 3 = 0 then 2997 else if t 3 = 1 then 2995 else 2757) else if t 2 = 1 then (if t 3 = 0 then 2996 else if t 3 = 1 then 2993 else 3002) else (if t 3 = 0 then 3330 else if t 3 = 1 then 3329 else 3152))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 802 else 270) else if t 2 = 1 then (if t 3 = 0 then 806 else if t 3 = 1 then 798 else 854) else (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1598)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 808 else if t 3 = 1 then 800 else 268) else if t 2 = 1 then (if t 3 = 0 then 804 else if t 3 = 1 then 796 else 852) else (if t 3 = 0 then 834 else if t 3 = 1 then 829 else 858)) else (if t 2 = 0 then (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 274) else if t 2 = 1 then (if t 3 = 0 then 821 else if t 3 = 1 then 816 else 856) else (if t 3 = 0 then 840 else if t 3 = 1 then 838 else 860))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 401 else 3345) else if t 2 = 1 then (if t 3 = 0 then 200 else if t 3 = 1 then 863 else 876) else (if t 3 = 0 then 2763 else if t 3 = 1 then 1689 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1500 else if t 3 = 1 then 399 else 1788) else if t 2 = 1 then (if t 3 = 0 then 198 else if t 3 = 1 then 861 else 870) else (if t 3 = 0 then 204 else if t 3 = 1 then 867 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 1502 else if t 3 = 1 then 403 else 1789) else if t 2 = 1 then (if t 3 = 0 then 202 else if t 3 = 1 then 865 else 871) else (if t 3 = 0 then 206 else if t 3 = 1 then 869 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4851 else (if jt.2.val < 2 then 4876 else 4856)) else (if jt.2.val < 4 then 4875 else (if jt.2.val < 5 then 4877 else 4854))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3765 else (if jt.2.val < 2 then 3788 else 3768)) else (if jt.2.val < 4 then 3786 else (if jt.2.val < 5 then 3787 else 3763)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2271 else (if jt.2.val < 2 then 2289 else 2274)) else (if jt.2.val < 4 then 2286 else (if jt.2.val < 5 then 2287 else 2269))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1225 else (if jt.2.val < 2 then 1234 else 1235)) else (if jt.2.val < 4 then 1226 else (if jt.2.val < 5 then 1228 else 1227)))))

checked_coverage fastCoverage0726 pairing0726 template0726 witness0726

theorem coverage0726 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0726) (maskBits m))
    cores template0726 witness0726 := by
  rw [← coresFast_eq]
  exact fastCoverage0726

theorem coverageSize0726 : ∀ q : Pattern,
    (cores (witness0726 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0726 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0726
#print axioms coverageSize0726

noncomputable def pairing0727 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0727 : List (Fin 4935) := templateData0727

noncomputable def witness0727 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 16 else 918) else if t 2 = 1 then (if t 3 = 0 then 20 else if t 3 = 1 then 12 else 62) else (if t 3 = 0 then 1510 else if t 3 = 1 then 1507 else 1849)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 22 else if t 3 = 1 then 14 else 916) else if t 2 = 1 then (if t 3 = 0 then 18 else if t 3 = 1 then 10 else 60) else (if t 3 = 0 then 48 else if t 3 = 1 then 43 else 73)) else (if t 2 = 0 then (if t 3 = 0 then 2789 else if t 3 = 1 then 2787 else 2983) else if t 2 = 1 then (if t 3 = 0 then 2788 else if t 3 = 1 then 2785 else 2794) else (if t 3 = 0 then 3192 else if t 3 = 1 then 3191 else 3312))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 15 else 917) else if t 2 = 1 then (if t 3 = 0 then 19 else if t 3 = 1 then 11 else 61) else (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1848)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 21 else if t 3 = 1 then 13 else 915) else if t 2 = 1 then (if t 3 = 0 then 17 else if t 3 = 1 then 9 else 59) else (if t 3 = 0 then 47 else if t 3 = 1 then 42 else 72)) else (if t 2 = 0 then (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 919) else if t 2 = 1 then (if t 3 = 0 then 34 else if t 3 = 1 then 29 else 68) else (if t 3 = 0 then 53 else if t 3 = 1 then 51 else 76))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 102 else 3229) else if t 2 = 1 then (if t 3 = 0 then 899 else if t 3 = 1 then 90 else 92) else (if t 3 = 0 then 2986 else if t 3 = 1 then 1521 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1806 else if t 3 = 1 then 96 else 1476) else if t 2 = 1 then (if t 3 = 0 then 897 else if t 3 = 1 then 78 else 82) else (if t 3 = 0 then 903 else if t 3 = 1 then 80 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 1808 else if t 3 = 1 then 97 else 1477) else if t 2 = 1 then (if t 3 = 0 then 901 else if t 3 = 1 then 79 else 83) else (if t 3 = 0 then 905 else if t 3 = 1 then 81 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4845 else (if jt.2.val < 2 then 4879 else 4850)) else (if jt.2.val < 4 then 4878 else (if jt.2.val < 5 then 4880 else 4848))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3693 else (if jt.2.val < 2 then 3740 else 3696)) else (if jt.2.val < 4 then 3738 else (if jt.2.val < 5 then 3739 else 3691)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1974 else (if jt.2.val < 2 then 1998 else 1977)) else (if jt.2.val < 4 then 1995 else (if jt.2.val < 5 then 1996 else 1972))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1227 else (if jt.2.val < 2 then 1244 else 1235)) else (if jt.2.val < 4 then 1236 else (if jt.2.val < 5 then 1237 else 1225)))))

checked_coverage fastCoverage0727 pairing0727 template0727 witness0727

theorem coverage0727 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0727) (maskBits m))
    cores template0727 witness0727 := by
  rw [← coresFast_eq]
  exact fastCoverage0727

theorem coverageSize0727 : ∀ q : Pattern,
    (cores (witness0727 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0727 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0727
#print axioms coverageSize0727

noncomputable def pairing0728 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0728 : List (Fin 4935) := templateData0728

noncomputable def witness0728 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3205) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2731) else (if t 3 = 0 then 2974 else if t 3 = 1 then 2973 else 2738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 343) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 342) else (if t 3 = 0 then 965 else if t 3 = 1 then 963 else 373)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2197 else 1490) else if t 2 = 1 then (if t 3 = 0 then 2199 else if t 3 = 1 then 2195 else 358) else (if t 3 = 0 then 980 else if t 3 = 1 then 979 else 380))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 441) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 440) else (if t 3 = 0 then 1043 else if t 3 = 1 then 1041 else 472)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2471) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3479) else (if t 3 = 0 then 3278 else if t 3 = 1 then 3472 else 3486)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2475) else if t 2 = 1 then (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3480) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3473 else 3487))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 585 else 1118) else if t 2 = 1 then (if t 3 = 0 then 586 else if t 3 = 1 then 584 else 1117) else (if t 3 = 0 then 1550 else if t 3 = 1 then 598 else 2149)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2572 else 2886) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3488 else 3492) else (if t 3 = 0 then 3167 else if t 3 = 1 then 3490 else 3494)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2574 else 2887) else if t 2 = 1 then (if t 3 = 0 then 3164 else if t 3 = 1 then 3489 else 3493) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3491 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4881 else (if jt.2.val < 2 then 4883 else 4886)) else (if jt.2.val < 4 then 4882 else (if jt.2.val < 5 then 4885 else 4884))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4648 else (if jt.2.val < 2 then 4652 else 4653)) else (if jt.2.val < 4 then 4649 else (if jt.2.val < 5 then 4651 else 4650)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3601 else (if jt.2.val < 2 then 3605 else 3606)) else (if jt.2.val < 4 then 3602 else (if jt.2.val < 5 then 3604 else 3603))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3538 else (if jt.2.val < 2 then 3542 else 3543)) else (if jt.2.val < 4 then 3539 else (if jt.2.val < 5 then 3541 else 3540)))))

checked_coverage fastCoverage0728 pairing0728 template0728 witness0728

theorem coverage0728 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0728) (maskBits m))
    cores template0728 witness0728 := by
  rw [← coresFast_eq]
  exact fastCoverage0728

theorem coverageSize0728 : ∀ q : Pattern,
    (cores (witness0728 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0728 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0728
#print axioms coverageSize0728

noncomputable def pairing0729 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0729 : List (Fin 4935) := templateData0729

noncomputable def witness0729 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3505) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 2730) else (if t 3 = 0 then 2770 else if t 3 = 1 then 2768 else 2987)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 341) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 340) else (if t 3 = 0 then 144 else if t 3 = 1 then 140 else 892)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1648 else 2159) else if t 2 = 1 then (if t 3 = 0 then 1650 else if t 3 = 1 then 1646 else 357) else (if t 3 = 0 then 159 else if t 3 = 1 then 157 else 896))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 439) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 438) else (if t 3 = 0 then 638 else if t 3 = 1 then 634 else 1135)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2470) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3080) else (if t 3 = 0 then 3091 else if t 3 = 1 then 3089 else 3094)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2474) else if t 2 = 1 then (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3083) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3092 else 3096))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1213 else 505) else if t 2 = 1 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1207 else 499) else (if t 3 = 0 then 2162 else if t 3 = 1 then 691 else 1525)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2956 else 2504) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3098 else 3100) else (if t 3 = 0 then 3500 else if t 3 = 1 then 3102 else 3104)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2957 else 2505) else if t 2 = 1 then (if t 3 = 0 then 3314 else if t 3 = 1 then 3099 else 3101) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3103 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4851 else (if jt.2.val < 2 then 4853 else 4856)) else (if jt.2.val < 4 then 4852 else (if jt.2.val < 5 then 4855 else 4854))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4315 else (if jt.2.val < 2 then 4319 else 4320)) else (if jt.2.val < 4 then 4316 else (if jt.2.val < 5 then 4318 else 4317)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3048 else (if jt.2.val < 2 then 3088 else 3090)) else (if jt.2.val < 4 then 3085 else (if jt.2.val < 5 then 3087 else 3086))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3540 else (if jt.2.val < 2 then 3551 else 3543)) else (if jt.2.val < 4 then 3549 else (if jt.2.val < 5 then 3550 else 3538)))))

checked_coverage fastCoverage0729 pairing0729 template0729 witness0729

theorem coverage0729 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0729) (maskBits m))
    cores template0729 witness0729 := by
  rw [← coresFast_eq]
  exact fastCoverage0729

theorem coverageSize0729 : ∀ q : Pattern,
    (cores (witness0729 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0729 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0729
#print axioms coverageSize0729

noncomputable def pairing0730 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0730 : List (Fin 4935) := templateData0730

noncomputable def witness0730 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2817 else 2485) else if t 2 = 1 then (if t 3 = 0 then 2813 else if t 3 = 1 then 2809 else 2855) else (if t 3 = 0 then 3520 else if t 3 = 1 then 3338 else 3226)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2815 else 1416) else if t 2 = 1 then (if t 3 = 0 then 2811 else if t 3 = 1 then 2807 else 1414) else (if t 3 = 0 then 962 else if t 3 = 1 then 960 else 992)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1173 else 758) else if t 2 = 1 then (if t 3 = 0 then 1171 else if t 3 = 1 then 1169 else 1202) else (if t 3 = 0 then 2138 else if t 3 = 1 then 1801 else 1433))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2816 else 1586) else if t 2 = 1 then (if t 3 = 0 then 2812 else if t 3 = 1 then 2808 else 1584) else (if t 3 = 0 then 1040 else if t 3 = 1 then 1038 else 1073)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2814 else 2484) else if t 2 = 1 then (if t 3 = 0 then 2810 else if t 3 = 1 then 2806 else 2854) else (if t 3 = 0 then 2837 else if t 3 = 1 then 2835 else 2857)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2487) else if t 2 = 1 then (if t 3 = 0 then 2828 else if t 3 = 1 then 2826 else 2856) else (if t 3 = 0 then 2841 else if t 3 = 1 then 2840 else 2858))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1687 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1685 else 1852) else (if t 3 = 0 then 788 else if t 3 = 1 then 1082 else 1093)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2576 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2721 else if t 3 = 1 then 2859 else 2864) else (if t 3 = 0 then 2724 else if t 3 = 1 then 2862 else 2866)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2578 else 3507) else if t 2 = 1 then (if t 3 = 0 then 2723 else if t 3 = 1 then 2861 else 2865) else (if t 3 = 0 then 2725 else if t 3 = 1 then 2863 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4857 else (if jt.2.val < 2 then 4859 else 4862)) else (if jt.2.val < 4 then 4858 else (if jt.2.val < 5 then 4861 else 4860))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3763 else (if jt.2.val < 2 then 3767 else 3768)) else (if jt.2.val < 4 then 3764 else (if jt.2.val < 5 then 3766 else 3765)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3603 else (if jt.2.val < 2 then 3614 else 3606)) else (if jt.2.val < 4 then 3612 else (if jt.2.val < 5 then 3613 else 3601))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2803 else (if jt.2.val < 2 then 2852 else 2853)) else (if jt.2.val < 4 then 2849 else (if jt.2.val < 5 then 2851 else 2850)))))

checked_coverage fastCoverage0730 pairing0730 template0730 witness0730

theorem coverage0730 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0730) (maskBits m))
    cores template0730 witness0730 := by
  rw [← coresFast_eq]
  exact fastCoverage0730

theorem coverageSize0730 : ∀ q : Pattern,
    (cores (witness0730 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0730 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0730
#print axioms coverageSize0730

noncomputable def pairing0731 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0731 : List (Fin 4935) := templateData0731

noncomputable def witness0731 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2598 else 2898) else if t 2 = 1 then (if t 3 = 0 then 2602 else if t 3 = 1 then 2594 else 2630) else (if t 3 = 0 then 3174 else if t 3 = 1 then 3172 else 3524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2596 else 1413) else if t 2 = 1 then (if t 3 = 0 then 2600 else if t 3 = 1 then 2592 else 1411) else (if t 3 = 0 then 143 else if t 3 = 1 then 139 else 171)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 536 else 1109) else if t 2 = 1 then (if t 3 = 0 then 538 else if t 3 = 1 then 534 else 567) else (if t 3 = 0 then 1538 else if t 3 = 1 then 1537 else 2117))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2597 else 1583) else if t 2 = 1 then (if t 3 = 0 then 2601 else if t 3 = 1 then 2593 else 1581) else (if t 3 = 0 then 637 else if t 3 = 1 then 633 else 663)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2595 else 2897) else if t 2 = 1 then (if t 3 = 0 then 2599 else if t 3 = 1 then 2591 else 2629) else (if t 3 = 0 then 2623 else if t 3 = 1 then 2620 else 2636)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2899) else if t 2 = 1 then (if t 3 = 0 then 2614 else if t 3 = 1 then 2611 else 2634) else (if t 3 = 0 then 2627 else if t 3 = 1 then 2625 else 2638))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2224 else 1621) else if t 2 = 1 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2221 else 1615) else (if t 3 = 0 then 1147 else if t 3 = 1 then 685 else 687)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2650 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2902 else if t 3 = 1 then 2640 else 2644) else (if t 3 = 0 then 2904 else if t 3 = 1 then 2642 else 2646)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2651 else 3184) else if t 2 = 1 then (if t 3 = 0 then 2903 else if t 3 = 1 then 2641 else 2645) else (if t 3 = 0 then 2905 else if t 3 = 1 then 2643 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4887 else (if jt.2.val < 2 then 4889 else 4892)) else (if jt.2.val < 4 then 4888 else (if jt.2.val < 5 then 4891 else 4890))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3715 else (if jt.2.val < 2 then 3719 else 3720)) else (if jt.2.val < 4 then 3716 else (if jt.2.val < 5 then 3718 else 3717)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3086 else (if jt.2.val < 2 then 3173 else 3090)) else (if jt.2.val < 4 then 3169 else (if jt.2.val < 5 then 3170 else 3048))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2850 else (if jt.2.val < 2 then 2896 else 2853)) else (if jt.2.val < 4 then 2888 else (if jt.2.val < 5 then 2889 else 2803)))))

checked_coverage fastCoverage0731 pairing0731 template0731 witness0731

theorem coverage0731 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0731) (maskBits m))
    cores template0731 witness0731 := by
  rw [← coresFast_eq]
  exact fastCoverage0731

theorem coverageSize0731 : ∀ q : Pattern,
    (cores (witness0731 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0731 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0731
#print axioms coverageSize0731

noncomputable def pairing0732 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0732 : List (Fin 4935) := templateData0732

noncomputable def witness0732 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1510) else if t 2 = 1 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 450) else (if t 3 = 0 then 1053 else if t 3 = 1 then 1051 else 477)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 48) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2090) else (if t 3 = 0 then 1733 else if t 3 = 1 then 2082 else 2098)) else (if t 2 = 0 then (if t 3 = 0 then 3532 else if t 3 = 1 then 3530 else 3192) else if t 2 = 1 then (if t 3 = 0 then 3531 else if t 3 = 1 then 3528 else 2690) else (if t 3 = 0 then 2940 else if t 3 = 1 then 2939 else 2706))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1509) else if t 2 = 1 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 449) else (if t 3 = 0 then 1052 else if t 3 = 1 then 1050 else 476)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 47) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2089) else (if t 3 = 0 then 1732 else if t 3 = 1 then 2081 else 2097)) else (if t 2 = 0 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 53) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2091) else (if t 3 = 0 then 1735 else if t 3 = 1 then 2083 else 2099))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 1545 else 2986) else if t 2 = 1 then (if t 3 = 0 then 590 else if t 3 = 1 then 588 else 1119) else (if t 3 = 0 then 3216 else if t 3 = 1 then 600 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 194 else if t 3 = 1 then 192 else 903) else if t 2 = 1 then (if t 3 = 0 then 1446 else if t 3 = 1 then 2100 else 2106) else (if t 3 = 0 then 1452 else if t 3 = 1 then 2103 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 197 else if t 3 = 1 then 196 else 905) else if t 2 = 1 then (if t 3 = 0 then 1448 else if t 3 = 1 then 2102 else 2108) else (if t 3 = 0 then 1454 else if t 3 = 1 then 2105 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4887 else (if jt.2.val < 2 then 4894 else 4892)) else (if jt.2.val < 4 then 4893 else (if jt.2.val < 5 then 4895 else 4890))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4650 else (if jt.2.val < 2 then 4667 else 4653)) else (if jt.2.val < 4 then 4665 else (if jt.2.val < 5 then 4666 else 4648)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2323 else (if jt.2.val < 2 then 2327 else 2328)) else (if jt.2.val < 4 then 2324 else (if jt.2.val < 5 then 2326 else 2325))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2233 else (if jt.2.val < 2 then 2237 else 2238)) else (if jt.2.val < 4 then 2234 else (if jt.2.val < 5 then 2236 else 2235)))))

checked_coverage fastCoverage0732 pairing0732 template0732 witness0732

theorem coverage0732 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0732) (maskBits m))
    cores template0732 witness0732 := by
  rw [← coresFast_eq]
  exact fastCoverage0732

theorem coverageSize0732 : ∀ q : Pattern,
    (cores (witness0732 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0732 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0732
#print axioms coverageSize0732

noncomputable def pairing0733 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0733 : List (Fin 4935) := templateData0733

noncomputable def witness0733 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 2125) else if t 2 = 1 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 448) else (if t 3 = 0 then 648 else if t 3 = 1 then 644 else 1138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 46) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1339) else (if t 3 = 0 then 1353 else if t 3 = 1 then 1350 else 1357)) else (if t 2 = 0 then (if t 3 = 0 then 3236 else if t 3 = 1 then 3234 else 3522) else if t 2 = 1 then (if t 3 = 0 then 3235 else if t 3 = 1 then 3232 else 2689) else (if t 3 = 0 then 2547 else if t 3 = 1 then 2545 else 2882))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 2124) else if t 2 = 1 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 447) else (if t 3 = 0 then 647 else if t 3 = 1 then 643 else 1137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 45) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1338) else (if t 3 = 0 then 1352 else if t 3 = 1 then 1349 else 1356)) else (if t 2 = 0 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 52) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1343) else (if t 3 = 0 then 1355 else if t 3 = 1 then 1354 else 1360))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1374 else 2744) else if t 2 = 1 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1208 else 500) else (if t 3 = 0 then 3523 else if t 3 = 1 then 692 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1011 else if t 3 = 1 then 998 else 98) else if t 2 = 1 then (if t 3 = 0 then 1776 else if t 3 = 1 then 1362 else 1364) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1366 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 1013 else if t 3 = 1 then 999 else 99) else if t 2 = 1 then (if t 3 = 0 then 1778 else if t 3 = 1 then 1363 else 1365) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1367 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4857 else (if jt.2.val < 2 then 4873 else 4862)) else (if jt.2.val < 4 then 4872 else (if jt.2.val < 5 then 4874 else 4860))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4317 else (if jt.2.val < 2 then 4352 else 4320)) else (if jt.2.val < 4 then 4350 else (if jt.2.val < 5 then 4351 else 4315)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1302 else (if jt.2.val < 2 then 1348 else 1351)) else (if jt.2.val < 4 then 1345 else (if jt.2.val < 5 then 1347 else 1346))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2235 else (if jt.2.val < 2 then 2246 else 2238)) else (if jt.2.val < 4 then 2244 else (if jt.2.val < 5 then 2245 else 2233)))))

checked_coverage fastCoverage0733 pairing0733 template0733 witness0733

theorem coverage0733 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0733) (maskBits m))
    cores template0733 witness0733 := by
  rw [← coresFast_eq]
  exact fastCoverage0733

theorem coverageSize0733 : ∀ q : Pattern,
    (cores (witness0733 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0733 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0733
#print axioms coverageSize0733

noncomputable def pairing0734 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0734 : List (Fin 4935) := templateData0734

noncomputable def witness0734 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 807 else 67) else if t 2 = 1 then (if t 3 = 0 then 803 else if t 3 = 1 then 799 else 855) else (if t 3 = 0 then 2146 else if t 3 = 1 then 1813 else 1599)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 809 else if t 3 = 1 then 805 else 65) else if t 2 = 1 then (if t 3 = 0 then 801 else if t 3 = 1 then 797 else 853) else (if t 3 = 0 then 833 else if t 3 = 1 then 830 else 859)) else (if t 2 = 0 then (if t 3 = 0 then 2997 else if t 3 = 1 then 2996 else 2795) else if t 2 = 1 then (if t 3 = 0 then 2995 else if t 3 = 1 then 2993 else 3002) else (if t 3 = 0 then 3514 else if t 3 = 1 then 3329 else 3152))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 806 else 66) else if t 2 = 1 then (if t 3 = 0 then 802 else if t 3 = 1 then 798 else 854) else (if t 3 = 0 then 2145 else if t 3 = 1 then 1812 else 1598)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 808 else if t 3 = 1 then 804 else 64) else if t 2 = 1 then (if t 3 = 0 then 800 else if t 3 = 1 then 796 else 852) else (if t 3 = 0 then 832 else if t 3 = 1 then 829 else 858)) else (if t 2 = 0 then (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 70) else if t 2 = 1 then (if t 3 = 0 then 819 else if t 3 = 1 then 816 else 856) else (if t 3 = 0 then 839 else if t 3 = 1 then 838 else 860))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 200 else 3525) else if t 2 = 1 then (if t 3 = 0 then 401 else if t 3 = 1 then 863 else 876) else (if t 3 = 0 then 2801 else if t 3 = 1 then 1689 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1500 else if t 3 = 1 then 198 else 2127) else if t 2 = 1 then (if t 3 = 0 then 399 else if t 3 = 1 then 861 else 870) else (if t 3 = 0 then 405 else if t 3 = 1 then 867 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 1502 else if t 3 = 1 then 202 else 2128) else if t 2 = 1 then (if t 3 = 0 then 403 else if t 3 = 1 then 865 else 871) else (if t 3 = 0 then 407 else if t 3 = 1 then 869 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4851 else (if jt.2.val < 2 then 4876 else 4856)) else (if jt.2.val < 4 then 4875 else (if jt.2.val < 5 then 4877 else 4854))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3765 else (if jt.2.val < 2 then 3788 else 3768)) else (if jt.2.val < 4 then 3786 else (if jt.2.val < 5 then 3787 else 3763)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2325 else (if jt.2.val < 2 then 2336 else 2328)) else (if jt.2.val < 4 then 2334 else (if jt.2.val < 5 then 2335 else 2323))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 793 else (if jt.2.val < 2 then 850 else 851)) else (if jt.2.val < 4 then 847 else (if jt.2.val < 5 then 849 else 848)))))

checked_coverage fastCoverage0734 pairing0734 template0734 witness0734

theorem coverage0734 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0734) (maskBits m))
    cores template0734 witness0734 := by
  rw [← coresFast_eq]
  exact fastCoverage0734

theorem coverageSize0734 : ∀ q : Pattern,
    (cores (witness0734 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0734 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0734
#print axioms coverageSize0734

noncomputable def pairing0735 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0735 : List (Fin 4935) := templateData0735

noncomputable def witness0735 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 224 else 918) else if t 2 = 1 then (if t 3 = 0 then 228 else if t 3 = 1 then 220 else 266) else (if t 3 = 0 then 1462 else if t 3 = 1 then 1459 else 2170)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 230 else if t 3 = 1 then 222 else 916) else if t 2 = 1 then (if t 3 = 0 then 226 else if t 3 = 1 then 218 else 264) else (if t 3 = 0 then 256 else if t 3 = 1 then 251 else 277)) else (if t 2 = 0 then (if t 3 = 0 then 2751 else if t 3 = 1 then 2749 else 2983) else if t 2 = 1 then (if t 3 = 0 then 2750 else if t 3 = 1 then 2747 else 2756) else (if t 3 = 0 then 3210 else if t 3 = 1 then 3209 else 3499))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 223 else 917) else if t 2 = 1 then (if t 3 = 0 then 227 else if t 3 = 1 then 219 else 265) else (if t 3 = 0 then 1461 else if t 3 = 1 then 1458 else 2169)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 229 else if t 3 = 1 then 221 else 915) else if t 2 = 1 then (if t 3 = 0 then 225 else if t 3 = 1 then 217 else 263) else (if t 3 = 0 then 255 else if t 3 = 1 then 250 else 276)) else (if t 2 = 0 then (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 919) else if t 2 = 1 then (if t 3 = 0 then 242 else if t 3 = 1 then 237 else 272) else (if t 3 = 0 then 261 else if t 3 = 1 then 259 else 280))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 306 else 3229) else if t 2 = 1 then (if t 3 = 0 then 930 else if t 3 = 1 then 294 else 296) else (if t 3 = 0 then 2990 else if t 3 = 1 then 1473 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2139 else if t 3 = 1 then 300 else 1476) else if t 2 = 1 then (if t 3 = 0 then 924 else if t 3 = 1 then 282 else 286) else (if t 3 = 0 then 926 else if t 3 = 1 then 284 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 2141 else if t 3 = 1 then 301 else 1477) else if t 2 = 1 then (if t 3 = 0 then 925 else if t 3 = 1 then 283 else 287) else (if t 3 = 0 then 927 else if t 3 = 1 then 285 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4881 else (if jt.2.val < 2 then 4897 else 4886)) else (if jt.2.val < 4 then 4896 else (if jt.2.val < 5 then 4898 else 4884))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3717 else (if jt.2.val < 2 then 3752 else 3720)) else (if jt.2.val < 4 then 3750 else (if jt.2.val < 5 then 3751 else 3715)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1346 else (if jt.2.val < 2 then 1460 else 1351)) else (if jt.2.val < 4 then 1455 else (if jt.2.val < 5 then 1456 else 1302))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 848 else (if jt.2.val < 2 then 914 else 851)) else (if jt.2.val < 4 then 906 else (if jt.2.val < 5 then 907 else 793)))))

checked_coverage fastCoverage0735 pairing0735 template0735 witness0735

theorem coverage0735 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0735) (maskBits m))
    cores template0735 witness0735 := by
  rw [← coresFast_eq]
  exact fastCoverage0735

theorem coverageSize0735 : ∀ q : Pattern,
    (cores (witness0735 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0735 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0735
#print axioms coverageSize0735

noncomputable def pairing0736 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0736 : List (Fin 4935) := templateData0736

noncomputable def witness0736 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3340) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2973) else (if t 3 = 0 then 2732 else if t 3 = 1 then 2731 else 2738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 964) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 963) else (if t 3 = 0 then 344 else if t 3 = 1 then 342 else 373)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2197 else 1802) else if t 2 = 1 then (if t 3 = 0 then 2199 else if t 3 = 1 then 2195 else 979) else (if t 3 = 0 then 359 else if t 3 = 1 then 358 else 380))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 1042) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 1041) else (if t 3 = 0 then 442 else if t 3 = 1 then 440 else 472)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2838) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3472) else (if t 3 = 0 then 3082 else if t 3 = 1 then 3479 else 3486)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2842) else if t 2 = 1 then (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3473) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3480 else 3487))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 585 else 599) else if t 2 = 1 then (if t 3 = 0 then 586 else if t 3 = 1 then 584 else 598) else (if t 3 = 0 then 1838 else if t 3 = 1 then 1117 else 2149)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2572 else 2579) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3488 else 3490) else (if t 3 = 0 then 3315 else if t 3 = 1 then 3492 else 3494)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2574 else 2580) else if t 2 = 1 then (if t 3 = 0 then 3164 else if t 3 = 1 then 3489 else 3491) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3493 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4881 else (if jt.2.val < 2 then 4883 else 4886)) else (if jt.2.val < 4 then 4882 else (if jt.2.val < 5 then 4885 else 4884))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4648 else (if jt.2.val < 2 then 4652 else 4653)) else (if jt.2.val < 4 then 4649 else (if jt.2.val < 5 then 4651 else 4650)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3439 else (if jt.2.val < 2 then 3477 else 3478)) else (if jt.2.val < 4 then 3474 else (if jt.2.val < 5 then 3476 else 3475))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3627 else (if jt.2.val < 2 then 3631 else 3632)) else (if jt.2.val < 4 then 3628 else (if jt.2.val < 5 then 3630 else 3629)))))

checked_coverage fastCoverage0736 pairing0736 template0736 witness0736

theorem coverage0736 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0736) (maskBits m))
    cores template0736 witness0736 := by
  rw [← coresFast_eq]
  exact fastCoverage0736

theorem coverageSize0736 : ∀ q : Pattern,
    (cores (witness0736 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0736 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0736
#print axioms coverageSize0736

noncomputable def pairing0737 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0737 : List (Fin 4935) := templateData0737

noncomputable def witness0737 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3520) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2972) else (if t 3 = 0 then 2770 else if t 3 = 1 then 2769 else 2776)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 962) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 961) else (if t 3 = 0 then 144 else if t 3 = 1 then 142 else 172)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1879 else 2138) else if t 2 = 1 then (if t 3 = 0 then 1881 else if t 3 = 1 then 1877 else 978) else (if t 3 = 0 then 159 else if t 3 = 1 then 158 else 179))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 1040) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 1039) else (if t 3 = 0 then 638 else if t 3 = 1 then 636 else 664)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2837) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3276) else (if t 3 = 0 then 3091 else if t 3 = 1 then 3291 else 3293)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2841) else if t 2 = 1 then (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3279) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3292 else 3294))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 774 else 788) else if t 2 = 1 then (if t 3 = 0 then 775 else if t 3 = 1 then 773 else 787) else (if t 3 = 0 then 2162 else if t 3 = 1 then 1141 else 1825)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2717 else 2724) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3295 else 3297) else (if t 3 = 0 then 3500 else if t 3 = 1 then 3299 else 3301)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2719 else 2725) else if t 2 = 1 then (if t 3 = 0 then 3166 else if t 3 = 1 then 3296 else 3298) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3300 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4845 else (if jt.2.val < 2 then 4847 else 4850)) else (if jt.2.val < 4 then 4846 else (if jt.2.val < 5 then 4849 else 4848))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4369 else (if jt.2.val < 2 then 4373 else 4374)) else (if jt.2.val < 4 then 4370 else (if jt.2.val < 5 then 4372 else 4371)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3244 else (if jt.2.val < 2 then 3289 else 3290)) else (if jt.2.val < 4 then 3286 else (if jt.2.val < 5 then 3288 else 3287))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3629 else (if jt.2.val < 2 then 3635 else 3632)) else (if jt.2.val < 4 then 3633 else (if jt.2.val < 5 then 3634 else 3627)))))

checked_coverage fastCoverage0737 pairing0737 template0737 witness0737

theorem coverage0737 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0737) (maskBits m))
    cores template0737 witness0737 := by
  rw [← coresFast_eq]
  exact fastCoverage0737

theorem coverageSize0737 : ∀ q : Pattern,
    (cores (witness0737 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0737 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0737
#print axioms coverageSize0737

noncomputable def pairing0738 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0738 : List (Fin 4935) := templateData0738

noncomputable def witness0738 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2450 else 2485) else if t 2 = 1 then (if t 3 = 0 then 2446 else if t 3 = 1 then 2442 else 2482) else (if t 3 = 0 then 3505 else if t 3 = 1 then 3203 else 3344)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2448 else 1416) else if t 2 = 1 then (if t 3 = 0 then 2444 else if t 3 = 1 then 2440 else 1412) else (if t 3 = 0 then 341 else if t 3 = 1 then 339 else 372)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 726 else 758) else if t 2 = 1 then (if t 3 = 0 then 724 else if t 3 = 1 then 722 else 756) else (if t 3 = 0 then 2159 else if t 3 = 1 then 1489 else 1775))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2449 else 1586) else if t 2 = 1 then (if t 3 = 0 then 2445 else if t 3 = 1 then 2441 else 1582) else (if t 3 = 0 then 439 else if t 3 = 1 then 437 else 471)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2447 else 2484) else if t 2 = 1 then (if t 3 = 0 then 2443 else if t 3 = 1 then 2439 else 2481) else (if t 3 = 0 then 2470 else if t 3 = 1 then 2468 else 2488)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2487) else if t 2 = 1 then (if t 3 = 0 then 2461 else if t 3 = 1 then 2459 else 2486) else (if t 3 = 0 then 2474 else if t 3 = 1 then 2473 else 2490))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1915 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1906 else 1618) else (if t 3 = 0 then 505 else if t 3 = 1 then 493 else 495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2883 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2502 else if t 3 = 1 then 2492 else 2496) else (if t 3 = 0 then 2504 else if t 3 = 1 then 2494 else 2498)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2885 else 3507) else if t 2 = 1 then (if t 3 = 0 then 2503 else if t 3 = 1 then 2493 else 2497) else (if t 3 = 0 then 2505 else if t 3 = 1 then 2495 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4863 else (if jt.2.val < 2 then 4865 else 4868)) else (if jt.2.val < 4 then 4864 else (if jt.2.val < 5 then 4867 else 4866))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3691 else (if jt.2.val < 2 then 3695 else 3696)) else (if jt.2.val < 4 then 3692 else (if jt.2.val < 5 then 3694 else 3693)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3475 else (if jt.2.val < 2 then 3504 else 3478)) else (if jt.2.val < 4 then 3502 else (if jt.2.val < 5 then 3503 else 3439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2436 else (if jt.2.val < 2 then 2480 else 2483)) else (if jt.2.val < 4 then 2477 else (if jt.2.val < 5 then 2479 else 2478)))))

checked_coverage fastCoverage0738 pairing0738 template0738 witness0738

theorem coverage0738 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0738) (maskBits m))
    cores template0738 witness0738 := by
  rw [← coresFast_eq]
  exact fastCoverage0738

theorem coverageSize0738 : ∀ q : Pattern,
    (cores (witness0738 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0738 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0738
#print axioms coverageSize0738

noncomputable def pairing0739 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0739 : List (Fin 4935) := templateData0739

noncomputable def witness0739 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2602 else 2633) else if t 2 = 1 then (if t 3 = 0 then 2598 else if t 3 = 1 then 2594 else 2630) else (if t 3 = 0 then 3320 else if t 3 = 1 then 3172 else 3524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2600 else 1415) else if t 2 = 1 then (if t 3 = 0 then 2596 else if t 3 = 1 then 2592 else 1411) else (if t 3 = 0 then 141 else if t 3 = 1 then 139 else 171)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 538 else 569) else if t 2 = 1 then (if t 3 = 0 then 536 else if t 3 = 1 then 534 else 567) else (if t 3 = 0 then 1835 else if t 3 = 1 then 1537 else 2117))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2601 else 1585) else if t 2 = 1 then (if t 3 = 0 then 2597 else if t 3 = 1 then 2593 else 1581) else (if t 3 = 0 then 635 else if t 3 = 1 then 633 else 663)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2599 else 2632) else if t 2 = 1 then (if t 3 = 0 then 2595 else if t 3 = 1 then 2591 else 2629) else (if t 3 = 0 then 2622 else if t 3 = 1 then 2620 else 2636)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2635) else if t 2 = 1 then (if t 3 = 0 then 2613 else if t 3 = 1 then 2611 else 2634) else (if t 3 = 0 then 2626 else if t 3 = 1 then 2625 else 2638))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2227 else 1855) else if t 2 = 1 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2221 else 1615) else (if t 3 = 0 then 697 else if t 3 = 1 then 685 else 687)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2902 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2650 else if t 3 = 1 then 2640 else 2644) else (if t 3 = 0 then 2652 else if t 3 = 1 then 2642 else 2646)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2903 else 3322) else if t 2 = 1 then (if t 3 = 0 then 2651 else if t 3 = 1 then 2641 else 2645) else (if t 3 = 0 then 2653 else if t 3 = 1 then 2643 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4887 else (if jt.2.val < 2 then 4889 else 4892)) else (if jt.2.val < 4 then 4888 else (if jt.2.val < 5 then 4891 else 4890))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3715 else (if jt.2.val < 2 then 3719 else 3720)) else (if jt.2.val < 4 then 3716 else (if jt.2.val < 5 then 3718 else 3717)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3287 else (if jt.2.val < 2 then 3319 else 3290)) else (if jt.2.val < 4 then 3317 else (if jt.2.val < 5 then 3318 else 3244))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2478 else (if jt.2.val < 2 then 2631 else 2483)) else (if jt.2.val < 4 then 2587 else (if jt.2.val < 5 then 2588 else 2436)))))

checked_coverage fastCoverage0739 pairing0739 template0739 witness0739

theorem coverage0739 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0739) (maskBits m))
    cores template0739 witness0739 := by
  rw [← coresFast_eq]
  exact fastCoverage0739

theorem coverageSize0739 : ∀ q : Pattern,
    (cores (witness0739 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0739 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0739
#print axioms coverageSize0739

noncomputable def pairing0740 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0740 : List (Fin 4935) := templateData0740

noncomputable def witness0740 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1816) else if t 2 = 1 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 1051) else (if t 3 = 0 then 452 else if t 3 = 1 then 450 else 477)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 835) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2082) else (if t 3 = 0 then 1342 else if t 3 = 1 then 2090 else 2098)) else (if t 2 = 0 then (if t 3 = 0 then 3532 else if t 3 = 1 then 3530 else 3330) else if t 2 = 1 then (if t 3 = 0 then 3531 else if t 3 = 1 then 3528 else 2939) else (if t 3 = 0 then 2691 else if t 3 = 1 then 2690 else 2706))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1815) else if t 2 = 1 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 1050) else (if t 3 = 0 then 451 else if t 3 = 1 then 449 else 476)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 834) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2081) else (if t 3 = 0 then 1341 else if t 3 = 1 then 2089 else 2097)) else (if t 2 = 0 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 840) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2083) else (if t 3 = 0 then 1344 else if t 3 = 1 then 2091 else 2099))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 1545 else 2763) else if t 2 = 1 then (if t 3 = 0 then 590 else if t 3 = 1 then 588 else 600) else (if t 3 = 0 then 3343 else if t 3 = 1 then 1119 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 194 else if t 3 = 1 then 192 else 204) else if t 2 = 1 then (if t 3 = 0 then 1446 else if t 3 = 1 then 2100 else 2103) else (if t 3 = 0 then 1779 else if t 3 = 1 then 2106 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 197 else if t 3 = 1 then 196 else 206) else if t 2 = 1 then (if t 3 = 0 then 1448 else if t 3 = 1 then 2102 else 2105) else (if t 3 = 0 then 1781 else if t 3 = 1 then 2108 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4887 else (if jt.2.val < 2 then 4894 else 4892)) else (if jt.2.val < 4 then 4893 else (if jt.2.val < 5 then 4895 else 4890))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4650 else (if jt.2.val < 2 then 4667 else 4653)) else (if jt.2.val < 4 then 4665 else (if jt.2.val < 5 then 4666 else 4648)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2044 else (if jt.2.val < 2 then 2087 else 2088)) else (if jt.2.val < 4 then 2084 else (if jt.2.val < 5 then 2086 else 2085))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2358 else (if jt.2.val < 2 then 2362 else 2363)) else (if jt.2.val < 4 then 2359 else (if jt.2.val < 5 then 2361 else 2360)))))

checked_coverage fastCoverage0740 pairing0740 template0740 witness0740

theorem coverage0740 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0740) (maskBits m))
    cores template0740 witness0740 := by
  rw [← coresFast_eq]
  exact fastCoverage0740

theorem coverageSize0740 : ∀ q : Pattern,
    (cores (witness0740 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0740 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0740
#print axioms coverageSize0740

noncomputable def pairing0741 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0741 : List (Fin 4935) := templateData0741

noncomputable def witness0741 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 2146) else if t 2 = 1 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 1049) else (if t 3 = 0 then 648 else if t 3 = 1 then 646 else 669)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 833) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1730) else (if t 3 = 0 then 1353 else if t 3 = 1 then 1747 else 1750)) else (if t 2 = 0 then (if t 3 = 0 then 3352 else if t 3 = 1 then 3350 else 3514) else if t 2 = 1 then (if t 3 = 0 then 3351 else if t 3 = 1 then 3348 else 2938) else (if t 3 = 0 then 2547 else if t 3 = 1 then 2546 else 2561))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 2145) else if t 2 = 1 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 1048) else (if t 3 = 0 then 647 else if t 3 = 1 then 645 else 668)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 832) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1729) else (if t 3 = 0 then 1352 else if t 3 = 1 then 1746 else 1749)) else (if t 2 = 0 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 839) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1734) else (if t 3 = 0 then 1355 else if t 3 = 1 then 1748 else 1751))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1497 else 2801) else if t 2 = 1 then (if t 3 = 0 then 779 else if t 3 = 1 then 777 else 789) else (if t 3 = 0 then 3523 else if t 3 = 1 then 1142 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 395 else if t 3 = 1 then 393 else 405) else if t 2 = 1 then (if t 3 = 0 then 1449 else if t 3 = 1 then 1752 else 1755) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1758 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 398 else if t 3 = 1 then 397 else 407) else if t 2 = 1 then (if t 3 = 0 then 1451 else if t 3 = 1 then 1754 else 1757) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1759 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4863 else (if jt.2.val < 2 then 4870 else 4868)) else (if jt.2.val < 4 then 4869 else (if jt.2.val < 5 then 4871 else 4866))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4371 else (if jt.2.val < 2 then 4388 else 4374)) else (if jt.2.val < 4 then 4386 else (if jt.2.val < 5 then 4387 else 4369)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1693 else (if jt.2.val < 2 then 1744 else 1745)) else (if jt.2.val < 4 then 1741 else (if jt.2.val < 5 then 1743 else 1742))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2360 else (if jt.2.val < 2 then 2366 else 2363)) else (if jt.2.val < 4 then 2364 else (if jt.2.val < 5 then 2365 else 2358)))))

checked_coverage fastCoverage0741 pairing0741 template0741 witness0741

theorem coverage0741 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0741) (maskBits m))
    cores template0741 witness0741 := by
  rw [← coresFast_eq]
  exact fastCoverage0741

theorem coverageSize0741 : ∀ q : Pattern,
    (cores (witness0741 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0741 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0741
#print axioms coverageSize0741

noncomputable def pairing0742 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0742 : List (Fin 4935) := templateData0742

noncomputable def witness0742 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 20 else 67) else if t 2 = 1 then (if t 3 = 0 then 16 else if t 3 = 1 then 12 else 62) else (if t 3 = 0 then 2125 else if t 3 = 1 then 1507 else 1849)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 22 else if t 3 = 1 then 18 else 65) else if t 2 = 1 then (if t 3 = 0 then 14 else if t 3 = 1 then 10 else 60) else (if t 3 = 0 then 46 else if t 3 = 1 then 43 else 73)) else (if t 2 = 0 then (if t 3 = 0 then 2789 else if t 3 = 1 then 2788 else 2795) else if t 2 = 1 then (if t 3 = 0 then 2787 else if t 3 = 1 then 2785 else 2794) else (if t 3 = 0 then 3522 else if t 3 = 1 then 3191 else 3312))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 19 else 66) else if t 2 = 1 then (if t 3 = 0 then 15 else if t 3 = 1 then 11 else 61) else (if t 3 = 0 then 2124 else if t 3 = 1 then 1506 else 1848)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 21 else if t 3 = 1 then 17 else 64) else if t 2 = 1 then (if t 3 = 0 then 13 else if t 3 = 1 then 9 else 59) else (if t 3 = 0 then 45 else if t 3 = 1 then 42 else 72)) else (if t 2 = 0 then (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 70) else if t 2 = 1 then (if t 3 = 0 then 32 else if t 3 = 1 then 29 else 68) else (if t 3 = 0 then 52 else if t 3 = 1 then 51 else 76))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 899 else 3525) else if t 2 = 1 then (if t 3 = 0 then 102 else if t 3 = 1 then 90 else 92) else (if t 3 = 0 then 2744 else if t 3 = 1 then 1521 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1806 else if t 3 = 1 then 897 else 2127) else if t 2 = 1 then (if t 3 = 0 then 96 else if t 3 = 1 then 78 else 82) else (if t 3 = 0 then 98 else if t 3 = 1 then 80 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 1808 else if t 3 = 1 then 901 else 2128) else if t 2 = 1 then (if t 3 = 0 then 97 else if t 3 = 1 then 79 else 83) else (if t 3 = 0 then 99 else if t 3 = 1 then 81 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4845 else (if jt.2.val < 2 then 4879 else 4850)) else (if jt.2.val < 4 then 4878 else (if jt.2.val < 5 then 4880 else 4848))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3693 else (if jt.2.val < 2 then 3740 else 3696)) else (if jt.2.val < 4 then 3738 else (if jt.2.val < 5 then 3739 else 3691)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2085 else (if jt.2.val < 2 then 2123 else 2088)) else (if jt.2.val < 4 then 2121 else (if jt.2.val < 5 then 2122 else 2044))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 6 else (if jt.2.val < 2 then 58 else 63)) else (if jt.2.val < 4 then 55 else (if jt.2.val < 5 then 57 else 56)))))

checked_coverage fastCoverage0742 pairing0742 template0742 witness0742

theorem coverage0742 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0742) (maskBits m))
    cores template0742 witness0742 := by
  rw [← coresFast_eq]
  exact fastCoverage0742

theorem coverageSize0742 : ∀ q : Pattern,
    (cores (witness0742 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0742 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0742
#print axioms coverageSize0742

noncomputable def pairing0743 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0743 : List (Fin 4935) := templateData0743

noncomputable def witness0743 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 228 else 271) else if t 2 = 1 then (if t 3 = 0 then 224 else if t 3 = 1 then 220 else 266) else (if t 3 = 0 then 1786 else if t 3 = 1 then 1459 else 2170)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 230 else if t 3 = 1 then 226 else 269) else if t 2 = 1 then (if t 3 = 0 then 222 else if t 3 = 1 then 218 else 264) else (if t 3 = 0 then 254 else if t 3 = 1 then 251 else 277)) else (if t 2 = 0 then (if t 3 = 0 then 2751 else if t 3 = 1 then 2750 else 2757) else if t 2 = 1 then (if t 3 = 0 then 2749 else if t 3 = 1 then 2747 else 2756) else (if t 3 = 0 then 3342 else if t 3 = 1 then 3209 else 3499))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 227 else 270) else if t 2 = 1 then (if t 3 = 0 then 223 else if t 3 = 1 then 219 else 265) else (if t 3 = 0 then 1785 else if t 3 = 1 then 1458 else 2169)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 229 else if t 3 = 1 then 225 else 268) else if t 2 = 1 then (if t 3 = 0 then 221 else if t 3 = 1 then 217 else 263) else (if t 3 = 0 then 253 else if t 3 = 1 then 250 else 276)) else (if t 2 = 0 then (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 274) else if t 2 = 1 then (if t 3 = 0 then 240 else if t 3 = 1 then 237 else 272) else (if t 3 = 0 then 260 else if t 3 = 1 then 259 else 280))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 930 else 3345) else if t 2 = 1 then (if t 3 = 0 then 306 else if t 3 = 1 then 294 else 296) else (if t 3 = 0 then 2782 else if t 3 = 1 then 1473 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2139 else if t 3 = 1 then 924 else 1788) else if t 2 = 1 then (if t 3 = 0 then 300 else if t 3 = 1 then 282 else 286) else (if t 3 = 0 then 302 else if t 3 = 1 then 284 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 2141 else if t 3 = 1 then 925 else 1789) else if t 2 = 1 then (if t 3 = 0 then 301 else if t 3 = 1 then 283 else 287) else (if t 3 = 0 then 303 else if t 3 = 1 then 285 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4881 else (if jt.2.val < 2 then 4897 else 4886)) else (if jt.2.val < 4 then 4896 else (if jt.2.val < 5 then 4898 else 4884))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3717 else (if jt.2.val < 2 then 3752 else 3720)) else (if jt.2.val < 4 then 3750 else (if jt.2.val < 5 then 3751 else 3715)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1742 else (if jt.2.val < 2 then 1784 else 1745)) else (if jt.2.val < 4 then 1782 else (if jt.2.val < 5 then 1783 else 1693))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 56 else (if jt.2.val < 2 then 267 else 63)) else (if jt.2.val < 4 then 213 else (if jt.2.val < 5 then 214 else 6)))))

checked_coverage fastCoverage0743 pairing0743 template0743 witness0743

theorem coverage0743 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0743) (maskBits m))
    cores template0743 witness0743 := by
  rw [← coresFast_eq]
  exact fastCoverage0743

theorem coverageSize0743 : ∀ q : Pattern,
    (cores (witness0743 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0743 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0743
#print axioms coverageSize0743

noncomputable def pairing0744 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0744 : List (Fin 4935) := templateData0744

noncomputable def witness0744 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 3925) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2750) else (if t 3 = 0 then 2997 else if t 3 = 1 then 2995 else 2757)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 538) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 537) else (if t 3 = 0 then 1174 else if t 3 = 1 then 1170 else 568)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1879 else 1538) else if t 2 = 1 then (if t 3 = 0 then 1882 else if t 3 = 1 then 1878 else 554) else (if t 3 = 0 then 1190 else if t 3 = 1 then 1188 else 575))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 243) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 242) else (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 274)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2614) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4015) else (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4017)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2627) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4016) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4003 else 4018))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 390 else 931) else if t 2 = 1 then (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 925) else (if t 3 = 0 then 1502 else if t 3 = 1 then 403 else 1789)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2903) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4023) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4021 else 4025)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2719 else 2905) else if t 2 = 1 then (if t 3 = 0 then 3918 else if t 3 = 1 then 4020 else 4024) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4022 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4899 else (if jt.2.val < 2 then 4901 else 4904)) else (if jt.2.val < 4 then 4900 else (if jt.2.val < 5 then 4903 else 4902))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4432 else (if jt.2.val < 2 then 4436 else 4437)) else (if jt.2.val < 4 then 4433 else (if jt.2.val < 5 then 4435 else 4434)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4234 else (if jt.2.val < 2 then 4238 else 4239)) else (if jt.2.val < 4 then 4235 else (if jt.2.val < 5 then 4237 else 4236))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4069 else (if jt.2.val < 2 then 4075 else 4076)) else (if jt.2.val < 4 then 4070 else (if jt.2.val < 5 then 4072 else 4071)))))

checked_coverage fastCoverage0744 pairing0744 template0744 witness0744

theorem coverage0744 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0744) (maskBits m))
    cores template0744 witness0744 := by
  rw [← coresFast_eq]
  exact fastCoverage0744

theorem coverageSize0744 : ∀ q : Pattern,
    (cores (witness0744 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0744 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0744
#print axioms coverageSize0744

noncomputable def pairing0745 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0745 : List (Fin 4935) := templateData0745

noncomputable def witness0745 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4044) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2749) else (if t 3 = 0 then 2789 else if t 3 = 1 then 2787 else 2983)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 536) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 535) else (if t 3 = 0 then 727 else if t 3 = 1 then 723 else 1108)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1648 else 1835) else if t 2 = 1 then (if t 3 = 0 then 1651 else if t 3 = 1 then 1647 else 553) else (if t 3 = 0 then 743 else if t 3 = 1 then 741 else 1112))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 241) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 240) else (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 919)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2613) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3843) else (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3848)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2626) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3846) else (if t 3 = 0 then 3838 else if t 3 = 1 then 3837 else 3850))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 1003 else 307) else if t 2 = 1 then (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 301) else (if t 3 = 0 then 1808 else if t 3 = 1 then 97 else 1477)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2651) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3856) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3854 else 3858)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2957 else 2653) else if t 2 = 1 then (if t 3 = 0 then 4038 else if t 3 = 1 then 3853 else 3857) else (if t 3 = 0 then 4040 else if t 3 = 1 then 3855 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4905 else (if jt.2.val < 2 then 4907 else 4910)) else (if jt.2.val < 4 then 4906 else (if jt.2.val < 5 then 4909 else 4908))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4396 else (if jt.2.val < 2 then 4400 else 4401)) else (if jt.2.val < 4 then 4397 else (if jt.2.val < 5 then 4399 else 4398)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4096 else (if jt.2.val < 2 then 4100 else 4101)) else (if jt.2.val < 4 then 4097 else (if jt.2.val < 5 then 4099 else 4098))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4071 else (if jt.2.val < 2 then 4085 else 4076)) else (if jt.2.val < 4 then 4080 else (if jt.2.val < 5 then 4081 else 4069)))))

checked_coverage fastCoverage0745 pairing0745 template0745 witness0745

theorem coverage0745 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0745) (maskBits m))
    cores template0745 witness0745 := by
  rw [← coresFast_eq]
  exact fastCoverage0745

theorem coverageSize0745 : ∀ q : Pattern,
    (cores (witness0745 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0745 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0745
#print axioms coverageSize0745

noncomputable def pairing0746 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0746 : List (Fin 4935) := templateData0746

noncomputable def witness0746 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2813 else 2633) else if t 2 = 1 then (if t 3 = 0 then 2817 else if t 3 = 1 then 2809 else 2855) else (if t 3 = 0 then 4056 else if t 3 = 1 then 4054 else 3954)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2811 else 1415) else if t 2 = 1 then (if t 3 = 0 then 2815 else if t 3 = 1 then 2807 else 1414) else (if t 3 = 0 then 1173 else if t 3 = 1 then 1169 else 1202)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 962 else 173) else if t 2 = 1 then (if t 3 = 0 then 964 else if t 3 = 1 then 960 else 992) else (if t 3 = 0 then 1802 else if t 3 = 1 then 1801 else 1433))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2812 else 1585) else if t 2 = 1 then (if t 3 = 0 then 2816 else if t 3 = 1 then 2808 else 1584) else (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 857)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2810 else 2632) else if t 2 = 1 then (if t 3 = 0 then 2814 else if t 3 = 1 then 2806 else 2854) else (if t 3 = 0 then 2829 else if t 3 = 1 then 2826 else 2856)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2637) else if t 2 = 1 then (if t 3 = 0 then 2838 else if t 3 = 1 then 2835 else 2857) else (if t 3 = 0 then 2842 else if t 3 = 1 then 2840 else 2858))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1686 else 1855) else if t 2 = 1 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1685 else 1852) else (if t 3 = 0 then 203 else if t 3 = 1 then 866 else 877)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2721 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2576 else if t 3 = 1 then 2859 else 2864) else (if t 3 = 0 then 2578 else if t 3 = 1 then 2861 else 2865)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2724 else 4045) else if t 2 = 1 then (if t 3 = 0 then 2579 else if t 3 = 1 then 2862 else 2866) else (if t 3 = 0 then 2580 else if t 3 = 1 then 2863 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4857 else (if jt.2.val < 2 then 4859 else 4862)) else (if jt.2.val < 4 then 4858 else (if jt.2.val < 5 then 4861 else 4860))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2804 else (if jt.2.val < 2 then 2834 else 2836)) else (if jt.2.val < 4 then 2831 else (if jt.2.val < 5 then 2833 else 2832)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4236 else (if jt.2.val < 2 then 4253 else 4239)) else (if jt.2.val < 4 then 4251 else (if jt.2.val < 5 then 4252 else 4234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3007 else (if jt.2.val < 2 then 3016 else 3017)) else (if jt.2.val < 4 then 3008 else (if jt.2.val < 5 then 3010 else 3009)))))

checked_coverage fastCoverage0746 pairing0746 template0746 witness0746

theorem coverage0746 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0746) (maskBits m))
    cores template0746 witness0746 := by
  rw [← coresFast_eq]
  exact fastCoverage0746

theorem coverageSize0746 : ∀ q : Pattern,
    (cores (witness0746 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0746 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0746
#print axioms coverageSize0746

noncomputable def pairing0747 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0747 : List (Fin 4935) := templateData0747

noncomputable def witness0747 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2446 else 2898) else if t 2 = 1 then (if t 3 = 0 then 2450 else if t 3 = 1 then 2442 else 2482) else (if t 3 = 0 then 3941 else if t 3 = 1 then 3939 else 4060)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2444 else 1413) else if t 2 = 1 then (if t 3 = 0 then 2448 else if t 3 = 1 then 2440 else 1412) else (if t 3 = 0 then 726 else if t 3 = 1 then 722 else 756)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 341 else 893) else if t 2 = 1 then (if t 3 = 0 then 343 else if t 3 = 1 then 339 else 372) else (if t 3 = 0 then 1490 else if t 3 = 1 then 1489 else 1775))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2445 else 1583) else if t 2 = 1 then (if t 3 = 0 then 2449 else if t 3 = 1 then 2441 else 1582) else (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 69)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2443 else 2897) else if t 2 = 1 then (if t 3 = 0 then 2447 else if t 3 = 1 then 2439 else 2481) else (if t 3 = 0 then 2462 else if t 3 = 1 then 2459 else 2486)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2900) else if t 2 = 1 then (if t 3 = 0 then 2471 else if t 3 = 1 then 2468 else 2488) else (if t 3 = 0 then 2475 else if t 3 = 1 then 2473 else 2490))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1909 else 1621) else if t 2 = 1 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1906 else 1618) else (if t 3 = 0 then 902 else if t 3 = 1 then 91 else 93)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2502 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2883 else if t 3 = 1 then 2492 else 2496) else (if t 3 = 0 then 2885 else if t 3 = 1 then 2493 else 2497)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2504 else 3928) else if t 2 = 1 then (if t 3 = 0 then 2886 else if t 3 = 1 then 2494 else 2498) else (if t 3 = 0 then 2887 else if t 3 = 1 then 2495 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4863 else (if jt.2.val < 2 then 4865 else 4868)) else (if jt.2.val < 4 then 4864 else (if jt.2.val < 5 then 4867 else 4866))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2437 else (if jt.2.val < 2 then 2467 else 2469)) else (if jt.2.val < 4 then 2464 else (if jt.2.val < 5 then 2466 else 2465)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4098 else (if jt.2.val < 2 then 4121 else 4101)) else (if jt.2.val < 4 then 4119 else (if jt.2.val < 5 then 4120 else 4096))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3009 else (if jt.2.val < 2 then 3026 else 3017)) else (if jt.2.val < 4 then 3018 else (if jt.2.val < 5 then 3019 else 3007)))))

checked_coverage fastCoverage0747 pairing0747 template0747 witness0747

theorem coverage0747 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0747) (maskBits m))
    cores template0747 witness0747 := by
  rw [← coresFast_eq]
  exact fastCoverage0747

theorem coverageSize0747 : ∀ q : Pattern,
    (cores (witness0747 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0747 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0747
#print axioms coverageSize0747

noncomputable def pairing0748 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0748 : List (Fin 4935) := templateData0748

noncomputable def witness0748 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 1462) else if t 2 = 1 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 256) else (if t 3 = 0 then 837 else if t 3 = 1 then 833 else 279)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 646) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1747) else (if t 3 = 0 then 1733 else if t 3 = 1 then 1730 else 1750)) else (if t 2 = 0 then (if t 3 = 0 then 4066 else if t 3 = 1 then 4064 else 3946) else if t 2 = 1 then (if t 3 = 0 then 3351 else if t 3 = 1 then 3348 else 2546) else (if t 3 = 0 then 2940 else if t 3 = 1 then 2938 else 2561))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 1461) else if t 2 = 1 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 255) else (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 278)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 645) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1746) else (if t 3 = 0 then 1732 else if t 3 = 1 then 1729 else 1749)) else (if t 2 = 0 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 651) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1748) else (if t 3 = 0 then 1735 else if t 3 = 1 then 1734 else 1751))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1497 else 2990) else if t 2 = 1 then (if t 3 = 0 then 395 else if t 3 = 1 then 393 else 926) else (if t 3 = 0 then 3952 else if t 3 = 1 then 405 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 779 else if t 3 = 1 then 777 else 1142) else if t 2 = 1 then (if t 3 = 0 then 1449 else if t 3 = 1 then 1752 else 1758) else (if t 3 = 0 then 1452 else if t 3 = 1 then 1755 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 782 else if t 3 = 1 then 781 else 1143) else if t 2 = 1 then (if t 3 = 0 then 1451 else if t 3 = 1 then 1754 else 1759) else (if t 3 = 0 then 1454 else if t 3 = 1 then 1757 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4863 else (if jt.2.val < 2 then 4870 else 4868)) else (if jt.2.val < 4 then 4869 else (if jt.2.val < 5 then 4871 else 4866))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4434 else (if jt.2.val < 2 then 4445 else 4437)) else (if jt.2.val < 4 then 4443 else (if jt.2.val < 5 then 4444 else 4432)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1694 else (if jt.2.val < 2 then 1728 else 1731)) else (if jt.2.val < 4 then 1725 else (if jt.2.val < 5 then 1727 else 1726))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1918 else (if jt.2.val < 2 then 1924 else 1925)) else (if jt.2.val < 4 then 1919 else (if jt.2.val < 5 then 1921 else 1920)))))

checked_coverage fastCoverage0748 pairing0748 template0748 witness0748

theorem coverage0748 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0748) (maskBits m))
    cores template0748 witness0748 := by
  rw [← coresFast_eq]
  exact fastCoverage0748

theorem coverageSize0748 : ∀ q : Pattern,
    (cores (witness0748 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0748 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0748
#print axioms coverageSize0748

noncomputable def pairing0749 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0749 : List (Fin 4935) := templateData0749

noncomputable def witness0749 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 1786) else if t 2 = 1 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 254) else (if t 3 = 0 then 50 else if t 3 = 1 then 46 else 922)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 644) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1350) else (if t 3 = 0 then 1342 else if t 3 = 1 then 1339 else 1357)) else (if t 2 = 0 then (if t 3 = 0 then 3965 else if t 3 = 1 then 3963 else 4058) else if t 2 = 1 then (if t 3 = 0 then 3235 else if t 3 = 1 then 3232 else 2545) else (if t 3 = 0 then 2691 else if t 3 = 1 then 2689 else 2882))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 1785) else if t 2 = 1 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 253) else (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 921)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 643) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1349) else (if t 3 = 0 then 1341 else if t 3 = 1 then 1338 else 1356)) else (if t 2 = 0 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 650) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1354) else (if t 3 = 0 then 1344 else if t 3 = 1 then 1343 else 1360))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1374 else 2782) else if t 2 = 1 then (if t 3 = 0 then 1011 else if t 3 = 1 then 998 else 302) else (if t 3 = 0 then 4059 else if t 3 = 1 then 98 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1208 else 692) else if t 2 = 1 then (if t 3 = 0 then 1776 else if t 3 = 1 then 1362 else 1366) else (if t 3 = 0 then 1779 else if t 3 = 1 then 1364 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 1223 else if t 3 = 1 then 1209 else 693) else if t 2 = 1 then (if t 3 = 0 then 1778 else if t 3 = 1 then 1363 else 1367) else (if t 3 = 0 then 1781 else if t 3 = 1 then 1365 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4857 else (if jt.2.val < 2 then 4873 else 4862)) else (if jt.2.val < 4 then 4872 else (if jt.2.val < 5 then 4874 else 4860))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4398 else (if jt.2.val < 2 then 4421 else 4401)) else (if jt.2.val < 4 then 4419 else (if jt.2.val < 5 then 4420 else 4396)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1303 else (if jt.2.val < 2 then 1337 else 1340)) else (if jt.2.val < 4 then 1334 else (if jt.2.val < 5 then 1336 else 1335))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1920 else (if jt.2.val < 2 then 1934 else 1925)) else (if jt.2.val < 4 then 1929 else (if jt.2.val < 5 then 1930 else 1918)))))

checked_coverage fastCoverage0749 pairing0749 template0749 witness0749

theorem coverage0749 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0749) (maskBits m))
    cores template0749 witness0749 := by
  rw [← coresFast_eq]
  exact fastCoverage0749

theorem coverageSize0749 : ∀ q : Pattern,
    (cores (witness0749 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0749 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0749
#print axioms coverageSize0749

noncomputable def pairing0750 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0750 : List (Fin 4935) := templateData0750

noncomputable def witness0750 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1025 else 661) else if t 2 = 1 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1021 else 1071) else (if t 3 = 0 then 1816 else if t 3 = 1 then 1813 else 1599)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1023 else 659) else if t 2 = 1 then (if t 3 = 0 then 1027 else if t 3 = 1 then 1019 else 1069) else (if t 3 = 0 then 1051 else if t 3 = 1 then 1046 else 1075)) else (if t 2 = 0 then (if t 3 = 0 then 2974 else if t 3 = 1 then 2972 else 2776) else if t 2 = 1 then (if t 3 = 0 then 2973 else if t 3 = 1 then 2970 else 2979) else (if t 3 = 0 then 4047 else if t 3 = 1 then 4046 else 3905))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1024 else 660) else if t 2 = 1 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1020 else 1070) else (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1598)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1022 else 658) else if t 2 = 1 then (if t 3 = 0 then 1026 else if t 3 = 1 then 1018 else 1068) else (if t 3 = 0 then 1050 else if t 3 = 1 then 1045 else 1074)) else (if t 2 = 0 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 664) else if t 2 = 1 then (if t 3 = 0 then 1041 else if t 3 = 1 then 1037 else 1072) else (if t 3 = 0 then 1056 else if t 3 = 1 then 1054 else 1076))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 785 else 4061) else if t 2 = 1 then (if t 3 = 0 then 596 else if t 3 = 1 then 1079 else 1092) else (if t 3 = 0 then 2763 else if t 3 = 1 then 1689 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1548 else if t 3 = 1 then 783 else 1824) else if t 2 = 1 then (if t 3 = 0 then 594 else if t 3 = 1 then 1077 else 1086) else (if t 3 = 0 then 600 else if t 3 = 1 then 1083 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 1550 else if t 3 = 1 then 787 else 1825) else if t 2 = 1 then (if t 3 = 0 then 598 else if t 3 = 1 then 1081 else 1087) else (if t 3 = 0 then 602 else if t 3 = 1 then 1085 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4905 else (if jt.2.val < 2 then 4912 else 4910)) else (if jt.2.val < 4 then 4911 else (if jt.2.val < 5 then 4913 else 4908))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2832 else (if jt.2.val < 2 then 2971 else 2836)) else (if jt.2.val < 4 then 2968 else (if jt.2.val < 5 then 2969 else 2804)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1726 else (if jt.2.val < 2 then 1814 else 1731)) else (if jt.2.val < 4 then 1809 else (if jt.2.val < 5 then 1810 else 1694))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1261 else (if jt.2.val < 2 then 1270 else 1271)) else (if jt.2.val < 4 then 1264 else (if jt.2.val < 5 then 1266 else 1265)))))

checked_coverage fastCoverage0750 pairing0750 template0750 witness0750

theorem coverage0750 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0750) (maskBits m))
    cores template0750 witness0750 := by
  rw [← coresFast_eq]
  exact fastCoverage0750

theorem coverageSize0750 : ∀ q : Pattern,
    (cores (witness0750 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0750 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0750
#print axioms coverageSize0750

noncomputable def pairing0751 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0751 : List (Fin 4935) := templateData0751

noncomputable def witness0751 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 424 else 1134) else if t 2 = 1 then (if t 3 = 0 then 428 else if t 3 = 1 then 420 else 464) else (if t 3 = 0 then 1510 else if t 3 = 1 then 1507 else 1849)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 430 else if t 3 = 1 then 422 else 1132) else if t 2 = 1 then (if t 3 = 0 then 426 else if t 3 = 1 then 418 else 462) else (if t 3 = 0 then 450 else if t 3 = 1 then 445 else 475)) else (if t 2 = 0 then (if t 3 = 0 then 2732 else if t 3 = 1 then 2730 else 2987) else if t 2 = 1 then (if t 3 = 0 then 2731 else if t 3 = 1 then 2728 else 2737) else (if t 3 = 0 then 3930 else if t 3 = 1 then 3929 else 4036))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 423 else 1133) else if t 2 = 1 then (if t 3 = 0 then 427 else if t 3 = 1 then 419 else 463) else (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1848)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 429 else if t 3 = 1 then 421 else 1131) else if t 2 = 1 then (if t 3 = 0 then 425 else if t 3 = 1 then 417 else 461) else (if t 3 = 0 then 449 else if t 3 = 1 then 444 else 474)) else (if t 2 = 0 then (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 1135) else if t 2 = 1 then (if t 3 = 0 then 440 else if t 3 = 1 then 436 else 470) else (if t 3 = 0 then 455 else if t 3 = 1 then 453 else 478))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 504 else 3960) else if t 2 = 1 then (if t 3 = 0 then 1115 else if t 3 = 1 then 492 else 494) else (if t 3 = 0 then 2986 else if t 3 = 1 then 1521 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1836 else if t 3 = 1 then 498 else 1524) else if t 2 = 1 then (if t 3 = 0 then 1113 else if t 3 = 1 then 480 else 484) else (if t 3 = 0 then 1119 else if t 3 = 1 then 482 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 1838 else if t 3 = 1 then 499 else 1525) else if t 2 = 1 then (if t 3 = 0 then 1117 else if t 3 = 1 then 481 else 485) else (if t 3 = 0 then 1121 else if t 3 = 1 then 483 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4899 else (if jt.2.val < 2 then 4915 else 4904)) else (if jt.2.val < 4 then 4914 else (if jt.2.val < 5 then 4916 else 4902))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2465 else (if jt.2.val < 2 then 2729 else 2469)) else (if jt.2.val < 4 then 2726 else (if jt.2.val < 5 then 2727 else 2437)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1335 else (if jt.2.val < 2 then 1508 else 1340)) else (if jt.2.val < 4 then 1503 else (if jt.2.val < 5 then 1504 else 1303))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1265 else (if jt.2.val < 2 then 1280 else 1271)) else (if jt.2.val < 4 then 1275 else (if jt.2.val < 5 then 1276 else 1261)))))

checked_coverage fastCoverage0751 pairing0751 template0751 witness0751

theorem coverage0751 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0751) (maskBits m))
    cores template0751 witness0751 := by
  rw [← coresFast_eq]
  exact fastCoverage0751

theorem coverageSize0751 : ∀ q : Pattern,
    (cores (witness0751 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0751 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0751
#print axioms coverageSize0751

noncomputable def pairing0752 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0752 : List (Fin 4935) := templateData0752

noncomputable def witness0752 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 3941) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2788) else (if t 3 = 0 then 2997 else if t 3 = 1 then 2996 else 2795)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 726) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 725) else (if t 3 = 0 then 1174 else if t 3 = 1 then 1172 else 757)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2197 else 1490) else if t 2 = 1 then (if t 3 = 0 then 2200 else if t 3 = 1 then 2196 else 742) else (if t 3 = 0 then 1190 else if t 3 = 1 then 1189 else 764))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 35) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 34) else (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 70)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2462) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4170) else (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4177)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2475) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4171) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4164 else 4178))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 189 else 902) else if t 2 = 1 then (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 901) else (if t 3 = 0 then 1502 else if t 3 = 1 then 202 else 2128)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2885) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4183) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4181 else 4185)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2574 else 2887) else if t 2 = 1 then (if t 3 = 0 then 3916 else if t 3 = 1 then 4180 else 4184) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4182 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4917 else (if jt.2.val < 2 then 4919 else 4922)) else (if jt.2.val < 4 then 4918 else (if jt.2.val < 5 then 4921 else 4920))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4693 else (if jt.2.val < 2 then 4697 else 4698)) else (if jt.2.val < 4 then 4694 else (if jt.2.val < 5 then 4696 else 4695)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4261 else (if jt.2.val < 2 then 4265 else 4266)) else (if jt.2.val < 4 then 4262 else (if jt.2.val < 5 then 4264 else 4263))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4216 else (if jt.2.val < 2 then 4220 else 4221)) else (if jt.2.val < 4 then 4217 else (if jt.2.val < 5 then 4219 else 4218)))))

checked_coverage fastCoverage0752 pairing0752 template0752 witness0752

theorem coverage0752 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0752) (maskBits m))
    cores template0752 witness0752 := by
  rw [← coresFast_eq]
  exact fastCoverage0752

theorem coverageSize0752 : ∀ q : Pattern,
    (cores (witness0752 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0752 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0752
#print axioms coverageSize0752

noncomputable def pairing0753 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0753 : List (Fin 4935) := templateData0753

noncomputable def witness0753 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4196) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2787) else (if t 3 = 0 then 2751 else if t 3 = 1 then 2749 else 2983)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 724) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 723) else (if t 3 = 0 then 539 else if t 3 = 1 then 535 else 1108)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1648 else 2159) else if t 2 = 1 then (if t 3 = 0 then 1651 else if t 3 = 1 then 1647 else 741) else (if t 3 = 0 then 555 else if t 3 = 1 then 553 else 1112))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 33) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 32) else (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 919)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2461) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3834) else (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3848)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2474) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3837) else (if t 3 = 0 then 3847 else if t 3 = 1 then 3846 else 3850))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 1003 else 103) else if t 2 = 1 then (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 97) else (if t 3 = 0 then 2141 else if t 3 = 1 then 301 else 1477)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2503) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3854) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3856 else 3858)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2957 else 2505) else if t 2 = 1 then (if t 3 = 0 then 4038 else if t 3 = 1 then 3853 else 3855) else (if t 3 = 0 then 4192 else if t 3 = 1 then 3857 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4905 else (if jt.2.val < 2 then 4907 else 4910)) else (if jt.2.val < 4 then 4906 else (if jt.2.val < 5 then 4909 else 4908))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4396 else (if jt.2.val < 2 then 4400 else 4401)) else (if jt.2.val < 4 then 4397 else (if jt.2.val < 5 then 4399 else 4398)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3804 else (if jt.2.val < 2 then 3842 else 3844)) else (if jt.2.val < 4 then 3839 else (if jt.2.val < 5 then 3841 else 3840))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4218 else (if jt.2.val < 2 then 4229 else 4221)) else (if jt.2.val < 4 then 4227 else (if jt.2.val < 5 then 4228 else 4216)))))

checked_coverage fastCoverage0753 pairing0753 template0753 witness0753

theorem coverage0753 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0753) (maskBits m))
    cores template0753 witness0753 := by
  rw [← coresFast_eq]
  exact fastCoverage0753

theorem coverageSize0753 : ∀ q : Pattern,
    (cores (witness0753 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0753 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0753
#print axioms coverageSize0753

noncomputable def pairing0754 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0754 : List (Fin 4935) := templateData0754

noncomputable def witness0754 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2817 else 2485) else if t 2 = 1 then (if t 3 = 0 then 2813 else if t 3 = 1 then 2809 else 2855) else (if t 3 = 0 then 4203 else if t 3 = 1 then 4054 else 3954)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2815 else 1416) else if t 2 = 1 then (if t 3 = 0 then 2811 else if t 3 = 1 then 2807 else 1414) else (if t 3 = 0 then 1171 else if t 3 = 1 then 1169 else 1202)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 964 else 374) else if t 2 = 1 then (if t 3 = 0 then 962 else if t 3 = 1 then 960 else 992) else (if t 3 = 0 then 2138 else if t 3 = 1 then 1801 else 1433))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2816 else 1586) else if t 2 = 1 then (if t 3 = 0 then 2812 else if t 3 = 1 then 2808 else 1584) else (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 857)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2814 else 2484) else if t 2 = 1 then (if t 3 = 0 then 2810 else if t 3 = 1 then 2806 else 2854) else (if t 3 = 0 then 2828 else if t 3 = 1 then 2826 else 2856)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2838 else 2489) else if t 2 = 1 then (if t 3 = 0 then 2837 else if t 3 = 1 then 2835 else 2857) else (if t 3 = 0 then 2841 else if t 3 = 1 then 2840 else 2858))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1687 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1685 else 1852) else (if t 3 = 0 then 404 else if t 3 = 1 then 866 else 877)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2576 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2721 else if t 3 = 1 then 2859 else 2864) else (if t 3 = 0 then 2723 else if t 3 = 1 then 2861 else 2865)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2579 else 4197) else if t 2 = 1 then (if t 3 = 0 then 2724 else if t 3 = 1 then 2862 else 2866) else (if t 3 = 0 then 2725 else if t 3 = 1 then 2863 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4857 else (if jt.2.val < 2 then 4859 else 4862)) else (if jt.2.val < 4 then 4858 else (if jt.2.val < 5 then 4861 else 4860))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2804 else (if jt.2.val < 2 then 2834 else 2836)) else (if jt.2.val < 4 then 2831 else (if jt.2.val < 5 then 2833 else 2832)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4263 else (if jt.2.val < 2 then 4274 else 4266)) else (if jt.2.val < 4 then 4272 else (if jt.2.val < 5 then 4273 else 4261))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2803 else (if jt.2.val < 2 then 2852 else 2853)) else (if jt.2.val < 4 then 2849 else (if jt.2.val < 5 then 2851 else 2850)))))

checked_coverage fastCoverage0754 pairing0754 template0754 witness0754

theorem coverage0754 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0754) (maskBits m))
    cores template0754 witness0754 := by
  rw [← coresFast_eq]
  exact fastCoverage0754

theorem coverageSize0754 : ∀ q : Pattern,
    (cores (witness0754 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0754 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0754
#print axioms coverageSize0754

noncomputable def pairing0755 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0755 : List (Fin 4935) := templateData0755

noncomputable def witness0755 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2598 else 2898) else if t 2 = 1 then (if t 3 = 0 then 2602 else if t 3 = 1 then 2594 else 2630) else (if t 3 = 0 then 3925 else if t 3 = 1 then 3923 else 4207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2596 else 1413) else if t 2 = 1 then (if t 3 = 0 then 2600 else if t 3 = 1 then 2592 else 1411) else (if t 3 = 0 then 538 else if t 3 = 1 then 534 else 567)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 141 else 893) else if t 2 = 1 then (if t 3 = 0 then 143 else if t 3 = 1 then 139 else 171) else (if t 3 = 0 then 1538 else if t 3 = 1 then 1537 else 2117))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2597 else 1583) else if t 2 = 1 then (if t 3 = 0 then 2601 else if t 3 = 1 then 2593 else 1581) else (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 273)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2595 else 2897) else if t 2 = 1 then (if t 3 = 0 then 2599 else if t 3 = 1 then 2591 else 2629) else (if t 3 = 0 then 2614 else if t 3 = 1 then 2611 else 2634)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2622 else 2900) else if t 2 = 1 then (if t 3 = 0 then 2623 else if t 3 = 1 then 2620 else 2636) else (if t 3 = 0 then 2627 else if t 3 = 1 then 2625 else 2638))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2224 else 1621) else if t 2 = 1 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2221 else 1615) else (if t 3 = 0 then 931 else if t 3 = 1 then 295 else 297)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2650 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2902 else if t 3 = 1 then 2640 else 2644) else (if t 3 = 0 then 2903 else if t 3 = 1 then 2641 else 2645)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2652 else 3928) else if t 2 = 1 then (if t 3 = 0 then 2904 else if t 3 = 1 then 2642 else 2646) else (if t 3 = 0 then 2905 else if t 3 = 1 then 2643 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4887 else (if jt.2.val < 2 then 4889 else 4892)) else (if jt.2.val < 4 then 4888 else (if jt.2.val < 5 then 4891 else 4890))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2589 else (if jt.2.val < 2 then 2619 else 2621)) else (if jt.2.val < 4 then 2616 else (if jt.2.val < 5 then 2618 else 2617)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3840 else (if jt.2.val < 2 then 3924 else 3844)) else (if jt.2.val < 4 then 3921 else (if jt.2.val < 5 then 3922 else 3804))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2850 else (if jt.2.val < 2 then 2896 else 2853)) else (if jt.2.val < 4 then 2888 else (if jt.2.val < 5 then 2889 else 2803)))))

checked_coverage fastCoverage0755 pairing0755 template0755 witness0755

theorem coverage0755 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0755) (maskBits m))
    cores template0755 witness0755 := by
  rw [← coresFast_eq]
  exact fastCoverage0755

theorem coverageSize0755 : ∀ q : Pattern,
    (cores (witness0755 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0755 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0755
#print axioms coverageSize0755

noncomputable def pairing0756 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0756 : List (Fin 4935) := templateData0756

noncomputable def witness0756 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1510) else if t 2 = 1 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 48) else (if t 3 = 0 then 837 else if t 3 = 1 then 835 else 75)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 450) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2090) else (if t 3 = 0 then 1733 else if t 3 = 1 then 2082 else 2098)) else (if t 2 = 0 then (if t 3 = 0 then 4213 else if t 3 = 1 then 4211 else 3930) else if t 2 = 1 then (if t 3 = 0 then 3531 else if t 3 = 1 then 3528 else 2690) else (if t 3 = 0 then 2940 else if t 3 = 1 then 2939 else 2706))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1509) else if t 2 = 1 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 47) else (if t 3 = 0 then 836 else if t 3 = 1 then 834 else 74)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 449) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2089) else (if t 3 = 0 then 1732 else if t 3 = 1 then 2081 else 2097)) else (if t 2 = 0 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 455) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2091) else (if t 3 = 0 then 1735 else if t 3 = 1 then 2083 else 2099))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 1545 else 2986) else if t 2 = 1 then (if t 3 = 0 then 194 else if t 3 = 1 then 192 else 903) else (if t 3 = 0 then 3952 else if t 3 = 1 then 204 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 590 else if t 3 = 1 then 588 else 1119) else if t 2 = 1 then (if t 3 = 0 then 1446 else if t 3 = 1 then 2100 else 2106) else (if t 3 = 0 then 1452 else if t 3 = 1 then 2103 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 593 else if t 3 = 1 then 592 else 1121) else if t 2 = 1 then (if t 3 = 0 then 1448 else if t 3 = 1 then 2102 else 2108) else (if t 3 = 0 then 1454 else if t 3 = 1 then 2105 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4887 else (if jt.2.val < 2 then 4894 else 4892)) else (if jt.2.val < 4 then 4893 else (if jt.2.val < 5 then 4895 else 4890))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4695 else (if jt.2.val < 2 then 4706 else 4698)) else (if jt.2.val < 4 then 4704 else (if jt.2.val < 5 then 4705 else 4693)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2045 else (if jt.2.val < 2 then 2079 else 2080)) else (if jt.2.val < 4 then 2076 else (if jt.2.val < 5 then 2078 else 2077))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2233 else (if jt.2.val < 2 then 2237 else 2238)) else (if jt.2.val < 4 then 2234 else (if jt.2.val < 5 then 2236 else 2235)))))

checked_coverage fastCoverage0756 pairing0756 template0756 witness0756

theorem coverage0756 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0756) (maskBits m))
    cores template0756 witness0756 := by
  rw [← coresFast_eq]
  exact fastCoverage0756

theorem coverageSize0756 : ∀ q : Pattern,
    (cores (witness0756 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0756 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0756
#print axioms coverageSize0756

noncomputable def pairing0757 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0757 : List (Fin 4935) := templateData0757

noncomputable def witness0757 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 2125) else if t 2 = 1 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 46) else (if t 3 = 0 then 258 else if t 3 = 1 then 254 else 922)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 448) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1339) else (if t 3 = 0 then 1353 else if t 3 = 1 then 1350 else 1357)) else (if t 2 = 0 then (if t 3 = 0 then 3965 else if t 3 = 1 then 3963 else 4205) else if t 2 = 1 then (if t 3 = 0 then 3235 else if t 3 = 1 then 3232 else 2689) else (if t 3 = 0 then 2547 else if t 3 = 1 then 2545 else 2882))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 2124) else if t 2 = 1 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 45) else (if t 3 = 0 then 257 else if t 3 = 1 then 253 else 921)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 447) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1338) else (if t 3 = 0 then 1352 else if t 3 = 1 then 1349 else 1356)) else (if t 2 = 0 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 454) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1343) else (if t 3 = 0 then 1355 else if t 3 = 1 then 1354 else 1360))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1374 else 2744) else if t 2 = 1 then (if t 3 = 0 then 1011 else if t 3 = 1 then 998 else 98) else (if t 3 = 0 then 4206 else if t 3 = 1 then 302 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1208 else 500) else if t 2 = 1 then (if t 3 = 0 then 1776 else if t 3 = 1 then 1362 else 1364) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1366 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 1223 else if t 3 = 1 then 1209 else 501) else if t 2 = 1 then (if t 3 = 0 then 1778 else if t 3 = 1 then 1363 else 1365) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1367 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4857 else (if jt.2.val < 2 then 4873 else 4862)) else (if jt.2.val < 4 then 4872 else (if jt.2.val < 5 then 4874 else 4860))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4398 else (if jt.2.val < 2 then 4421 else 4401)) else (if jt.2.val < 4 then 4419 else (if jt.2.val < 5 then 4420 else 4396)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1971 else (if jt.2.val < 2 then 1981 else 1982)) else (if jt.2.val < 4 then 1978 else (if jt.2.val < 5 then 1980 else 1979))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2235 else (if jt.2.val < 2 then 2246 else 2238)) else (if jt.2.val < 4 then 2244 else (if jt.2.val < 5 then 2245 else 2233)))))

checked_coverage fastCoverage0757 pairing0757 template0757 witness0757

theorem coverage0757 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0757) (maskBits m))
    cores template0757 witness0757 := by
  rw [← coresFast_eq]
  exact fastCoverage0757

theorem coverageSize0757 : ∀ q : Pattern,
    (cores (witness0757 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0757 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0757
#print axioms coverageSize0757

noncomputable def pairing0758 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0758 : List (Fin 4935) := templateData0758

noncomputable def witness0758 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1029 else 469) else if t 2 = 1 then (if t 3 = 0 then 1025 else if t 3 = 1 then 1021 else 1071) else (if t 3 = 0 then 2146 else if t 3 = 1 then 1813 else 1599)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1027 else 467) else if t 2 = 1 then (if t 3 = 0 then 1023 else if t 3 = 1 then 1019 else 1069) else (if t 3 = 0 then 1049 else if t 3 = 1 then 1046 else 1075)) else (if t 2 = 0 then (if t 3 = 0 then 2974 else if t 3 = 1 then 2973 else 2738) else if t 2 = 1 then (if t 3 = 0 then 2972 else if t 3 = 1 then 2970 else 2979) else (if t 3 = 0 then 4198 else if t 3 = 1 then 4046 else 3905))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1028 else 468) else if t 2 = 1 then (if t 3 = 0 then 1024 else if t 3 = 1 then 1020 else 1070) else (if t 3 = 0 then 2145 else if t 3 = 1 then 1812 else 1598)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1026 else 466) else if t 2 = 1 then (if t 3 = 0 then 1022 else if t 3 = 1 then 1018 else 1068) else (if t 3 = 0 then 1048 else if t 3 = 1 then 1045 else 1074)) else (if t 2 = 0 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1041 else 472) else if t 2 = 1 then (if t 3 = 0 then 1039 else if t 3 = 1 then 1037 else 1072) else (if t 3 = 0 then 1055 else if t 3 = 1 then 1054 else 1076))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 596 else 4208) else if t 2 = 1 then (if t 3 = 0 then 785 else if t 3 = 1 then 1079 else 1092) else (if t 3 = 0 then 2801 else if t 3 = 1 then 1689 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1548 else if t 3 = 1 then 594 else 2148) else if t 2 = 1 then (if t 3 = 0 then 783 else if t 3 = 1 then 1077 else 1086) else (if t 3 = 0 then 789 else if t 3 = 1 then 1083 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 1550 else if t 3 = 1 then 598 else 2149) else if t 2 = 1 then (if t 3 = 0 then 787 else if t 3 = 1 then 1081 else 1087) else (if t 3 = 0 then 791 else if t 3 = 1 then 1085 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4905 else (if jt.2.val < 2 then 4912 else 4910)) else (if jt.2.val < 4 then 4911 else (if jt.2.val < 5 then 4913 else 4908))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2832 else (if jt.2.val < 2 then 2971 else 2836)) else (if jt.2.val < 4 then 2968 else (if jt.2.val < 5 then 2969 else 2804)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2077 else (if jt.2.val < 2 then 2144 else 2080)) else (if jt.2.val < 4 then 2142 else (if jt.2.val < 5 then 2143 else 2045))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1017 else (if jt.2.val < 2 then 1066 else 1067)) else (if jt.2.val < 4 then 1063 else (if jt.2.val < 5 then 1065 else 1064)))))

checked_coverage fastCoverage0758 pairing0758 template0758 witness0758

theorem coverage0758 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0758) (maskBits m))
    cores template0758 witness0758 := by
  rw [← coresFast_eq]
  exact fastCoverage0758

theorem coverageSize0758 : ∀ q : Pattern,
    (cores (witness0758 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0758 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0758
#print axioms coverageSize0758

noncomputable def pairing0759 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0759 : List (Fin 4935) := templateData0759

noncomputable def witness0759 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 620 else 1134) else if t 2 = 1 then (if t 3 = 0 then 624 else if t 3 = 1 then 616 else 656) else (if t 3 = 0 then 1462 else if t 3 = 1 then 1459 else 2170)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 626 else if t 3 = 1 then 618 else 1132) else if t 2 = 1 then (if t 3 = 0 then 622 else if t 3 = 1 then 614 else 654) else (if t 3 = 0 then 646 else if t 3 = 1 then 641 else 667)) else (if t 2 = 0 then (if t 3 = 0 then 2770 else if t 3 = 1 then 2768 else 2987) else if t 2 = 1 then (if t 3 = 0 then 2769 else if t 3 = 1 then 2766 else 2775) else (if t 3 = 0 then 3946 else if t 3 = 1 then 3945 else 4190))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 619 else 1133) else if t 2 = 1 then (if t 3 = 0 then 623 else if t 3 = 1 then 615 else 655) else (if t 3 = 0 then 1461 else if t 3 = 1 then 1458 else 2169)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 625 else if t 3 = 1 then 617 else 1131) else if t 2 = 1 then (if t 3 = 0 then 621 else if t 3 = 1 then 613 else 653) else (if t 3 = 0 then 645 else if t 3 = 1 then 640 else 666)) else (if t 2 = 0 then (if t 3 = 0 then 638 else if t 3 = 1 then 634 else 1135) else if t 2 = 1 then (if t 3 = 0 then 636 else if t 3 = 1 then 632 else 662) else (if t 3 = 0 then 651 else if t 3 = 1 then 649 else 670))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 696 else 3960) else if t 2 = 1 then (if t 3 = 0 then 1146 else if t 3 = 1 then 684 else 686) else (if t 3 = 0 then 2990 else if t 3 = 1 then 1473 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2160 else if t 3 = 1 then 690 else 1524) else if t 2 = 1 then (if t 3 = 0 then 1140 else if t 3 = 1 then 672 else 676) else (if t 3 = 0 then 1142 else if t 3 = 1 then 674 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 2162 else if t 3 = 1 then 691 else 1525) else if t 2 = 1 then (if t 3 = 0 then 1141 else if t 3 = 1 then 673 else 677) else (if t 3 = 0 then 1143 else if t 3 = 1 then 675 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4917 else (if jt.2.val < 2 then 4924 else 4922)) else (if jt.2.val < 4 then 4923 else (if jt.2.val < 5 then 4925 else 4920))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2617 else (if jt.2.val < 2 then 2767 else 2621)) else (if jt.2.val < 4 then 2764 else (if jt.2.val < 5 then 2765 else 2589)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1979 else (if jt.2.val < 2 then 2016 else 1982)) else (if jt.2.val < 4 then 2013 else (if jt.2.val < 5 then 2014 else 1971))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1064 else (if jt.2.val < 2 then 1130 else 1067)) else (if jt.2.val < 4 then 1125 else (if jt.2.val < 5 then 1126 else 1017)))))

checked_coverage fastCoverage0759 pairing0759 template0759 witness0759

theorem coverage0759 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0759) (maskBits m))
    cores template0759 witness0759 := by
  rw [← coresFast_eq]
  exact fastCoverage0759

theorem coverageSize0759 : ∀ q : Pattern,
    (cores (witness0759 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0759 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0759
#print axioms coverageSize0759

end Crown.CertificateData
