import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0004

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0160 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0160 : List (Fin 4935) := templateData0160

noncomputable def witness0160 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3174) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2769) else (if t 3 = 0 then 2798 else if t 3 = 1 then 2797 else 2989)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 143) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 142) else (if t 3 = 0 then 88 else if t 3 = 1 then 86 else 898)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 962 else 173) else if t 2 = 1 then (if t 3 = 0 then 965 else if t 3 = 1 then 961 else 172) else (if t 3 = 0 then 1478 else if t 3 = 1 then 100 else 1807))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 637) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 636) else (if t 3 = 0 then 775 else if t 3 = 1 then 773 else 1141)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2623) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3291) else (if t 3 = 0 then 3165 else if t 3 = 1 then 3295 else 3299)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2637) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3276 else 3293) else (if t 3 = 0 then 3167 else if t 3 = 1 then 3297 else 3301))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 1464) else if t 2 = 1 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 651) else (if t 3 = 0 then 782 else if t 3 = 1 then 781 else 1143)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2627) else if t 2 = 1 then (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3292) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3296 else 3300)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2841 else 2639) else if t 2 = 1 then (if t 3 = 0 then 3280 else if t 3 = 1 then 3279 else 3294) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3298 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3246 else (if jt.2.val < 2 then 3266 else 3268)) else (if jt.2.val < 4 then 3263 else (if jt.2.val < 5 then 3265 else 3264))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3245 else (if jt.2.val < 2 then 3275 else 3277)) else (if jt.2.val < 4 then 3272 else (if jt.2.val < 5 then 3274 else 3273)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3357 else (if jt.2.val < 2 then 3363 else 3368)) else (if jt.2.val < 4 then 3362 else (if jt.2.val < 5 then 3367 else 3366))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3358 else (if jt.2.val < 2 then 3364 else 3365)) else (if jt.2.val < 4 then 3359 else (if jt.2.val < 5 then 3361 else 3360)))))

checked_coverage fastCoverage0160 pairing0160 template0160 witness0160

theorem coverage0160 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0160) (maskBits m))
    cores template0160 witness0160 := by
  rw [← coresFast_eq]
  exact fastCoverage0160

theorem coverageSize0160 : ∀ q : Pattern,
    (cores (witness0160 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0160 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0160
#print axioms coverageSize0160

noncomputable def pairing0161 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0161 : List (Fin 4935) := templateData0161

noncomputable def witness0161 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3320) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 2768) else (if t 3 = 0 then 3004 else if t 3 = 1 then 3003 else 2781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 141) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 140) else (if t 3 = 0 then 874 else if t 3 = 1 then 862 else 199)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 341 else 893) else if t 2 = 1 then (if t 3 = 0 then 344 else if t 3 = 1 then 340 else 892) else (if t 3 = 0 then 1790 else if t 3 = 1 then 400 else 1501))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 635) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 634) else (if t 3 = 0 then 1219 else if t 3 = 1 then 1207 else 691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2622) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3089) else (if t 3 = 0 then 3313 else if t 3 = 1 then 3098 else 3102)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2900) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3080 else 3094) else (if t 3 = 0 then 3315 else if t 3 = 1 then 3100 else 3104))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 1787) else if t 2 = 1 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 650) else (if t 3 = 0 then 1223 else if t 3 = 1 then 1209 else 693)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2626) else if t 2 = 1 then (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3092) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3099 else 3103)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2474 else 2901) else if t 2 = 1 then (if t 3 = 0 then 3084 else if t 3 = 1 then 3083 else 3096) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3101 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3050 else (if jt.2.val < 2 then 3070 else 3072)) else (if jt.2.val < 4 then 3067 else (if jt.2.val < 5 then 3069 else 3068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3049 else (if jt.2.val < 2 then 3079 else 3081)) else (if jt.2.val < 4 then 3076 else (if jt.2.val < 5 then 3078 else 3077)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3371 else (if jt.2.val < 2 then 3373 else 3377)) else (if jt.2.val < 4 then 3372 else (if jt.2.val < 5 then 3376 else 3375))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3360 else (if jt.2.val < 2 then 3374 else 3365)) else (if jt.2.val < 4 then 3369 else (if jt.2.val < 5 then 3370 else 3358)))))

checked_coverage fastCoverage0161 pairing0161 template0161 witness0161

theorem coverage0161 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0161) (maskBits m))
    cores template0161 witness0161 := by
  rw [← coresFast_eq]
  exact fastCoverage0161

theorem coverageSize0161 : ∀ q : Pattern,
    (cores (witness0161 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0161 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0161
#print axioms coverageSize0161

noncomputable def pairing0162 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0162 : List (Fin 4935) := templateData0162

noncomputable def witness0162 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2710 else 2906) else if t 2 = 1 then (if t 3 = 0 then 2705 else if t 3 = 1 then 2688 else 2690) else (if t 3 = 0 then 3312 else if t 3 = 1 then 3191 else 3192)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2708 else 2107) else if t 2 = 1 then (if t 3 = 0 then 2703 else if t 3 = 1 then 2682 else 2090) else (if t 3 = 0 then 73 else if t 3 = 1 then 43 else 48)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1371 else 1780) else if t 2 = 1 then (if t 3 = 0 then 1357 else if t 3 = 1 then 1339 else 1342) else (if t 3 = 0 then 922 else if t 3 = 1 then 46 else 50))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2709 else 2227) else if t 2 = 1 then (if t 3 = 0 then 2704 else if t 3 = 1 then 2685 else 2212) else (if t 3 = 0 then 760 else if t 3 = 1 then 733 else 737)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2707 else 2902) else if t 2 = 1 then (if t 3 = 0 then 2695 else if t 3 = 1 then 2664 else 2674) else (if t 3 = 0 then 2697 else if t 3 = 1 then 2668 else 2676)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2721 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2878 else if t 3 = 1 then 2670 else 2678) else (if t 3 = 0 then 2880 else if t 3 = 1 then 2672 else 2680))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 390 else 931) else if t 2 = 1 then (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 353) else (if t 3 = 0 then 1774 else if t 3 = 1 then 1484 else 1488)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2903) else if t 2 = 1 then (if t 3 = 0 then 2696 else if t 3 = 1 then 2666 else 2675) else (if t 3 = 0 then 2698 else if t 3 = 1 then 2669 else 2677)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2723 else 3322) else if t 2 = 1 then (if t 3 = 0 then 2879 else if t 3 = 1 then 2671 else 2679) else (if t 3 = 0 then 2881 else if t 3 = 1 then 2673 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2661 else (if jt.2.val < 2 then 2663 else 2684)) else (if jt.2.val < 4 then 2662 else (if jt.2.val < 5 then 2683 else 2665))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3185 else (if jt.2.val < 2 then 3187 else 3190)) else (if jt.2.val < 4 then 3186 else (if jt.2.val < 5 then 3189 else 3188)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3366 else (if jt.2.val < 2 then 3380 else 3368)) else (if jt.2.val < 4 then 3378 else (if jt.2.val < 5 then 3379 else 3357))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3029 else (if jt.2.val < 2 then 3031 else 3035)) else (if jt.2.val < 4 then 3030 else (if jt.2.val < 5 then 3034 else 3032)))))

checked_coverage fastCoverage0162 pairing0162 template0162 witness0162

theorem coverage0162 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0162) (maskBits m))
    cores template0162 witness0162 := by
  rw [← coresFast_eq]
  exact fastCoverage0162

theorem coverageSize0162 : ∀ q : Pattern,
    (cores (witness0162 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0162 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0162
#print axioms coverageSize0162

noncomputable def pairing0163 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0163 : List (Fin 4935) := templateData0163

noncomputable def witness0163 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2960 else 2654) else if t 2 = 1 then (if t 3 = 0 then 2953 else if t 3 = 1 then 2937 else 2939) else (if t 3 = 0 then 3152 else if t 3 = 1 then 3329 else 3330)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2958 else 2104) else if t 2 = 1 then (if t 3 = 0 then 2951 else if t 3 = 1 then 2931 else 2082) else (if t 3 = 0 then 859 else if t 3 = 1 then 830 else 835)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1756 else 1453) else if t 2 = 1 then (if t 3 = 0 then 1750 else if t 3 = 1 then 1730 else 1733) else (if t 3 = 0 then 279 else if t 3 = 1 then 833 else 837))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2959 else 2224) else if t 2 = 1 then (if t 3 = 0 then 2952 else if t 3 = 1 then 2934 else 2206) else (if t 3 = 0 then 1204 else if t 3 = 1 then 1180 else 1184)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2954 else 2650) else if t 2 = 1 then (if t 3 = 0 then 2947 else if t 3 = 1 then 2913 else 2923) else (if t 3 = 0 then 2949 else if t 3 = 1 then 2917 else 2925)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2502 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2554 else if t 3 = 1 then 2919 else 2927) else (if t 3 = 0 then 2556 else if t 3 = 1 then 2921 else 2929))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 1003 else 307) else if t 2 = 1 then (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 974) else (if t 3 = 0 then 1431 else if t 3 = 1 then 1796 else 1800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2651) else if t 2 = 1 then (if t 3 = 0 then 2948 else if t 3 = 1 then 2915 else 2924) else (if t 3 = 0 then 2950 else if t 3 = 1 then 2918 else 2926)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2503 else 3184) else if t 2 = 1 then (if t 3 = 0 then 2555 else if t 3 = 1 then 2920 else 2928) else (if t 3 = 0 then 2557 else if t 3 = 1 then 2922 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2910 else (if jt.2.val < 2 then 2912 else 2933)) else (if jt.2.val < 4 then 2911 else (if jt.2.val < 5 then 2932 else 2914))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3323 else (if jt.2.val < 2 then 3325 else 3328)) else (if jt.2.val < 4 then 3324 else (if jt.2.val < 5 then 3327 else 3326)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3375 else (if jt.2.val < 2 then 3383 else 3377)) else (if jt.2.val < 4 then 3381 else (if jt.2.val < 5 then 3382 else 3371))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3032 else (if jt.2.val < 2 then 3039 else 3035)) else (if jt.2.val < 4 then 3038 else (if jt.2.val < 5 then 3041 else 3029)))))

checked_coverage fastCoverage0163 pairing0163 template0163 witness0163

theorem coverage0163 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0163) (maskBits m))
    cores template0163 witness0163 := by
  rw [← coresFast_eq]
  exact fastCoverage0163

theorem coverageSize0163 : ∀ q : Pattern,
    (cores (witness0163 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0163 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0163
#print axioms coverageSize0163

noncomputable def pairing0164 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0164 : List (Fin 4935) := templateData0164

noncomputable def witness0164 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1025 else 661) else if t 2 = 1 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1023 else 659) else (if t 3 = 0 then 1549 else if t 3 = 1 then 784 else 1826)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1021 else 1071) else if t 2 = 1 then (if t 3 = 0 then 1027 else if t 3 = 1 then 1019 else 1069) else (if t 3 = 0 then 595 else if t 3 = 1 then 1078 else 1090)) else (if t 2 = 0 then (if t 3 = 0 then 3340 else if t 3 = 1 then 3338 else 3226) else if t 2 = 1 then (if t 3 = 0 then 2973 else if t 3 = 1 then 2970 else 2979) else (if t 3 = 0 then 2762 else if t 3 = 1 then 2980 else 2981))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1024 else 660) else if t 2 = 1 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1022 else 658) else (if t 3 = 0 then 1548 else if t 3 = 1 then 783 else 1824)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1020 else 1070) else if t 2 = 1 then (if t 3 = 0 then 1026 else if t 3 = 1 then 1018 else 1068) else (if t 3 = 0 then 594 else if t 3 = 1 then 1077 else 1086)) else (if t 2 = 0 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1073) else if t 2 = 1 then (if t 3 = 0 then 1041 else if t 3 = 1 then 1037 else 1072) else (if t 3 = 0 then 598 else if t 3 = 1 then 1081 else 1087))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 2145 else 2777) else if t 2 = 1 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 668) else (if t 3 = 0 then 3216 else if t 3 = 1 then 789 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1598) else if t 2 = 1 then (if t 3 = 0 then 1050 else if t 3 = 1 then 1045 else 1074) else (if t 3 = 0 then 600 else if t 3 = 1 then 1083 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 1818 else if t 3 = 1 then 1817 else 1601) else if t 2 = 1 then (if t 3 = 0 then 1056 else if t 3 = 1 then 1054 else 1076) else (if t 3 = 0 then 602 else if t 3 = 1 then 1085 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2910 else (if jt.2.val < 2 then 2977 else 2933)) else (if jt.2.val < 4 then 2975 else (if jt.2.val < 5 then 2976 else 2914))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3273 else (if jt.2.val < 2 then 3339 else 3277)) else (if jt.2.val < 4 then 3336 else (if jt.2.val < 5 then 3337 else 3245)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1944 else (if jt.2.val < 2 then 1946 else 1949)) else (if jt.2.val < 4 then 1945 else (if jt.2.val < 5 then 1948 else 1947))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1261 else (if jt.2.val < 2 then 1270 else 1271)) else (if jt.2.val < 4 then 1264 else (if jt.2.val < 5 then 1266 else 1265)))))

checked_coverage fastCoverage0164 pairing0164 template0164 witness0164

theorem coverage0164 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0164) (maskBits m))
    cores template0164 witness0164 := by
  rw [← coresFast_eq]
  exact fastCoverage0164

theorem coverageSize0164 : ∀ q : Pattern,
    (cores (witness0164 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0164 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0164
#print axioms coverageSize0164

noncomputable def pairing0165 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0165 : List (Fin 4935) := templateData0165

noncomputable def witness0165 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 424 else 1134) else if t 2 = 1 then (if t 3 = 0 then 430 else if t 3 = 1 then 422 else 1132) else (if t 3 = 0 then 1837 else if t 3 = 1 then 502 else 1526)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 428 else if t 3 = 1 then 420 else 464) else if t 2 = 1 then (if t 3 = 0 then 426 else if t 3 = 1 then 418 else 462) else (if t 3 = 0 then 1114 else if t 3 = 1 then 488 else 490)) else (if t 2 = 0 then (if t 3 = 0 then 3205 else if t 3 = 1 then 3203 else 3344) else if t 2 = 1 then (if t 3 = 0 then 2731 else if t 3 = 1 then 2728 else 2737) else (if t 3 = 0 then 2985 else if t 3 = 1 then 2740 else 2741))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 423 else 1133) else if t 2 = 1 then (if t 3 = 0 then 429 else if t 3 = 1 then 421 else 1131) else (if t 3 = 0 then 1836 else if t 3 = 1 then 498 else 1524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 427 else if t 3 = 1 then 419 else 463) else if t 2 = 1 then (if t 3 = 0 then 425 else if t 3 = 1 then 417 else 461) else (if t 3 = 0 then 1113 else if t 3 = 1 then 480 else 484)) else (if t 2 = 0 then (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 471) else if t 2 = 1 then (if t 3 = 0 then 440 else if t 3 = 1 then 436 else 470) else (if t 3 = 0 then 1117 else if t 3 = 1 then 481 else 485))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 2124 else 2988) else if t 2 = 1 then (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 1137) else (if t 3 = 0 then 3343 else if t 3 = 1 then 500 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1848) else if t 2 = 1 then (if t 3 = 0 then 449 else if t 3 = 1 then 444 else 474) else (if t 3 = 0 then 1119 else if t 3 = 1 then 482 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 1512 else if t 3 = 1 then 1511 else 1850) else if t 2 = 1 then (if t 3 = 0 then 455 else if t 3 = 1 then 453 else 478) else (if t 3 = 0 then 1121 else if t 3 = 1 then 483 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2661 else (if jt.2.val < 2 then 2735 else 2684)) else (if jt.2.val < 4 then 2733 else (if jt.2.val < 5 then 2734 else 2665))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3077 else (if jt.2.val < 2 then 3204 else 3081)) else (if jt.2.val < 4 then 3201 else (if jt.2.val < 5 then 3202 else 3049)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1950 else (if jt.2.val < 2 then 1952 else 1955)) else (if jt.2.val < 4 then 1951 else (if jt.2.val < 5 then 1954 else 1953))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1265 else (if jt.2.val < 2 then 1280 else 1271)) else (if jt.2.val < 4 then 1275 else (if jt.2.val < 5 then 1276 else 1261)))))

checked_coverage fastCoverage0165 pairing0165 template0165 witness0165

theorem coverage0165 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0165) (maskBits m))
    cores template0165 witness0165 := by
  rw [← coresFast_eq]
  exact fastCoverage0165

theorem coverageSize0165 : ∀ q : Pattern,
    (cores (witness0165 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0165 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0165
#print axioms coverageSize0165

noncomputable def pairing0166 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0166 : List (Fin 4935) := templateData0166

noncomputable def witness0166 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1680 else 1856) else if t 2 = 1 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1660 else 1661) else (if t 3 = 0 then 1112 else if t 3 = 1 then 741 else 743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1678 else 1853) else if t 2 = 1 then (if t 3 = 0 then 1669 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 553 else if t 3 = 1 then 1647 else 1651)) else (if t 2 = 0 then (if t 3 = 0 then 2577 else if t 3 = 1 then 2860 else 2868) else if t 2 = 1 then (if t 3 = 0 then 2545 else if t 3 = 1 then 3232 else 3235) else (if t 3 = 0 then 3342 else if t 3 = 1 then 3234 else 3236))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1679 else 1854) else if t 2 = 1 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1656 else 1658) else (if t 3 = 0 then 1110 else if t 3 = 1 then 734 else 738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1677 else 1851) else if t 2 = 1 then (if t 3 = 0 then 1665 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 546 else if t 3 = 1 then 1632 else 1640)) else (if t 2 = 0 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1685 else 1852) else if t 2 = 1 then (if t 3 = 0 then 1666 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 547 else if t 3 = 1 then 1633 else 1641))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 401 else 3345) else if t 2 = 1 then (if t 3 = 0 then 894 else if t 3 = 1 then 350 else 354) else (if t 3 = 0 then 2984 else if t 3 = 1 then 2157 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 200 else if t 3 = 1 then 863 else 876) else if t 2 = 1 then (if t 3 = 0 then 150 else if t 3 = 1 then 1630 else 1638) else (if t 3 = 0 then 1833 else if t 3 = 1 then 1634 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 203 else if t 3 = 1 then 866 else 877) else if t 2 = 1 then (if t 3 = 0 then 151 else if t 3 = 1 then 1631 else 1639) else (if t 3 = 0 then 1834 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3050 else (if jt.2.val < 2 then 3231 else 3072)) else (if jt.2.val < 4 then 3230 else (if jt.2.val < 5 then 3233 else 3068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3188 else (if jt.2.val < 2 then 3238 else 3190)) else (if jt.2.val < 4 then 3237 else (if jt.2.val < 5 then 3239 else 3185)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1947 else (if jt.2.val < 2 then 1964 else 1949)) else (if jt.2.val < 4 then 1959 else (if jt.2.val < 5 then 1960 else 1944))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1956 else (if jt.2.val < 2 then 1958 else 1963)) else (if jt.2.val < 4 then 1957 else (if jt.2.val < 5 then 1962 else 1961)))))

checked_coverage fastCoverage0166 pairing0166 template0166 witness0166

theorem coverage0166 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0166) (maskBits m))
    cores template0166 witness0166 := by
  rw [← coresFast_eq]
  exact fastCoverage0166

theorem coverageSize0166 : ∀ q : Pattern,
    (cores (witness0166 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0166 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0166
#print axioms coverageSize0166

noncomputable def pairing0167 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0167 : List (Fin 4935) := templateData0167

noncomputable def witness0167 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1910 else 1622) else if t 2 = 1 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1891 else 1892) else (if t 3 = 0 then 575 else if t 3 = 1 then 1188 else 1190)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1907 else 1619) else if t 2 = 1 then (if t 3 = 0 then 1901 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 554 else if t 3 = 1 then 1878 else 1882)) else (if t 2 = 0 then (if t 3 = 0 then 2884 else if t 3 = 1 then 2500 else 2501) else if t 2 = 1 then (if t 3 = 0 then 2546 else if t 3 = 1 then 3348 else 3351) else (if t 3 = 0 then 3210 else if t 3 = 1 then 3350 else 3352))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1908 else 1620) else if t 2 = 1 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1887 else 1889) else (if t 3 = 0 then 572 else if t 3 = 1 then 1181 else 1185)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1905 else 1617) else if t 2 = 1 then (if t 3 = 0 then 1899 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 548 else if t 3 = 1 then 1863 else 1871)) else (if t 2 = 0 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1906 else 1618) else if t 2 = 1 then (if t 3 = 0 then 1900 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 549 else if t 3 = 1 then 1864 else 1872))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 102 else 3229) else if t 2 = 1 then (if t 3 = 0 then 176 else if t 3 = 1 then 971 else 975) else (if t 3 = 0 then 2758 else if t 3 = 1 then 2136 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 899 else if t 3 = 1 then 90 else 92) else if t 2 = 1 then (if t 3 = 0 then 152 else if t 3 = 1 then 1861 else 1869) else (if t 3 = 0 then 1535 else if t 3 = 1 then 1865 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 902 else if t 3 = 1 then 91 else 93) else if t 2 = 1 then (if t 3 = 0 then 153 else if t 3 = 1 then 1862 else 1870) else (if t 3 = 0 then 1536 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3246 else (if jt.2.val < 2 then 3347 else 3268)) else (if jt.2.val < 4 then 3346 else (if jt.2.val < 5 then 3349 else 3264))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3326 else (if jt.2.val < 2 then 3354 else 3328)) else (if jt.2.val < 4 then 3353 else (if jt.2.val < 5 then 3355 else 3323)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1953 else (if jt.2.val < 2 then 1970 else 1955)) else (if jt.2.val < 4 then 1967 else (if jt.2.val < 5 then 1968 else 1950))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1961 else (if jt.2.val < 2 then 1966 else 1963)) else (if jt.2.val < 4 then 1965 else (if jt.2.val < 5 then 1969 else 1956)))))

checked_coverage fastCoverage0167 pairing0167 template0167 witness0167

theorem coverage0167 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0167) (maskBits m))
    cores template0167 witness0167 := by
  rw [← coresFast_eq]
  exact fastCoverage0167

theorem coverageSize0167 : ∀ q : Pattern,
    (cores (witness0167 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0167 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0167
#print axioms coverageSize0167

noncomputable def pairing0168 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0168 : List (Fin 4935) := templateData0168

noncomputable def witness0168 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3106) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 3003) else (if t 3 = 0 then 2732 else if t 3 = 1 then 2730 else 2743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 868) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 862) else (if t 3 = 0 then 344 else if t 3 = 1 then 340 else 400)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 141 else 205) else if t 2 = 1 then (if t 3 = 0 then 144 else if t 3 = 1 then 140 else 199) else (if t 3 = 0 then 1496 else if t 3 = 1 then 892 else 1501))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 1213) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 1207) else (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 499)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2956) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3098) else (if t 3 = 0 then 3082 else if t 3 = 1 then 3080 else 3100)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2622 else 2652) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3089 else 3102) else (if t 3 = 0 then 3095 else if t 3 = 1 then 3094 else 3104))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 1375) else if t 2 = 1 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 1209) else (if t 3 = 0 then 456 else if t 3 = 1 then 454 else 501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2957) else if t 2 = 1 then (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3099) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3083 else 3101)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2626 else 2653) else if t 2 = 1 then (if t 3 = 0 then 3093 else if t 3 = 1 then 3092 else 3103) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3096 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3050 else (if jt.2.val < 2 then 3070 else 3072)) else (if jt.2.val < 4 then 3067 else (if jt.2.val < 5 then 3069 else 3068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3384 else (if jt.2.val < 2 then 3394 else 3395)) else (if jt.2.val < 4 then 3391 else (if jt.2.val < 5 then 3393 else 3392)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3385 else (if jt.2.val < 2 then 3389 else 3390)) else (if jt.2.val < 4 then 3386 else (if jt.2.val < 5 then 3388 else 3387))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3042 else (if jt.2.val < 2 then 3044 else 3047)) else (if jt.2.val < 4 then 3043 else (if jt.2.val < 5 then 3046 else 3045)))))

checked_coverage fastCoverage0168 pairing0168 template0168 witness0168

theorem coverage0168 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0168) (maskBits m))
    cores template0168 witness0168 := by
  rw [← coresFast_eq]
  exact fastCoverage0168

theorem coverageSize0168 : ∀ q : Pattern,
    (cores (witness0168 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0168 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0168
#print axioms coverageSize0168

noncomputable def pairing0169 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0169 : List (Fin 4935) := templateData0169

noncomputable def witness0169 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3152) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 3002) else (if t 3 = 0 then 2760 else if t 3 = 1 then 2756 else 2757)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 859) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 853) else (if t 3 = 0 then 292 else if t 3 = 1 then 264 else 269)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 73 else 75) else if t 2 = 1 then (if t 3 = 0 then 88 else if t 3 = 1 then 60 else 65) else (if t 3 = 0 then 1478 else if t 3 = 1 then 916 else 1471))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 1204) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 1198) else (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 563)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2949) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3130) else (if t 3 = 0 then 3163 else if t 3 = 1 then 3123 else 3132)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2697 else 2701) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3126 else 3134) else (if t 3 = 0 then 3167 else if t 3 = 1 then 3128 else 3136))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 1431) else if t 2 = 1 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 1200) else (if t 3 = 0 then 593 else if t 3 = 1 then 559 else 565)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2950) else if t 2 = 1 then (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3131) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3124 else 3133)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2698 else 2702) else if t 2 = 1 then (if t 3 = 0 then 3166 else if t 3 = 1 then 3127 else 3135) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3129 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3116 else (if jt.2.val < 2 then 3118 else 3140)) else (if jt.2.val < 4 then 3117 else (if jt.2.val < 5 then 3139 else 3120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3396 else (if jt.2.val < 2 then 3398 else 3405)) else (if jt.2.val < 4 then 3397 else (if jt.2.val < 5 then 3404 else 3403)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3399 else (if jt.2.val < 2 then 3401 else 3407)) else (if jt.2.val < 4 then 3400 else (if jt.2.val < 5 then 3406 else 3402))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3045 else (if jt.2.val < 2 then 3109 else 3047)) else (if jt.2.val < 4 then 3107 else (if jt.2.val < 5 then 3108 else 3042)))))

checked_coverage fastCoverage0169 pairing0169 template0169 witness0169

theorem coverage0169 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0169) (maskBits m))
    cores template0169 witness0169 := by
  rw [← coresFast_eq]
  exact fastCoverage0169

theorem coverageSize0169 : ∀ q : Pattern,
    (cores (witness0169 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0169 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0169
#print axioms coverageSize0169

noncomputable def pairing0170 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0170 : List (Fin 4935) := templateData0170

noncomputable def witness0170 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2446 else 2506) else if t 2 = 1 then (if t 3 = 0 then 2450 else if t 3 = 1 then 2442 else 2500) else (if t 3 = 0 then 3205 else if t 3 = 1 then 3203 else 3207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2444 else 1756) else if t 2 = 1 then (if t 3 = 0 then 2448 else if t 3 = 1 then 2440 else 1753) else (if t 3 = 0 then 343 else if t 3 = 1 then 339 else 394)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1413 else 1453) else if t 2 = 1 then (if t 3 = 0 then 1416 else if t 3 = 1 then 1412 else 1450) else (if t 3 = 0 then 374 else if t 3 = 1 then 372 else 396))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2445 else 1909) else if t 2 = 1 then (if t 3 = 0 then 2449 else if t 3 = 1 then 2441 else 1906) else (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 493)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2443 else 2502) else if t 2 = 1 then (if t 3 = 0 then 2447 else if t 3 = 1 then 2439 else 2492) else (if t 3 = 0 then 2471 else if t 3 = 1 then 2468 else 2494)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2897 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2484 else if t 3 = 1 then 2481 else 2496) else (if t 3 = 0 then 2489 else if t 3 = 1 then 2488 else 2498))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 33 else 103) else if t 2 = 1 then (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 91) else (if t 3 = 0 then 1512 else if t 3 = 1 then 1511 else 1522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2503) else if t 2 = 1 then (if t 3 = 0 then 2462 else if t 3 = 1 then 2459 else 2493) else (if t 3 = 0 then 2475 else if t 3 = 1 then 2473 else 2495)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2899 else 3184) else if t 2 = 1 then (if t 3 = 0 then 2487 else if t 3 = 1 then 2486 else 2497) else (if t 3 = 0 then 2491 else if t 3 = 1 then 2490 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2438 else (if jt.2.val < 2 then 2458 else 2460)) else (if jt.2.val < 4 then 2455 else (if jt.2.val < 5 then 2457 else 2456))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3410 else (if jt.2.val < 2 then 3415 else 3416)) else (if jt.2.val < 4 then 3412 else (if jt.2.val < 5 then 3414 else 3413)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3387 else (if jt.2.val < 2 then 3411 else 3390)) else (if jt.2.val < 4 then 3408 else (if jt.2.val < 5 then 3409 else 3385))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2430 else (if jt.2.val < 2 then 2432 else 2435)) else (if jt.2.val < 4 then 2431 else (if jt.2.val < 5 then 2434 else 2433)))))

checked_coverage fastCoverage0170 pairing0170 template0170 witness0170

theorem coverage0170 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0170) (maskBits m))
    cores template0170 witness0170 := by
  rw [← coresFast_eq]
  exact fastCoverage0170

theorem coverageSize0170 : ∀ q : Pattern,
    (cores (witness0170 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0170 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0170
#print axioms coverageSize0170

noncomputable def pairing0171 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0171 : List (Fin 4935) := templateData0171

noncomputable def witness0171 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2560 else 2561) else if t 2 = 1 then (if t 3 = 0 then 2565 else if t 3 = 1 then 2544 else 2546) else (if t 3 = 0 then 3215 else if t 3 = 1 then 3209 else 3210)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2558 else 1750) else if t 2 = 1 then (if t 3 = 0 then 2563 else if t 3 = 1 then 2538 else 1747) else (if t 3 = 0 then 291 else if t 3 = 1 then 251 else 256)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1357 else 1359) else if t 2 = 1 then (if t 3 = 0 then 1372 else if t 3 = 1 then 1350 else 1353) else (if t 3 = 0 then 305 else if t 3 = 1 then 254 else 258))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2559 else 1903) else if t 2 = 1 then (if t 3 = 0 then 2564 else if t 3 = 1 then 2541 else 1900) else (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 549)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2548 else 2554) else if t 2 = 1 then (if t 3 = 0 then 2562 else if t 3 = 1 then 2519 else 2530) else (if t 3 = 0 then 2572 else if t 3 = 1 then 2523 else 2532)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2878 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2576 else if t 3 = 1 then 2526 else 2534) else (if t 3 = 0 then 2579 else if t 3 = 1 then 2528 else 2536))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 175 else 177) else if t 2 = 1 then (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 153) else (if t 3 = 0 then 1547 else if t 3 = 1 then 1532 else 1536)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2555) else if t 2 = 1 then (if t 3 = 0 then 2570 else if t 3 = 1 then 2521 else 2531) else (if t 3 = 0 then 2574 else if t 3 = 1 then 2524 else 2533)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2879 else 3197) else if t 2 = 1 then (if t 3 = 0 then 2578 else if t 3 = 1 then 2527 else 2535) else (if t 3 = 0 then 2580 else if t 3 = 1 then 2529 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2516 else (if jt.2.val < 2 then 2518 else 2540)) else (if jt.2.val < 4 then 2517 else (if jt.2.val < 5 then 2539 else 2520))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3417 else (if jt.2.val < 2 then 3419 else 3422)) else (if jt.2.val < 4 then 3418 else (if jt.2.val < 5 then 3421 else 3420)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3402 else (if jt.2.val < 2 then 3424 else 3407)) else (if jt.2.val < 4 then 3423 else (if jt.2.val < 5 then 3425 else 3399))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2433 else (if jt.2.val < 2 then 2509 else 2435)) else (if jt.2.val < 4 then 2507 else (if jt.2.val < 5 then 2508 else 2430)))))

checked_coverage fastCoverage0171 pairing0171 template0171 witness0171

theorem coverage0171 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0171) (maskBits m))
    cores template0171 witness0171 := by
  rw [← coresFast_eq]
  exact fastCoverage0171

theorem coverageSize0171 : ∀ q : Pattern,
    (cores (witness0171 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0171 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0171
#print axioms coverageSize0171

noncomputable def pairing0172 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0172 : List (Fin 4935) := templateData0172

noncomputable def witness0172 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 620 else 698) else if t 2 = 1 then (if t 3 = 0 then 626 else if t 3 = 1 then 618 else 694) else (if t 3 = 0 then 1519 else if t 3 = 1 then 1132 else 1526)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 624 else if t 3 = 1 then 616 else 688) else if t 2 = 1 then (if t 3 = 0 then 622 else if t 3 = 1 then 614 else 680) else (if t 3 = 0 then 659 else if t 3 = 1 then 654 else 682)) else (if t 2 = 0 then (if t 3 = 0 then 3174 else if t 3 = 1 then 3172 else 3182) else if t 2 = 1 then (if t 3 = 0 then 2769 else if t 3 = 1 then 2766 else 2778) else (if t 3 = 0 then 2776 else if t 3 = 1 then 2775 else 2779))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 619 else 696) else if t 2 = 1 then (if t 3 = 0 then 625 else if t 3 = 1 then 617 else 690) else (if t 3 = 0 then 1518 else if t 3 = 1 then 1131 else 1524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 623 else if t 3 = 1 then 615 else 684) else if t 2 = 1 then (if t 3 = 0 then 621 else if t 3 = 1 then 613 else 672) else (if t 3 = 0 then 658 else if t 3 = 1 then 653 else 676)) else (if t 2 = 0 then (if t 3 = 0 then 637 else if t 3 = 1 then 633 else 685) else if t 2 = 1 then (if t 3 = 0 then 636 else if t 3 = 1 then 632 else 673) else (if t 3 = 0 then 664 else if t 3 = 1 then 662 else 677))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1785 else 2782) else if t 2 = 1 then (if t 3 = 0 then 647 else if t 3 = 1 then 643 else 692) else (if t 3 = 0 then 3206 else if t 3 = 1 then 1137 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1461 else if t 3 = 1 then 1458 else 1473) else if t 2 = 1 then (if t 3 = 0 then 645 else if t 3 = 1 then 640 else 674) else (if t 3 = 0 then 668 else if t 3 = 1 then 666 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 1464 else if t 3 = 1 then 1463 else 1474) else if t 2 = 1 then (if t 3 = 0 then 651 else if t 3 = 1 then 649 else 675) else (if t 3 = 0 then 671 else if t 3 = 1 then 670 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2516 else (if jt.2.val < 2 then 2773 else 2540)) else (if jt.2.val < 4 then 2771 else (if jt.2.val < 5 then 2772 else 2520))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3392 else (if jt.2.val < 2 then 3428 else 3395)) else (if jt.2.val < 4 then 3426 else (if jt.2.val < 5 then 3427 else 3384)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2015 else (if jt.2.val < 2 then 2020 else 2021)) else (if jt.2.val < 4 then 2017 else (if jt.2.val < 5 then 2019 else 2018))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 603 else (if jt.2.val < 2 then 605 else 608)) else (if jt.2.val < 4 then 604 else (if jt.2.val < 5 then 607 else 606)))))

checked_coverage fastCoverage0172 pairing0172 template0172 witness0172

theorem coverage0172 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0172) (maskBits m))
    cores template0172 witness0172 := by
  rw [← coresFast_eq]
  exact fastCoverage0172

theorem coverageSize0172 : ∀ q : Pattern,
    (cores (witness0172 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0172 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0172
#print axioms coverageSize0172

noncomputable def pairing0173 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0173 : List (Fin 4935) := templateData0173

noncomputable def witness0173 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 763 else 764) else if t 2 = 1 then (if t 3 = 0 then 770 else if t 3 = 1 then 755 else 757) else (if t 3 = 0 then 1549 else if t 3 = 1 then 1108 else 1544)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 768 else if t 3 = 1 then 740 else 742) else if t 2 = 1 then (if t 3 = 0 then 766 else if t 3 = 1 then 720 else 725) else (if t 3 = 0 then 784 else if t 3 = 1 then 723 else 727)) else (if t 2 = 0 then (if t 3 = 0 then 3198 else if t 3 = 1 then 3191 else 3192) else if t 2 = 1 then (if t 3 = 0 then 2797 else if t 3 = 1 then 2785 else 2788) else (if t 3 = 0 then 2800 else if t 3 = 1 then 2787 else 2789))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 759 else 761) else if t 2 = 1 then (if t 3 = 0 then 769 else if t 3 = 1 then 747 else 751) else (if t 3 = 0 then 1548 else if t 3 = 1 then 1104 else 1542)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 767 else if t 3 = 1 then 732 else 736) else if t 2 = 1 then (if t 3 = 0 then 765 else if t 3 = 1 then 704 else 712) else (if t 3 = 0 then 783 else if t 3 = 1 then 708 else 716)) else (if t 2 = 0 then (if t 3 = 0 then 774 else if t 3 = 1 then 733 else 737) else if t 2 = 1 then (if t 3 = 0 then 773 else if t 3 = 1 then 705 else 713) else (if t 3 = 0 then 787 else if t 3 = 1 then 709 else 717))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1773 else 2796) else if t 2 = 1 then (if t 3 = 0 then 779 else if t 3 = 1 then 749 else 753) else (if t 3 = 0 then 3216 else if t 3 = 1 then 1106 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1497 else if t 3 = 1 then 1483 else 1487) else if t 2 = 1 then (if t 3 = 0 then 777 else if t 3 = 1 then 706 else 714) else (if t 3 = 0 then 789 else if t 3 = 1 then 710 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 1499 else if t 3 = 1 then 1484 else 1488) else if t 2 = 1 then (if t 3 = 0 then 781 else if t 3 = 1 then 707 else 715) else (if t 3 = 0 then 791 else if t 3 = 1 then 711 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2438 else (if jt.2.val < 2 then 2784 else 2460)) else (if jt.2.val < 4 then 2783 else (if jt.2.val < 5 then 2786 else 2456))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3403 else (if jt.2.val < 2 then 3430 else 3405)) else (if jt.2.val < 4 then 3429 else (if jt.2.val < 5 then 3431 else 3396)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2022 else (if jt.2.val < 2 then 2024 else 2027)) else (if jt.2.val < 4 then 2023 else (if jt.2.val < 5 then 2026 else 2025))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 606 else (if jt.2.val < 2 then 701 else 608)) else (if jt.2.val < 4 then 699 else (if jt.2.val < 5 then 700 else 603)))))

checked_coverage fastCoverage0173 pairing0173 template0173 witness0173

theorem coverage0173 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0173) (maskBits m))
    cores template0173 witness0173 := by
  rw [← coresFast_eq]
  exact fastCoverage0173

theorem coverageSize0173 : ∀ q : Pattern,
    (cores (witness0173 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0173 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0173
#print axioms coverageSize0173

noncomputable def pairing0174 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0174 : List (Fin 4935) := templateData0174

noncomputable def witness0174 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1568 else 1622) else if t 2 = 1 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1566 else 1619) else (if t 3 = 0 then 469 else if t 3 = 1 then 464 else 497)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1564 else 1616) else if t 2 = 1 then (if t 3 = 0 then 1570 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 1071 else if t 3 = 1 then 1593 else 1612)) else (if t 2 = 0 then (if t 3 = 0 then 2633 else if t 3 = 1 then 2630 else 2649) else if t 2 = 1 then (if t 3 = 0 then 2855 else if t 3 = 1 then 3219 else 3227) else (if t 3 = 0 then 3226 else if t 3 = 1 then 3225 else 3228))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1567 else 1620) else if t 2 = 1 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1565 else 1617) else (if t 3 = 0 then 468 else if t 3 = 1 then 463 else 494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1563 else 1614) else if t 2 = 1 then (if t 3 = 0 then 1569 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 1070 else if t 3 = 1 then 1592 else 1606)) else (if t 2 = 0 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1581 else 1615) else if t 2 = 1 then (if t 3 = 0 then 1584 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 1073 else if t 3 = 1 then 1595 else 1607))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 917 else 3229) else if t 2 = 1 then (if t 3 = 0 then 66 else if t 3 = 1 then 61 else 92) else (if t 3 = 0 then 2739 else if t 3 = 1 then 1848 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 270 else if t 3 = 1 then 265 else 296) else if t 2 = 1 then (if t 3 = 0 then 854 else if t 3 = 1 then 1588 else 1604) else (if t 3 = 0 then 1598 else if t 3 = 1 then 1596 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 275 else if t 3 = 1 then 273 else 297) else if t 2 = 1 then (if t 3 = 0 then 857 else if t 3 = 1 then 1591 else 1605) else (if t 3 = 0 then 1601 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3116 else (if jt.2.val < 2 then 3223 else 3140)) else (if jt.2.val < 4 then 3221 else (if jt.2.val < 5 then 3222 else 3120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3413 else (if jt.2.val < 2 then 3434 else 3416)) else (if jt.2.val < 4 then 3432 else (if jt.2.val < 5 then 3433 else 3410)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2018 else (if jt.2.val < 2 then 2036 else 2021)) else (if jt.2.val < 4 then 2033 else (if jt.2.val < 5 then 2034 else 2015))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1551 else (if jt.2.val < 2 then 1553 else 1556)) else (if jt.2.val < 4 then 1552 else (if jt.2.val < 5 then 1555 else 1554)))))

checked_coverage fastCoverage0174 pairing0174 template0174 witness0174

theorem coverage0174 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0174) (maskBits m))
    cores template0174 witness0174 := by
  rw [← coresFast_eq]
  exact fastCoverage0174

theorem coverageSize0174 : ∀ q : Pattern,
    (cores (witness0174 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0174 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0174
#print axioms coverageSize0174

noncomputable def pairing0175 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0175 : List (Fin 4935) := templateData0175

noncomputable def witness0175 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1675 else 1676) else if t 2 = 1 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1669 else 1670) else (if t 3 = 0 then 597 else if t 3 = 1 then 553 else 555)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1660 else 1661) else if t 2 = 1 then (if t 3 = 0 then 1678 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 1080 else if t 3 = 1 then 1647 else 1651)) else (if t 2 = 0 then (if t 3 = 0 then 2722 else if t 3 = 1 then 2689 else 2691) else if t 2 = 1 then (if t 3 = 0 then 2860 else if t 3 = 1 then 3232 else 3235) else (if t 3 = 0 then 3242 else if t 3 = 1 then 3234 else 3236))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1671 else 1673) else if t 2 = 1 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1665 else 1667) else (if t 3 = 0 then 596 else if t 3 = 1 then 546 else 550)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1656 else 1658) else if t 2 = 1 then (if t 3 = 0 then 1677 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 1079 else if t 3 = 1 then 1632 else 1640)) else (if t 2 = 0 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1657 else 1659) else if t 2 = 1 then (if t 3 = 0 then 1685 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 1082 else if t 3 = 1 then 1633 else 1641))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 894 else 3240) else if t 2 = 1 then (if t 3 = 0 then 200 else if t 3 = 1 then 150 else 154) else (if t 3 = 0 then 2763 else if t 3 = 1 then 1833 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 401 else if t 3 = 1 then 350 else 354) else if t 2 = 1 then (if t 3 = 0 then 863 else if t 3 = 1 then 1630 else 1638) else (if t 3 = 0 then 1689 else if t 3 = 1 then 1634 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 404 else if t 3 = 1 then 351 else 355) else if t 2 = 1 then (if t 3 = 0 then 866 else if t 3 = 1 then 1631 else 1639) else (if t 3 = 0 then 1691 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3050 else (if jt.2.val < 2 then 3231 else 3072)) else (if jt.2.val < 4 then 3230 else (if jt.2.val < 5 then 3233 else 3068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3420 else (if jt.2.val < 2 then 3436 else 3422)) else (if jt.2.val < 4 then 3435 else (if jt.2.val < 5 then 3437 else 3417)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2025 else (if jt.2.val < 2 then 2038 else 2027)) else (if jt.2.val < 4 then 2037 else (if jt.2.val < 5 then 2039 else 2022))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1554 else (if jt.2.val < 2 then 1625 else 1556)) else (if jt.2.val < 4 then 1623 else (if jt.2.val < 5 then 1624 else 1551)))))

checked_coverage fastCoverage0175 pairing0175 template0175 witness0175

theorem coverage0175 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0175) (maskBits m))
    cores template0175 witness0175 := by
  rw [← coresFast_eq]
  exact fastCoverage0175

theorem coverageSize0175 : ∀ q : Pattern,
    (cores (witness0175 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0175 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0175
#print axioms coverageSize0175

noncomputable def pairing0176 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0176 : List (Fin 4935) := templateData0176

noncomputable def witness0176 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3215) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2759) else (if t 3 = 0 then 2732 else if t 3 = 1 then 2731 else 2985)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 291) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 290) else (if t 3 = 0 then 344 else if t 3 = 1 then 342 else 928)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 964 else 305) else if t 2 = 1 then (if t 3 = 0 then 965 else if t 3 = 1 then 963 else 304) else (if t 3 = 0 then 1496 else if t 3 = 1 then 373 else 2140))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 585) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 584) else (if t 3 = 0 then 442 else if t 3 = 1 then 440 else 1117)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2572) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3488) else (if t 3 = 0 then 3082 else if t 3 = 1 then 3479 else 3492)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2838 else 2579) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3472 else 3490) else (if t 3 = 0 then 3095 else if t 3 = 1 then 3486 else 3494))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1547) else if t 2 = 1 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 592) else (if t 3 = 0 then 456 else if t 3 = 1 then 455 else 1121)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2574) else if t 2 = 1 then (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3489) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3480 else 3493)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2842 else 2580) else if t 2 = 1 then (if t 3 = 0 then 3280 else if t 3 = 1 then 3473 else 3491) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3487 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3441 else (if jt.2.val < 2 then 3461 else 3463)) else (if jt.2.val < 4 then 3458 else (if jt.2.val < 5 then 3460 else 3459))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3440 else (if jt.2.val < 2 then 3470 else 3471)) else (if jt.2.val < 4 then 3467 else (if jt.2.val < 5 then 3469 else 3468)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3439 else (if jt.2.val < 2 then 3477 else 3478)) else (if jt.2.val < 4 then 3474 else (if jt.2.val < 5 then 3476 else 3475))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3438 else (if jt.2.val < 2 then 3482 else 3485)) else (if jt.2.val < 4 then 3481 else (if jt.2.val < 5 then 3484 else 3483)))))

checked_coverage fastCoverage0176 pairing0176 template0176 witness0176

theorem coverage0176 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0176) (maskBits m))
    cores template0176 witness0176 := by
  rw [← coresFast_eq]
  exact fastCoverage0176

theorem coverageSize0176 : ∀ q : Pattern,
    (cores (witness0176 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0176 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0176
#print axioms coverageSize0176

noncomputable def pairing0177 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0177 : List (Fin 4935) := templateData0177

noncomputable def witness0177 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3499) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 2756) else (if t 3 = 0 then 3004 else if t 3 = 1 then 3002 else 2757)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 277) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 264) else (if t 3 = 0 then 874 else if t 3 = 1 then 853 else 269)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 73 else 922) else if t 2 = 1 then (if t 3 = 0 then 88 else if t 3 = 1 then 60 else 916) else (if t 3 = 0 then 2129 else if t 3 = 1 then 65 else 1471))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 571) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 557) else (if t 3 = 0 then 1219 else if t 3 = 1 then 1198 else 563)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2550) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3123) else (if t 3 = 0 then 3313 else if t 3 = 1 then 3130 else 3132)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2697 else 2880) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3126 else 3128) else (if t 3 = 0 then 3500 else if t 3 = 1 then 3134 else 3136))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 2116) else if t 2 = 1 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 559) else (if t 3 = 0 then 1223 else if t 3 = 1 then 1200 else 565)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2551) else if t 2 = 1 then (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3124) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3131 else 3133)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2698 else 2881) else if t 2 = 1 then (if t 3 = 0 then 3166 else if t 3 = 1 then 3127 else 3129) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3135 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3116 else (if jt.2.val < 2 then 3118 else 3140)) else (if jt.2.val < 4 then 3117 else (if jt.2.val < 5 then 3139 else 3120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3396 else (if jt.2.val < 2 then 3398 else 3405)) else (if jt.2.val < 4 then 3397 else (if jt.2.val < 5 then 3404 else 3403)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3305 else (if jt.2.val < 2 then 3307 else 3311)) else (if jt.2.val < 4 then 3306 else (if jt.2.val < 5 then 3310 else 3309))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3483 else (if jt.2.val < 2 then 3498 else 3485)) else (if jt.2.val < 4 then 3496 else (if jt.2.val < 5 then 3497 else 3438)))))

checked_coverage fastCoverage0177 pairing0177 template0177 witness0177

theorem coverage0177 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0177) (maskBits m))
    cores template0177 witness0177 := by
  rw [← coresFast_eq]
  exact fastCoverage0177

theorem coverageSize0177 : ∀ q : Pattern,
    (cores (witness0177 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0177 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0177
#print axioms coverageSize0177

noncomputable def pairing0178 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0178 : List (Fin 4935) := templateData0178

noncomputable def witness0178 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2450 else 2884) else if t 2 = 1 then (if t 3 = 0 then 2446 else if t 3 = 1 then 2442 else 2500) else (if t 3 = 0 then 3505 else if t 3 = 1 then 3203 else 3207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2448 else 1762) else if t 2 = 1 then (if t 3 = 0 then 2444 else if t 3 = 1 then 2440 else 1753) else (if t 3 = 0 then 341 else if t 3 = 1 then 339 else 394)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1416 else 2119) else if t 2 = 1 then (if t 3 = 0 then 1413 else if t 3 = 1 then 1412 else 1450) else (if t 3 = 0 then 893 else if t 3 = 1 then 372 else 396))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2449 else 1915) else if t 2 = 1 then (if t 3 = 0 then 2445 else if t 3 = 1 then 2441 else 1906) else (if t 3 = 0 then 439 else if t 3 = 1 then 437 else 493)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2447 else 2883) else if t 2 = 1 then (if t 3 = 0 then 2443 else if t 3 = 1 then 2439 else 2492) else (if t 3 = 0 then 2470 else if t 3 = 1 then 2468 else 2494)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2484 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2897 else if t 3 = 1 then 2481 else 2496) else (if t 3 = 0 then 2900 else if t 3 = 1 then 2488 else 2498))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 35 else 902) else if t 2 = 1 then (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 91) else (if t 3 = 0 then 2126 else if t 3 = 1 then 1511 else 1522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2885) else if t 2 = 1 then (if t 3 = 0 then 2461 else if t 3 = 1 then 2459 else 2493) else (if t 3 = 0 then 2474 else if t 3 = 1 then 2473 else 2495)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2487 else 3507) else if t 2 = 1 then (if t 3 = 0 then 2899 else if t 3 = 1 then 2486 else 2497) else (if t 3 = 0 then 2901 else if t 3 = 1 then 2490 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2438 else (if jt.2.val < 2 then 2458 else 2460)) else (if jt.2.val < 4 then 2455 else (if jt.2.val < 5 then 2457 else 2456))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3410 else (if jt.2.val < 2 then 3415 else 3416)) else (if jt.2.val < 4 then 3412 else (if jt.2.val < 5 then 3414 else 3413)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3475 else (if jt.2.val < 2 then 3504 else 3478)) else (if jt.2.val < 4 then 3502 else (if jt.2.val < 5 then 3503 else 3439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3020 else (if jt.2.val < 2 then 3022 else 3025)) else (if jt.2.val < 4 then 3021 else (if jt.2.val < 5 then 3024 else 3023)))))

checked_coverage fastCoverage0178 pairing0178 template0178 witness0178

theorem coverage0178 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0178) (maskBits m))
    cores template0178 witness0178 := by
  rw [← coresFast_eq]
  exact fastCoverage0178

theorem coverageSize0178 : ∀ q : Pattern,
    (cores (witness0178 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0178 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0178
#print axioms coverageSize0178

noncomputable def pairing0179 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0179 : List (Fin 4935) := templateData0179

noncomputable def witness0179 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2953 else 2561) else if t 2 = 1 then (if t 3 = 0 then 2960 else if t 3 = 1 then 2937 else 2938) else (if t 3 = 0 then 3106 else if t 3 = 1 then 3329 else 3514)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2951 else 1750) else if t 2 = 1 then (if t 3 = 0 then 2958 else if t 3 = 1 then 2931 else 1730) else (if t 3 = 0 then 868 else if t 3 = 1 then 830 else 833)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2098 else 1359) else if t 2 = 1 then (if t 3 = 0 then 2104 else if t 3 = 1 then 2082 else 1733) else (if t 3 = 0 then 205 else if t 3 = 1 then 835 else 837))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2952 else 1903) else if t 2 = 1 then (if t 3 = 0 then 2959 else if t 3 = 1 then 2934 else 1888) else (if t 3 = 0 then 1213 else if t 3 = 1 then 1180 else 1182)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2947 else 2554) else if t 2 = 1 then (if t 3 = 0 then 2954 else if t 3 = 1 then 2913 else 2919) else (if t 3 = 0 then 2956 else if t 3 = 1 then 2917 else 2921)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2699 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2650 else if t 3 = 1 then 2923 else 2927) else (if t 3 = 0 then 2652 else if t 3 = 1 then 2925 else 2929))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 994 else 177) else if t 2 = 1 then (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 972) else (if t 3 = 0 then 1375 else if t 3 = 1 then 1796 else 2137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2555) else if t 2 = 1 then (if t 3 = 0 then 2955 else if t 3 = 1 then 2915 else 2920) else (if t 3 = 0 then 2957 else if t 3 = 1 then 2918 else 2922)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2700 else 3197) else if t 2 = 1 then (if t 3 = 0 then 2651 else if t 3 = 1 then 2924 else 2928) else (if t 3 = 0 then 2653 else if t 3 = 1 then 2926 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2910 else (if jt.2.val < 2 then 2912 else 2933)) else (if jt.2.val < 4 then 2911 else (if jt.2.val < 5 then 2932 else 2914))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3508 else (if jt.2.val < 2 then 3510 else 3513)) else (if jt.2.val < 4 then 3509 else (if jt.2.val < 5 then 3512 else 3511)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3309 else (if jt.2.val < 2 then 3332 else 3311)) else (if jt.2.val < 4 then 3331 else (if jt.2.val < 5 then 3333 else 3305))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3023 else (if jt.2.val < 2 then 3040 else 3025)) else (if jt.2.val < 4 then 3036 else (if jt.2.val < 5 then 3037 else 3020)))))

checked_coverage fastCoverage0179 pairing0179 template0179 witness0179

theorem coverage0179 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0179) (maskBits m))
    cores template0179 witness0179 := by
  rw [← coresFast_eq]
  exact fastCoverage0179

theorem coverageSize0179 : ∀ q : Pattern,
    (cores (witness0179 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0179 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0179
#print axioms coverageSize0179

noncomputable def pairing0180 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0180 : List (Fin 4935) := templateData0180

noncomputable def witness0180 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1029 else 597) else if t 2 = 1 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1027 else 595) else (if t 3 = 0 then 1519 else if t 3 = 1 then 467 else 2150)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1025 else if t 3 = 1 then 1021 else 1080) else if t 2 = 1 then (if t 3 = 0 then 1023 else if t 3 = 1 then 1019 else 1078) else (if t 3 = 0 then 659 else if t 3 = 1 then 1069 else 1090)) else (if t 2 = 0 then (if t 3 = 0 then 3520 else if t 3 = 1 then 3338 else 3242) else if t 2 = 1 then (if t 3 = 0 then 2972 else if t 3 = 1 then 2970 else 2980) else (if t 3 = 0 then 2776 else if t 3 = 1 then 2979 else 2981))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1028 else 596) else if t 2 = 1 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1026 else 594) else (if t 3 = 0 then 1518 else if t 3 = 1 then 466 else 2148)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1024 else if t 3 = 1 then 1020 else 1079) else if t 2 = 1 then (if t 3 = 0 then 1022 else if t 3 = 1 then 1018 else 1077) else (if t 3 = 0 then 658 else if t 3 = 1 then 1068 else 1086)) else (if t 2 = 0 then (if t 3 = 0 then 1040 else if t 3 = 1 then 1038 else 1082) else if t 2 = 1 then (if t 3 = 0 then 1039 else if t 3 = 1 then 1037 else 1081) else (if t 3 = 0 then 664 else if t 3 = 1 then 1072 else 1087))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 1815 else 2763) else if t 2 = 1 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1050 else 600) else (if t 3 = 0 then 3206 else if t 3 = 1 then 476 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2145 else if t 3 = 1 then 1812 else 1689) else if t 2 = 1 then (if t 3 = 0 then 1048 else if t 3 = 1 then 1045 else 1083) else (if t 3 = 0 then 668 else if t 3 = 1 then 1074 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 2147 else if t 3 = 1 then 1817 else 1691) else if t 2 = 1 then (if t 3 = 0 then 1055 else if t 3 = 1 then 1054 else 1085) else (if t 3 = 0 then 671 else if t 3 = 1 then 1076 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2910 else (if jt.2.val < 2 then 2977 else 2933)) else (if jt.2.val < 4 then 2975 else (if jt.2.val < 5 then 2976 else 2914))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3468 else (if jt.2.val < 2 then 3519 else 3471)) else (if jt.2.val < 4 then 3517 else (if jt.2.val < 5 then 3518 else 3440)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1811 else (if jt.2.val < 2 then 1822 else 1823)) else (if jt.2.val < 4 then 1819 else (if jt.2.val < 5 then 1821 else 1820))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1260 else (if jt.2.val < 2 then 1263 else 1269)) else (if jt.2.val < 4 then 1262 else (if jt.2.val < 5 then 1268 else 1267)))))

checked_coverage fastCoverage0180 pairing0180 template0180 witness0180

theorem coverage0180 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0180) (maskBits m))
    cores template0180 witness0180 := by
  rw [← coresFast_eq]
  exact fastCoverage0180

theorem coverageSize0180 : ∀ q : Pattern,
    (cores (witness0180 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0180 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0180
#print axioms coverageSize0180

noncomputable def pairing0181 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0181 : List (Fin 4935) := templateData0181

noncomputable def witness0181 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 763 else 1112) else if t 2 = 1 then (if t 3 = 0 then 770 else if t 3 = 1 then 755 else 1108) else (if t 3 = 0 then 2161 else if t 3 = 1 then 757 else 1544)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 768 else if t 3 = 1 then 740 else 741) else if t 2 = 1 then (if t 3 = 0 then 766 else if t 3 = 1 then 720 else 723) else (if t 3 = 0 then 1144 else if t 3 = 1 then 725 else 727)) else (if t 2 = 0 then (if t 3 = 0 then 3198 else if t 3 = 1 then 3191 else 3522) else if t 2 = 1 then (if t 3 = 0 then 2797 else if t 3 = 1 then 2785 else 2787) else (if t 3 = 0 then 2989 else if t 3 = 1 then 2788 else 2789))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 759 else 1110) else if t 2 = 1 then (if t 3 = 0 then 769 else if t 3 = 1 then 747 else 1104) else (if t 3 = 0 then 2160 else if t 3 = 1 then 751 else 1542)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 767 else if t 3 = 1 then 732 else 734) else if t 2 = 1 then (if t 3 = 0 then 765 else if t 3 = 1 then 704 else 708) else (if t 3 = 0 then 1140 else if t 3 = 1 then 712 else 716)) else (if t 2 = 0 then (if t 3 = 0 then 774 else if t 3 = 1 then 733 else 735) else if t 2 = 1 then (if t 3 = 0 then 773 else if t 3 = 1 then 705 else 709) else (if t 3 = 0 then 1141 else if t 3 = 1 then 713 else 717))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1773 else 2984) else if t 2 = 1 then (if t 3 = 0 then 779 else if t 3 = 1 then 749 else 1106) else (if t 3 = 0 then 3523 else if t 3 = 1 then 753 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1497 else if t 3 = 1 then 1483 else 2157) else if t 2 = 1 then (if t 3 = 0 then 777 else if t 3 = 1 then 706 else 710) else (if t 3 = 0 then 1142 else if t 3 = 1 then 714 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 1499 else if t 3 = 1 then 1484 else 2158) else if t 2 = 1 then (if t 3 = 0 then 781 else if t 3 = 1 then 707 else 711) else (if t 3 = 0 then 1143 else if t 3 = 1 then 715 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2438 else (if jt.2.val < 2 then 2784 else 2460)) else (if jt.2.val < 4 then 2783 else (if jt.2.val < 5 then 2786 else 2456))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3403 else (if jt.2.val < 2 then 3430 else 3405)) else (if jt.2.val < 4 then 3429 else (if jt.2.val < 5 then 3431 else 3396)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2151 else (if jt.2.val < 2 then 2153 else 2156)) else (if jt.2.val < 4 then 2152 else (if jt.2.val < 5 then 2155 else 2154))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1267 else (if jt.2.val < 2 then 1287 else 1269)) else (if jt.2.val < 4 then 1284 else (if jt.2.val < 5 then 1285 else 1260)))))

checked_coverage fastCoverage0181 pairing0181 template0181 witness0181

theorem coverage0181 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0181) (maskBits m))
    cores template0181 witness0181 := by
  rw [← coresFast_eq]
  exact fastCoverage0181

theorem coverageSize0181 : ∀ q : Pattern,
    (cores (witness0181 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0181 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0181
#print axioms coverageSize0181

noncomputable def pairing0182 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0182 : List (Fin 4935) := templateData0182

noncomputable def witness0182 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1574 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1566 else 1619) else (if t 3 = 0 then 1134 else if t 3 = 1 then 464 else 497)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1570 else 1853) else if t 2 = 1 then (if t 3 = 0 then 1564 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 656 else if t 3 = 1 then 1593 else 1612)) else (if t 2 = 0 then (if t 3 = 0 then 2633 else if t 3 = 1 then 2855 else 2868) else if t 2 = 1 then (if t 3 = 0 then 2630 else if t 3 = 1 then 3219 else 3227) else (if t 3 = 0 then 3524 else if t 3 = 1 then 3225 else 3228))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1573 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1565 else 1617) else (if t 3 = 0 then 1133 else if t 3 = 1 then 463 else 494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1569 else 1851) else if t 2 = 1 then (if t 3 = 0 then 1563 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 655 else if t 3 = 1 then 1592 else 1606)) else (if t 2 = 0 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1584 else 1852) else if t 2 = 1 then (if t 3 = 0 then 1581 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 663 else if t 3 = 1 then 1595 else 1607))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 66 else 3525) else if t 2 = 1 then (if t 3 = 0 then 917 else if t 3 = 1 then 61 else 92) else (if t 3 = 0 then 2988 else if t 3 = 1 then 1848 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 270 else if t 3 = 1 then 854 else 876) else if t 2 = 1 then (if t 3 = 0 then 265 else if t 3 = 1 then 1588 else 1604) else (if t 3 = 0 then 2169 else if t 3 = 1 then 1596 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 275 else if t 3 = 1 then 857 else 877) else if t 2 = 1 then (if t 3 = 0 then 273 else if t 3 = 1 then 1591 else 1605) else (if t 3 = 0 then 2171 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3116 else (if jt.2.val < 2 then 3223 else 3140)) else (if jt.2.val < 4 then 3221 else (if jt.2.val < 5 then 3222 else 3120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3413 else (if jt.2.val < 2 then 3434 else 3416)) else (if jt.2.val < 4 then 3432 else (if jt.2.val < 5 then 3433 else 3410)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1820 else (if jt.2.val < 2 then 1847 else 1823)) else (if jt.2.val < 4 then 1842 else (if jt.2.val < 5 then 1843 else 1811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2163 else (if jt.2.val < 2 then 2165 else 2168)) else (if jt.2.val < 4 then 2164 else (if jt.2.val < 5 then 2167 else 2166)))))

checked_coverage fastCoverage0182 pairing0182 template0182 witness0182

theorem coverage0182 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0182) (maskBits m))
    cores template0182 witness0182 := by
  rw [← coresFast_eq]
  exact fastCoverage0182

theorem coverageSize0182 : ∀ q : Pattern,
    (cores (witness0182 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0182 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0182
#print axioms coverageSize0182

noncomputable def pairing0183 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0183 : List (Fin 4935) := templateData0183

noncomputable def witness0183 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2219 else 1676) else if t 2 = 1 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2207 else 1892) else (if t 3 = 0 then 698 else if t 3 = 1 then 1189 else 1190)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2213 else 1661) else if t 2 = 1 then (if t 3 = 0 then 2222 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 688 else if t 3 = 1 then 2196 else 2200)) else (if t 2 = 0 then (if t 3 = 0 then 2906 else if t 3 = 1 then 2690 else 2691) else if t 2 = 1 then (if t 3 = 0 then 2648 else if t 3 = 1 then 3528 else 3531) else (if t 3 = 0 then 3182 else if t 3 = 1 then 3530 else 3532))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2217 else 1673) else if t 2 = 1 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2205 else 1889) else (if t 3 = 0 then 696 else if t 3 = 1 then 1183 else 1185)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2211 else 1658) else if t 2 = 1 then (if t 3 = 0 then 2220 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 684 else if t 3 = 1 then 2181 else 2189)) else (if t 2 = 0 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2212 else 1659) else if t 2 = 1 then (if t 3 = 0 then 2221 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 685 else if t 3 = 1 then 2182 else 2190))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 377 else 3240) else if t 2 = 1 then (if t 3 = 0 then 306 else if t 3 = 1 then 973 else 975) else (if t 3 = 0 then 2782 else if t 3 = 1 then 1799 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 930 else if t 3 = 1 then 352 else 354) else if t 2 = 1 then (if t 3 = 0 then 294 else if t 3 = 1 then 2179 else 2187) else (if t 3 = 0 then 1473 else if t 3 = 1 then 2183 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 931 else if t 3 = 1 then 353 else 355) else if t 2 = 1 then (if t 3 = 0 then 295 else if t 3 = 1 then 2180 else 2188) else (if t 3 = 0 then 1474 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3441 else (if jt.2.val < 2 then 3527 else 3463)) else (if jt.2.val < 4 then 3526 else (if jt.2.val < 5 then 3529 else 3459))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3511 else (if jt.2.val < 2 then 3534 else 3513)) else (if jt.2.val < 4 then 3533 else (if jt.2.val < 5 then 3535 else 3508)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2154 else (if jt.2.val < 2 then 2209 else 2156)) else (if jt.2.val < 4 then 2208 else (if jt.2.val < 5 then 2210 else 2151))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2166 else (if jt.2.val < 2 then 2216 else 2168)) else (if jt.2.val < 4 then 2214 else (if jt.2.val < 5 then 2215 else 2163)))))

checked_coverage fastCoverage0183 pairing0183 template0183 witness0183

theorem coverage0183 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0183) (maskBits m))
    cores template0183 witness0183 := by
  rw [← coresFast_eq]
  exact fastCoverage0183

theorem coverageSize0183 : ∀ q : Pattern,
    (cores (witness0183 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0183 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0183
#print axioms coverageSize0183

noncomputable def pairing0184 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0184 : List (Fin 4935) := templateData0184

noncomputable def witness0184 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3205) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2731) else (if t 3 = 0 then 2760 else if t 3 = 1 then 2759 else 2985)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 343) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 342) else (if t 3 = 0 then 292 else if t 3 = 1 then 290 else 928)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 964 else 374) else if t 2 = 1 then (if t 3 = 0 then 965 else if t 3 = 1 then 963 else 373) else (if t 3 = 0 then 1478 else if t 3 = 1 then 304 else 2140))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 441) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 440) else (if t 3 = 0 then 586 else if t 3 = 1 then 584 else 1117)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2471) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3479) else (if t 3 = 0 then 3163 else if t 3 = 1 then 3488 else 3492)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2838 else 2489) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3472 else 3486) else (if t 3 = 0 then 3167 else if t 3 = 1 then 3490 else 3494))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1512) else if t 2 = 1 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 455) else (if t 3 = 0 then 593 else if t 3 = 1 then 592 else 1121)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2475) else if t 2 = 1 then (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3480) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3489 else 3493)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2842 else 2491) else if t 2 = 1 then (if t 3 = 0 then 3280 else if t 3 = 1 then 3473 else 3487) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3491 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3441 else (if jt.2.val < 2 then 3461 else 3463)) else (if jt.2.val < 4 then 3458 else (if jt.2.val < 5 then 3460 else 3459))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3440 else (if jt.2.val < 2 then 3470 else 3471)) else (if jt.2.val < 4 then 3467 else (if jt.2.val < 5 then 3469 else 3468)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3537 else (if jt.2.val < 2 then 3545 else 3548)) else (if jt.2.val < 4 then 3544 else (if jt.2.val < 5 then 3547 else 3546))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3538 else (if jt.2.val < 2 then 3542 else 3543)) else (if jt.2.val < 4 then 3539 else (if jt.2.val < 5 then 3541 else 3540)))))

checked_coverage fastCoverage0184 pairing0184 template0184 witness0184

theorem coverage0184 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0184) (maskBits m))
    cores template0184 witness0184 := by
  rw [← coresFast_eq]
  exact fastCoverage0184

theorem coverageSize0184 : ∀ q : Pattern,
    (cores (witness0184 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0184 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0184
#print axioms coverageSize0184

noncomputable def pairing0185 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0185 : List (Fin 4935) := templateData0185

noncomputable def witness0185 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3505) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 2730) else (if t 3 = 0 then 3004 else if t 3 = 1 then 3003 else 2743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 341) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 340) else (if t 3 = 0 then 874 else if t 3 = 1 then 862 else 400)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 141 else 893) else if t 2 = 1 then (if t 3 = 0 then 144 else if t 3 = 1 then 140 else 892) else (if t 3 = 0 then 2129 else if t 3 = 1 then 199 else 1501))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 439) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 438) else (if t 3 = 0 then 1219 else if t 3 = 1 then 1207 else 499)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2470) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3080) else (if t 3 = 0 then 3313 else if t 3 = 1 then 3098 else 3100)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2622 else 2900) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3089 else 3094) else (if t 3 = 0 then 3500 else if t 3 = 1 then 3102 else 3104))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 2126) else if t 2 = 1 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 454) else (if t 3 = 0 then 1223 else if t 3 = 1 then 1209 else 501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2474) else if t 2 = 1 then (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3083) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3099 else 3101)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2626 else 2901) else if t 2 = 1 then (if t 3 = 0 then 3093 else if t 3 = 1 then 3092 else 3096) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3103 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3050 else (if jt.2.val < 2 then 3070 else 3072)) else (if jt.2.val < 4 then 3067 else (if jt.2.val < 5 then 3069 else 3068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3384 else (if jt.2.val < 2 then 3394 else 3395)) else (if jt.2.val < 4 then 3391 else (if jt.2.val < 5 then 3393 else 3392)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3371 else (if jt.2.val < 2 then 3373 else 3377)) else (if jt.2.val < 4 then 3372 else (if jt.2.val < 5 then 3376 else 3375))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3540 else (if jt.2.val < 2 then 3551 else 3543)) else (if jt.2.val < 4 then 3549 else (if jt.2.val < 5 then 3550 else 3538)))))

checked_coverage fastCoverage0185 pairing0185 template0185 witness0185

theorem coverage0185 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0185) (maskBits m))
    cores template0185 witness0185 := by
  rw [← coresFast_eq]
  exact fastCoverage0185

theorem coverageSize0185 : ∀ q : Pattern,
    (cores (witness0185 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0185 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0185
#print axioms coverageSize0185

noncomputable def pairing0186 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0186 : List (Fin 4935) := templateData0186

noncomputable def witness0186 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2565 else 2884) else if t 2 = 1 then (if t 3 = 0 then 2560 else if t 3 = 1 then 2544 else 2546) else (if t 3 = 0 then 3499 else if t 3 = 1 then 3209 else 3210)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2563 else 1762) else if t 2 = 1 then (if t 3 = 0 then 2558 else if t 3 = 1 then 2538 else 1747) else (if t 3 = 0 then 277 else if t 3 = 1 then 251 else 256)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1372 else 2119) else if t 2 = 1 then (if t 3 = 0 then 1357 else if t 3 = 1 then 1350 else 1353) else (if t 3 = 0 then 922 else if t 3 = 1 then 254 else 258))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2564 else 1915) else if t 2 = 1 then (if t 3 = 0 then 2559 else if t 3 = 1 then 2541 else 1900) else (if t 3 = 0 then 571 else if t 3 = 1 then 545 else 549)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2562 else 2883) else if t 2 = 1 then (if t 3 = 0 then 2548 else if t 3 = 1 then 2519 else 2530) else (if t 3 = 0 then 2550 else if t 3 = 1 then 2523 else 2532)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2576 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2878 else if t 3 = 1 then 2526 else 2534) else (if t 3 = 0 then 2880 else if t 3 = 1 then 2528 else 2536))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 189 else 902) else if t 2 = 1 then (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 153) else (if t 3 = 0 then 2116 else if t 3 = 1 then 1532 else 1536)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2885) else if t 2 = 1 then (if t 3 = 0 then 2549 else if t 3 = 1 then 2521 else 2531) else (if t 3 = 0 then 2551 else if t 3 = 1 then 2524 else 2533)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2578 else 3507) else if t 2 = 1 then (if t 3 = 0 then 2879 else if t 3 = 1 then 2527 else 2535) else (if t 3 = 0 then 2881 else if t 3 = 1 then 2529 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2516 else (if jt.2.val < 2 then 2518 else 2540)) else (if jt.2.val < 4 then 2517 else (if jt.2.val < 5 then 2539 else 2520))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3417 else (if jt.2.val < 2 then 3419 else 3422)) else (if jt.2.val < 4 then 3418 else (if jt.2.val < 5 then 3421 else 3420)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3546 else (if jt.2.val < 2 then 3554 else 3548)) else (if jt.2.val < 4 then 3552 else (if jt.2.val < 5 then 3553 else 3537))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2871 else (if jt.2.val < 2 then 2873 else 2877)) else (if jt.2.val < 4 then 2872 else (if jt.2.val < 5 then 2876 else 2875)))))

checked_coverage fastCoverage0186 pairing0186 template0186 witness0186

theorem coverage0186 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0186) (maskBits m))
    cores template0186 witness0186 := by
  rw [← coresFast_eq]
  exact fastCoverage0186

theorem coverageSize0186 : ∀ q : Pattern,
    (cores (witness0186 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0186 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0186
#print axioms coverageSize0186

noncomputable def pairing0187 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0187 : List (Fin 4935) := templateData0187

noncomputable def witness0187 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2960 else 2506) else if t 2 = 1 then (if t 3 = 0 then 2953 else if t 3 = 1 then 2937 else 2938) else (if t 3 = 0 then 3152 else if t 3 = 1 then 3329 else 3514)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2958 else 1756) else if t 2 = 1 then (if t 3 = 0 then 2951 else if t 3 = 1 then 2931 else 1730) else (if t 3 = 0 then 859 else if t 3 = 1 then 830 else 833)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2104 else 1453) else if t 2 = 1 then (if t 3 = 0 then 2098 else if t 3 = 1 then 2082 else 1733) else (if t 3 = 0 then 75 else if t 3 = 1 then 835 else 837))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2959 else 1909) else if t 2 = 1 then (if t 3 = 0 then 2952 else if t 3 = 1 then 2934 else 1888) else (if t 3 = 0 then 1204 else if t 3 = 1 then 1180 else 1182)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2954 else 2502) else if t 2 = 1 then (if t 3 = 0 then 2947 else if t 3 = 1 then 2913 else 2919) else (if t 3 = 0 then 2949 else if t 3 = 1 then 2917 else 2921)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2650 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2699 else if t 3 = 1 then 2923 else 2927) else (if t 3 = 0 then 2701 else if t 3 = 1 then 2925 else 2929))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 1003 else 103) else if t 2 = 1 then (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 972) else (if t 3 = 0 then 1431 else if t 3 = 1 then 1796 else 2137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2503) else if t 2 = 1 then (if t 3 = 0 then 2948 else if t 3 = 1 then 2915 else 2920) else (if t 3 = 0 then 2950 else if t 3 = 1 then 2918 else 2922)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2651 else 3184) else if t 2 = 1 then (if t 3 = 0 then 2700 else if t 3 = 1 then 2924 else 2928) else (if t 3 = 0 then 2702 else if t 3 = 1 then 2926 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2910 else (if jt.2.val < 2 then 2912 else 2933)) else (if jt.2.val < 4 then 2911 else (if jt.2.val < 5 then 2932 else 2914))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3508 else (if jt.2.val < 2 then 3510 else 3513)) else (if jt.2.val < 4 then 3509 else (if jt.2.val < 5 then 3512 else 3511)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3375 else (if jt.2.val < 2 then 3383 else 3377)) else (if jt.2.val < 4 then 3381 else (if jt.2.val < 5 then 3382 else 3371))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2875 else (if jt.2.val < 2 then 2945 else 2877)) else (if jt.2.val < 4 then 2944 else (if jt.2.val < 5 then 2946 else 2871)))))

checked_coverage fastCoverage0187 pairing0187 template0187 witness0187

theorem coverage0187 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0187) (maskBits m))
    cores template0187 witness0187 := by
  rw [← coresFast_eq]
  exact fastCoverage0187

theorem coverageSize0187 : ∀ q : Pattern,
    (cores (witness0187 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0187 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0187
#print axioms coverageSize0187

noncomputable def pairing0188 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0188 : List (Fin 4935) := templateData0188

noncomputable def witness0188 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1029 else 469) else if t 2 = 1 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1027 else 467) else (if t 3 = 0 then 1549 else if t 3 = 1 then 595 else 2150)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1025 else if t 3 = 1 then 1021 else 1071) else if t 2 = 1 then (if t 3 = 0 then 1023 else if t 3 = 1 then 1019 else 1069) else (if t 3 = 0 then 784 else if t 3 = 1 then 1078 else 1090)) else (if t 2 = 0 then (if t 3 = 0 then 3520 else if t 3 = 1 then 3338 else 3226) else if t 2 = 1 then (if t 3 = 0 then 2972 else if t 3 = 1 then 2970 else 2979) else (if t 3 = 0 then 2800 else if t 3 = 1 then 2980 else 2981))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1028 else 468) else if t 2 = 1 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1026 else 466) else (if t 3 = 0 then 1548 else if t 3 = 1 then 594 else 2148)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1024 else if t 3 = 1 then 1020 else 1070) else if t 2 = 1 then (if t 3 = 0 then 1022 else if t 3 = 1 then 1018 else 1068) else (if t 3 = 0 then 783 else if t 3 = 1 then 1077 else 1086)) else (if t 2 = 0 then (if t 3 = 0 then 1040 else if t 3 = 1 then 1038 else 1073) else if t 2 = 1 then (if t 3 = 0 then 1039 else if t 3 = 1 then 1037 else 1072) else (if t 3 = 0 then 787 else if t 3 = 1 then 1081 else 1087))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 1815 else 2739) else if t 2 = 1 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1050 else 476) else (if t 3 = 0 then 3216 else if t 3 = 1 then 600 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2145 else if t 3 = 1 then 1812 else 1598) else if t 2 = 1 then (if t 3 = 0 then 1048 else if t 3 = 1 then 1045 else 1074) else (if t 3 = 0 then 789 else if t 3 = 1 then 1083 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 2147 else if t 3 = 1 then 1817 else 1601) else if t 2 = 1 then (if t 3 = 0 then 1055 else if t 3 = 1 then 1054 else 1076) else (if t 3 = 0 then 791 else if t 3 = 1 then 1085 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2910 else (if jt.2.val < 2 then 2977 else 2933)) else (if jt.2.val < 4 then 2975 else (if jt.2.val < 5 then 2976 else 2914))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3468 else (if jt.2.val < 2 then 3519 else 3471)) else (if jt.2.val < 4 then 3517 else (if jt.2.val < 5 then 3518 else 3440)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1944 else (if jt.2.val < 2 then 1946 else 1949)) else (if jt.2.val < 4 then 1945 else (if jt.2.val < 5 then 1948 else 1947))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1017 else (if jt.2.val < 2 then 1066 else 1067)) else (if jt.2.val < 4 then 1063 else (if jt.2.val < 5 then 1065 else 1064)))))

checked_coverage fastCoverage0188 pairing0188 template0188 witness0188

theorem coverage0188 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0188) (maskBits m))
    cores template0188 witness0188 := by
  rw [← coresFast_eq]
  exact fastCoverage0188

theorem coverageSize0188 : ∀ q : Pattern,
    (cores (witness0188 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0188 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0188
#print axioms coverageSize0188

noncomputable def pairing0189 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0189 : List (Fin 4935) := templateData0189

noncomputable def witness0189 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 620 else 1134) else if t 2 = 1 then (if t 3 = 0 then 626 else if t 3 = 1 then 618 else 1132) else (if t 3 = 0 then 2161 else if t 3 = 1 then 694 else 1526)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 624 else if t 3 = 1 then 616 else 656) else if t 2 = 1 then (if t 3 = 0 then 622 else if t 3 = 1 then 614 else 654) else (if t 3 = 0 then 1144 else if t 3 = 1 then 680 else 682)) else (if t 2 = 0 then (if t 3 = 0 then 3174 else if t 3 = 1 then 3172 else 3524) else if t 2 = 1 then (if t 3 = 0 then 2769 else if t 3 = 1 then 2766 else 2775) else (if t 3 = 0 then 2989 else if t 3 = 1 then 2778 else 2779))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 619 else 1133) else if t 2 = 1 then (if t 3 = 0 then 625 else if t 3 = 1 then 617 else 1131) else (if t 3 = 0 then 2160 else if t 3 = 1 then 690 else 1524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 623 else if t 3 = 1 then 615 else 655) else if t 2 = 1 then (if t 3 = 0 then 621 else if t 3 = 1 then 613 else 653) else (if t 3 = 0 then 1140 else if t 3 = 1 then 672 else 676)) else (if t 2 = 0 then (if t 3 = 0 then 637 else if t 3 = 1 then 633 else 663) else if t 2 = 1 then (if t 3 = 0 then 636 else if t 3 = 1 then 632 else 662) else (if t 3 = 0 then 1141 else if t 3 = 1 then 673 else 677))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1785 else 2988) else if t 2 = 1 then (if t 3 = 0 then 647 else if t 3 = 1 then 643 else 1137) else (if t 3 = 0 then 3523 else if t 3 = 1 then 692 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1461 else if t 3 = 1 then 1458 else 2169) else if t 2 = 1 then (if t 3 = 0 then 645 else if t 3 = 1 then 640 else 666) else (if t 3 = 0 then 1142 else if t 3 = 1 then 674 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 1464 else if t 3 = 1 then 1463 else 2171) else if t 2 = 1 then (if t 3 = 0 then 651 else if t 3 = 1 then 649 else 670) else (if t 3 = 0 then 1143 else if t 3 = 1 then 675 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2516 else (if jt.2.val < 2 then 2773 else 2540)) else (if jt.2.val < 4 then 2771 else (if jt.2.val < 5 then 2772 else 2520))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3392 else (if jt.2.val < 2 then 3428 else 3395)) else (if jt.2.val < 4 then 3426 else (if jt.2.val < 5 then 3427 else 3384)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2250 else (if jt.2.val < 2 then 2252 else 2255)) else (if jt.2.val < 4 then 2251 else (if jt.2.val < 5 then 2254 else 2253))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1064 else (if jt.2.val < 2 then 1130 else 1067)) else (if jt.2.val < 4 then 1125 else (if jt.2.val < 5 then 1126 else 1017)))))

checked_coverage fastCoverage0189 pairing0189 template0189 witness0189

theorem coverage0189 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0189) (maskBits m))
    cores template0189 witness0189 := by
  rw [← coresFast_eq]
  exact fastCoverage0189

theorem coverageSize0189 : ∀ q : Pattern,
    (cores (witness0189 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0189 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0189
#print axioms coverageSize0189

noncomputable def pairing0190 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0190 : List (Fin 4935) := templateData0190

noncomputable def witness0190 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1682 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1669 else 1670) else (if t 3 = 0 then 1112 else if t 3 = 1 then 553 else 555)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1678 else 1853) else if t 2 = 1 then (if t 3 = 0 then 1660 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 741 else if t 3 = 1 then 1647 else 1651)) else (if t 2 = 0 then (if t 3 = 0 then 2722 else if t 3 = 1 then 2860 else 2868) else if t 2 = 1 then (if t 3 = 0 then 2689 else if t 3 = 1 then 3232 else 3235) else (if t 3 = 0 then 3522 else if t 3 = 1 then 3234 else 3236))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1681 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1665 else 1667) else (if t 3 = 0 then 1110 else if t 3 = 1 then 546 else 550)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1677 else 1851) else if t 2 = 1 then (if t 3 = 0 then 1656 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 734 else if t 3 = 1 then 1632 else 1640)) else (if t 2 = 0 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1685 else 1852) else if t 2 = 1 then (if t 3 = 0 then 1657 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 735 else if t 3 = 1 then 1633 else 1641))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 200 else 3525) else if t 2 = 1 then (if t 3 = 0 then 894 else if t 3 = 1 then 150 else 154) else (if t 3 = 0 then 2984 else if t 3 = 1 then 1833 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 401 else if t 3 = 1 then 863 else 876) else if t 2 = 1 then (if t 3 = 0 then 350 else if t 3 = 1 then 1630 else 1638) else (if t 3 = 0 then 2157 else if t 3 = 1 then 1634 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 404 else if t 3 = 1 then 866 else 877) else if t 2 = 1 then (if t 3 = 0 then 351 else if t 3 = 1 then 1631 else 1639) else (if t 3 = 0 then 2158 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3050 else (if jt.2.val < 2 then 3231 else 3072)) else (if jt.2.val < 4 then 3230 else (if jt.2.val < 5 then 3233 else 3068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3420 else (if jt.2.val < 2 then 3436 else 3422)) else (if jt.2.val < 4 then 3435 else (if jt.2.val < 5 then 3437 else 3417)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1947 else (if jt.2.val < 2 then 1964 else 1949)) else (if jt.2.val < 4 then 1959 else (if jt.2.val < 5 then 1960 else 1944))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2256 else (if jt.2.val < 2 then 2258 else 2261)) else (if jt.2.val < 4 then 2257 else (if jt.2.val < 5 then 2260 else 2259)))))

checked_coverage fastCoverage0190 pairing0190 template0190 witness0190

theorem coverage0190 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0190) (maskBits m))
    cores template0190 witness0190 := by
  rw [← coresFast_eq]
  exact fastCoverage0190

theorem coverageSize0190 : ∀ q : Pattern,
    (cores (witness0190 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0190 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0190
#print axioms coverageSize0190

noncomputable def pairing0191 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0191 : List (Fin 4935) := templateData0191

noncomputable def witness0191 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2225 else 1622) else if t 2 = 1 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2207 else 1892) else (if t 3 = 0 then 764 else if t 3 = 1 then 1189 else 1190)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2222 else 1616) else if t 2 = 1 then (if t 3 = 0 then 2213 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 742 else if t 3 = 1 then 2196 else 2200)) else (if t 2 = 0 then (if t 3 = 0 then 2906 else if t 3 = 1 then 2648 else 2649) else if t 2 = 1 then (if t 3 = 0 then 2690 else if t 3 = 1 then 3528 else 3531) else (if t 3 = 0 then 3192 else if t 3 = 1 then 3530 else 3532))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2223 else 1620) else if t 2 = 1 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2205 else 1889) else (if t 3 = 0 then 761 else if t 3 = 1 then 1183 else 1185)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2220 else 1614) else if t 2 = 1 then (if t 3 = 0 then 2211 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 736 else if t 3 = 1 then 2181 else 2189)) else (if t 2 = 0 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2221 else 1615) else if t 2 = 1 then (if t 3 = 0 then 2212 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 737 else if t 3 = 1 then 2182 else 2190))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 306 else 3229) else if t 2 = 1 then (if t 3 = 0 then 377 else if t 3 = 1 then 973 else 975) else (if t 3 = 0 then 2796 else if t 3 = 1 then 1799 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 930 else if t 3 = 1 then 294 else 296) else if t 2 = 1 then (if t 3 = 0 then 352 else if t 3 = 1 then 2179 else 2187) else (if t 3 = 0 then 1487 else if t 3 = 1 then 2183 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 931 else if t 3 = 1 then 295 else 297) else if t 2 = 1 then (if t 3 = 0 then 353 else if t 3 = 1 then 2180 else 2188) else (if t 3 = 0 then 1488 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3441 else (if jt.2.val < 2 then 3527 else 3463)) else (if jt.2.val < 4 then 3526 else (if jt.2.val < 5 then 3529 else 3459))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3511 else (if jt.2.val < 2 then 3534 else 3513)) else (if jt.2.val < 4 then 3533 else (if jt.2.val < 5 then 3535 else 3508)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2253 else (if jt.2.val < 2 then 2267 else 2255)) else (if jt.2.val < 4 then 2265 else (if jt.2.val < 5 then 2266 else 2250))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2259 else (if jt.2.val < 2 then 2263 else 2261)) else (if jt.2.val < 4 then 2262 else (if jt.2.val < 5 then 2264 else 2256)))))

checked_coverage fastCoverage0191 pairing0191 template0191 witness0191

theorem coverage0191 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0191) (maskBits m))
    cores template0191 witness0191 := by
  rw [← coresFast_eq]
  exact fastCoverage0191

theorem coverageSize0191 : ∀ q : Pattern,
    (cores (witness0191 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0191 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0191
#print axioms coverageSize0191

noncomputable def pairing0192 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0192 : List (Fin 4935) := templateData0192

noncomputable def witness0192 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3198) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2797) else (if t 3 = 0 then 2974 else if t 3 = 1 then 2972 else 2800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 87) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 86) else (if t 3 = 0 then 965 else if t 3 = 1 then 961 else 100)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 143 else 904) else if t 2 = 1 then (if t 3 = 0 then 144 else if t 3 = 1 then 142 else 898) else (if t 3 = 0 then 1496 else if t 3 = 1 then 172 else 1807))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 774) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 773) else (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 787)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2717) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3295) else (if t 3 = 0 then 3278 else if t 3 = 1 then 3276 else 3297)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2623 else 2904) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3291 else 3299) else (if t 3 = 0 then 3095 else if t 3 = 1 then 3293 else 3301))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 1499) else if t 2 = 1 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 781) else (if t 3 = 0 then 1057 else if t 3 = 1 then 1055 else 791)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2719) else if t 2 = 1 then (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3296) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3279 else 3298)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2627 else 2905) else if t 2 = 1 then (if t 3 = 0 then 3093 else if t 3 = 1 then 3292 else 3300) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3294 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3246 else (if jt.2.val < 2 then 3266 else 3268)) else (if jt.2.val < 4 then 3263 else (if jt.2.val < 5 then 3265 else 3264))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3555 else (if jt.2.val < 2 then 3565 else 3566)) else (if jt.2.val < 4 then 3562 else (if jt.2.val < 5 then 3564 else 3563)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3556 else (if jt.2.val < 2 then 3560 else 3561)) else (if jt.2.val < 4 then 3557 else (if jt.2.val < 5 then 3559 else 3558))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3243 else (if jt.2.val < 2 then 3282 else 3285)) else (if jt.2.val < 4 then 3281 else (if jt.2.val < 5 then 3284 else 3283)))))

checked_coverage fastCoverage0192 pairing0192 template0192 witness0192

theorem coverage0192 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0192) (maskBits m))
    cores template0192 witness0192 := by
  rw [← coresFast_eq]
  exact fastCoverage0192

theorem coverageSize0192 : ∀ q : Pattern,
    (cores (witness0192 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0192 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0192
#print axioms coverageSize0192

noncomputable def pairing0193 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0193 : List (Fin 4935) := templateData0193

noncomputable def witness0193 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3312) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 2794) else (if t 3 = 0 then 2760 else if t 3 = 1 then 2756 else 2983)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 73) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 60) else (if t 3 = 0 then 292 else if t 3 = 1 then 264 else 916)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 859 else 75) else if t 2 = 1 then (if t 3 = 0 then 874 else if t 3 = 1 then 853 else 65) else (if t 3 = 0 then 1790 else if t 3 = 1 then 269 else 1471))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 760) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 748) else (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 1105)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2697) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3126) else (if t 3 = 0 then 3163 else if t 3 = 1 then 3123 else 3128)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2949 else 2701) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3130 else 3134) else (if t 3 = 0 then 3315 else if t 3 = 1 then 3132 else 3136))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 1774) else if t 2 = 1 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 750) else (if t 3 = 0 then 593 else if t 3 = 1 then 559 else 1107)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2698) else if t 2 = 1 then (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3127) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3124 else 3129)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2950 else 2702) else if t 2 = 1 then (if t 3 = 0 then 3314 else if t 3 = 1 then 3131 else 3135) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3133 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3116 else (if jt.2.val < 2 then 3118 else 3140)) else (if jt.2.val < 4 then 3117 else (if jt.2.val < 5 then 3139 else 3120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3567 else (if jt.2.val < 2 then 3569 else 3572)) else (if jt.2.val < 4 then 3568 else (if jt.2.val < 5 then 3571 else 3570)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3399 else (if jt.2.val < 2 then 3401 else 3407)) else (if jt.2.val < 4 then 3400 else (if jt.2.val < 5 then 3406 else 3402))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3283 else (if jt.2.val < 2 then 3308 else 3285)) else (if jt.2.val < 4 then 3303 else (if jt.2.val < 5 then 3304 else 3243)))))

checked_coverage fastCoverage0193 pairing0193 template0193 witness0193

theorem coverage0193 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0193) (maskBits m))
    cores template0193 witness0193 := by
  rw [← coresFast_eq]
  exact fastCoverage0193

theorem coverageSize0193 : ∀ q : Pattern,
    (cores (witness0193 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0193 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0193
#print axioms coverageSize0193

noncomputable def pairing0194 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0194 : List (Fin 4935) := templateData0194

noncomputable def witness0194 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2813 else 2722) else if t 2 = 1 then (if t 3 = 0 then 2817 else if t 3 = 1 then 2809 else 2860) else (if t 3 = 0 then 3340 else if t 3 = 1 then 3338 else 3242)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2811 else 1371) else if t 2 = 1 then (if t 3 = 0 then 2815 else if t 3 = 1 then 2807 else 1370) else (if t 3 = 0 then 964 else if t 3 = 1 then 960 else 1001)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1415 else 1780) else if t 2 = 1 then (if t 3 = 0 then 1416 else if t 3 = 1 then 1414 else 1777) else (if t 3 = 0 then 374 else if t 3 = 1 then 992 else 1012))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2812 else 1686) else if t 2 = 1 then (if t 3 = 0 then 2816 else if t 3 = 1 then 2808 else 1685) else (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1082)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2810 else 2721) else if t 2 = 1 then (if t 3 = 0 then 2814 else if t 3 = 1 then 2806 else 2859) else (if t 3 = 0 then 2838 else if t 3 = 1 then 2835 else 2862)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2632 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2484 else if t 3 = 1 then 2854 else 2864) else (if t 3 = 0 then 2489 else if t 3 = 1 then 2857 else 2866))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 820 else 404) else if t 2 = 1 then (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 866) else (if t 3 = 0 then 1818 else if t 3 = 1 then 1817 else 1691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2723) else if t 2 = 1 then (if t 3 = 0 then 2829 else if t 3 = 1 then 2826 else 2861) else (if t 3 = 0 then 2842 else if t 3 = 1 then 2840 else 2863)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2635 else 3322) else if t 2 = 1 then (if t 3 = 0 then 2487 else if t 3 = 1 then 2856 else 2865) else (if t 3 = 0 then 2491 else if t 3 = 1 then 2858 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2805 else (if jt.2.val < 2 then 2825 else 2827)) else (if jt.2.val < 4 then 2822 else (if jt.2.val < 5 then 2824 else 2823))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3575 else (if jt.2.val < 2 then 3580 else 3581)) else (if jt.2.val < 4 then 3577 else (if jt.2.val < 5 then 3579 else 3578)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3558 else (if jt.2.val < 2 then 3576 else 3561)) else (if jt.2.val < 4 then 3573 else (if jt.2.val < 5 then 3574 else 3556))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2802 else (if jt.2.val < 2 then 2845 else 2848)) else (if jt.2.val < 4 then 2844 else (if jt.2.val < 5 then 2847 else 2846)))))

checked_coverage fastCoverage0194 pairing0194 template0194 witness0194

theorem coverage0194 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0194) (maskBits m))
    cores template0194 witness0194 := by
  rw [← coresFast_eq]
  exact fastCoverage0194

theorem coverageSize0194 : ∀ q : Pattern,
    (cores (witness0194 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0194 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0194
#print axioms coverageSize0194

noncomputable def pairing0195 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0195 : List (Fin 4935) := templateData0195

noncomputable def witness0195 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2560 else 2882) else if t 2 = 1 then (if t 3 = 0 then 2565 else if t 3 = 1 then 2544 else 2545) else (if t 3 = 0 then 3215 else if t 3 = 1 then 3209 else 3342)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2558 else 1357) else if t 2 = 1 then (if t 3 = 0 then 2563 else if t 3 = 1 then 2538 else 1350) else (if t 3 = 0 then 291 else if t 3 = 1 then 251 else 254)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1750 else 1359) else if t 2 = 1 then (if t 3 = 0 then 1762 else if t 3 = 1 then 1747 else 1353) else (if t 3 = 0 then 929 else if t 3 = 1 then 256 else 258))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2559 else 1672) else if t 2 = 1 then (if t 3 = 0 then 2564 else if t 3 = 1 then 2541 else 1666) else (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 547)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2548 else 2878) else if t 2 = 1 then (if t 3 = 0 then 2562 else if t 3 = 1 then 2519 else 2526) else (if t 3 = 0 then 2572 else if t 3 = 1 then 2523 else 2528)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2554 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2883 else if t 3 = 1 then 2530 else 2534) else (if t 3 = 0 then 2886 else if t 3 = 1 then 2532 else 2536))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 175 else 895) else if t 2 = 1 then (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 151) else (if t 3 = 0 then 1547 else if t 3 = 1 then 1532 else 1834)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2879) else if t 2 = 1 then (if t 3 = 0 then 2570 else if t 3 = 1 then 2521 else 2527) else (if t 3 = 0 then 2574 else if t 3 = 1 then 2524 else 2529)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2555 else 3197) else if t 2 = 1 then (if t 3 = 0 then 2885 else if t 3 = 1 then 2531 else 2535) else (if t 3 = 0 then 2887 else if t 3 = 1 then 2533 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2516 else (if jt.2.val < 2 then 2518 else 2540)) else (if jt.2.val < 4 then 2517 else (if jt.2.val < 5 then 2539 else 2520))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3582 else (if jt.2.val < 2 then 3584 else 3587)) else (if jt.2.val < 4 then 3583 else (if jt.2.val < 5 then 3586 else 3585)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3402 else (if jt.2.val < 2 then 3424 else 3407)) else (if jt.2.val < 4 then 3423 else (if jt.2.val < 5 then 3425 else 3399))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2846 else (if jt.2.val < 2 then 2874 else 2848)) else (if jt.2.val < 4 then 2869 else (if jt.2.val < 5 then 2870 else 2802)))))

checked_coverage fastCoverage0195 pairing0195 template0195 witness0195

theorem coverage0195 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0195) (maskBits m))
    cores template0195 witness0195 := by
  rw [← coresFast_eq]
  exact fastCoverage0195

theorem coverageSize0195 : ∀ q : Pattern,
    (cores (witness0195 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0195 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0195
#print axioms coverageSize0195

noncomputable def pairing0196 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0196 : List (Fin 4935) := templateData0196

noncomputable def witness0196 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 624 else 1148) else if t 2 = 1 then (if t 3 = 0 then 626 else if t 3 = 1 then 622 else 1144) else (if t 3 = 0 then 1519 else if t 3 = 1 then 659 else 1826)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 620 else if t 3 = 1 then 616 else 688) else if t 2 = 1 then (if t 3 = 0 then 618 else if t 3 = 1 then 614 else 680) else (if t 3 = 0 then 1132 else if t 3 = 1 then 654 else 682)) else (if t 2 = 0 then (if t 3 = 0 then 3320 else if t 3 = 1 then 3172 else 3182) else if t 2 = 1 then (if t 3 = 0 then 2768 else if t 3 = 1 then 2766 else 2778) else (if t 3 = 0 then 2987 else if t 3 = 1 then 2775 else 2779))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 623 else 1146) else if t 2 = 1 then (if t 3 = 0 then 625 else if t 3 = 1 then 621 else 1140) else (if t 3 = 0 then 1518 else if t 3 = 1 then 658 else 1824)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 619 else if t 3 = 1 then 615 else 684) else if t 2 = 1 then (if t 3 = 0 then 617 else if t 3 = 1 then 613 else 672) else (if t 3 = 0 then 1131 else if t 3 = 1 then 653 else 676)) else (if t 2 = 0 then (if t 3 = 0 then 635 else if t 3 = 1 then 633 else 685) else if t 2 = 1 then (if t 3 = 0 then 634 else if t 3 = 1 then 632 else 673) else (if t 3 = 0 then 1135 else if t 3 = 1 then 662 else 677))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1461 else 2990) else if t 2 = 1 then (if t 3 = 0 then 647 else if t 3 = 1 then 645 else 1142) else (if t 3 = 0 then 3206 else if t 3 = 1 then 668 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1785 else if t 3 = 1 then 1458 else 1473) else if t 2 = 1 then (if t 3 = 0 then 643 else if t 3 = 1 then 640 else 674) else (if t 3 = 0 then 1137 else if t 3 = 1 then 666 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 1787 else if t 3 = 1 then 1463 else 1474) else if t 2 = 1 then (if t 3 = 0 then 650 else if t 3 = 1 then 649 else 675) else (if t 3 = 0 then 1139 else if t 3 = 1 then 670 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2516 else (if jt.2.val < 2 then 2773 else 2540)) else (if jt.2.val < 4 then 2771 else (if jt.2.val < 5 then 2772 else 2520))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3563 else (if jt.2.val < 2 then 3590 else 3566)) else (if jt.2.val < 4 then 3588 else (if jt.2.val < 5 then 3589 else 3555)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2015 else (if jt.2.val < 2 then 2020 else 2021)) else (if jt.2.val < 4 then 2017 else (if jt.2.val < 5 then 2019 else 2018))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1122 else (if jt.2.val < 2 then 1124 else 1129)) else (if jt.2.val < 4 then 1123 else (if jt.2.val < 5 then 1128 else 1127)))))

checked_coverage fastCoverage0196 pairing0196 template0196 witness0196

theorem coverage0196 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0196) (maskBits m))
    cores template0196 witness0196 := by
  rw [← coresFast_eq]
  exact fastCoverage0196

theorem coverageSize0196 : ∀ q : Pattern,
    (cores (witness0196 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0196 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0196
#print axioms coverageSize0196

noncomputable def pairing0197 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0197 : List (Fin 4935) := templateData0197

noncomputable def witness0197 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1205 else 764) else if t 2 = 1 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1201 else 757) else (if t 3 = 0 then 1837 else if t 3 = 1 then 568 else 1544)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1214 else if t 3 = 1 then 1187 else 1189) else if t 2 = 1 then (if t 3 = 0 then 1210 else if t 3 = 1 then 1167 else 1172) else (if t 3 = 0 then 502 else if t 3 = 1 then 1170 else 1174)) else (if t 2 = 0 then (if t 3 = 0 then 3106 else if t 3 = 1 then 3329 else 3330) else if t 2 = 1 then (if t 3 = 0 then 3003 else if t 3 = 1 then 2993 else 2996) else (if t 3 = 0 then 2743 else if t 3 = 1 then 2995 else 2997))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1203 else 761) else if t 2 = 1 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1197 else 751) else (if t 3 = 0 then 1836 else if t 3 = 1 then 562 else 1542)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1212 else if t 3 = 1 then 1179 else 1183) else if t 2 = 1 then (if t 3 = 0 then 1206 else if t 3 = 1 then 1151 else 1159) else (if t 3 = 0 then 498 else if t 3 = 1 then 1155 else 1163)) else (if t 2 = 0 then (if t 3 = 0 then 1213 else if t 3 = 1 then 1180 else 1184) else if t 2 = 1 then (if t 3 = 0 then 1207 else if t 3 = 1 then 1152 else 1160) else (if t 3 = 0 then 499 else if t 3 = 1 then 1156 else 1164))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1430 else 2796) else if t 2 = 1 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1199 else 753) else (if t 3 = 0 then 3343 else if t 3 = 1 then 564 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1374 else if t 3 = 1 then 1795 else 1799) else if t 2 = 1 then (if t 3 = 0 then 1208 else if t 3 = 1 then 1153 else 1161) else (if t 3 = 0 then 500 else if t 3 = 1 then 1157 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 1375 else if t 3 = 1 then 1796 else 1800) else if t 2 = 1 then (if t 3 = 0 then 1209 else if t 3 = 1 then 1154 else 1162) else (if t 3 = 0 then 501 else if t 3 = 1 then 1158 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2805 else (if jt.2.val < 2 then 2992 else 2827)) else (if jt.2.val < 4 then 2991 else (if jt.2.val < 5 then 2994 else 2823))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3570 else (if jt.2.val < 2 then 3592 else 3572)) else (if jt.2.val < 4 then 3591 else (if jt.2.val < 5 then 3593 else 3567)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2304 else (if jt.2.val < 2 then 2306 else 2309)) else (if jt.2.val < 4 then 2305 else (if jt.2.val < 5 then 2308 else 2307))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1127 else (if jt.2.val < 2 then 1193 else 1129)) else (if jt.2.val < 4 then 1191 else (if jt.2.val < 5 then 1192 else 1122)))))

checked_coverage fastCoverage0197 pairing0197 template0197 witness0197

theorem coverage0197 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0197) (maskBits m))
    cores template0197 witness0197 := by
  rw [← coresFast_eq]
  exact fastCoverage0197

theorem coverageSize0197 : ∀ q : Pattern,
    (cores (witness0197 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0197 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0197
#print axioms coverageSize0197

noncomputable def pairing0198 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0198 : List (Fin 4935) := templateData0198

noncomputable def witness0198 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1572 else 1856) else if t 2 = 1 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1570 else 1853) else (if t 3 = 0 then 469 else if t 3 = 1 then 1071 else 1094)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1564 else 1616) else if t 2 = 1 then (if t 3 = 0 then 1566 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 464 else if t 3 = 1 then 1593 else 1612)) else (if t 2 = 0 then (if t 3 = 0 then 2898 else if t 3 = 1 then 2630 else 2649) else if t 2 = 1 then (if t 3 = 0 then 2482 else if t 3 = 1 then 3219 else 3227) else (if t 3 = 0 then 3344 else if t 3 = 1 then 3225 else 3228))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1571 else 1854) else if t 2 = 1 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1569 else 1851) else (if t 3 = 0 then 468 else if t 3 = 1 then 1070 else 1092)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1563 else 1614) else if t 2 = 1 then (if t 3 = 0 then 1565 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 463 else if t 3 = 1 then 1592 else 1606)) else (if t 2 = 0 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1581 else 1615) else if t 2 = 1 then (if t 3 = 0 then 1582 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 471 else if t 3 = 1 then 1595 else 1607))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 270 else 3345) else if t 2 = 1 then (if t 3 = 0 then 66 else if t 3 = 1 then 854 else 876) else (if t 3 = 0 then 2739 else if t 3 = 1 then 1598 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 917 else if t 3 = 1 then 265 else 296) else if t 2 = 1 then (if t 3 = 0 then 61 else if t 3 = 1 then 1588 else 1604) else (if t 3 = 0 then 1848 else if t 3 = 1 then 1596 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 920 else if t 3 = 1 then 273 else 297) else if t 2 = 1 then (if t 3 = 0 then 69 else if t 3 = 1 then 1591 else 1605) else (if t 3 = 0 then 1850 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3116 else (if jt.2.val < 2 then 3223 else 3140)) else (if jt.2.val < 4 then 3221 else (if jt.2.val < 5 then 3222 else 3120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3578 else (if jt.2.val < 2 then 3596 else 3581)) else (if jt.2.val < 4 then 3594 else (if jt.2.val < 5 then 3595 else 3575)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2018 else (if jt.2.val < 2 then 2036 else 2021)) else (if jt.2.val < 4 then 2033 else (if jt.2.val < 5 then 2034 else 2015))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1839 else (if jt.2.val < 2 then 1841 else 1846)) else (if jt.2.val < 4 then 1840 else (if jt.2.val < 5 then 1845 else 1844)))))

checked_coverage fastCoverage0198 pairing0198 template0198 witness0198

theorem coverage0198 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0198) (maskBits m))
    cores template0198 witness0198 := by
  rw [← coresFast_eq]
  exact fastCoverage0198

theorem coverageSize0198 : ∀ q : Pattern,
    (cores (witness0198 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0198 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0198
#print axioms coverageSize0198

noncomputable def pairing0199 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0199 : List (Fin 4935) := templateData0199

noncomputable def witness0199 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1904 else 1676) else if t 2 = 1 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1901 else 1670) else (if t 3 = 0 then 1116 else if t 3 = 1 then 554 else 555)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1891 else 1892) else if t 2 = 1 then (if t 3 = 0 then 1907 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 496 else if t 3 = 1 then 1878 else 1882)) else (if t 2 = 0 then (if t 3 = 0 then 2506 else if t 3 = 1 then 2938 else 2940) else if t 2 = 1 then (if t 3 = 0 then 2500 else if t 3 = 1 then 3348 else 3351) else (if t 3 = 0 then 3207 else if t 3 = 1 then 3350 else 3352))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1902 else 1673) else if t 2 = 1 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1899 else 1667) else (if t 3 = 0 then 1115 else if t 3 = 1 then 548 else 550)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1887 else 1889) else if t 2 = 1 then (if t 3 = 0 then 1905 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 492 else if t 3 = 1 then 1863 else 1871)) else (if t 2 = 0 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1888 else 1890) else if t 2 = 1 then (if t 3 = 0 then 1906 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 493 else if t 3 = 1 then 1864 else 1872))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 176 else 3240) else if t 2 = 1 then (if t 3 = 0 then 899 else if t 3 = 1 then 152 else 154) else (if t 3 = 0 then 2986 else if t 3 = 1 then 1535 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 102 else if t 3 = 1 then 971 else 975) else if t 2 = 1 then (if t 3 = 0 then 90 else if t 3 = 1 then 1861 else 1869) else (if t 3 = 0 then 1521 else if t 3 = 1 then 1865 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 103 else if t 3 = 1 then 972 else 976) else if t 2 = 1 then (if t 3 = 0 then 91 else if t 3 = 1 then 1862 else 1870) else (if t 3 = 0 then 1522 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3246 else (if jt.2.val < 2 then 3347 else 3268)) else (if jt.2.val < 4 then 3346 else (if jt.2.val < 5 then 3349 else 3264))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3585 else (if jt.2.val < 2 then 3598 else 3587)) else (if jt.2.val < 4 then 3597 else (if jt.2.val < 5 then 3599 else 3582)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2307 else (if jt.2.val < 2 then 2317 else 2309)) else (if jt.2.val < 4 then 2316 else (if jt.2.val < 5 then 2318 else 2304))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1844 else (if jt.2.val < 2 then 1895 else 1846)) else (if jt.2.val < 4 then 1893 else (if jt.2.val < 5 then 1894 else 1839)))))

checked_coverage fastCoverage0199 pairing0199 template0199 witness0199

theorem coverage0199 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0199) (maskBits m))
    cores template0199 witness0199 := by
  rw [← coresFast_eq]
  exact fastCoverage0199

theorem coverageSize0199 : ∀ q : Pattern,
    (cores (witness0199 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0199 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0199
#print axioms coverageSize0199

end Crown.CertificateData
