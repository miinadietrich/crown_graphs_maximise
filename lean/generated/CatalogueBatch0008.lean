import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0007

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0280 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0280 : List (Fin 4935) := templateData0280

noncomputable def witness0280 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 3925) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2750) else (if t 3 = 0 then 2741 else if t 3 = 1 then 2740 else 2985)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 538) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 537) else (if t 3 = 0 then 490 else if t 3 = 1 then 488 else 1114)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1171 else 569) else if t 2 = 1 then (if t 3 = 0 then 1174 else if t 3 = 1 then 1170 else 568) else (if t 3 = 0 then 1526 else if t 3 = 1 then 502 else 1837))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 243) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 242) else (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 925)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2614) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4015) else (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4023)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2635) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4017) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4021 else 4025))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 1464) else if t 2 = 1 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 261) else (if t 3 = 0 then 398 else if t 3 = 1 then 397 else 927)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2627) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4016) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4020 else 4024)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2841 else 2639) else if t 2 = 1 then (if t 3 = 0 then 4004 else if t 3 = 1 then 4003 else 4018) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4022 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3972 else (if jt.2.val < 2 then 3992 else 3994)) else (if jt.2.val < 4 then 3989 else (if jt.2.val < 5 then 3991 else 3990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3971 else (if jt.2.val < 2 then 3999 else 4001)) else (if jt.2.val < 4 then 3996 else (if jt.2.val < 5 then 3998 else 3997)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4068 else (if jt.2.val < 2 then 4074 else 4079)) else (if jt.2.val < 4 then 4073 else (if jt.2.val < 5 then 4078 else 4077))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4069 else (if jt.2.val < 2 then 4075 else 4076)) else (if jt.2.val < 4 then 4070 else (if jt.2.val < 5 then 4072 else 4071)))))

checked_coverage fastCoverage0280 pairing0280 template0280 witness0280

theorem coverage0280 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0280) (maskBits m))
    cores template0280 witness0280 := by
  rw [← coresFast_eq]
  exact fastCoverage0280

theorem coverageSize0280 : ∀ q : Pattern,
    (cores (witness0280 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0280 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0280
#print axioms coverageSize0280

noncomputable def pairing0281 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0281 : List (Fin 4935) := templateData0281

noncomputable def witness0281 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4044) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2749) else (if t 3 = 0 then 2981 else if t 3 = 1 then 2980 else 2762)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 536) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 535) else (if t 3 = 0 then 1090 else if t 3 = 1 then 1078 else 595)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 724 else 1109) else if t 2 = 1 then (if t 3 = 0 then 727 else if t 3 = 1 then 723 else 1108) else (if t 3 = 0 then 1826 else if t 3 = 1 then 784 else 1549))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 241) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 240) else (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 301)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2613) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3843) else (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3856)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2899) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3848) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3854 else 3858))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 1787) else if t 2 = 1 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 260) else (if t 3 = 0 then 1013 else if t 3 = 1 then 999 else 303)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2626) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3846) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3853 else 3857)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2474 else 2901) else if t 2 = 1 then (if t 3 = 0 then 3838 else if t 3 = 1 then 3837 else 3850) else (if t 3 = 0 then 4040 else if t 3 = 1 then 3855 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3806 else (if jt.2.val < 2 then 3826 else 3828)) else (if jt.2.val < 4 then 3823 else (if jt.2.val < 5 then 3825 else 3824))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3805 else (if jt.2.val < 2 then 3833 else 3835)) else (if jt.2.val < 4 then 3830 else (if jt.2.val < 5 then 3832 else 3831)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4082 else (if jt.2.val < 2 then 4084 else 4088)) else (if jt.2.val < 4 then 4083 else (if jt.2.val < 5 then 4087 else 4086))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4071 else (if jt.2.val < 2 then 4085 else 4076)) else (if jt.2.val < 4 then 4080 else (if jt.2.val < 5 then 4081 else 4069)))))

checked_coverage fastCoverage0281 pairing0281 template0281 witness0281

theorem coverage0281 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0281) (maskBits m))
    cores template0281 witness0281 := by
  rw [← coresFast_eq]
  exact fastCoverage0281

theorem coverageSize0281 : ∀ q : Pattern,
    (cores (witness0281 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0281 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0281
#print axioms coverageSize0281

noncomputable def pairing0282 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0282 : List (Fin 4935) := templateData0282

noncomputable def witness0282 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2710 else 2906) else if t 2 = 1 then (if t 3 = 0 then 2705 else if t 3 = 1 then 2688 else 2690) else (if t 3 = 0 then 4036 else if t 3 = 1 then 3929 else 3930)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2708 else 2107) else if t 2 = 1 then (if t 3 = 0 then 2703 else if t 3 = 1 then 2682 else 2090) else (if t 3 = 0 then 475 else if t 3 = 1 then 445 else 450)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1371 else 1780) else if t 2 = 1 then (if t 3 = 0 then 1357 else if t 3 = 1 then 1339 else 1342) else (if t 3 = 0 then 1138 else if t 3 = 1 then 448 else 452))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2709 else 2227) else if t 2 = 1 then (if t 3 = 0 then 2704 else if t 3 = 1 then 2685 else 2212) else (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 353)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2707 else 2902) else if t 2 = 1 then (if t 3 = 0 then 2695 else if t 3 = 1 then 2664 else 2674) else (if t 3 = 0 then 2696 else if t 3 = 1 then 2666 else 2675)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2721 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2878 else if t 3 = 1 then 2670 else 2678) else (if t 3 = 0 then 2879 else if t 3 = 1 then 2671 else 2679))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 774 else 1147) else if t 2 = 1 then (if t 3 = 0 then 760 else if t 3 = 1 then 733 else 737) else (if t 3 = 0 then 1774 else if t 3 = 1 then 1484 else 1488)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2717 else 2904) else if t 2 = 1 then (if t 3 = 0 then 2697 else if t 3 = 1 then 2668 else 2676) else (if t 3 = 0 then 2698 else if t 3 = 1 then 2669 else 2677)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2724 else 4045) else if t 2 = 1 then (if t 3 = 0 then 2880 else if t 3 = 1 then 2672 else 2680) else (if t 3 = 0 then 2881 else if t 3 = 1 then 2673 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3726 else (if jt.2.val < 2 then 3728 else 3735)) else (if jt.2.val < 4 then 3727 else (if jt.2.val < 5 then 3734 else 3733))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3185 else (if jt.2.val < 2 then 3187 else 3190)) else (if jt.2.val < 4 then 3186 else (if jt.2.val < 5 then 3189 else 3188)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4077 else (if jt.2.val < 2 then 4091 else 4079)) else (if jt.2.val < 4 then 4089 else (if jt.2.val < 5 then 4090 else 4068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3029 else (if jt.2.val < 2 then 3031 else 3035)) else (if jt.2.val < 4 then 3030 else (if jt.2.val < 5 then 3034 else 3032)))))

checked_coverage fastCoverage0282 pairing0282 template0282 witness0282

theorem coverage0282 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0282) (maskBits m))
    cores template0282 witness0282 := by
  rw [← coresFast_eq]
  exact fastCoverage0282

theorem coverageSize0282 : ∀ q : Pattern,
    (cores (witness0282 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0282 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0282
#print axioms coverageSize0282

noncomputable def pairing0283 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0283 : List (Fin 4935) := templateData0283

noncomputable def witness0283 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2960 else 2654) else if t 2 = 1 then (if t 3 = 0 then 2953 else if t 3 = 1 then 2937 else 2939) else (if t 3 = 0 then 3905 else if t 3 = 1 then 4046 else 4047)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2958 else 2104) else if t 2 = 1 then (if t 3 = 0 then 2951 else if t 3 = 1 then 2931 else 2082) else (if t 3 = 0 then 1075 else if t 3 = 1 then 1046 else 1051)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1756 else 1453) else if t 2 = 1 then (if t 3 = 0 then 1750 else if t 3 = 1 then 1730 else 1733) else (if t 3 = 0 then 669 else if t 3 = 1 then 1049 else 1053))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2959 else 2224) else if t 2 = 1 then (if t 3 = 0 then 2952 else if t 3 = 1 then 2934 else 2206) else (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 974)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2954 else 2650) else if t 2 = 1 then (if t 3 = 0 then 2947 else if t 3 = 1 then 2913 else 2923) else (if t 3 = 0 then 2948 else if t 3 = 1 then 2915 else 2924)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2502 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2554 else if t 3 = 1 then 2919 else 2927) else (if t 3 = 0 then 2555 else if t 3 = 1 then 2920 else 2928))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1213 else 697) else if t 2 = 1 then (if t 3 = 0 then 1204 else if t 3 = 1 then 1180 else 1184) else (if t 3 = 0 then 1431 else if t 3 = 1 then 1796 else 1800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2956 else 2652) else if t 2 = 1 then (if t 3 = 0 then 2949 else if t 3 = 1 then 2917 else 2925) else (if t 3 = 0 then 2950 else if t 3 = 1 then 2918 else 2926)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2504 else 3928) else if t 2 = 1 then (if t 3 = 0 then 2556 else if t 3 = 1 then 2921 else 2929) else (if t 3 = 0 then 2557 else if t 3 = 1 then 2922 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3774 else (if jt.2.val < 2 then 3776 else 3783)) else (if jt.2.val < 4 then 3775 else (if jt.2.val < 5 then 3782 else 3781))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3323 else (if jt.2.val < 2 then 3325 else 3328)) else (if jt.2.val < 4 then 3324 else (if jt.2.val < 5 then 3327 else 3326)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4086 else (if jt.2.val < 2 then 4094 else 4088)) else (if jt.2.val < 4 then 4092 else (if jt.2.val < 5 then 4093 else 4082))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3032 else (if jt.2.val < 2 then 3039 else 3035)) else (if jt.2.val < 4 then 3038 else (if jt.2.val < 5 then 3041 else 3029)))))

checked_coverage fastCoverage0283 pairing0283 template0283 witness0283

theorem coverage0283 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0283) (maskBits m))
    cores template0283 witness0283 := by
  rw [← coresFast_eq]
  exact fastCoverage0283

theorem coverageSize0283 : ∀ q : Pattern,
    (cores (witness0283 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0283 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0283
#print axioms coverageSize0283

noncomputable def pairing0284 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0284 : List (Fin 4935) := templateData0284

noncomputable def witness0284 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 803 else 271) else if t 2 = 1 then (if t 3 = 0 then 809 else if t 3 = 1 then 801 else 269) else (if t 3 = 0 then 1501 else if t 3 = 1 then 400 else 1790)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 807 else if t 3 = 1 then 799 else 855) else if t 2 = 1 then (if t 3 = 0 then 805 else if t 3 = 1 then 797 else 853) else (if t 3 = 0 then 199 else if t 3 = 1 then 862 else 874)) else (if t 2 = 0 then (if t 3 = 0 then 4056 else if t 3 = 1 then 4054 else 3954) else if t 2 = 1 then (if t 3 = 0 then 2996 else if t 3 = 1 then 2993 else 3002) else (if t 3 = 0 then 2781 else if t 3 = 1 then 3003 else 3004))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 802 else 270) else if t 2 = 1 then (if t 3 = 0 then 808 else if t 3 = 1 then 800 else 268) else (if t 3 = 0 then 1500 else if t 3 = 1 then 399 else 1788)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 806 else if t 3 = 1 then 798 else 854) else if t 2 = 1 then (if t 3 = 0 then 804 else if t 3 = 1 then 796 else 852) else (if t 3 = 0 then 198 else if t 3 = 1 then 861 else 870)) else (if t 2 = 0 then (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 857) else if t 2 = 1 then (if t 3 = 0 then 821 else if t 3 = 1 then 816 else 856) else (if t 3 = 0 then 202 else if t 3 = 1 then 865 else 871))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 2145 else 2777) else if t 2 = 1 then (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 278) else (if t 3 = 0 then 3952 else if t 3 = 1 then 405 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1598) else if t 2 = 1 then (if t 3 = 0 then 834 else if t 3 = 1 then 829 else 858) else (if t 3 = 0 then 204 else if t 3 = 1 then 867 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 1818 else if t 3 = 1 then 1817 else 1601) else if t 2 = 1 then (if t 3 = 0 then 840 else if t 3 = 1 then 838 else 860) else (if t 3 = 0 then 206 else if t 3 = 1 then 869 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3774 else (if jt.2.val < 2 then 3791 else 3783)) else (if jt.2.val < 4 then 3789 else (if jt.2.val < 5 then 3790 else 3781))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3997 else (if jt.2.val < 2 then 4055 else 4001)) else (if jt.2.val < 4 then 4052 else (if jt.2.val < 5 then 4053 else 3971)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2388 else (if jt.2.val < 2 then 2390 else 2393)) else (if jt.2.val < 4 then 2389 else (if jt.2.val < 5 then 2392 else 2391))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1225 else (if jt.2.val < 2 then 1234 else 1235)) else (if jt.2.val < 4 then 1226 else (if jt.2.val < 5 then 1228 else 1227)))))

checked_coverage fastCoverage0284 pairing0284 template0284 witness0284

theorem coverage0284 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0284) (maskBits m))
    cores template0284 witness0284 := by
  rw [← coresFast_eq]
  exact fastCoverage0284

theorem coverageSize0284 : ∀ q : Pattern,
    (cores (witness0284 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0284 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0284
#print axioms coverageSize0284

noncomputable def pairing0285 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0285 : List (Fin 4935) := templateData0285

noncomputable def witness0285 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 16 else 918) else if t 2 = 1 then (if t 3 = 0 then 22 else if t 3 = 1 then 14 else 916) else (if t 3 = 0 then 1807 else if t 3 = 1 then 100 else 1478)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 20 else if t 3 = 1 then 12 else 62) else if t 2 = 1 then (if t 3 = 0 then 18 else if t 3 = 1 then 10 else 60) else (if t 3 = 0 then 898 else if t 3 = 1 then 86 else 88)) else (if t 2 = 0 then (if t 3 = 0 then 3941 else if t 3 = 1 then 3939 else 4060) else if t 2 = 1 then (if t 3 = 0 then 2788 else if t 3 = 1 then 2785 else 2794) else (if t 3 = 0 then 2989 else if t 3 = 1 then 2797 else 2798))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 15 else 917) else if t 2 = 1 then (if t 3 = 0 then 21 else if t 3 = 1 then 13 else 915) else (if t 3 = 0 then 1806 else if t 3 = 1 then 96 else 1476)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 19 else if t 3 = 1 then 11 else 61) else if t 2 = 1 then (if t 3 = 0 then 17 else if t 3 = 1 then 9 else 59) else (if t 3 = 0 then 897 else if t 3 = 1 then 78 else 82)) else (if t 2 = 0 then (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 69) else if t 2 = 1 then (if t 3 = 0 then 34 else if t 3 = 1 then 29 else 68) else (if t 3 = 0 then 901 else if t 3 = 1 then 79 else 83))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 2124 else 2988) else if t 2 = 1 then (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 921) else (if t 3 = 0 then 4059 else if t 3 = 1 then 98 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1848) else if t 2 = 1 then (if t 3 = 0 then 47 else if t 3 = 1 then 42 else 72) else (if t 3 = 0 then 903 else if t 3 = 1 then 80 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 1512 else if t 3 = 1 then 1511 else 1850) else if t 2 = 1 then (if t 3 = 0 then 53 else if t 3 = 1 then 51 else 76) else (if t 3 = 0 then 905 else if t 3 = 1 then 81 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3726 else (if jt.2.val < 2 then 3743 else 3735)) else (if jt.2.val < 4 then 3741 else (if jt.2.val < 5 then 3742 else 3733))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3831 else (if jt.2.val < 2 then 3940 else 3835)) else (if jt.2.val < 4 then 3937 else (if jt.2.val < 5 then 3938 else 3805)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2394 else (if jt.2.val < 2 then 2396 else 2399)) else (if jt.2.val < 4 then 2395 else (if jt.2.val < 5 then 2398 else 2397))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1227 else (if jt.2.val < 2 then 1244 else 1235)) else (if jt.2.val < 4 then 1236 else (if jt.2.val < 5 then 1237 else 1225)))))

checked_coverage fastCoverage0285 pairing0285 template0285 witness0285

theorem coverage0285 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0285) (maskBits m))
    cores template0285 witness0285 := by
  rw [← coresFast_eq]
  exact fastCoverage0285

theorem coverageSize0285 : ∀ q : Pattern,
    (cores (witness0285 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0285 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0285
#print axioms coverageSize0285

noncomputable def pairing0286 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0286 : List (Fin 4935) := templateData0286

noncomputable def witness0286 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1680 else 1856) else if t 2 = 1 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1660 else 1661) else (if t 3 = 0 then 896 else if t 3 = 1 then 357 else 359)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1678 else 1853) else if t 2 = 1 then (if t 3 = 0 then 1669 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 157 else if t 3 = 1 then 1646 else 1650)) else (if t 2 = 0 then (if t 3 = 0 then 2577 else if t 3 = 1 then 2860 else 2868) else if t 2 = 1 then (if t 3 = 0 then 2545 else if t 3 = 1 then 3232 else 3235) else (if t 3 = 0 then 4058 else if t 3 = 1 then 3963 else 3965))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1679 else 1854) else if t 2 = 1 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1656 else 1658) else (if t 3 = 0 then 894 else if t 3 = 1 then 350 else 354)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1677 else 1851) else if t 2 = 1 then (if t 3 = 0 then 1665 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 150 else if t 3 = 1 then 1630 else 1638)) else (if t 2 = 0 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1685 else 1852) else if t 2 = 1 then (if t 3 = 0 then 1666 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 151 else if t 3 = 1 then 1631 else 1639))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 785 else 4061) else if t 2 = 1 then (if t 3 = 0 then 1110 else if t 3 = 1 then 734 else 738) else (if t 3 = 0 then 2984 else if t 3 = 1 then 2157 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 596 else if t 3 = 1 then 1079 else 1092) else if t 2 = 1 then (if t 3 = 0 then 546 else if t 3 = 1 then 1632 else 1640) else (if t 3 = 0 then 1833 else if t 3 = 1 then 1634 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 599 else if t 3 = 1 then 1082 else 1093) else if t 2 = 1 then (if t 3 = 0 then 547 else if t 3 = 1 then 1633 else 1641) else (if t 3 = 0 then 1834 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3806 else (if jt.2.val < 2 then 3962 else 3828)) else (if jt.2.val < 4 then 3961 else (if jt.2.val < 5 then 3964 else 3824))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3188 else (if jt.2.val < 2 then 3238 else 3190)) else (if jt.2.val < 4 then 3237 else (if jt.2.val < 5 then 3239 else 3185)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2391 else (if jt.2.val < 2 then 2408 else 2393)) else (if jt.2.val < 4 then 2406 else (if jt.2.val < 5 then 2407 else 2388))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1956 else (if jt.2.val < 2 then 1958 else 1963)) else (if jt.2.val < 4 then 1957 else (if jt.2.val < 5 then 1962 else 1961)))))

checked_coverage fastCoverage0286 pairing0286 template0286 witness0286

theorem coverage0286 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0286) (maskBits m))
    cores template0286 witness0286 := by
  rw [← coresFast_eq]
  exact fastCoverage0286

theorem coverageSize0286 : ∀ q : Pattern,
    (cores (witness0286 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0286 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0286
#print axioms coverageSize0286

noncomputable def pairing0287 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0287 : List (Fin 4935) := templateData0287

noncomputable def witness0287 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1910 else 1622) else if t 2 = 1 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1891 else 1892) else (if t 3 = 0 then 179 else if t 3 = 1 then 978 else 980)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1907 else 1619) else if t 2 = 1 then (if t 3 = 0 then 1901 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 158 else if t 3 = 1 then 1877 else 1881)) else (if t 2 = 0 then (if t 3 = 0 then 2884 else if t 3 = 1 then 2500 else 2501) else if t 2 = 1 then (if t 3 = 0 then 2546 else if t 3 = 1 then 3348 else 3351) else (if t 3 = 0 then 3946 else if t 3 = 1 then 4064 else 4066))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1908 else 1620) else if t 2 = 1 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1887 else 1889) else (if t 3 = 0 then 176 else if t 3 = 1 then 971 else 975)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1905 else 1617) else if t 2 = 1 then (if t 3 = 0 then 1899 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 152 else if t 3 = 1 then 1861 else 1869)) else (if t 2 = 0 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1906 else 1618) else if t 2 = 1 then (if t 3 = 0 then 1900 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 153 else if t 3 = 1 then 1862 else 1870))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 504 else 3960) else if t 2 = 1 then (if t 3 = 0 then 572 else if t 3 = 1 then 1181 else 1185) else (if t 3 = 0 then 2758 else if t 3 = 1 then 2136 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1115 else if t 3 = 1 then 492 else 494) else if t 2 = 1 then (if t 3 = 0 then 548 else if t 3 = 1 then 1863 else 1871) else (if t 3 = 0 then 1535 else if t 3 = 1 then 1865 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 1118 else if t 3 = 1 then 493 else 495) else if t 2 = 1 then (if t 3 = 0 then 549 else if t 3 = 1 then 1864 else 1872) else (if t 3 = 0 then 1536 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3972 else (if jt.2.val < 2 then 4063 else 3994)) else (if jt.2.val < 4 then 4062 else (if jt.2.val < 5 then 4065 else 3990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3326 else (if jt.2.val < 2 then 3354 else 3328)) else (if jt.2.val < 4 then 3353 else (if jt.2.val < 5 then 3355 else 3323)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2397 else (if jt.2.val < 2 then 2411 else 2399)) else (if jt.2.val < 4 then 2409 else (if jt.2.val < 5 then 2410 else 2394))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1961 else (if jt.2.val < 2 then 1966 else 1963)) else (if jt.2.val < 4 then 1965 else (if jt.2.val < 5 then 1969 else 1956)))))

checked_coverage fastCoverage0287 pairing0287 template0287 witness0287

theorem coverage0287 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0287) (maskBits m))
    cores template0287 witness0287 := by
  rw [← coresFast_eq]
  exact fastCoverage0287

theorem coverageSize0287 : ∀ q : Pattern,
    (cores (witness0287 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0287 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0287
#print axioms coverageSize0287

noncomputable def pairing0288 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0288 : List (Fin 4935) := templateData0288

noncomputable def witness0288 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 3860) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2980) else (if t 3 = 0 then 2789 else if t 3 = 1 then 2787 else 2800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 1084) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 1078) else (if t 3 = 0 then 727 else if t 3 = 1 then 723 else 784)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 536 else 601) else if t 2 = 1 then (if t 3 = 0 then 539 else if t 3 = 1 then 535 else 595) else (if t 3 = 0 then 1544 else if t 3 = 1 then 1108 else 1549))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 1003) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 997) else (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 97)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2955) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3852) else (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3854)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2651) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3856) else (if t 3 = 0 then 3849 else if t 3 = 1 then 3848 else 3858))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 1375) else if t 2 = 1 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 999) else (if t 3 = 0 then 54 else if t 3 = 1 then 52 else 99)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2957) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3853) else (if t 3 = 0 then 3838 else if t 3 = 1 then 3837 else 3855)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2626 else 2653) else if t 2 = 1 then (if t 3 = 0 then 3847 else if t 3 = 1 then 3846 else 3857) else (if t 3 = 0 then 3851 else if t 3 = 1 then 3850 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3806 else (if jt.2.val < 2 then 3826 else 3828)) else (if jt.2.val < 4 then 3823 else (if jt.2.val < 5 then 3825 else 3824))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4095 else (if jt.2.val < 2 then 4105 else 4106)) else (if jt.2.val < 4 then 4102 else (if jt.2.val < 5 then 4104 else 4103)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4096 else (if jt.2.val < 2 then 4100 else 4101)) else (if jt.2.val < 4 then 4097 else (if jt.2.val < 5 then 4099 else 4098))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3798 else (if jt.2.val < 2 then 3800 else 3803)) else (if jt.2.val < 4 then 3799 else (if jt.2.val < 5 then 3802 else 3801)))))

checked_coverage fastCoverage0288 pairing0288 template0288 witness0288

theorem coverage0288 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0288) (maskBits m))
    cores template0288 witness0288 := by
  rw [← coresFast_eq]
  exact fastCoverage0288

theorem coverageSize0288 : ∀ q : Pattern,
    (cores (witness0288 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0288 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0288
#print axioms coverageSize0288

noncomputable def pairing0289 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0289 : List (Fin 4935) := templateData0289

noncomputable def witness0289 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 3905) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2979) else (if t 3 = 0 then 2779 else if t 3 = 1 then 2775 else 2776)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 1075) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 1069) else (if t 3 = 0 then 682 else if t 3 = 1 then 654 else 659)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 475 else 477) else if t 2 = 1 then (if t 3 = 0 then 490 else if t 3 = 1 then 462 else 467) else (if t 3 = 0 then 1526 else if t 3 = 1 then 1132 else 1519))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 994) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 988) else (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 167)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2948) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3884) else (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3886)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2700) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3888) else (if t 3 = 0 then 3919 else if t 3 = 1 then 3882 else 3890))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 1431) else if t 2 = 1 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 990) else (if t 3 = 0 then 197 else if t 3 = 1 then 163 else 169)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2950) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3885) else (if t 3 = 0 then 3916 else if t 3 = 1 then 3878 else 3887)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2698 else 2702) else if t 2 = 1 then (if t 3 = 0 then 3918 else if t 3 = 1 then 3881 else 3889) else (if t 3 = 0 then 3920 else if t 3 = 1 then 3883 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3870 else (if jt.2.val < 2 then 3872 else 3894)) else (if jt.2.val < 4 then 3871 else (if jt.2.val < 5 then 3893 else 3874))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4107 else (if jt.2.val < 2 then 4109 else 4116)) else (if jt.2.val < 4 then 4108 else (if jt.2.val < 5 then 4115 else 4114)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4110 else (if jt.2.val < 2 then 4112 else 4118)) else (if jt.2.val < 4 then 4111 else (if jt.2.val < 5 then 4117 else 4113))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3801 else (if jt.2.val < 2 then 3863 else 3803)) else (if jt.2.val < 4 then 3861 else (if jt.2.val < 5 then 3862 else 3798)))))

checked_coverage fastCoverage0289 pairing0289 template0289 witness0289

theorem coverage0289 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0289) (maskBits m))
    cores template0289 witness0289 := by
  rw [← coresFast_eq]
  exact fastCoverage0289

theorem coverageSize0289 : ∀ q : Pattern,
    (cores (witness0289 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0289 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0289
#print axioms coverageSize0289

noncomputable def pairing0290 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0290 : List (Fin 4935) := templateData0290

noncomputable def witness0290 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2446 else 2506) else if t 2 = 1 then (if t 3 = 0 then 2450 else if t 3 = 1 then 2442 else 2500) else (if t 3 = 0 then 3941 else if t 3 = 1 then 3939 else 3943)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2444 else 1756) else if t 2 = 1 then (if t 3 = 0 then 2448 else if t 3 = 1 then 2440 else 1753) else (if t 3 = 0 then 726 else if t 3 = 1 then 722 else 778)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1413 else 1453) else if t 2 = 1 then (if t 3 = 0 then 1416 else if t 3 = 1 then 1412 else 1450) else (if t 3 = 0 then 758 else if t 3 = 1 then 756 else 780))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2445 else 1909) else if t 2 = 1 then (if t 3 = 0 then 2449 else if t 3 = 1 then 2441 else 1906) else (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 91)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2443 else 2502) else if t 2 = 1 then (if t 3 = 0 then 2447 else if t 3 = 1 then 2439 else 2492) else (if t 3 = 0 then 2462 else if t 3 = 1 then 2459 else 2493)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2897 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2484 else if t 3 = 1 then 2481 else 2496) else (if t 3 = 0 then 2487 else if t 3 = 1 then 2486 else 2497))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 439 else 505) else if t 2 = 1 then (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 493) else (if t 3 = 0 then 1512 else if t 3 = 1 then 1511 else 1522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2504) else if t 2 = 1 then (if t 3 = 0 then 2471 else if t 3 = 1 then 2468 else 2494) else (if t 3 = 0 then 2475 else if t 3 = 1 then 2473 else 2495)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2900 else 3928) else if t 2 = 1 then (if t 3 = 0 then 2489 else if t 3 = 1 then 2488 else 2498) else (if t 3 = 0 then 2491 else if t 3 = 1 then 2490 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3690 else (if jt.2.val < 2 then 3700 else 3701)) else (if jt.2.val < 4 then 3697 else (if jt.2.val < 5 then 3699 else 3698))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3410 else (if jt.2.val < 2 then 3415 else 3416)) else (if jt.2.val < 4 then 3412 else (if jt.2.val < 5 then 3414 else 3413)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4098 else (if jt.2.val < 2 then 4121 else 4101)) else (if jt.2.val < 4 then 4119 else (if jt.2.val < 5 then 4120 else 4096))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2430 else (if jt.2.val < 2 then 2432 else 2435)) else (if jt.2.val < 4 then 2431 else (if jt.2.val < 5 then 2434 else 2433)))))

checked_coverage fastCoverage0290 pairing0290 template0290 witness0290

theorem coverage0290 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0290) (maskBits m))
    cores template0290 witness0290 := by
  rw [← coresFast_eq]
  exact fastCoverage0290

theorem coverageSize0290 : ∀ q : Pattern,
    (cores (witness0290 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0290 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0290
#print axioms coverageSize0290

noncomputable def pairing0291 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0291 : List (Fin 4935) := templateData0291

noncomputable def witness0291 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2560 else 2561) else if t 2 = 1 then (if t 3 = 0 then 2565 else if t 3 = 1 then 2544 else 2546) else (if t 3 = 0 then 3951 else if t 3 = 1 then 3945 else 3946)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2558 else 1750) else if t 2 = 1 then (if t 3 = 0 then 2563 else if t 3 = 1 then 2538 else 1747) else (if t 3 = 0 then 681 else if t 3 = 1 then 641 else 646)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1357 else 1359) else if t 2 = 1 then (if t 3 = 0 then 1372 else if t 3 = 1 then 1350 else 1353) else (if t 3 = 0 then 695 else if t 3 = 1 then 644 else 648))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2559 else 1903) else if t 2 = 1 then (if t 3 = 0 then 2564 else if t 3 = 1 then 2541 else 1900) else (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 153)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2548 else 2554) else if t 2 = 1 then (if t 3 = 0 then 2562 else if t 3 = 1 then 2519 else 2530) else (if t 3 = 0 then 2570 else if t 3 = 1 then 2521 else 2531)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2878 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2576 else if t 3 = 1 then 2526 else 2534) else (if t 3 = 0 then 2578 else if t 3 = 1 then 2527 else 2535))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 571 else 573) else if t 2 = 1 then (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 549) else (if t 3 = 0 then 1547 else if t 3 = 1 then 1532 else 1536)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2556) else if t 2 = 1 then (if t 3 = 0 then 2572 else if t 3 = 1 then 2523 else 2532) else (if t 3 = 0 then 2574 else if t 3 = 1 then 2524 else 2533)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2880 else 3934) else if t 2 = 1 then (if t 3 = 0 then 2579 else if t 3 = 1 then 2528 else 2536) else (if t 3 = 0 then 2580 else if t 3 = 1 then 2529 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3702 else (if jt.2.val < 2 then 3704 else 3711)) else (if jt.2.val < 4 then 3703 else (if jt.2.val < 5 then 3710 else 3709))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3417 else (if jt.2.val < 2 then 3419 else 3422)) else (if jt.2.val < 4 then 3418 else (if jt.2.val < 5 then 3421 else 3420)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4113 else (if jt.2.val < 2 then 4123 else 4118)) else (if jt.2.val < 4 then 4122 else (if jt.2.val < 5 then 4124 else 4110))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2433 else (if jt.2.val < 2 then 2509 else 2435)) else (if jt.2.val < 4 then 2507 else (if jt.2.val < 5 then 2508 else 2430)))))

checked_coverage fastCoverage0291 pairing0291 template0291 witness0291

theorem coverage0291 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0291) (maskBits m))
    cores template0291 witness0291 := by
  rw [← coresFast_eq]
  exact fastCoverage0291

theorem coverageSize0291 : ∀ q : Pattern,
    (cores (witness0291 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0291 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0291
#print axioms coverageSize0291

noncomputable def pairing0292 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0292 : List (Fin 4935) := templateData0292

noncomputable def witness0292 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 224 else 308) else if t 2 = 1 then (if t 3 = 0 then 230 else if t 3 = 1 then 222 else 304) else (if t 3 = 0 then 1471 else if t 3 = 1 then 916 else 1478)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 228 else if t 3 = 1 then 220 else 298) else if t 2 = 1 then (if t 3 = 0 then 226 else if t 3 = 1 then 218 else 290) else (if t 3 = 0 then 269 else if t 3 = 1 then 264 else 292)) else (if t 2 = 0 then (if t 3 = 0 then 3925 else if t 3 = 1 then 3923 else 3927) else if t 2 = 1 then (if t 3 = 0 then 2750 else if t 3 = 1 then 2747 else 2759) else (if t 3 = 0 then 2757 else if t 3 = 1 then 2756 else 2760))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 223 else 306) else if t 2 = 1 then (if t 3 = 0 then 229 else if t 3 = 1 then 221 else 300) else (if t 3 = 0 then 1470 else if t 3 = 1 then 915 else 1476)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 227 else if t 3 = 1 then 219 else 294) else if t 2 = 1 then (if t 3 = 0 then 225 else if t 3 = 1 then 217 else 282) else (if t 3 = 0 then 268 else if t 3 = 1 then 263 else 286)) else (if t 2 = 0 then (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 295) else if t 2 = 1 then (if t 3 = 0 then 242 else if t 3 = 1 then 237 else 283) else (if t 3 = 0 then 274 else if t 3 = 1 then 272 else 287))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1785 else 2782) else if t 2 = 1 then (if t 3 = 0 then 257 else if t 3 = 1 then 253 else 302) else (if t 3 = 0 then 3942 else if t 3 = 1 then 921 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1461 else if t 3 = 1 then 1458 else 1473) else if t 2 = 1 then (if t 3 = 0 then 255 else if t 3 = 1 then 250 else 284) else (if t 3 = 0 then 278 else if t 3 = 1 then 276 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 1464 else if t 3 = 1 then 1463 else 1474) else if t 2 = 1 then (if t 3 = 0 then 261 else if t 3 = 1 then 259 else 285) else (if t 3 = 0 then 281 else if t 3 = 1 then 280 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3702 else (if jt.2.val < 2 then 3755 else 3711)) else (if jt.2.val < 4 then 3753 else (if jt.2.val < 5 then 3754 else 3709))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4103 else (if jt.2.val < 2 then 4127 else 4106)) else (if jt.2.val < 4 then 4125 else (if jt.2.val < 5 then 4126 else 4095)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1457 else (if jt.2.val < 2 then 1468 else 1469)) else (if jt.2.val < 4 then 1465 else (if jt.2.val < 5 then 1467 else 1466))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 207 else (if jt.2.val < 2 then 209 else 212)) else (if jt.2.val < 4 then 208 else (if jt.2.val < 5 then 211 else 210)))))

checked_coverage fastCoverage0292 pairing0292 template0292 witness0292

theorem coverage0292 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0292) (maskBits m))
    cores template0292 witness0292 := by
  rw [← coresFast_eq]
  exact fastCoverage0292

theorem coverageSize0292 : ∀ q : Pattern,
    (cores (witness0292 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0292 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0292
#print axioms coverageSize0292

noncomputable def pairing0293 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0293 : List (Fin 4935) := templateData0293

noncomputable def witness0293 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 379 else 380) else if t 2 = 1 then (if t 3 = 0 then 386 else if t 3 = 1 then 371 else 373) else (if t 3 = 0 then 1501 else if t 3 = 1 then 892 else 1496)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 384 else if t 3 = 1 then 356 else 358) else if t 2 = 1 then (if t 3 = 0 then 382 else if t 3 = 1 then 336 else 342) else (if t 3 = 0 then 400 else if t 3 = 1 then 340 else 344)) else (if t 2 = 0 then (if t 3 = 0 then 3935 else if t 3 = 1 then 3929 else 3930) else if t 2 = 1 then (if t 3 = 0 then 2740 else if t 3 = 1 then 2728 else 2731) else (if t 3 = 0 then 2743 else if t 3 = 1 then 2730 else 2732))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 375 else 377) else if t 2 = 1 then (if t 3 = 0 then 385 else if t 3 = 1 then 363 else 367) else (if t 3 = 0 then 1500 else if t 3 = 1 then 888 else 1494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 383 else if t 3 = 1 then 346 else 352) else if t 2 = 1 then (if t 3 = 0 then 381 else if t 3 = 1 then 318 else 328) else (if t 3 = 0 then 399 else if t 3 = 1 then 324 else 332)) else (if t 2 = 0 then (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 353) else if t 2 = 1 then (if t 3 = 0 then 389 else if t 3 = 1 then 320 else 329) else (if t 3 = 0 then 403 else if t 3 = 1 then 325 else 333))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1773 else 2796) else if t 2 = 1 then (if t 3 = 0 then 395 else if t 3 = 1 then 365 else 369) else (if t 3 = 0 then 3952 else if t 3 = 1 then 890 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1497 else if t 3 = 1 then 1483 else 1487) else if t 2 = 1 then (if t 3 = 0 then 393 else if t 3 = 1 then 322 else 330) else (if t 3 = 0 then 405 else if t 3 = 1 then 326 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 1499 else if t 3 = 1 then 1484 else 1488) else if t 2 = 1 then (if t 3 = 0 then 397 else if t 3 = 1 then 323 else 331) else (if t 3 = 0 then 407 else if t 3 = 1 then 327 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3690 else (if jt.2.val < 2 then 3757 else 3701)) else (if jt.2.val < 4 then 3756 else (if jt.2.val < 5 then 3758 else 3698))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4114 else (if jt.2.val < 2 then 4129 else 4116)) else (if jt.2.val < 4 then 4128 else (if jt.2.val < 5 then 4130 else 4107)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1479 else (if jt.2.val < 2 then 1481 else 1486)) else (if jt.2.val < 4 then 1480 else (if jt.2.val < 5 then 1485 else 1482))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 210 else (if jt.2.val < 2 then 311 else 212)) else (if jt.2.val < 4 then 309 else (if jt.2.val < 5 then 310 else 207)))))

checked_coverage fastCoverage0293 pairing0293 template0293 witness0293

theorem coverage0293 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0293) (maskBits m))
    cores template0293 witness0293 := by
  rw [← coresFast_eq]
  exact fastCoverage0293

theorem coverageSize0293 : ∀ q : Pattern,
    (cores (witness0293 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0293 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0293
#print axioms coverageSize0293

noncomputable def pairing0294 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0294 : List (Fin 4935) := templateData0294

noncomputable def witness0294 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1568 else 1622) else if t 2 = 1 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1566 else 1619) else (if t 3 = 0 then 67 else if t 3 = 1 then 62 else 95)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1564 else 1616) else if t 2 = 1 then (if t 3 = 0 then 1570 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 855 else if t 3 = 1 then 1589 else 1611)) else (if t 2 = 0 then (if t 3 = 0 then 2633 else if t 3 = 1 then 2630 else 2649) else if t 2 = 1 then (if t 3 = 0 then 2855 else if t 3 = 1 then 3219 else 3227) else (if t 3 = 0 then 3954 else if t 3 = 1 then 3953 else 3959))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1567 else 1620) else if t 2 = 1 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1565 else 1617) else (if t 3 = 0 then 66 else if t 3 = 1 then 61 else 92)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1563 else 1614) else if t 2 = 1 then (if t 3 = 0 then 1569 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 854 else if t 3 = 1 then 1588 else 1604)) else (if t 2 = 0 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1581 else 1615) else if t 2 = 1 then (if t 3 = 0 then 1584 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 857 else if t 3 = 1 then 1591 else 1605))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 1133 else 3960) else if t 2 = 1 then (if t 3 = 0 then 468 else if t 3 = 1 then 463 else 494) else (if t 3 = 0 then 2739 else if t 3 = 1 then 1848 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 660 else if t 3 = 1 then 655 else 686) else if t 2 = 1 then (if t 3 = 0 then 1070 else if t 3 = 1 then 1592 else 1606) else (if t 3 = 0 then 1598 else if t 3 = 1 then 1596 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 665 else if t 3 = 1 then 663 else 687) else if t 2 = 1 then (if t 3 = 0 then 1073 else if t 3 = 1 then 1595 else 1607) else (if t 3 = 0 then 1601 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3870 else (if jt.2.val < 2 then 3957 else 3894)) else (if jt.2.val < 4 then 3955 else (if jt.2.val < 5 then 3956 else 3874))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3413 else (if jt.2.val < 2 then 3434 else 3416)) else (if jt.2.val < 4 then 3432 else (if jt.2.val < 5 then 3433 else 3410)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1466 else (if jt.2.val < 2 then 1590 else 1469)) else (if jt.2.val < 4 then 1559 else (if jt.2.val < 5 then 1560 else 1457))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1551 else (if jt.2.val < 2 then 1553 else 1556)) else (if jt.2.val < 4 then 1552 else (if jt.2.val < 5 then 1555 else 1554)))))

checked_coverage fastCoverage0294 pairing0294 template0294 witness0294

theorem coverage0294 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0294) (maskBits m))
    cores template0294 witness0294 := by
  rw [← coresFast_eq]
  exact fastCoverage0294

theorem coverageSize0294 : ∀ q : Pattern,
    (cores (witness0294 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0294 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0294
#print axioms coverageSize0294

noncomputable def pairing0295 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0295 : List (Fin 4935) := templateData0295

noncomputable def witness0295 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1675 else 1676) else if t 2 = 1 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1669 else 1670) else (if t 3 = 0 then 201 else if t 3 = 1 then 157 else 159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1660 else 1661) else if t 2 = 1 then (if t 3 = 0 then 1678 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 864 else if t 3 = 1 then 1646 else 1650)) else (if t 2 = 0 then (if t 3 = 0 then 2722 else if t 3 = 1 then 2689 else 2691) else if t 2 = 1 then (if t 3 = 0 then 2860 else if t 3 = 1 then 3232 else 3235) else (if t 3 = 0 then 3967 else if t 3 = 1 then 3963 else 3965))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1671 else 1673) else if t 2 = 1 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1665 else 1667) else (if t 3 = 0 then 200 else if t 3 = 1 then 150 else 154)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1656 else 1658) else if t 2 = 1 then (if t 3 = 0 then 1677 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 863 else if t 3 = 1 then 1630 else 1638)) else (if t 2 = 0 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1657 else 1659) else if t 2 = 1 then (if t 3 = 0 then 1685 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 866 else if t 3 = 1 then 1631 else 1639))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 1110 else 3966) else if t 2 = 1 then (if t 3 = 0 then 596 else if t 3 = 1 then 546 else 550) else (if t 3 = 0 then 2763 else if t 3 = 1 then 1833 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 785 else if t 3 = 1 then 734 else 738) else if t 2 = 1 then (if t 3 = 0 then 1079 else if t 3 = 1 then 1632 else 1640) else (if t 3 = 0 then 1689 else if t 3 = 1 then 1634 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 788 else if t 3 = 1 then 735 else 739) else if t 2 = 1 then (if t 3 = 0 then 1082 else if t 3 = 1 then 1633 else 1641) else (if t 3 = 0 then 1691 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3806 else (if jt.2.val < 2 then 3962 else 3828)) else (if jt.2.val < 4 then 3961 else (if jt.2.val < 5 then 3964 else 3824))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3420 else (if jt.2.val < 2 then 3436 else 3422)) else (if jt.2.val < 4 then 3435 else (if jt.2.val < 5 then 3437 else 3417)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1482 else (if jt.2.val < 2 then 1654 else 1486)) else (if jt.2.val < 4 then 1653 else (if jt.2.val < 5 then 1655 else 1479))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1554 else (if jt.2.val < 2 then 1625 else 1556)) else (if jt.2.val < 4 then 1623 else (if jt.2.val < 5 then 1624 else 1551)))))

checked_coverage fastCoverage0295 pairing0295 template0295 witness0295

theorem coverage0295 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0295) (maskBits m))
    cores template0295 witness0295 := by
  rw [← coresFast_eq]
  exact fastCoverage0295

theorem coverageSize0295 : ∀ q : Pattern,
    (cores (witness0295 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0295 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0295
#print axioms coverageSize0295

noncomputable def pairing0296 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0296 : List (Fin 4935) := templateData0296

noncomputable def witness0296 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 3951) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2778) else (if t 3 = 0 then 2789 else if t 3 = 1 then 2788 else 2989)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 681) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 680) else (if t 3 = 0 then 727 else if t 3 = 1 then 725 else 1144)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1173 else 695) else if t 2 = 1 then (if t 3 = 0 then 1174 else if t 3 = 1 then 1172 else 694) else (if t 3 = 0 then 1544 else if t 3 = 1 then 757 else 2161))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 189) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 188) else (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 901)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2570) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4179) else (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4183)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2578) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4181) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4177 else 4185))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1547) else if t 2 = 1 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 196) else (if t 3 = 0 then 54 else if t 3 = 1 then 53 else 905)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2574) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4180) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4171 else 4184)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2842 else 2580) else if t 2 = 1 then (if t 3 = 0 then 4004 else if t 3 = 1 then 4164 else 4182) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4178 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4134 else (if jt.2.val < 2 then 4154 else 4156)) else (if jt.2.val < 4 then 4151 else (if jt.2.val < 5 then 4153 else 4152))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4133 else (if jt.2.val < 2 then 4161 else 4162)) else (if jt.2.val < 4 then 4158 else (if jt.2.val < 5 then 4160 else 4159)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4132 else (if jt.2.val < 2 then 4168 else 4169)) else (if jt.2.val < 4 then 4165 else (if jt.2.val < 5 then 4167 else 4166))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4131 else (if jt.2.val < 2 then 4173 else 4176)) else (if jt.2.val < 4 then 4172 else (if jt.2.val < 5 then 4175 else 4174)))))

checked_coverage fastCoverage0296 pairing0296 template0296 witness0296

theorem coverage0296 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0296) (maskBits m))
    cores template0296 witness0296 := by
  rw [← coresFast_eq]
  exact fastCoverage0296

theorem coverageSize0296 : ∀ q : Pattern,
    (cores (witness0296 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0296 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0296
#print axioms coverageSize0296

noncomputable def pairing0297 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0297 : List (Fin 4935) := templateData0297

noncomputable def witness0297 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4190) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2775) else (if t 3 = 0 then 2981 else if t 3 = 1 then 2979 else 2776)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 667) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 654) else (if t 3 = 0 then 1090 else if t 3 = 1 then 1069 else 659)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 475 else 1138) else if t 2 = 1 then (if t 3 = 0 then 490 else if t 3 = 1 then 462 else 1132) else (if t 3 = 0 then 2150 else if t 3 = 1 then 467 else 1519))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 175) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 161) else (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 167)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2549) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3877) else (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3886)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2879) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3882) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3888 else 3890))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 2116) else if t 2 = 1 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 163) else (if t 3 = 0 then 1013 else if t 3 = 1 then 990 else 169)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2551) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3878) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3885 else 3887)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2698 else 2881) else if t 2 = 1 then (if t 3 = 0 then 3918 else if t 3 = 1 then 3881 else 3883) else (if t 3 = 0 then 4192 else if t 3 = 1 then 3889 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3870 else (if jt.2.val < 2 then 3872 else 3894)) else (if jt.2.val < 4 then 3871 else (if jt.2.val < 5 then 3893 else 3874))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4107 else (if jt.2.val < 2 then 4109 else 4116)) else (if jt.2.val < 4 then 4108 else (if jt.2.val < 5 then 4115 else 4114)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4029 else (if jt.2.val < 2 then 4031 else 4035)) else (if jt.2.val < 4 then 4030 else (if jt.2.val < 5 then 4034 else 4033))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4174 else (if jt.2.val < 2 then 4189 else 4176)) else (if jt.2.val < 4 then 4187 else (if jt.2.val < 5 then 4188 else 4131)))))

checked_coverage fastCoverage0297 pairing0297 template0297 witness0297

theorem coverage0297 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0297) (maskBits m))
    cores template0297 witness0297 := by
  rw [← coresFast_eq]
  exact fastCoverage0297

theorem coverageSize0297 : ∀ q : Pattern,
    (cores (witness0297 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0297 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0297
#print axioms coverageSize0297

noncomputable def pairing0298 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0298 : List (Fin 4935) := templateData0298

noncomputable def witness0298 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2450 else 2884) else if t 2 = 1 then (if t 3 = 0 then 2446 else if t 3 = 1 then 2442 else 2500) else (if t 3 = 0 then 4196 else if t 3 = 1 then 3939 else 3943)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2448 else 1762) else if t 2 = 1 then (if t 3 = 0 then 2444 else if t 3 = 1 then 2440 else 1753) else (if t 3 = 0 then 724 else if t 3 = 1 then 722 else 778)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1416 else 2119) else if t 2 = 1 then (if t 3 = 0 then 1413 else if t 3 = 1 then 1412 else 1450) else (if t 3 = 0 then 1109 else if t 3 = 1 then 756 else 780))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2449 else 1915) else if t 2 = 1 then (if t 3 = 0 then 2445 else if t 3 = 1 then 2441 else 1906) else (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 91)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2447 else 2883) else if t 2 = 1 then (if t 3 = 0 then 2443 else if t 3 = 1 then 2439 else 2492) else (if t 3 = 0 then 2461 else if t 3 = 1 then 2459 else 2493)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2484 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2897 else if t 3 = 1 then 2481 else 2496) else (if t 3 = 0 then 2899 else if t 3 = 1 then 2486 else 2497))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 441 else 1118) else if t 2 = 1 then (if t 3 = 0 then 439 else if t 3 = 1 then 437 else 493) else (if t 3 = 0 then 2126 else if t 3 = 1 then 1511 else 1522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2471 else 2886) else if t 2 = 1 then (if t 3 = 0 then 2470 else if t 3 = 1 then 2468 else 2494) else (if t 3 = 0 then 2474 else if t 3 = 1 then 2473 else 2495)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2489 else 4197) else if t 2 = 1 then (if t 3 = 0 then 2900 else if t 3 = 1 then 2488 else 2498) else (if t 3 = 0 then 2901 else if t 3 = 1 then 2490 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3690 else (if jt.2.val < 2 then 3700 else 3701)) else (if jt.2.val < 4 then 3697 else (if jt.2.val < 5 then 3699 else 3698))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3410 else (if jt.2.val < 2 then 3415 else 3416)) else (if jt.2.val < 4 then 3412 else (if jt.2.val < 5 then 3414 else 3413)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4166 else (if jt.2.val < 2 then 4195 else 4169)) else (if jt.2.val < 4 then 4193 else (if jt.2.val < 5 then 4194 else 4132))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3020 else (if jt.2.val < 2 then 3022 else 3025)) else (if jt.2.val < 4 then 3021 else (if jt.2.val < 5 then 3024 else 3023)))))

checked_coverage fastCoverage0298 pairing0298 template0298 witness0298

theorem coverage0298 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0298) (maskBits m))
    cores template0298 witness0298 := by
  rw [← coresFast_eq]
  exact fastCoverage0298

theorem coverageSize0298 : ∀ q : Pattern,
    (cores (witness0298 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0298 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0298
#print axioms coverageSize0298

noncomputable def pairing0299 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0299 : List (Fin 4935) := templateData0299

noncomputable def witness0299 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2953 else 2561) else if t 2 = 1 then (if t 3 = 0 then 2960 else if t 3 = 1 then 2937 else 2938) else (if t 3 = 0 then 3860 else if t 3 = 1 then 4046 else 4198)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2951 else 1750) else if t 2 = 1 then (if t 3 = 0 then 2958 else if t 3 = 1 then 2931 else 1730) else (if t 3 = 0 then 1084 else if t 3 = 1 then 1046 else 1049)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2098 else 1359) else if t 2 = 1 then (if t 3 = 0 then 2104 else if t 3 = 1 then 2082 else 1733) else (if t 3 = 0 then 601 else if t 3 = 1 then 1051 else 1053))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2952 else 1903) else if t 2 = 1 then (if t 3 = 0 then 2959 else if t 3 = 1 then 2934 else 1888) else (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 972)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2947 else 2554) else if t 2 = 1 then (if t 3 = 0 then 2954 else if t 3 = 1 then 2913 else 2919) else (if t 3 = 0 then 2955 else if t 3 = 1 then 2915 else 2920)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2699 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2650 else if t 3 = 1 then 2923 else 2927) else (if t 3 = 0 then 2651 else if t 3 = 1 then 2924 else 2928))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1204 else 573) else if t 2 = 1 then (if t 3 = 0 then 1213 else if t 3 = 1 then 1180 else 1182) else (if t 3 = 0 then 1375 else if t 3 = 1 then 1796 else 2137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2949 else 2556) else if t 2 = 1 then (if t 3 = 0 then 2956 else if t 3 = 1 then 2917 else 2921) else (if t 3 = 0 then 2957 else if t 3 = 1 then 2918 else 2922)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2701 else 3934) else if t 2 = 1 then (if t 3 = 0 then 2652 else if t 3 = 1 then 2925 else 2929) else (if t 3 = 0 then 2653 else if t 3 = 1 then 2926 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3774 else (if jt.2.val < 2 then 3776 else 3783)) else (if jt.2.val < 4 then 3775 else (if jt.2.val < 5 then 3782 else 3781))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3508 else (if jt.2.val < 2 then 3510 else 3513)) else (if jt.2.val < 4 then 3509 else (if jt.2.val < 5 then 3512 else 3511)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4033 else (if jt.2.val < 2 then 4049 else 4035)) else (if jt.2.val < 4 then 4048 else (if jt.2.val < 5 then 4050 else 4029))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3023 else (if jt.2.val < 2 then 3040 else 3025)) else (if jt.2.val < 4 then 3036 else (if jt.2.val < 5 then 3037 else 3020)))))

checked_coverage fastCoverage0299 pairing0299 template0299 witness0299

theorem coverage0299 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0299) (maskBits m))
    cores template0299 witness0299 := by
  rw [← coresFast_eq]
  exact fastCoverage0299

theorem coverageSize0299 : ∀ q : Pattern,
    (cores (witness0299 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0299 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0299
#print axioms coverageSize0299

noncomputable def pairing0300 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0300 : List (Fin 4935) := templateData0300

noncomputable def witness0300 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 807 else 201) else if t 2 = 1 then (if t 3 = 0 then 809 else if t 3 = 1 then 805 else 199) else (if t 3 = 0 then 1471 else if t 3 = 1 then 65 else 2129)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 803 else if t 3 = 1 then 799 else 864) else if t 2 = 1 then (if t 3 = 0 then 801 else if t 3 = 1 then 797 else 862) else (if t 3 = 0 then 269 else if t 3 = 1 then 853 else 874)) else (if t 2 = 0 then (if t 3 = 0 then 4203 else if t 3 = 1 then 4054 else 3967) else if t 2 = 1 then (if t 3 = 0 then 2995 else if t 3 = 1 then 2993 else 3003) else (if t 3 = 0 then 2757 else if t 3 = 1 then 3002 else 3004))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 806 else 200) else if t 2 = 1 then (if t 3 = 0 then 808 else if t 3 = 1 then 804 else 198) else (if t 3 = 0 then 1470 else if t 3 = 1 then 64 else 2127)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 802 else if t 3 = 1 then 798 else 863) else if t 2 = 1 then (if t 3 = 0 then 800 else if t 3 = 1 then 796 else 861) else (if t 3 = 0 then 268 else if t 3 = 1 then 852 else 870)) else (if t 2 = 0 then (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 866) else if t 2 = 1 then (if t 3 = 0 then 819 else if t 3 = 1 then 816 else 865) else (if t 3 = 0 then 274 else if t 3 = 1 then 856 else 871))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 1815 else 2763) else if t 2 = 1 then (if t 3 = 0 then 836 else if t 3 = 1 then 834 else 204) else (if t 3 = 0 then 3942 else if t 3 = 1 then 74 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2145 else if t 3 = 1 then 1812 else 1689) else if t 2 = 1 then (if t 3 = 0 then 832 else if t 3 = 1 then 829 else 867) else (if t 3 = 0 then 278 else if t 3 = 1 then 858 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 2147 else if t 3 = 1 then 1817 else 1691) else if t 2 = 1 then (if t 3 = 0 then 839 else if t 3 = 1 then 838 else 869) else (if t 3 = 0 then 281 else if t 3 = 1 then 860 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3774 else (if jt.2.val < 2 then 3791 else 3783)) else (if jt.2.val < 4 then 3789 else (if jt.2.val < 5 then 3790 else 3781))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4159 else (if jt.2.val < 2 then 4202 else 4162)) else (if jt.2.val < 4 then 4200 else (if jt.2.val < 5 then 4201 else 4133)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2288 else (if jt.2.val < 2 then 2293 else 2294)) else (if jt.2.val < 4 then 2290 else (if jt.2.val < 5 then 2292 else 2291))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1224 else (if jt.2.val < 2 then 1230 else 1233)) else (if jt.2.val < 4 then 1229 else (if jt.2.val < 5 then 1232 else 1231)))))

checked_coverage fastCoverage0300 pairing0300 template0300 witness0300

theorem coverage0300 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0300) (maskBits m))
    cores template0300 witness0300 := by
  rw [← coresFast_eq]
  exact fastCoverage0300

theorem coverageSize0300 : ∀ q : Pattern,
    (cores (witness0300 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0300 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0300
#print axioms coverageSize0300

noncomputable def pairing0301 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0301 : List (Fin 4935) := templateData0301

noncomputable def witness0301 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 379 else 896) else if t 2 = 1 then (if t 3 = 0 then 386 else if t 3 = 1 then 371 else 892) else (if t 3 = 0 then 2140 else if t 3 = 1 then 373 else 1496)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 384 else if t 3 = 1 then 356 else 357) else if t 2 = 1 then (if t 3 = 0 then 382 else if t 3 = 1 then 336 else 340) else (if t 3 = 0 then 928 else if t 3 = 1 then 342 else 344)) else (if t 2 = 0 then (if t 3 = 0 then 3935 else if t 3 = 1 then 3929 else 4205) else if t 2 = 1 then (if t 3 = 0 then 2740 else if t 3 = 1 then 2728 else 2730) else (if t 3 = 0 then 2985 else if t 3 = 1 then 2731 else 2732))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 375 else 894) else if t 2 = 1 then (if t 3 = 0 then 385 else if t 3 = 1 then 363 else 888) else (if t 3 = 0 then 2139 else if t 3 = 1 then 367 else 1494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 383 else if t 3 = 1 then 346 else 350) else if t 2 = 1 then (if t 3 = 0 then 381 else if t 3 = 1 then 318 else 324) else (if t 3 = 0 then 924 else if t 3 = 1 then 328 else 332)) else (if t 2 = 0 then (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 351) else if t 2 = 1 then (if t 3 = 0 then 389 else if t 3 = 1 then 320 else 325) else (if t 3 = 0 then 925 else if t 3 = 1 then 329 else 333))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1773 else 2984) else if t 2 = 1 then (if t 3 = 0 then 395 else if t 3 = 1 then 365 else 890) else (if t 3 = 0 then 4206 else if t 3 = 1 then 369 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1497 else if t 3 = 1 then 1483 else 2157) else if t 2 = 1 then (if t 3 = 0 then 393 else if t 3 = 1 then 322 else 326) else (if t 3 = 0 then 926 else if t 3 = 1 then 330 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 1499 else if t 3 = 1 then 1484 else 2158) else if t 2 = 1 then (if t 3 = 0 then 397 else if t 3 = 1 then 323 else 327) else (if t 3 = 0 then 927 else if t 3 = 1 then 331 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3690 else (if jt.2.val < 2 then 3757 else 3701)) else (if jt.2.val < 4 then 3756 else (if jt.2.val < 5 then 3758 else 3698))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4114 else (if jt.2.val < 2 then 4129 else 4116)) else (if jt.2.val < 4 then 4128 else (if jt.2.val < 5 then 4130 else 4107)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2337 else (if jt.2.val < 2 then 2339 else 2342)) else (if jt.2.val < 4 then 2338 else (if jt.2.val < 5 then 2341 else 2340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1231 else (if jt.2.val < 2 then 1251 else 1233)) else (if jt.2.val < 4 then 1245 else (if jt.2.val < 5 then 1246 else 1224)))))

checked_coverage fastCoverage0301 pairing0301 template0301 witness0301

theorem coverage0301 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0301) (maskBits m))
    cores template0301 witness0301 := by
  rw [← coresFast_eq]
  exact fastCoverage0301

theorem coverageSize0301 : ∀ q : Pattern,
    (cores (witness0301 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0301 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0301
#print axioms coverageSize0301

noncomputable def pairing0302 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0302 : List (Fin 4935) := templateData0302

noncomputable def witness0302 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1574 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1566 else 1619) else (if t 3 = 0 then 918 else if t 3 = 1 then 62 else 95)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1570 else 1853) else if t 2 = 1 then (if t 3 = 0 then 1564 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 266 else if t 3 = 1 then 1589 else 1611)) else (if t 2 = 0 then (if t 3 = 0 then 2633 else if t 3 = 1 then 2855 else 2868) else if t 2 = 1 then (if t 3 = 0 then 2630 else if t 3 = 1 then 3219 else 3227) else (if t 3 = 0 then 4207 else if t 3 = 1 then 3953 else 3959))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1573 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1565 else 1617) else (if t 3 = 0 then 917 else if t 3 = 1 then 61 else 92)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1569 else 1851) else if t 2 = 1 then (if t 3 = 0 then 1563 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 265 else if t 3 = 1 then 1588 else 1604)) else (if t 2 = 0 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1584 else 1852) else if t 2 = 1 then (if t 3 = 0 then 1581 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 273 else if t 3 = 1 then 1591 else 1605))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 468 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1133 else if t 3 = 1 then 463 else 494) else (if t 3 = 0 then 2988 else if t 3 = 1 then 1848 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 660 else if t 3 = 1 then 1070 else 1092) else if t 2 = 1 then (if t 3 = 0 then 655 else if t 3 = 1 then 1592 else 1606) else (if t 3 = 0 then 2169 else if t 3 = 1 then 1596 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 665 else if t 3 = 1 then 1073 else 1093) else if t 2 = 1 then (if t 3 = 0 then 663 else if t 3 = 1 then 1595 else 1607) else (if t 3 = 0 then 2171 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3870 else (if jt.2.val < 2 then 3957 else 3894)) else (if jt.2.val < 4 then 3955 else (if jt.2.val < 5 then 3956 else 3874))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3413 else (if jt.2.val < 2 then 3434 else 3416)) else (if jt.2.val < 4 then 3432 else (if jt.2.val < 5 then 3433 else 3410)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2291 else (if jt.2.val < 2 then 2315 else 2294)) else (if jt.2.val < 4 then 2313 else (if jt.2.val < 5 then 2314 else 2288))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2163 else (if jt.2.val < 2 then 2165 else 2168)) else (if jt.2.val < 4 then 2164 else (if jt.2.val < 5 then 2167 else 2166)))))

checked_coverage fastCoverage0302 pairing0302 template0302 witness0302

theorem coverage0302 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0302) (maskBits m))
    cores template0302 witness0302 := by
  rw [← coresFast_eq]
  exact fastCoverage0302

theorem coverageSize0302 : ∀ q : Pattern,
    (cores (witness0302 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0302 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0302
#print axioms coverageSize0302

noncomputable def pairing0303 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0303 : List (Fin 4935) := templateData0303

noncomputable def witness0303 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2219 else 1676) else if t 2 = 1 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2207 else 1892) else (if t 3 = 0 then 308 else if t 3 = 1 then 979 else 980)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2213 else 1661) else if t 2 = 1 then (if t 3 = 0 then 2222 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 298 else if t 3 = 1 then 2195 else 2199)) else (if t 2 = 0 then (if t 3 = 0 then 2906 else if t 3 = 1 then 2690 else 2691) else if t 2 = 1 then (if t 3 = 0 then 2648 else if t 3 = 1 then 3528 else 3531) else (if t 3 = 0 then 3927 else if t 3 = 1 then 4211 else 4213))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2217 else 1673) else if t 2 = 1 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2205 else 1889) else (if t 3 = 0 then 306 else if t 3 = 1 then 973 else 975)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2211 else 1658) else if t 2 = 1 then (if t 3 = 0 then 2220 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 294 else if t 3 = 1 then 2179 else 2187)) else (if t 2 = 0 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2212 else 1659) else if t 2 = 1 then (if t 3 = 0 then 2221 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 295 else if t 3 = 1 then 2180 else 2188))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 761 else 3966) else if t 2 = 1 then (if t 3 = 0 then 696 else if t 3 = 1 then 1183 else 1185) else (if t 3 = 0 then 2782 else if t 3 = 1 then 1799 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1146 else if t 3 = 1 then 736 else 738) else if t 2 = 1 then (if t 3 = 0 then 684 else if t 3 = 1 then 2181 else 2189) else (if t 3 = 0 then 1473 else if t 3 = 1 then 2183 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 1147 else if t 3 = 1 then 737 else 739) else if t 2 = 1 then (if t 3 = 0 then 685 else if t 3 = 1 then 2182 else 2190) else (if t 3 = 0 then 1474 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4134 else (if jt.2.val < 2 then 4210 else 4156)) else (if jt.2.val < 4 then 4209 else (if jt.2.val < 5 then 4212 else 4152))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3511 else (if jt.2.val < 2 then 3534 else 3513)) else (if jt.2.val < 4 then 3533 else (if jt.2.val < 5 then 3535 else 3508)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2340 else (if jt.2.val < 2 then 2356 else 2342)) else (if jt.2.val < 4 then 2355 else (if jt.2.val < 5 then 2357 else 2337))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2166 else (if jt.2.val < 2 then 2216 else 2168)) else (if jt.2.val < 4 then 2214 else (if jt.2.val < 5 then 2215 else 2163)))))

checked_coverage fastCoverage0303 pairing0303 template0303 witness0303

theorem coverage0303 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0303) (maskBits m))
    cores template0303 witness0303 := by
  rw [← coresFast_eq]
  exact fastCoverage0303

theorem coverageSize0303 : ∀ q : Pattern,
    (cores (witness0303 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0303 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0303
#print axioms coverageSize0303

noncomputable def pairing0304 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0304 : List (Fin 4935) := templateData0304

noncomputable def witness0304 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 3941) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2788) else (if t 3 = 0 then 2779 else if t 3 = 1 then 2778 else 2989)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 726) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 725) else (if t 3 = 0 then 682 else if t 3 = 1 then 680 else 1144)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1173 else 758) else if t 2 = 1 then (if t 3 = 0 then 1174 else if t 3 = 1 then 1172 else 757) else (if t 3 = 0 then 1526 else if t 3 = 1 then 694 else 2161))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 35) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 34) else (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 901)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2462) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4170) else (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4183)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2487) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4177) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4181 else 4185))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1512) else if t 2 = 1 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 53) else (if t 3 = 0 then 197 else if t 3 = 1 then 196 else 905)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2475) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4171) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4180 else 4184)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2842 else 2491) else if t 2 = 1 then (if t 3 = 0 then 4004 else if t 3 = 1 then 4164 else 4178) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4182 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4134 else (if jt.2.val < 2 then 4154 else 4156)) else (if jt.2.val < 4 then 4151 else (if jt.2.val < 5 then 4153 else 4152))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4133 else (if jt.2.val < 2 then 4161 else 4162)) else (if jt.2.val < 4 then 4158 else (if jt.2.val < 5 then 4160 else 4159)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4215 else (if jt.2.val < 2 then 4223 else 4226)) else (if jt.2.val < 4 then 4222 else (if jt.2.val < 5 then 4225 else 4224))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4216 else (if jt.2.val < 2 then 4220 else 4221)) else (if jt.2.val < 4 then 4217 else (if jt.2.val < 5 then 4219 else 4218)))))

checked_coverage fastCoverage0304 pairing0304 template0304 witness0304

theorem coverage0304 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0304) (maskBits m))
    cores template0304 witness0304 := by
  rw [← coresFast_eq]
  exact fastCoverage0304

theorem coverageSize0304 : ∀ q : Pattern,
    (cores (witness0304 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0304 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0304
#print axioms coverageSize0304

noncomputable def pairing0305 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0305 : List (Fin 4935) := templateData0305

noncomputable def witness0305 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4196) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2787) else (if t 3 = 0 then 2981 else if t 3 = 1 then 2980 else 2800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 724) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 723) else (if t 3 = 0 then 1090 else if t 3 = 1 then 1078 else 784)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 536 else 1109) else if t 2 = 1 then (if t 3 = 0 then 539 else if t 3 = 1 then 535 else 1108) else (if t 3 = 0 then 2150 else if t 3 = 1 then 595 else 1549))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 33) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 32) else (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 97)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2461) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3834) else (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3854)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2899) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3848) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3856 else 3858))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 2126) else if t 2 = 1 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 52) else (if t 3 = 0 then 1013 else if t 3 = 1 then 999 else 99)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2474) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3837) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3853 else 3855)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2626 else 2901) else if t 2 = 1 then (if t 3 = 0 then 3847 else if t 3 = 1 then 3846 else 3850) else (if t 3 = 0 then 4192 else if t 3 = 1 then 3857 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3806 else (if jt.2.val < 2 then 3826 else 3828)) else (if jt.2.val < 4 then 3823 else (if jt.2.val < 5 then 3825 else 3824))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4095 else (if jt.2.val < 2 then 4105 else 4106)) else (if jt.2.val < 4 then 4102 else (if jt.2.val < 5 then 4104 else 4103)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4082 else (if jt.2.val < 2 then 4084 else 4088)) else (if jt.2.val < 4 then 4083 else (if jt.2.val < 5 then 4087 else 4086))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4218 else (if jt.2.val < 2 then 4229 else 4221)) else (if jt.2.val < 4 then 4227 else (if jt.2.val < 5 then 4228 else 4216)))))

checked_coverage fastCoverage0305 pairing0305 template0305 witness0305

theorem coverage0305 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0305) (maskBits m))
    cores template0305 witness0305 := by
  rw [← coresFast_eq]
  exact fastCoverage0305

theorem coverageSize0305 : ∀ q : Pattern,
    (cores (witness0305 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0305 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0305
#print axioms coverageSize0305

noncomputable def pairing0306 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0306 : List (Fin 4935) := templateData0306

noncomputable def witness0306 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2565 else 2884) else if t 2 = 1 then (if t 3 = 0 then 2560 else if t 3 = 1 then 2544 else 2546) else (if t 3 = 0 then 4190 else if t 3 = 1 then 3945 else 3946)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2563 else 1762) else if t 2 = 1 then (if t 3 = 0 then 2558 else if t 3 = 1 then 2538 else 1747) else (if t 3 = 0 then 667 else if t 3 = 1 then 641 else 646)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1372 else 2119) else if t 2 = 1 then (if t 3 = 0 then 1357 else if t 3 = 1 then 1350 else 1353) else (if t 3 = 0 then 1138 else if t 3 = 1 then 644 else 648))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2564 else 1915) else if t 2 = 1 then (if t 3 = 0 then 2559 else if t 3 = 1 then 2541 else 1900) else (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 153)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2562 else 2883) else if t 2 = 1 then (if t 3 = 0 then 2548 else if t 3 = 1 then 2519 else 2530) else (if t 3 = 0 then 2549 else if t 3 = 1 then 2521 else 2531)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2576 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2878 else if t 3 = 1 then 2526 else 2534) else (if t 3 = 0 then 2879 else if t 3 = 1 then 2527 else 2535))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 585 else 1118) else if t 2 = 1 then (if t 3 = 0 then 571 else if t 3 = 1 then 545 else 549) else (if t 3 = 0 then 2116 else if t 3 = 1 then 1532 else 1536)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2572 else 2886) else if t 2 = 1 then (if t 3 = 0 then 2550 else if t 3 = 1 then 2523 else 2532) else (if t 3 = 0 then 2551 else if t 3 = 1 then 2524 else 2533)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2579 else 4197) else if t 2 = 1 then (if t 3 = 0 then 2880 else if t 3 = 1 then 2528 else 2536) else (if t 3 = 0 then 2881 else if t 3 = 1 then 2529 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3702 else (if jt.2.val < 2 then 3704 else 3711)) else (if jt.2.val < 4 then 3703 else (if jt.2.val < 5 then 3710 else 3709))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3417 else (if jt.2.val < 2 then 3419 else 3422)) else (if jt.2.val < 4 then 3418 else (if jt.2.val < 5 then 3421 else 3420)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4224 else (if jt.2.val < 2 then 4232 else 4226)) else (if jt.2.val < 4 then 4230 else (if jt.2.val < 5 then 4231 else 4215))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2871 else (if jt.2.val < 2 then 2873 else 2877)) else (if jt.2.val < 4 then 2872 else (if jt.2.val < 5 then 2876 else 2875)))))

checked_coverage fastCoverage0306 pairing0306 template0306 witness0306

theorem coverage0306 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0306) (maskBits m))
    cores template0306 witness0306 := by
  rw [← coresFast_eq]
  exact fastCoverage0306

theorem coverageSize0306 : ∀ q : Pattern,
    (cores (witness0306 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0306 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0306
#print axioms coverageSize0306

noncomputable def pairing0307 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0307 : List (Fin 4935) := templateData0307

noncomputable def witness0307 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2960 else 2506) else if t 2 = 1 then (if t 3 = 0 then 2953 else if t 3 = 1 then 2937 else 2938) else (if t 3 = 0 then 3905 else if t 3 = 1 then 4046 else 4198)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2958 else 1756) else if t 2 = 1 then (if t 3 = 0 then 2951 else if t 3 = 1 then 2931 else 1730) else (if t 3 = 0 then 1075 else if t 3 = 1 then 1046 else 1049)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2104 else 1453) else if t 2 = 1 then (if t 3 = 0 then 2098 else if t 3 = 1 then 2082 else 1733) else (if t 3 = 0 then 477 else if t 3 = 1 then 1051 else 1053))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2959 else 1909) else if t 2 = 1 then (if t 3 = 0 then 2952 else if t 3 = 1 then 2934 else 1888) else (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 972)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2954 else 2502) else if t 2 = 1 then (if t 3 = 0 then 2947 else if t 3 = 1 then 2913 else 2919) else (if t 3 = 0 then 2948 else if t 3 = 1 then 2915 else 2920)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2650 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2699 else if t 3 = 1 then 2923 else 2927) else (if t 3 = 0 then 2700 else if t 3 = 1 then 2924 else 2928))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1213 else 505) else if t 2 = 1 then (if t 3 = 0 then 1204 else if t 3 = 1 then 1180 else 1182) else (if t 3 = 0 then 1431 else if t 3 = 1 then 1796 else 2137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2956 else 2504) else if t 2 = 1 then (if t 3 = 0 then 2949 else if t 3 = 1 then 2917 else 2921) else (if t 3 = 0 then 2950 else if t 3 = 1 then 2918 else 2922)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2652 else 3928) else if t 2 = 1 then (if t 3 = 0 then 2701 else if t 3 = 1 then 2925 else 2929) else (if t 3 = 0 then 2702 else if t 3 = 1 then 2926 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3774 else (if jt.2.val < 2 then 3776 else 3783)) else (if jt.2.val < 4 then 3775 else (if jt.2.val < 5 then 3782 else 3781))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3508 else (if jt.2.val < 2 then 3510 else 3513)) else (if jt.2.val < 4 then 3509 else (if jt.2.val < 5 then 3512 else 3511)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4086 else (if jt.2.val < 2 then 4094 else 4088)) else (if jt.2.val < 4 then 4092 else (if jt.2.val < 5 then 4093 else 4082))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2875 else (if jt.2.val < 2 then 2945 else 2877)) else (if jt.2.val < 4 then 2944 else (if jt.2.val < 5 then 2946 else 2871)))))

checked_coverage fastCoverage0307 pairing0307 template0307 witness0307

theorem coverage0307 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0307) (maskBits m))
    cores template0307 witness0307 := by
  rw [← coresFast_eq]
  exact fastCoverage0307

theorem coverageSize0307 : ∀ q : Pattern,
    (cores (witness0307 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0307 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0307
#print axioms coverageSize0307

noncomputable def pairing0308 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0308 : List (Fin 4935) := templateData0308

noncomputable def witness0308 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 807 else 67) else if t 2 = 1 then (if t 3 = 0 then 809 else if t 3 = 1 then 805 else 65) else (if t 3 = 0 then 1501 else if t 3 = 1 then 199 else 2129)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 803 else if t 3 = 1 then 799 else 855) else if t 2 = 1 then (if t 3 = 0 then 801 else if t 3 = 1 then 797 else 853) else (if t 3 = 0 then 400 else if t 3 = 1 then 862 else 874)) else (if t 2 = 0 then (if t 3 = 0 then 4203 else if t 3 = 1 then 4054 else 3954) else if t 2 = 1 then (if t 3 = 0 then 2995 else if t 3 = 1 then 2993 else 3002) else (if t 3 = 0 then 2743 else if t 3 = 1 then 3003 else 3004))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 806 else 66) else if t 2 = 1 then (if t 3 = 0 then 808 else if t 3 = 1 then 804 else 64) else (if t 3 = 0 then 1500 else if t 3 = 1 then 198 else 2127)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 802 else if t 3 = 1 then 798 else 854) else if t 2 = 1 then (if t 3 = 0 then 800 else if t 3 = 1 then 796 else 852) else (if t 3 = 0 then 399 else if t 3 = 1 then 861 else 870)) else (if t 2 = 0 then (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 857) else if t 2 = 1 then (if t 3 = 0 then 819 else if t 3 = 1 then 816 else 856) else (if t 3 = 0 then 403 else if t 3 = 1 then 865 else 871))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 1815 else 2739) else if t 2 = 1 then (if t 3 = 0 then 836 else if t 3 = 1 then 834 else 74) else (if t 3 = 0 then 3952 else if t 3 = 1 then 204 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2145 else if t 3 = 1 then 1812 else 1598) else if t 2 = 1 then (if t 3 = 0 then 832 else if t 3 = 1 then 829 else 858) else (if t 3 = 0 then 405 else if t 3 = 1 then 867 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 2147 else if t 3 = 1 then 1817 else 1601) else if t 2 = 1 then (if t 3 = 0 then 839 else if t 3 = 1 then 838 else 860) else (if t 3 = 0 then 407 else if t 3 = 1 then 869 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3774 else (if jt.2.val < 2 then 3791 else 3783)) else (if jt.2.val < 4 then 3789 else (if jt.2.val < 5 then 3790 else 3781))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4159 else (if jt.2.val < 2 then 4202 else 4162)) else (if jt.2.val < 4 then 4200 else (if jt.2.val < 5 then 4201 else 4133)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2388 else (if jt.2.val < 2 then 2390 else 2393)) else (if jt.2.val < 4 then 2389 else (if jt.2.val < 5 then 2392 else 2391))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 793 else (if jt.2.val < 2 then 850 else 851)) else (if jt.2.val < 4 then 847 else (if jt.2.val < 5 then 849 else 848)))))

checked_coverage fastCoverage0308 pairing0308 template0308 witness0308

theorem coverage0308 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0308) (maskBits m))
    cores template0308 witness0308 := by
  rw [← coresFast_eq]
  exact fastCoverage0308

theorem coverageSize0308 : ∀ q : Pattern,
    (cores (witness0308 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0308 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0308
#print axioms coverageSize0308

noncomputable def pairing0309 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0309 : List (Fin 4935) := templateData0309

noncomputable def witness0309 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 224 else 918) else if t 2 = 1 then (if t 3 = 0 then 230 else if t 3 = 1 then 222 else 916) else (if t 3 = 0 then 2140 else if t 3 = 1 then 304 else 1478)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 228 else if t 3 = 1 then 220 else 266) else if t 2 = 1 then (if t 3 = 0 then 226 else if t 3 = 1 then 218 else 264) else (if t 3 = 0 then 928 else if t 3 = 1 then 290 else 292)) else (if t 2 = 0 then (if t 3 = 0 then 3925 else if t 3 = 1 then 3923 else 4207) else if t 2 = 1 then (if t 3 = 0 then 2750 else if t 3 = 1 then 2747 else 2756) else (if t 3 = 0 then 2985 else if t 3 = 1 then 2759 else 2760))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 223 else 917) else if t 2 = 1 then (if t 3 = 0 then 229 else if t 3 = 1 then 221 else 915) else (if t 3 = 0 then 2139 else if t 3 = 1 then 300 else 1476)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 227 else if t 3 = 1 then 219 else 265) else if t 2 = 1 then (if t 3 = 0 then 225 else if t 3 = 1 then 217 else 263) else (if t 3 = 0 then 924 else if t 3 = 1 then 282 else 286)) else (if t 2 = 0 then (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 273) else if t 2 = 1 then (if t 3 = 0 then 242 else if t 3 = 1 then 237 else 272) else (if t 3 = 0 then 925 else if t 3 = 1 then 283 else 287))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1785 else 2988) else if t 2 = 1 then (if t 3 = 0 then 257 else if t 3 = 1 then 253 else 921) else (if t 3 = 0 then 4206 else if t 3 = 1 then 302 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1461 else if t 3 = 1 then 1458 else 2169) else if t 2 = 1 then (if t 3 = 0 then 255 else if t 3 = 1 then 250 else 276) else (if t 3 = 0 then 926 else if t 3 = 1 then 284 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 1464 else if t 3 = 1 then 1463 else 2171) else if t 2 = 1 then (if t 3 = 0 then 261 else if t 3 = 1 then 259 else 280) else (if t 3 = 0 then 927 else if t 3 = 1 then 285 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3702 else (if jt.2.val < 2 then 3755 else 3711)) else (if jt.2.val < 4 then 3753 else (if jt.2.val < 5 then 3754 else 3709))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4103 else (if jt.2.val < 2 then 4127 else 4106)) else (if jt.2.val < 4 then 4125 else (if jt.2.val < 5 then 4126 else 4095)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2418 else (if jt.2.val < 2 then 2420 else 2423)) else (if jt.2.val < 4 then 2419 else (if jt.2.val < 5 then 2422 else 2421))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 848 else (if jt.2.val < 2 then 914 else 851)) else (if jt.2.val < 4 then 906 else (if jt.2.val < 5 then 907 else 793)))))

checked_coverage fastCoverage0309 pairing0309 template0309 witness0309

theorem coverage0309 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0309) (maskBits m))
    cores template0309 witness0309 := by
  rw [← coresFast_eq]
  exact fastCoverage0309

theorem coverageSize0309 : ∀ q : Pattern,
    (cores (witness0309 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0309 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0309
#print axioms coverageSize0309

noncomputable def pairing0310 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0310 : List (Fin 4935) := templateData0310

noncomputable def witness0310 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1682 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1669 else 1670) else (if t 3 = 0 then 896 else if t 3 = 1 then 157 else 159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1678 else 1853) else if t 2 = 1 then (if t 3 = 0 then 1660 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 357 else if t 3 = 1 then 1646 else 1650)) else (if t 2 = 0 then (if t 3 = 0 then 2722 else if t 3 = 1 then 2860 else 2868) else if t 2 = 1 then (if t 3 = 0 then 2689 else if t 3 = 1 then 3232 else 3235) else (if t 3 = 0 then 4205 else if t 3 = 1 then 3963 else 3965))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1681 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1665 else 1667) else (if t 3 = 0 then 894 else if t 3 = 1 then 150 else 154)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1677 else 1851) else if t 2 = 1 then (if t 3 = 0 then 1656 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 350 else if t 3 = 1 then 1630 else 1638)) else (if t 2 = 0 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1685 else 1852) else if t 2 = 1 then (if t 3 = 0 then 1657 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 351 else if t 3 = 1 then 1631 else 1639))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 596 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1110 else if t 3 = 1 then 546 else 550) else (if t 3 = 0 then 2984 else if t 3 = 1 then 1833 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 785 else if t 3 = 1 then 1079 else 1092) else if t 2 = 1 then (if t 3 = 0 then 734 else if t 3 = 1 then 1632 else 1640) else (if t 3 = 0 then 2157 else if t 3 = 1 then 1634 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 788 else if t 3 = 1 then 1082 else 1093) else if t 2 = 1 then (if t 3 = 0 then 735 else if t 3 = 1 then 1633 else 1641) else (if t 3 = 0 then 2158 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3806 else (if jt.2.val < 2 then 3962 else 3828)) else (if jt.2.val < 4 then 3961 else (if jt.2.val < 5 then 3964 else 3824))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3420 else (if jt.2.val < 2 then 3436 else 3422)) else (if jt.2.val < 4 then 3435 else (if jt.2.val < 5 then 3437 else 3417)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2391 else (if jt.2.val < 2 then 2408 else 2393)) else (if jt.2.val < 4 then 2406 else (if jt.2.val < 5 then 2407 else 2388))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2256 else (if jt.2.val < 2 then 2258 else 2261)) else (if jt.2.val < 4 then 2257 else (if jt.2.val < 5 then 2260 else 2259)))))

checked_coverage fastCoverage0310 pairing0310 template0310 witness0310

theorem coverage0310 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0310) (maskBits m))
    cores template0310 witness0310 := by
  rw [← coresFast_eq]
  exact fastCoverage0310

theorem coverageSize0310 : ∀ q : Pattern,
    (cores (witness0310 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0310 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0310
#print axioms coverageSize0310

noncomputable def pairing0311 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0311 : List (Fin 4935) := templateData0311

noncomputable def witness0311 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2225 else 1622) else if t 2 = 1 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2207 else 1892) else (if t 3 = 0 then 380 else if t 3 = 1 then 979 else 980)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2222 else 1616) else if t 2 = 1 then (if t 3 = 0 then 2213 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 358 else if t 3 = 1 then 2195 else 2199)) else (if t 2 = 0 then (if t 3 = 0 then 2906 else if t 3 = 1 then 2648 else 2649) else if t 2 = 1 then (if t 3 = 0 then 2690 else if t 3 = 1 then 3528 else 3531) else (if t 3 = 0 then 3930 else if t 3 = 1 then 4211 else 4213))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2223 else 1620) else if t 2 = 1 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2205 else 1889) else (if t 3 = 0 then 377 else if t 3 = 1 then 973 else 975)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2220 else 1614) else if t 2 = 1 then (if t 3 = 0 then 2211 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 352 else if t 3 = 1 then 2179 else 2187)) else (if t 2 = 0 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2221 else 1615) else if t 2 = 1 then (if t 3 = 0 then 2212 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 353 else if t 3 = 1 then 2180 else 2188))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 696 else 3960) else if t 2 = 1 then (if t 3 = 0 then 761 else if t 3 = 1 then 1183 else 1185) else (if t 3 = 0 then 2796 else if t 3 = 1 then 1799 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1146 else if t 3 = 1 then 684 else 686) else if t 2 = 1 then (if t 3 = 0 then 736 else if t 3 = 1 then 2181 else 2189) else (if t 3 = 0 then 1487 else if t 3 = 1 then 2183 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 1147 else if t 3 = 1 then 685 else 687) else if t 2 = 1 then (if t 3 = 0 then 737 else if t 3 = 1 then 2182 else 2190) else (if t 3 = 0 then 1488 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4134 else (if jt.2.val < 2 then 4210 else 4156)) else (if jt.2.val < 4 then 4209 else (if jt.2.val < 5 then 4212 else 4152))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3511 else (if jt.2.val < 2 then 3534 else 3513)) else (if jt.2.val < 4 then 3533 else (if jt.2.val < 5 then 3535 else 3508)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2421 else (if jt.2.val < 2 then 2429 else 2423)) else (if jt.2.val < 4 then 2427 else (if jt.2.val < 5 then 2428 else 2418))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2259 else (if jt.2.val < 2 then 2263 else 2261)) else (if jt.2.val < 4 then 2262 else (if jt.2.val < 5 then 2264 else 2256)))))

checked_coverage fastCoverage0311 pairing0311 template0311 witness0311

theorem coverage0311 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0311) (maskBits m))
    cores template0311 witness0311 := by
  rw [← coresFast_eq]
  exact fastCoverage0311

theorem coverageSize0311 : ∀ q : Pattern,
    (cores (witness0311 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0311 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0311
#print axioms coverageSize0311

noncomputable def pairing0312 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0312 : List (Fin 4935) := templateData0312

noncomputable def witness0312 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 3935) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2740) else (if t 3 = 0 then 2997 else if t 3 = 1 then 2995 else 2743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 489) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 488) else (if t 3 = 0 then 1174 else if t 3 = 1 then 1170 else 502)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 538 else 1120) else if t 2 = 1 then (if t 3 = 0 then 539 else if t 3 = 1 then 537 else 1114) else (if t 3 = 0 then 1544 else if t 3 = 1 then 568 else 1837))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 390) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 389) else (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 403)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2715) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4019) else (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4021)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2903) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4023) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4017 else 4025))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 1499) else if t 2 = 1 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 397) else (if t 3 = 0 then 841 else if t 3 = 1 then 839 else 407)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2719) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4020) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4003 else 4022)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2627 else 2905) else if t 2 = 1 then (if t 3 = 0 then 3847 else if t 3 = 1 then 4016 else 4024) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4018 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3972 else (if jt.2.val < 2 then 3992 else 3994)) else (if jt.2.val < 4 then 3989 else (if jt.2.val < 5 then 3991 else 3990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4233 else (if jt.2.val < 2 then 4243 else 4244)) else (if jt.2.val < 4 then 4240 else (if jt.2.val < 5 then 4242 else 4241)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4234 else (if jt.2.val < 2 then 4238 else 4239)) else (if jt.2.val < 4 then 4235 else (if jt.2.val < 5 then 4237 else 4236))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3969 else (if jt.2.val < 2 then 4006 else 4009)) else (if jt.2.val < 4 then 4005 else (if jt.2.val < 5 then 4008 else 4007)))))

checked_coverage fastCoverage0312 pairing0312 template0312 witness0312

theorem coverage0312 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0312) (maskBits m))
    cores template0312 witness0312 := by
  rw [← coresFast_eq]
  exact fastCoverage0312

theorem coverageSize0312 : ∀ q : Pattern,
    (cores (witness0312 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0312 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0312
#print axioms coverageSize0312

noncomputable def pairing0313 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0313 : List (Fin 4935) := templateData0313

noncomputable def witness0313 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4036) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2737) else (if t 3 = 0 then 2779 else if t 3 = 1 then 2775 else 2987)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 475) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 462) else (if t 3 = 0 then 682 else if t 3 = 1 then 654 else 1132)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1075 else 477) else if t 2 = 1 then (if t 3 = 0 then 1090 else if t 3 = 1 then 1069 else 467) else (if t 3 = 0 then 1826 else if t 3 = 1 then 659 else 1519))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 376) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 364) else (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 889)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2696) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3880) else (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3882)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2700) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3888) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3886 else 3890))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 1774) else if t 2 = 1 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 366) else (if t 3 = 0 then 197 else if t 3 = 1 then 163 else 891)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2698) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3881) else (if t 3 = 0 then 3916 else if t 3 = 1 then 3878 else 3883)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2950 else 2702) else if t 2 = 1 then (if t 3 = 0 then 4038 else if t 3 = 1 then 3885 else 3889) else (if t 3 = 0 then 4040 else if t 3 = 1 then 3887 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3870 else (if jt.2.val < 2 then 3872 else 3894)) else (if jt.2.val < 4 then 3871 else (if jt.2.val < 5 then 3893 else 3874))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4245 else (if jt.2.val < 2 then 4247 else 4250)) else (if jt.2.val < 4 then 4246 else (if jt.2.val < 5 then 4249 else 4248)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4110 else (if jt.2.val < 2 then 4112 else 4118)) else (if jt.2.val < 4 then 4111 else (if jt.2.val < 5 then 4117 else 4113))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4007 else (if jt.2.val < 2 then 4032 else 4009)) else (if jt.2.val < 4 then 4027 else (if jt.2.val < 5 then 4028 else 3969)))))

checked_coverage fastCoverage0313 pairing0313 template0313 witness0313

theorem coverage0313 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0313) (maskBits m))
    cores template0313 witness0313 := by
  rw [← coresFast_eq]
  exact fastCoverage0313

theorem coverageSize0313 : ∀ q : Pattern,
    (cores (witness0313 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0313 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0313
#print axioms coverageSize0313

noncomputable def pairing0314 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0314 : List (Fin 4935) := templateData0314

noncomputable def witness0314 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2813 else 2722) else if t 2 = 1 then (if t 3 = 0 then 2817 else if t 3 = 1 then 2809 else 2860) else (if t 3 = 0 then 4056 else if t 3 = 1 then 4054 else 3967)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2811 else 1371) else if t 2 = 1 then (if t 3 = 0 then 2815 else if t 3 = 1 then 2807 else 1370) else (if t 3 = 0 then 1173 else if t 3 = 1 then 1169 else 1211)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1415 else 1780) else if t 2 = 1 then (if t 3 = 0 then 1416 else if t 3 = 1 then 1414 else 1777) else (if t 3 = 0 then 758 else if t 3 = 1 then 1202 else 1222))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2812 else 1686) else if t 2 = 1 then (if t 3 = 0 then 2816 else if t 3 = 1 then 2808 else 1685) else (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 866)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2810 else 2721) else if t 2 = 1 then (if t 3 = 0 then 2814 else if t 3 = 1 then 2806 else 2859) else (if t 3 = 0 then 2829 else if t 3 = 1 then 2826 else 2861)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2632 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2484 else if t 3 = 1 then 2854 else 2864) else (if t 3 = 0 then 2487 else if t 3 = 1 then 2856 else 2865))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1040 else 788) else if t 2 = 1 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1082) else (if t 3 = 0 then 1818 else if t 3 = 1 then 1817 else 1691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2724) else if t 2 = 1 then (if t 3 = 0 then 2838 else if t 3 = 1 then 2835 else 2862) else (if t 3 = 0 then 2842 else if t 3 = 1 then 2840 else 2863)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2637 else 4045) else if t 2 = 1 then (if t 3 = 0 then 2489 else if t 3 = 1 then 2857 else 2866) else (if t 3 = 0 then 2491 else if t 3 = 1 then 2858 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3762 else (if jt.2.val < 2 then 3772 else 3773)) else (if jt.2.val < 4 then 3769 else (if jt.2.val < 5 then 3771 else 3770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3575 else (if jt.2.val < 2 then 3580 else 3581)) else (if jt.2.val < 4 then 3577 else (if jt.2.val < 5 then 3579 else 3578)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4236 else (if jt.2.val < 2 then 4253 else 4239)) else (if jt.2.val < 4 then 4251 else (if jt.2.val < 5 then 4252 else 4234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2802 else (if jt.2.val < 2 then 2845 else 2848)) else (if jt.2.val < 4 then 2844 else (if jt.2.val < 5 then 2847 else 2846)))))

checked_coverage fastCoverage0314 pairing0314 template0314 witness0314

theorem coverage0314 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0314) (maskBits m))
    cores template0314 witness0314 := by
  rw [← coresFast_eq]
  exact fastCoverage0314

theorem coverageSize0314 : ∀ q : Pattern,
    (cores (witness0314 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0314 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0314
#print axioms coverageSize0314

noncomputable def pairing0315 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0315 : List (Fin 4935) := templateData0315

noncomputable def witness0315 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2560 else 2882) else if t 2 = 1 then (if t 3 = 0 then 2565 else if t 3 = 1 then 2544 else 2545) else (if t 3 = 0 then 3951 else if t 3 = 1 then 3945 else 4058)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2558 else 1357) else if t 2 = 1 then (if t 3 = 0 then 2563 else if t 3 = 1 then 2538 else 1350) else (if t 3 = 0 then 681 else if t 3 = 1 then 641 else 644)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1750 else 1359) else if t 2 = 1 then (if t 3 = 0 then 1762 else if t 3 = 1 then 1747 else 1353) else (if t 3 = 0 then 1145 else if t 3 = 1 then 646 else 648))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2559 else 1672) else if t 2 = 1 then (if t 3 = 0 then 2564 else if t 3 = 1 then 2541 else 1666) else (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 151)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2548 else 2878) else if t 2 = 1 then (if t 3 = 0 then 2562 else if t 3 = 1 then 2519 else 2526) else (if t 3 = 0 then 2570 else if t 3 = 1 then 2521 else 2527)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2554 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2883 else if t 3 = 1 then 2530 else 2534) else (if t 3 = 0 then 2885 else if t 3 = 1 then 2531 else 2535))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 571 else 1111) else if t 2 = 1 then (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 547) else (if t 3 = 0 then 1547 else if t 3 = 1 then 1532 else 1834)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2880) else if t 2 = 1 then (if t 3 = 0 then 2572 else if t 3 = 1 then 2523 else 2528) else (if t 3 = 0 then 2574 else if t 3 = 1 then 2524 else 2529)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2556 else 3934) else if t 2 = 1 then (if t 3 = 0 then 2886 else if t 3 = 1 then 2532 else 2536) else (if t 3 = 0 then 2887 else if t 3 = 1 then 2533 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3702 else (if jt.2.val < 2 then 3704 else 3711)) else (if jt.2.val < 4 then 3703 else (if jt.2.val < 5 then 3710 else 3709))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3582 else (if jt.2.val < 2 then 3584 else 3587)) else (if jt.2.val < 4 then 3583 else (if jt.2.val < 5 then 3586 else 3585)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4113 else (if jt.2.val < 2 then 4123 else 4118)) else (if jt.2.val < 4 then 4122 else (if jt.2.val < 5 then 4124 else 4110))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2846 else (if jt.2.val < 2 then 2874 else 2848)) else (if jt.2.val < 4 then 2869 else (if jt.2.val < 5 then 2870 else 2802)))))

checked_coverage fastCoverage0315 pairing0315 template0315 witness0315

theorem coverage0315 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0315) (maskBits m))
    cores template0315 witness0315 := by
  rw [← coresFast_eq]
  exact fastCoverage0315

theorem coverageSize0315 : ∀ q : Pattern,
    (cores (witness0315 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0315 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0315
#print axioms coverageSize0315

noncomputable def pairing0316 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0316 : List (Fin 4935) := templateData0316

noncomputable def witness0316 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 228 else 932) else if t 2 = 1 then (if t 3 = 0 then 230 else if t 3 = 1 then 226 else 928) else (if t 3 = 0 then 1471 else if t 3 = 1 then 269 else 1790)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 224 else if t 3 = 1 then 220 else 298) else if t 2 = 1 then (if t 3 = 0 then 222 else if t 3 = 1 then 218 else 290) else (if t 3 = 0 then 916 else if t 3 = 1 then 264 else 292)) else (if t 2 = 0 then (if t 3 = 0 then 4044 else if t 3 = 1 then 3923 else 3927) else if t 2 = 1 then (if t 3 = 0 then 2749 else if t 3 = 1 then 2747 else 2759) else (if t 3 = 0 then 2983 else if t 3 = 1 then 2756 else 2760))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 227 else 930) else if t 2 = 1 then (if t 3 = 0 then 229 else if t 3 = 1 then 225 else 924) else (if t 3 = 0 then 1470 else if t 3 = 1 then 268 else 1788)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 223 else if t 3 = 1 then 219 else 294) else if t 2 = 1 then (if t 3 = 0 then 221 else if t 3 = 1 then 217 else 282) else (if t 3 = 0 then 915 else if t 3 = 1 then 263 else 286)) else (if t 2 = 0 then (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 295) else if t 2 = 1 then (if t 3 = 0 then 240 else if t 3 = 1 then 237 else 283) else (if t 3 = 0 then 919 else if t 3 = 1 then 272 else 287))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1461 else 2990) else if t 2 = 1 then (if t 3 = 0 then 257 else if t 3 = 1 then 255 else 926) else (if t 3 = 0 then 3942 else if t 3 = 1 then 278 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1785 else if t 3 = 1 then 1458 else 1473) else if t 2 = 1 then (if t 3 = 0 then 253 else if t 3 = 1 then 250 else 284) else (if t 3 = 0 then 921 else if t 3 = 1 then 276 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 1787 else if t 3 = 1 then 1463 else 1474) else if t 2 = 1 then (if t 3 = 0 then 260 else if t 3 = 1 then 259 else 285) else (if t 3 = 0 then 923 else if t 3 = 1 then 280 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3702 else (if jt.2.val < 2 then 3755 else 3711)) else (if jt.2.val < 4 then 3753 else (if jt.2.val < 5 then 3754 else 3709))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4241 else (if jt.2.val < 2 then 4256 else 4244)) else (if jt.2.val < 4 then 4254 else (if jt.2.val < 5 then 4255 else 4233)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1457 else (if jt.2.val < 2 then 1468 else 1469)) else (if jt.2.val < 4 then 1465 else (if jt.2.val < 5 then 1467 else 1466))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 908 else (if jt.2.val < 2 then 910 else 913)) else (if jt.2.val < 4 then 909 else (if jt.2.val < 5 then 912 else 911)))))

checked_coverage fastCoverage0316 pairing0316 template0316 witness0316

theorem coverage0316 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0316) (maskBits m))
    cores template0316 witness0316 := by
  rw [← coresFast_eq]
  exact fastCoverage0316

theorem coverageSize0316 : ∀ q : Pattern,
    (cores (witness0316 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0316 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0316
#print axioms coverageSize0316

noncomputable def pairing0317 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0317 : List (Fin 4935) := templateData0317

noncomputable def witness0317 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 995 else 380) else if t 2 = 1 then (if t 3 = 0 then 1006 else if t 3 = 1 then 991 else 373) else (if t 3 = 0 then 1807 else if t 3 = 1 then 172 else 1496)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1004 else if t 3 = 1 then 977 else 979) else if t 2 = 1 then (if t 3 = 0 then 1000 else if t 3 = 1 then 957 else 963) else (if t 3 = 0 then 100 else if t 3 = 1 then 961 else 965)) else (if t 2 = 0 then (if t 3 = 0 then 3860 else if t 3 = 1 then 4046 else 4047) else if t 2 = 1 then (if t 3 = 0 then 2980 else if t 3 = 1 then 2970 else 2973) else (if t 3 = 0 then 2800 else if t 3 = 1 then 2972 else 2974))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 993 else 377) else if t 2 = 1 then (if t 3 = 0 then 1005 else if t 3 = 1 then 987 else 367) else (if t 3 = 0 then 1806 else if t 3 = 1 then 166 else 1494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1002 else if t 3 = 1 then 967 else 973) else if t 2 = 1 then (if t 3 = 0 then 996 else if t 3 = 1 then 939 else 949) else (if t 3 = 0 then 96 else if t 3 = 1 then 945 else 953)) else (if t 2 = 0 then (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 974) else if t 2 = 1 then (if t 3 = 0 then 997 else if t 3 = 1 then 941 else 950) else (if t 3 = 0 then 97 else if t 3 = 1 then 946 else 954))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1430 else 2796) else if t 2 = 1 then (if t 3 = 0 then 1011 else if t 3 = 1 then 989 else 369) else (if t 3 = 0 then 4059 else if t 3 = 1 then 168 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1374 else if t 3 = 1 then 1795 else 1799) else if t 2 = 1 then (if t 3 = 0 then 998 else if t 3 = 1 then 943 else 951) else (if t 3 = 0 then 98 else if t 3 = 1 then 947 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 1375 else if t 3 = 1 then 1796 else 1800) else if t 2 = 1 then (if t 3 = 0 then 999 else if t 3 = 1 then 944 else 952) else (if t 3 = 0 then 99 else if t 3 = 1 then 948 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3762 else (if jt.2.val < 2 then 3793 else 3773)) else (if jt.2.val < 4 then 3792 else (if jt.2.val < 5 then 3794 else 3770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4248 else (if jt.2.val < 2 then 4258 else 4250)) else (if jt.2.val < 4 then 4257 else (if jt.2.val < 5 then 4259 else 4245)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1791 else (if jt.2.val < 2 then 1793 else 1798)) else (if jt.2.val < 4 then 1792 else (if jt.2.val < 5 then 1797 else 1794))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 911 else (if jt.2.val < 2 then 983 else 913)) else (if jt.2.val < 4 then 981 else (if jt.2.val < 5 then 982 else 908)))))

checked_coverage fastCoverage0317 pairing0317 template0317 witness0317

theorem coverage0317 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0317) (maskBits m))
    cores template0317 witness0317 := by
  rw [← coresFast_eq]
  exact fastCoverage0317

theorem coverageSize0317 : ∀ q : Pattern,
    (cores (witness0317 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0317 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0317
#print axioms coverageSize0317

noncomputable def pairing0318 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0318 : List (Fin 4935) := templateData0318

noncomputable def witness0318 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1572 else 1856) else if t 2 = 1 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1570 else 1853) else (if t 3 = 0 then 67 else if t 3 = 1 then 855 else 878)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1564 else 1616) else if t 2 = 1 then (if t 3 = 0 then 1566 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 62 else if t 3 = 1 then 1589 else 1611)) else (if t 2 = 0 then (if t 3 = 0 then 2898 else if t 3 = 1 then 2630 else 2649) else if t 2 = 1 then (if t 3 = 0 then 2482 else if t 3 = 1 then 3219 else 3227) else (if t 3 = 0 then 4060 else if t 3 = 1 then 3953 else 3959))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1571 else 1854) else if t 2 = 1 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1569 else 1851) else (if t 3 = 0 then 66 else if t 3 = 1 then 854 else 876)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1563 else 1614) else if t 2 = 1 then (if t 3 = 0 then 1565 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 61 else if t 3 = 1 then 1588 else 1604)) else (if t 2 = 0 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1581 else 1615) else if t 2 = 1 then (if t 3 = 0 then 1582 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 69 else if t 3 = 1 then 1591 else 1605))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 660 else 4061) else if t 2 = 1 then (if t 3 = 0 then 468 else if t 3 = 1 then 1070 else 1092) else (if t 3 = 0 then 2739 else if t 3 = 1 then 1598 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1133 else if t 3 = 1 then 655 else 686) else if t 2 = 1 then (if t 3 = 0 then 463 else if t 3 = 1 then 1592 else 1606) else (if t 3 = 0 then 1848 else if t 3 = 1 then 1596 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 1136 else if t 3 = 1 then 663 else 687) else if t 2 = 1 then (if t 3 = 0 then 471 else if t 3 = 1 then 1595 else 1607) else (if t 3 = 0 then 1850 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3870 else (if jt.2.val < 2 then 3957 else 3894)) else (if jt.2.val < 4 then 3955 else (if jt.2.val < 5 then 3956 else 3874))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3578 else (if jt.2.val < 2 then 3596 else 3581)) else (if jt.2.val < 4 then 3594 else (if jt.2.val < 5 then 3595 else 3575)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1466 else (if jt.2.val < 2 then 1590 else 1469)) else (if jt.2.val < 4 then 1559 else (if jt.2.val < 5 then 1560 else 1457))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1839 else (if jt.2.val < 2 then 1841 else 1846)) else (if jt.2.val < 4 then 1840 else (if jt.2.val < 5 then 1845 else 1844)))))

checked_coverage fastCoverage0318 pairing0318 template0318 witness0318

theorem coverage0318 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0318) (maskBits m))
    cores template0318 witness0318 := by
  rw [← coresFast_eq]
  exact fastCoverage0318

theorem coverageSize0318 : ∀ q : Pattern,
    (cores (witness0318 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0318 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0318
#print axioms coverageSize0318

noncomputable def pairing0319 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0319 : List (Fin 4935) := templateData0319

noncomputable def witness0319 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1904 else 1676) else if t 2 = 1 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1901 else 1670) else (if t 3 = 0 then 900 else if t 3 = 1 then 158 else 159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1891 else 1892) else if t 2 = 1 then (if t 3 = 0 then 1907 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 94 else if t 3 = 1 then 1877 else 1881)) else (if t 2 = 0 then (if t 3 = 0 then 2506 else if t 3 = 1 then 2938 else 2940) else if t 2 = 1 then (if t 3 = 0 then 2500 else if t 3 = 1 then 3348 else 3351) else (if t 3 = 0 then 3943 else if t 3 = 1 then 4064 else 4066))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1902 else 1673) else if t 2 = 1 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1899 else 1667) else (if t 3 = 0 then 899 else if t 3 = 1 then 152 else 154)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1887 else 1889) else if t 2 = 1 then (if t 3 = 0 then 1905 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 90 else if t 3 = 1 then 1861 else 1869)) else (if t 2 = 0 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1888 else 1890) else if t 2 = 1 then (if t 3 = 0 then 1906 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 91 else if t 3 = 1 then 1862 else 1870))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 572 else 3966) else if t 2 = 1 then (if t 3 = 0 then 1115 else if t 3 = 1 then 548 else 550) else (if t 3 = 0 then 2986 else if t 3 = 1 then 1535 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 504 else if t 3 = 1 then 1181 else 1185) else if t 2 = 1 then (if t 3 = 0 then 492 else if t 3 = 1 then 1863 else 1871) else (if t 3 = 0 then 1521 else if t 3 = 1 then 1865 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 505 else if t 3 = 1 then 1182 else 1186) else if t 2 = 1 then (if t 3 = 0 then 493 else if t 3 = 1 then 1864 else 1872) else (if t 3 = 0 then 1522 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3972 else (if jt.2.val < 2 then 4063 else 3994)) else (if jt.2.val < 4 then 4062 else (if jt.2.val < 5 then 4065 else 3990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3585 else (if jt.2.val < 2 then 3598 else 3587)) else (if jt.2.val < 4 then 3597 else (if jt.2.val < 5 then 3599 else 3582)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1794 else (if jt.2.val < 2 then 1885 else 1798)) else (if jt.2.val < 4 then 1884 else (if jt.2.val < 5 then 1886 else 1791))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1844 else (if jt.2.val < 2 then 1895 else 1846)) else (if jt.2.val < 4 then 1893 else (if jt.2.val < 5 then 1894 else 1839)))))

checked_coverage fastCoverage0319 pairing0319 template0319 witness0319

theorem coverage0319 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0319) (maskBits m))
    cores template0319 witness0319 := by
  rw [← coresFast_eq]
  exact fastCoverage0319

theorem coverageSize0319 : ∀ q : Pattern,
    (cores (witness0319 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0319 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0319
#print axioms coverageSize0319

end Crown.CertificateData
