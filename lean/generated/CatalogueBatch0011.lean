import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0010

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0400 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0400 : List (Fin 4935) := templateData0400

noncomputable def witness0400 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 3925) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2750) else (if t 3 = 0 then 2741 else if t 3 = 1 then 2740 else 2985)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 538) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 537) else (if t 3 = 0 then 490 else if t 3 = 1 then 488 else 1114)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1879 else 1538) else if t 2 = 1 then (if t 3 = 0 then 1882 else if t 3 = 1 then 1878 else 554) else (if t 3 = 0 then 497 else if t 3 = 1 then 496 else 1116))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 243) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 242) else (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 925)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2614) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4015) else (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4023)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2627) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4016) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4020 else 4024))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 820 else 275) else if t 2 = 1 then (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 274) else (if t 3 = 0 then 1502 else if t 3 = 1 then 403 else 1789)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2635) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4017) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4021 else 4025)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2841 else 2639) else if t 2 = 1 then (if t 3 = 0 then 4004 else if t 3 = 1 then 4003 else 4018) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4022 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4431 else (if jt.2.val < 2 then 4441 else 4442)) else (if jt.2.val < 4 then 4438 else (if jt.2.val < 5 then 4440 else 4439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4432 else (if jt.2.val < 2 then 4436 else 4437)) else (if jt.2.val < 4 then 4433 else (if jt.2.val < 5 then 4435 else 4434)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4068 else (if jt.2.val < 2 then 4074 else 4079)) else (if jt.2.val < 4 then 4073 else (if jt.2.val < 5 then 4078 else 4077))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4069 else (if jt.2.val < 2 then 4075 else 4076)) else (if jt.2.val < 4 then 4070 else (if jt.2.val < 5 then 4072 else 4071)))))

checked_coverage fastCoverage0400 pairing0400 template0400 witness0400

theorem coverage0400 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0400) (maskBits m))
    cores template0400 witness0400 := by
  rw [← coresFast_eq]
  exact fastCoverage0400

theorem coverageSize0400 : ∀ q : Pattern,
    (cores (witness0400 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0400 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0400
#print axioms coverageSize0400

noncomputable def pairing0401 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0401 : List (Fin 4935) := templateData0401

noncomputable def witness0401 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4044) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2749) else (if t 3 = 0 then 2981 else if t 3 = 1 then 2980 else 2762)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 536) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 535) else (if t 3 = 0 then 1090 else if t 3 = 1 then 1078 else 595)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1648 else 1835) else if t 2 = 1 then (if t 3 = 0 then 1651 else if t 3 = 1 then 1647 else 553) else (if t 3 = 0 then 1094 else if t 3 = 1 then 1080 else 597))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 241) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 240) else (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 301)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2613) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3843) else (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3856)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2626) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3846) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3853 else 3857))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 33 else 920) else if t 2 = 1 then (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 919) else (if t 3 = 0 then 1808 else if t 3 = 1 then 97 else 1477)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2899) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3848) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3854 else 3858)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2474 else 2901) else if t 2 = 1 then (if t 3 = 0 then 3838 else if t 3 = 1 then 3837 else 3850) else (if t 3 = 0 then 4040 else if t 3 = 1 then 3855 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4395 else (if jt.2.val < 2 then 4405 else 4406)) else (if jt.2.val < 4 then 4402 else (if jt.2.val < 5 then 4404 else 4403))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4396 else (if jt.2.val < 2 then 4400 else 4401)) else (if jt.2.val < 4 then 4397 else (if jt.2.val < 5 then 4399 else 4398)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4082 else (if jt.2.val < 2 then 4084 else 4088)) else (if jt.2.val < 4 then 4083 else (if jt.2.val < 5 then 4087 else 4086))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4071 else (if jt.2.val < 2 then 4085 else 4076)) else (if jt.2.val < 4 then 4080 else (if jt.2.val < 5 then 4081 else 4069)))))

checked_coverage fastCoverage0401 pairing0401 template0401 witness0401

theorem coverage0401 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0401) (maskBits m))
    cores template0401 witness0401 := by
  rw [← coresFast_eq]
  exact fastCoverage0401

theorem coverageSize0401 : ∀ q : Pattern,
    (cores (witness0401 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0401 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0401
#print axioms coverageSize0401

noncomputable def pairing0402 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0402 : List (Fin 4935) := templateData0402

noncomputable def witness0402 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2710 else 2906) else if t 2 = 1 then (if t 3 = 0 then 2705 else if t 3 = 1 then 2688 else 2690) else (if t 3 = 0 then 4036 else if t 3 = 1 then 3929 else 3930)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2708 else 2107) else if t 2 = 1 then (if t 3 = 0 then 2703 else if t 3 = 1 then 2682 else 2090) else (if t 3 = 0 then 475 else if t 3 = 1 then 445 else 450)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 87 else 904) else if t 2 = 1 then (if t 3 = 0 then 73 else if t 3 = 1 then 43 else 48) else (if t 3 = 0 then 1849 else if t 3 = 1 then 1507 else 1510))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2709 else 2227) else if t 2 = 1 then (if t 3 = 0 then 2704 else if t 3 = 1 then 2685 else 2212) else (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 353)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2707 else 2902) else if t 2 = 1 then (if t 3 = 0 then 2695 else if t 3 = 1 then 2664 else 2674) else (if t 3 = 0 then 2696 else if t 3 = 1 then 2666 else 2675)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2717 else 2904) else if t 2 = 1 then (if t 3 = 0 then 2697 else if t 3 = 1 then 2668 else 2676) else (if t 3 = 0 then 2698 else if t 3 = 1 then 2669 else 2677))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1686 else 1855) else if t 2 = 1 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1657 else 1659) else (if t 3 = 0 then 895 else if t 3 = 1 then 351 else 355)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2721 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2878 else if t 3 = 1 then 2670 else 2678) else (if t 3 = 0 then 2879 else if t 3 = 1 then 2671 else 2679)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2724 else 4045) else if t 2 = 1 then (if t 3 = 0 then 2880 else if t 3 = 1 then 2672 else 2680) else (if t 3 = 0 then 2881 else if t 3 = 1 then 2673 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4344 else (if jt.2.val < 2 then 4346 else 4349)) else (if jt.2.val < 4 then 4345 else (if jt.2.val < 5 then 4348 else 4347))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2658 else (if jt.2.val < 2 then 2660 else 2687)) else (if jt.2.val < 4 then 2659 else (if jt.2.val < 5 then 2686 else 2667)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4077 else (if jt.2.val < 2 then 4091 else 4079)) else (if jt.2.val < 4 then 4089 else (if jt.2.val < 5 then 4090 else 4068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3029 else (if jt.2.val < 2 then 3031 else 3035)) else (if jt.2.val < 4 then 3030 else (if jt.2.val < 5 then 3034 else 3032)))))

checked_coverage fastCoverage0402 pairing0402 template0402 witness0402

theorem coverage0402 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0402) (maskBits m))
    cores template0402 witness0402 := by
  rw [← coresFast_eq]
  exact fastCoverage0402

theorem coverageSize0402 : ∀ q : Pattern,
    (cores (witness0402 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0402 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0402
#print axioms coverageSize0402

noncomputable def pairing0403 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0403 : List (Fin 4935) := templateData0403

noncomputable def witness0403 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2960 else 2654) else if t 2 = 1 then (if t 3 = 0 then 2953 else if t 3 = 1 then 2937 else 2939) else (if t 3 = 0 then 3905 else if t 3 = 1 then 4046 else 4047)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2958 else 2104) else if t 2 = 1 then (if t 3 = 0 then 2951 else if t 3 = 1 then 2931 else 2082) else (if t 3 = 0 then 1075 else if t 3 = 1 then 1046 else 1051)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 868 else 205) else if t 2 = 1 then (if t 3 = 0 then 859 else if t 3 = 1 then 830 else 835) else (if t 3 = 0 then 1599 else if t 3 = 1 then 1813 else 1816))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2959 else 2224) else if t 2 = 1 then (if t 3 = 0 then 2952 else if t 3 = 1 then 2934 else 2206) else (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 974)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2954 else 2650) else if t 2 = 1 then (if t 3 = 0 then 2947 else if t 3 = 1 then 2913 else 2923) else (if t 3 = 0 then 2948 else if t 3 = 1 then 2915 else 2924)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2956 else 2652) else if t 2 = 1 then (if t 3 = 0 then 2949 else if t 3 = 1 then 2917 else 2925) else (if t 3 = 0 then 2950 else if t 3 = 1 then 2918 else 2926))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1909 else 1621) else if t 2 = 1 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1888 else 1890) else (if t 3 = 0 then 177 else if t 3 = 1 then 972 else 976)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2502 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2554 else if t 3 = 1 then 2919 else 2927) else (if t 3 = 0 then 2555 else if t 3 = 1 then 2920 else 2928)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2504 else 3928) else if t 2 = 1 then (if t 3 = 0 then 2556 else if t 3 = 1 then 2921 else 2929) else (if t 3 = 0 then 2557 else if t 3 = 1 then 2922 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4380 else (if jt.2.val < 2 then 4382 else 4385)) else (if jt.2.val < 4 then 4381 else (if jt.2.val < 5 then 4384 else 4383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2907 else (if jt.2.val < 2 then 2909 else 2936)) else (if jt.2.val < 4 then 2908 else (if jt.2.val < 5 then 2935 else 2916)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4086 else (if jt.2.val < 2 then 4094 else 4088)) else (if jt.2.val < 4 then 4092 else (if jt.2.val < 5 then 4093 else 4082))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3032 else (if jt.2.val < 2 then 3039 else 3035)) else (if jt.2.val < 4 then 3038 else (if jt.2.val < 5 then 3041 else 3029)))))

checked_coverage fastCoverage0403 pairing0403 template0403 witness0403

theorem coverage0403 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0403) (maskBits m))
    cores template0403 witness0403 := by
  rw [← coresFast_eq]
  exact fastCoverage0403

theorem coverageSize0403 : ∀ q : Pattern,
    (cores (witness0403 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0403 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0403
#print axioms coverageSize0403

noncomputable def pairing0404 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0404 : List (Fin 4935) := templateData0404

noncomputable def witness0404 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 1462) else if t 2 = 1 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 256) else (if t 3 = 0 then 396 else if t 3 = 1 then 394 else 929)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 646) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1747) else (if t 3 = 0 then 1450 else if t 3 = 1 then 1753 else 1762)) else (if t 2 = 0 then (if t 3 = 0 then 4066 else if t 3 = 1 then 4064 else 3946) else if t 2 = 1 then (if t 3 = 0 then 3351 else if t 3 = 1 then 3348 else 2546) else (if t 3 = 0 then 2501 else if t 3 = 1 then 2500 else 2884))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 1461) else if t 2 = 1 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 255) else (if t 3 = 0 then 395 else if t 3 = 1 then 393 else 926)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 645) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1746) else (if t 3 = 0 then 1449 else if t 3 = 1 then 1752 else 1758)) else (if t 2 = 0 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 651) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1748) else (if t 3 = 0 then 1451 else if t 3 = 1 then 1754 else 1759))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 2145 else 2777) else if t 2 = 1 then (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 278) else (if t 3 = 0 then 3952 else if t 3 = 1 then 405 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 668) else if t 2 = 1 then (if t 3 = 0 then 1732 else if t 3 = 1 then 1729 else 1749) else (if t 3 = 0 then 1452 else if t 3 = 1 then 1755 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 1057 else if t 3 = 1 then 1055 else 671) else if t 2 = 1 then (if t 3 = 0 then 1735 else if t 3 = 1 then 1734 else 1751) else (if t 3 = 0 then 1454 else if t 3 = 1 then 1757 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4380 else (if jt.2.val < 2 then 4391 else 4385)) else (if jt.2.val < 4 then 4389 else (if jt.2.val < 5 then 4390 else 4383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4434 else (if jt.2.val < 2 then 4445 else 4437)) else (if jt.2.val < 4 then 4443 else (if jt.2.val < 5 then 4444 else 4432)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2376 else (if jt.2.val < 2 then 2378 else 2381)) else (if jt.2.val < 4 then 2377 else (if jt.2.val < 5 then 2380 else 2379))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1918 else (if jt.2.val < 2 then 1924 else 1925)) else (if jt.2.val < 4 then 1919 else (if jt.2.val < 5 then 1921 else 1920)))))

checked_coverage fastCoverage0404 pairing0404 template0404 witness0404

theorem coverage0404 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0404) (maskBits m))
    cores template0404 witness0404 := by
  rw [← coresFast_eq]
  exact fastCoverage0404

theorem coverageSize0404 : ∀ q : Pattern,
    (cores (witness0404 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0404 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0404
#print axioms coverageSize0404

noncomputable def pairing0405 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0405 : List (Fin 4935) := templateData0405

noncomputable def witness0405 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 1786) else if t 2 = 1 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 254) else (if t 3 = 0 then 1012 else if t 3 = 1 then 1001 else 305)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 644) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1350) else (if t 3 = 0 then 1777 else if t 3 = 1 then 1370 else 1372)) else (if t 2 = 0 then (if t 3 = 0 then 3965 else if t 3 = 1 then 3963 else 4058) else if t 2 = 1 then (if t 3 = 0 then 3235 else if t 3 = 1 then 3232 else 2545) else (if t 3 = 0 then 2868 else if t 3 = 1 then 2860 else 2577))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 1785) else if t 2 = 1 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 253) else (if t 3 = 0 then 1011 else if t 3 = 1 then 998 else 302)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 643) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1349) else (if t 3 = 0 then 1776 else if t 3 = 1 then 1362 else 1366)) else (if t 2 = 0 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 650) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1354) else (if t 3 = 0 then 1778 else if t 3 = 1 then 1363 else 1367))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 2124 else 2988) else if t 2 = 1 then (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 921) else (if t 3 = 0 then 4059 else if t 3 = 1 then 98 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 1137) else if t 2 = 1 then (if t 3 = 0 then 1341 else if t 3 = 1 then 1338 else 1356) else (if t 3 = 0 then 1779 else if t 3 = 1 then 1364 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 456 else if t 3 = 1 then 454 else 1139) else if t 2 = 1 then (if t 3 = 0 then 1344 else if t 3 = 1 then 1343 else 1360) else (if t 3 = 0 then 1781 else if t 3 = 1 then 1365 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4344 else (if jt.2.val < 2 then 4355 else 4349)) else (if jt.2.val < 4 then 4353 else (if jt.2.val < 5 then 4354 else 4347))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4398 else (if jt.2.val < 2 then 4421 else 4401)) else (if jt.2.val < 4 then 4419 else (if jt.2.val < 5 then 4420 else 4396)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2382 else (if jt.2.val < 2 then 2384 else 2387)) else (if jt.2.val < 4 then 2383 else (if jt.2.val < 5 then 2386 else 2385))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1920 else (if jt.2.val < 2 then 1934 else 1925)) else (if jt.2.val < 4 then 1929 else (if jt.2.val < 5 then 1930 else 1918)))))

checked_coverage fastCoverage0405 pairing0405 template0405 witness0405

theorem coverage0405 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0405) (maskBits m))
    cores template0405 witness0405 := by
  rw [← coresFast_eq]
  exact fastCoverage0405

theorem coverageSize0405 : ∀ q : Pattern,
    (cores (witness0405 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0405 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0405
#print axioms coverageSize0405

noncomputable def pairing0406 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0406 : List (Fin 4935) := templateData0406

noncomputable def witness0406 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 768 else 1148) else if t 2 = 1 then (if t 3 = 0 then 763 else if t 3 = 1 then 740 else 742) else (if t 3 = 0 then 1775 else if t 3 = 1 then 1489 else 1490)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 770 else if t 3 = 1 then 766 else 1144) else if t 2 = 1 then (if t 3 = 0 then 755 else if t 3 = 1 then 720 else 725) else (if t 3 = 0 then 756 else if t 3 = 1 then 722 else 726)) else (if t 2 = 0 then (if t 3 = 0 then 2798 else if t 3 = 1 then 2797 else 2989) else if t 2 = 1 then (if t 3 = 0 then 2794 else if t 3 = 1 then 2785 else 2788) else (if t 3 = 0 then 4060 else if t 3 = 1 then 3939 else 3941))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 767 else 1146) else if t 2 = 1 then (if t 3 = 0 then 759 else if t 3 = 1 then 732 else 736) else (if t 3 = 0 then 1773 else if t 3 = 1 then 1483 else 1487)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 769 else if t 3 = 1 then 765 else 1140) else if t 2 = 1 then (if t 3 = 0 then 747 else if t 3 = 1 then 704 else 712) else (if t 3 = 0 then 749 else if t 3 = 1 then 706 else 714)) else (if t 2 = 0 then (if t 3 = 0 then 775 else if t 3 = 1 then 773 else 1141) else if t 2 = 1 then (if t 3 = 0 then 748 else if t 3 = 1 then 705 else 713) else (if t 3 = 0 then 750 else if t 3 = 1 then 707 else 715))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 785 else 4061) else if t 2 = 1 then (if t 3 = 0 then 1110 else if t 3 = 1 then 734 else 738) else (if t 3 = 0 then 2984 else if t 3 = 1 then 2157 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1548 else if t 3 = 1 then 783 else 1824) else if t 2 = 1 then (if t 3 = 0 then 1104 else if t 3 = 1 then 708 else 716) else (if t 3 = 0 then 1106 else if t 3 = 1 then 710 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 1550 else if t 3 = 1 then 787 else 1825) else if t 2 = 1 then (if t 3 = 0 then 1105 else if t 3 = 1 then 709 else 717) else (if t 3 = 0 then 1107 else if t 3 = 1 then 711 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4395 else (if jt.2.val < 2 then 4429 else 4406)) else (if jt.2.val < 4 then 4428 else (if jt.2.val < 5 then 4430 else 4403))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2667 else (if jt.2.val < 2 then 2791 else 2687)) else (if jt.2.val < 4 then 2790 else (if jt.2.val < 5 then 2792 else 2658)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2379 else (if jt.2.val < 2 then 2402 else 2381)) else (if jt.2.val < 4 then 2400 else (if jt.2.val < 5 then 2401 else 2376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1281 else (if jt.2.val < 2 then 1283 else 1289)) else (if jt.2.val < 4 then 1282 else (if jt.2.val < 5 then 1288 else 1286)))))

checked_coverage fastCoverage0406 pairing0406 template0406 witness0406

theorem coverage0406 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0406) (maskBits m))
    cores template0406 witness0406 := by
  rw [← coresFast_eq]
  exact fastCoverage0406

theorem coverageSize0406 : ∀ q : Pattern,
    (cores (witness0406 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0406 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0406
#print axioms coverageSize0406

noncomputable def pairing0407 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0407 : List (Fin 4935) := templateData0407

noncomputable def witness0407 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1214 else 698) else if t 2 = 1 then (if t 3 = 0 then 1205 else if t 3 = 1 then 1187 else 1189) else (if t 3 = 0 then 1433 else if t 3 = 1 then 1801 else 1802)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1210 else 694) else if t 2 = 1 then (if t 3 = 0 then 1201 else if t 3 = 1 then 1167 else 1172) else (if t 3 = 0 then 1202 else if t 3 = 1 then 1169 else 1173)) else (if t 2 = 0 then (if t 3 = 0 then 3004 else if t 3 = 1 then 3003 else 2781) else if t 2 = 1 then (if t 3 = 0 then 3002 else if t 3 = 1 then 2993 else 2996) else (if t 3 = 0 then 3954 else if t 3 = 1 then 4054 else 4056))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1212 else 696) else if t 2 = 1 then (if t 3 = 0 then 1203 else if t 3 = 1 then 1179 else 1183) else (if t 3 = 0 then 1430 else if t 3 = 1 then 1795 else 1799)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1206 else 690) else if t 2 = 1 then (if t 3 = 0 then 1197 else if t 3 = 1 then 1151 else 1159) else (if t 3 = 0 then 1199 else if t 3 = 1 then 1153 else 1161)) else (if t 2 = 0 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1207 else 691) else if t 2 = 1 then (if t 3 = 0 then 1198 else if t 3 = 1 then 1152 else 1160) else (if t 3 = 0 then 1200 else if t 3 = 1 then 1154 else 1162))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 504 else 3960) else if t 2 = 1 then (if t 3 = 0 then 572 else if t 3 = 1 then 1181 else 1185) else (if t 3 = 0 then 2758 else if t 3 = 1 then 2136 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1836 else if t 3 = 1 then 498 else 1524) else if t 2 = 1 then (if t 3 = 0 then 562 else if t 3 = 1 then 1155 else 1163) else (if t 3 = 0 then 564 else if t 3 = 1 then 1157 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 1838 else if t 3 = 1 then 499 else 1525) else if t 2 = 1 then (if t 3 = 0 then 563 else if t 3 = 1 then 1156 else 1164) else (if t 3 = 0 then 565 else if t 3 = 1 then 1158 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4431 else (if jt.2.val < 2 then 4447 else 4442)) else (if jt.2.val < 4 then 4446 else (if jt.2.val < 5 then 4448 else 4439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2916 else (if jt.2.val < 2 then 2999 else 2936)) else (if jt.2.val < 4 then 2998 else (if jt.2.val < 5 then 3000 else 2907)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2385 else (if jt.2.val < 2 then 2405 else 2387)) else (if jt.2.val < 4 then 2403 else (if jt.2.val < 5 then 2404 else 2382))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1286 else (if jt.2.val < 2 then 1291 else 1289)) else (if jt.2.val < 4 then 1290 else (if jt.2.val < 5 then 1295 else 1281)))))

checked_coverage fastCoverage0407 pairing0407 template0407 witness0407

theorem coverage0407 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0407) (maskBits m))
    cores template0407 witness0407 := by
  rw [← coresFast_eq]
  exact fastCoverage0407

theorem coverageSize0407 : ∀ q : Pattern,
    (cores (witness0407 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0407 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0407
#print axioms coverageSize0407

noncomputable def pairing0408 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0408 : List (Fin 4935) := templateData0408

noncomputable def witness0408 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 3860) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2980) else (if t 3 = 0 then 3236 else if t 3 = 1 then 3234 else 3242)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 1084) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 1078) else (if t 3 = 0 then 1651 else if t 3 = 1 then 1647 else 1080)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 536 else 601) else if t 2 = 1 then (if t 3 = 0 then 539 else if t 3 = 1 then 535 else 595) else (if t 3 = 0 then 555 else if t 3 = 1 then 553 else 597))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 1003) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 997) else (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 999)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2955) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3852) else (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3853)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2651) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3856) else (if t 3 = 0 then 3847 else if t 3 = 1 then 3846 else 3857))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 33 else 103) else if t 2 = 1 then (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 97) else (if t 3 = 0 then 54 else if t 3 = 1 then 52 else 99)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2503) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3854) else (if t 3 = 0 then 3838 else if t 3 = 1 then 3837 else 3855)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2899 else 3184) else if t 2 = 1 then (if t 3 = 0 then 3849 else if t 3 = 1 then 3848 else 3858) else (if t 3 = 0 then 3851 else if t 3 = 1 then 3850 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4395 else (if jt.2.val < 2 then 4405 else 4406)) else (if jt.2.val < 4 then 4402 else (if jt.2.val < 5 then 4404 else 4403))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4095 else (if jt.2.val < 2 then 4105 else 4106)) else (if jt.2.val < 4 then 4102 else (if jt.2.val < 5 then 4104 else 4103)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4449 else (if jt.2.val < 2 then 4453 else 4454)) else (if jt.2.val < 4 then 4450 else (if jt.2.val < 5 then 4452 else 4451))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3798 else (if jt.2.val < 2 then 3800 else 3803)) else (if jt.2.val < 4 then 3799 else (if jt.2.val < 5 then 3802 else 3801)))))

checked_coverage fastCoverage0408 pairing0408 template0408 witness0408

theorem coverage0408 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0408) (maskBits m))
    cores template0408 witness0408 := by
  rw [← coresFast_eq]
  exact fastCoverage0408

theorem coverageSize0408 : ∀ q : Pattern,
    (cores (witness0408 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0408 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0408
#print axioms coverageSize0408

noncomputable def pairing0409 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0409 : List (Fin 4935) := templateData0409

noncomputable def witness0409 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 3905) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2979) else (if t 3 = 0 then 3228 else if t 3 = 1 then 3225 else 3226)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 1075) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 1069) else (if t 3 = 0 then 1612 else if t 3 = 1 then 1593 else 1071)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 475 else 477) else if t 2 = 1 then (if t 3 = 0 then 490 else if t 3 = 1 then 462 else 467) else (if t 3 = 0 then 497 else if t 3 = 1 then 464 else 469))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 994) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 988) else (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 990)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2948) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3884) else (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3885)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2700) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3888) else (if t 3 = 0 then 3918 else if t 3 = 1 then 3881 else 3889))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 175 else 177) else if t 2 = 1 then (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 167) else (if t 3 = 0 then 197 else if t 3 = 1 then 163 else 169)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2555) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3886) else (if t 3 = 0 then 3916 else if t 3 = 1 then 3878 else 3887)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2879 else 3197) else if t 2 = 1 then (if t 3 = 0 then 3919 else if t 3 = 1 then 3882 else 3890) else (if t 3 = 0 then 3920 else if t 3 = 1 then 3883 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4407 else (if jt.2.val < 2 then 4409 else 4416)) else (if jt.2.val < 4 then 4408 else (if jt.2.val < 5 then 4415 else 4414))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4107 else (if jt.2.val < 2 then 4109 else 4116)) else (if jt.2.val < 4 then 4108 else (if jt.2.val < 5 then 4115 else 4114)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4455 else (if jt.2.val < 2 then 4457 else 4460)) else (if jt.2.val < 4 then 4456 else (if jt.2.val < 5 then 4459 else 4458))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3801 else (if jt.2.val < 2 then 3863 else 3803)) else (if jt.2.val < 4 then 3861 else (if jt.2.val < 5 then 3862 else 3798)))))

checked_coverage fastCoverage0409 pairing0409 template0409 witness0409

theorem coverage0409 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0409) (maskBits m))
    cores template0409 witness0409 := by
  rw [← coresFast_eq]
  exact fastCoverage0409

theorem coverageSize0409 : ∀ q : Pattern,
    (cores (witness0409 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0409 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0409
#print axioms coverageSize0409

noncomputable def pairing0410 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0410 : List (Fin 4935) := templateData0410

noncomputable def witness0410 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3106) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 3003) else (if t 3 = 0 then 3965 else if t 3 = 1 then 3963 else 3967)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 868) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 862) else (if t 3 = 0 then 1650 else if t 3 = 1 then 1646 else 864)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 141 else 205) else if t 2 = 1 then (if t 3 = 0 then 144 else if t 3 = 1 then 140 else 199) else (if t 3 = 0 then 159 else if t 3 = 1 then 157 else 201))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 1213) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 1207) else (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 1209)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2956) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3098) else (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3099)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2622 else 2652) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3089 else 3102) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3092 else 3103))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 439 else 505) else if t 2 = 1 then (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 499) else (if t 3 = 0 then 456 else if t 3 = 1 then 454 else 501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2504) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3080 else 3100) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3083 else 3101)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2900 else 3928) else if t 2 = 1 then (if t 3 = 0 then 3095 else if t 3 = 1 then 3094 else 3104) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3096 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4314 else (if jt.2.val < 2 then 4324 else 4325)) else (if jt.2.val < 4 then 4321 else (if jt.2.val < 5 then 4323 else 4322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3384 else (if jt.2.val < 2 then 3394 else 3395)) else (if jt.2.val < 4 then 3391 else (if jt.2.val < 5 then 3393 else 3392)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4451 else (if jt.2.val < 2 then 4463 else 4454)) else (if jt.2.val < 4 then 4461 else (if jt.2.val < 5 then 4462 else 4449))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3042 else (if jt.2.val < 2 then 3044 else 3047)) else (if jt.2.val < 4 then 3043 else (if jt.2.val < 5 then 3046 else 3045)))))

checked_coverage fastCoverage0410 pairing0410 template0410 witness0410

theorem coverage0410 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0410) (maskBits m))
    cores template0410 witness0410 := by
  rw [← coresFast_eq]
  exact fastCoverage0410

theorem coverageSize0410 : ∀ q : Pattern,
    (cores (witness0410 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0410 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0410
#print axioms coverageSize0410

noncomputable def pairing0411 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0411 : List (Fin 4935) := templateData0411

noncomputable def witness0411 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3152) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 3002) else (if t 3 = 0 then 3959 else if t 3 = 1 then 3953 else 3954)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 859) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 853) else (if t 3 = 0 then 1611 else if t 3 = 1 then 1589 else 855)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 73 else 75) else if t 2 = 1 then (if t 3 = 0 then 88 else if t 3 = 1 then 60 else 65) else (if t 3 = 0 then 95 else if t 3 = 1 then 62 else 67))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 1204) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 1198) else (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 1200)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2949) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3130) else (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3131)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2697 else 2701) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3126 else 3134) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3127 else 3135))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 571 else 573) else if t 2 = 1 then (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 563) else (if t 3 = 0 then 593 else if t 3 = 1 then 559 else 565)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2556) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3123 else 3132) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3124 else 3133)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2880 else 3934) else if t 2 = 1 then (if t 3 = 0 then 3167 else if t 3 = 1 then 3128 else 3136) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3129 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4326 else (if jt.2.val < 2 then 4328 else 4335)) else (if jt.2.val < 4 then 4327 else (if jt.2.val < 5 then 4334 else 4333))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3396 else (if jt.2.val < 2 then 3398 else 3405)) else (if jt.2.val < 4 then 3397 else (if jt.2.val < 5 then 3404 else 3403)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4458 else (if jt.2.val < 2 then 4465 else 4460)) else (if jt.2.val < 4 then 4464 else (if jt.2.val < 5 then 4466 else 4455))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3045 else (if jt.2.val < 2 then 3109 else 3047)) else (if jt.2.val < 4 then 3107 else (if jt.2.val < 5 then 3108 else 3042)))))

checked_coverage fastCoverage0411 pairing0411 template0411 witness0411

theorem coverage0411 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0411) (maskBits m))
    cores template0411 witness0411 := by
  rw [← coresFast_eq]
  exact fastCoverage0411

theorem coverageSize0411 : ∀ q : Pattern,
    (cores (witness0411 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0411 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0411
#print axioms coverageSize0411

noncomputable def pairing0412 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0412 : List (Fin 4935) := templateData0412

noncomputable def witness0412 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 224 else 308) else if t 2 = 1 then (if t 3 = 0 then 230 else if t 3 = 1 then 222 else 304) else (if t 3 = 0 then 258 else if t 3 = 1 then 254 else 305)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 228 else if t 3 = 1 then 220 else 298) else if t 2 = 1 then (if t 3 = 0 then 226 else if t 3 = 1 then 218 else 290) else (if t 3 = 0 then 256 else if t 3 = 1 then 251 else 291)) else (if t 2 = 0 then (if t 3 = 0 then 3925 else if t 3 = 1 then 3923 else 3927) else if t 2 = 1 then (if t 3 = 0 then 2750 else if t 3 = 1 then 2747 else 2759) else (if t 3 = 0 then 3210 else if t 3 = 1 then 3209 else 3215))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 223 else 306) else if t 2 = 1 then (if t 3 = 0 then 229 else if t 3 = 1 then 221 else 300) else (if t 3 = 0 then 257 else if t 3 = 1 then 253 else 302)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 227 else if t 3 = 1 then 219 else 294) else if t 2 = 1 then (if t 3 = 0 then 225 else if t 3 = 1 then 217 else 282) else (if t 3 = 0 then 255 else if t 3 = 1 then 250 else 284)) else (if t 2 = 0 then (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 295) else if t 2 = 1 then (if t 3 = 0 then 242 else if t 3 = 1 then 237 else 283) else (if t 3 = 0 then 261 else if t 3 = 1 then 259 else 285))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 917 else 3229) else if t 2 = 1 then (if t 3 = 0 then 1470 else if t 3 = 1 then 915 else 1476) else (if t 3 = 0 then 3942 else if t 3 = 1 then 921 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 270 else if t 3 = 1 then 265 else 296) else if t 2 = 1 then (if t 3 = 0 then 268 else if t 3 = 1 then 263 else 286) else (if t 3 = 0 then 278 else if t 3 = 1 then 276 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 275 else if t 3 = 1 then 273 else 297) else if t 2 = 1 then (if t 3 = 0 then 274 else if t 3 = 1 then 272 else 287) else (if t 3 = 0 then 281 else if t 3 = 1 then 280 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4326 else (if jt.2.val < 2 then 4364 else 4335)) else (if jt.2.val < 4 then 4362 else (if jt.2.val < 5 then 4363 else 4333))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4103 else (if jt.2.val < 2 then 4127 else 4106)) else (if jt.2.val < 4 then 4125 else (if jt.2.val < 5 then 4126 else 4095)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 215 else (if jt.2.val < 2 then 249 else 252)) else (if jt.2.val < 4 then 246 else (if jt.2.val < 5 then 248 else 247))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 207 else (if jt.2.val < 2 then 209 else 212)) else (if jt.2.val < 4 then 208 else (if jt.2.val < 5 then 211 else 210)))))

checked_coverage fastCoverage0412 pairing0412 template0412 witness0412

theorem coverage0412 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0412) (maskBits m))
    cores template0412 witness0412 := by
  rw [← coresFast_eq]
  exact fastCoverage0412

theorem coverageSize0412 : ∀ q : Pattern,
    (cores (witness0412 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0412 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0412
#print axioms coverageSize0412

noncomputable def pairing0413 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0413 : List (Fin 4935) := templateData0413

noncomputable def witness0413 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 379 else 380) else if t 2 = 1 then (if t 3 = 0 then 386 else if t 3 = 1 then 371 else 373) else (if t 3 = 0 then 396 else if t 3 = 1 then 372 else 374)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 384 else if t 3 = 1 then 356 else 358) else if t 2 = 1 then (if t 3 = 0 then 382 else if t 3 = 1 then 336 else 342) else (if t 3 = 0 then 394 else if t 3 = 1 then 339 else 343)) else (if t 2 = 0 then (if t 3 = 0 then 3935 else if t 3 = 1 then 3929 else 3930) else if t 2 = 1 then (if t 3 = 0 then 2740 else if t 3 = 1 then 2728 else 2731) else (if t 3 = 0 then 3207 else if t 3 = 1 then 3203 else 3205))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 375 else 377) else if t 2 = 1 then (if t 3 = 0 then 385 else if t 3 = 1 then 363 else 367) else (if t 3 = 0 then 395 else if t 3 = 1 then 365 else 369)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 383 else if t 3 = 1 then 346 else 352) else if t 2 = 1 then (if t 3 = 0 then 381 else if t 3 = 1 then 318 else 328) else (if t 3 = 0 then 393 else if t 3 = 1 then 322 else 330)) else (if t 2 = 0 then (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 353) else if t 2 = 1 then (if t 3 = 0 then 389 else if t 3 = 1 then 320 else 329) else (if t 3 = 0 then 397 else if t 3 = 1 then 323 else 331))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 894 else 3240) else if t 2 = 1 then (if t 3 = 0 then 1500 else if t 3 = 1 then 888 else 1494) else (if t 3 = 0 then 3952 else if t 3 = 1 then 890 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 401 else if t 3 = 1 then 350 else 354) else if t 2 = 1 then (if t 3 = 0 then 399 else if t 3 = 1 then 324 else 332) else (if t 3 = 0 then 405 else if t 3 = 1 then 326 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 404 else if t 3 = 1 then 351 else 355) else if t 2 = 1 then (if t 3 = 0 then 403 else if t 3 = 1 then 325 else 333) else (if t 3 = 0 then 407 else if t 3 = 1 then 327 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4314 else (if jt.2.val < 2 then 4366 else 4325)) else (if jt.2.val < 4 then 4365 else (if jt.2.val < 5 then 4367 else 4322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4114 else (if jt.2.val < 2 then 4129 else 4116)) else (if jt.2.val < 4 then 4128 else (if jt.2.val < 5 then 4130 else 4107)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 312 else (if jt.2.val < 2 then 314 else 349)) else (if jt.2.val < 4 then 313 else (if jt.2.val < 5 then 348 else 321))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 210 else (if jt.2.val < 2 then 311 else 212)) else (if jt.2.val < 4 then 309 else (if jt.2.val < 5 then 310 else 207)))))

checked_coverage fastCoverage0413 pairing0413 template0413 witness0413

theorem coverage0413 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0413) (maskBits m))
    cores template0413 witness0413 := by
  rw [← coresFast_eq]
  exact fastCoverage0413

theorem coverageSize0413 : ∀ q : Pattern,
    (cores (witness0413 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0413 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0413
#print axioms coverageSize0413

noncomputable def pairing0414 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0414 : List (Fin 4935) := templateData0414

noncomputable def witness0414 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 620 else 698) else if t 2 = 1 then (if t 3 = 0 then 626 else if t 3 = 1 then 618 else 694) else (if t 3 = 0 then 648 else if t 3 = 1 then 644 else 695)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 624 else if t 3 = 1 then 616 else 688) else if t 2 = 1 then (if t 3 = 0 then 622 else if t 3 = 1 then 614 else 680) else (if t 3 = 0 then 646 else if t 3 = 1 then 641 else 681)) else (if t 2 = 0 then (if t 3 = 0 then 3174 else if t 3 = 1 then 3172 else 3182) else if t 2 = 1 then (if t 3 = 0 then 2769 else if t 3 = 1 then 2766 else 2778) else (if t 3 = 0 then 3946 else if t 3 = 1 then 3945 else 3951))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 619 else 696) else if t 2 = 1 then (if t 3 = 0 then 625 else if t 3 = 1 then 617 else 690) else (if t 3 = 0 then 647 else if t 3 = 1 then 643 else 692)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 623 else if t 3 = 1 then 615 else 684) else if t 2 = 1 then (if t 3 = 0 then 621 else if t 3 = 1 then 613 else 672) else (if t 3 = 0 then 645 else if t 3 = 1 then 640 else 674)) else (if t 2 = 0 then (if t 3 = 0 then 637 else if t 3 = 1 then 633 else 685) else if t 2 = 1 then (if t 3 = 0 then 636 else if t 3 = 1 then 632 else 673) else (if t 3 = 0 then 651 else if t 3 = 1 then 649 else 675))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 1133 else 3960) else if t 2 = 1 then (if t 3 = 0 then 1518 else if t 3 = 1 then 1131 else 1524) else (if t 3 = 0 then 3206 else if t 3 = 1 then 1137 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 660 else if t 3 = 1 then 655 else 686) else if t 2 = 1 then (if t 3 = 0 then 658 else if t 3 = 1 then 653 else 676) else (if t 3 = 0 then 668 else if t 3 = 1 then 666 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 665 else if t 3 = 1 then 663 else 687) else if t 2 = 1 then (if t 3 = 0 then 664 else if t 3 = 1 then 662 else 677) else (if t 3 = 0 then 671 else if t 3 = 1 then 670 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4407 else (if jt.2.val < 2 then 4427 else 4416)) else (if jt.2.val < 4 then 4425 else (if jt.2.val < 5 then 4426 else 4414))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3392 else (if jt.2.val < 2 then 3428 else 3395)) else (if jt.2.val < 4 then 3426 else (if jt.2.val < 5 then 3427 else 3384)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 247 else (if jt.2.val < 2 then 642 else 252)) else (if jt.2.val < 4 then 611 else (if jt.2.val < 5 then 612 else 215))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 603 else (if jt.2.val < 2 then 605 else 608)) else (if jt.2.val < 4 then 604 else (if jt.2.val < 5 then 607 else 606)))))

checked_coverage fastCoverage0414 pairing0414 template0414 witness0414

theorem coverage0414 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0414) (maskBits m))
    cores template0414 witness0414 := by
  rw [← coresFast_eq]
  exact fastCoverage0414

theorem coverageSize0414 : ∀ q : Pattern,
    (cores (witness0414 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0414 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0414
#print axioms coverageSize0414

noncomputable def pairing0415 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0415 : List (Fin 4935) := templateData0415

noncomputable def witness0415 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 763 else 764) else if t 2 = 1 then (if t 3 = 0 then 770 else if t 3 = 1 then 755 else 757) else (if t 3 = 0 then 780 else if t 3 = 1 then 756 else 758)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 768 else if t 3 = 1 then 740 else 742) else if t 2 = 1 then (if t 3 = 0 then 766 else if t 3 = 1 then 720 else 725) else (if t 3 = 0 then 778 else if t 3 = 1 then 722 else 726)) else (if t 2 = 0 then (if t 3 = 0 then 3198 else if t 3 = 1 then 3191 else 3192) else if t 2 = 1 then (if t 3 = 0 then 2797 else if t 3 = 1 then 2785 else 2788) else (if t 3 = 0 then 3943 else if t 3 = 1 then 3939 else 3941))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 759 else 761) else if t 2 = 1 then (if t 3 = 0 then 769 else if t 3 = 1 then 747 else 751) else (if t 3 = 0 then 779 else if t 3 = 1 then 749 else 753)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 767 else if t 3 = 1 then 732 else 736) else if t 2 = 1 then (if t 3 = 0 then 765 else if t 3 = 1 then 704 else 712) else (if t 3 = 0 then 777 else if t 3 = 1 then 706 else 714)) else (if t 2 = 0 then (if t 3 = 0 then 774 else if t 3 = 1 then 733 else 737) else if t 2 = 1 then (if t 3 = 0 then 773 else if t 3 = 1 then 705 else 713) else (if t 3 = 0 then 781 else if t 3 = 1 then 707 else 715))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 1110 else 3966) else if t 2 = 1 then (if t 3 = 0 then 1548 else if t 3 = 1 then 1104 else 1542) else (if t 3 = 0 then 3216 else if t 3 = 1 then 1106 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 785 else if t 3 = 1 then 734 else 738) else if t 2 = 1 then (if t 3 = 0 then 783 else if t 3 = 1 then 708 else 716) else (if t 3 = 0 then 789 else if t 3 = 1 then 710 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 788 else if t 3 = 1 then 735 else 739) else if t 2 = 1 then (if t 3 = 0 then 787 else if t 3 = 1 then 709 else 717) else (if t 3 = 0 then 791 else if t 3 = 1 then 711 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4395 else (if jt.2.val < 2 then 4429 else 4406)) else (if jt.2.val < 4 then 4428 else (if jt.2.val < 5 then 4430 else 4403))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3403 else (if jt.2.val < 2 then 3430 else 3405)) else (if jt.2.val < 4 then 3429 else (if jt.2.val < 5 then 3431 else 3396)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 321 else (if jt.2.val < 2 then 730 else 349)) else (if jt.2.val < 4 then 729 else (if jt.2.val < 5 then 731 else 312))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 606 else (if jt.2.val < 2 then 701 else 608)) else (if jt.2.val < 4 then 699 else (if jt.2.val < 5 then 700 else 603)))))

checked_coverage fastCoverage0415 pairing0415 template0415 witness0415

theorem coverage0415 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0415) (maskBits m))
    cores template0415 witness0415 := by
  rw [← coresFast_eq]
  exact fastCoverage0415

theorem coverageSize0415 : ∀ q : Pattern,
    (cores (witness0415 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0415 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0415
#print axioms coverageSize0415

noncomputable def pairing0416 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0416 : List (Fin 4935) := templateData0416

noncomputable def witness0416 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 3959) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3227) else (if t 3 = 0 then 3236 else if t 3 = 1 then 3235 else 2868)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1611) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1610) else (if t 3 = 0 then 1651 else if t 3 = 1 then 1649 else 1853)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1881 else 95) else if t 2 = 1 then (if t 3 = 0 then 1882 else if t 3 = 1 then 1880 else 1619) else (if t 3 = 0 then 555 else if t 3 = 1 then 1670 else 2174))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1443) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1442) else (if t 3 = 0 then 1332 else if t 3 = 1 then 1330 else 1778)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3161) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4514) else (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4518)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3270 else 3166) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4516) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4507 else 4520))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2073 else 593) else if t 2 = 1 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2072 else 1448) else (if t 3 = 0 then 54 else if t 3 = 1 then 1344 else 1781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3465 else 3164) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4515) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4506 else 4519)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 3280 else 3168) else if t 2 = 1 then (if t 3 = 0 then 4004 else if t 3 = 1 then 4499 else 4517) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4513 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4470 else (if jt.2.val < 2 then 4490 else 4491)) else (if jt.2.val < 4 then 4487 else (if jt.2.val < 5 then 4489 else 4488))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4469 else (if jt.2.val < 2 then 4496 else 4497)) else (if jt.2.val < 4 then 4493 else (if jt.2.val < 5 then 4495 else 4494)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4468 else (if jt.2.val < 2 then 4503 else 4504)) else (if jt.2.val < 4 then 4500 else (if jt.2.val < 5 then 4502 else 4501))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4467 else (if jt.2.val < 2 then 4509 else 4512)) else (if jt.2.val < 4 then 4508 else (if jt.2.val < 5 then 4511 else 4510)))))

checked_coverage fastCoverage0416 pairing0416 template0416 witness0416

theorem coverage0416 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0416) (maskBits m))
    cores template0416 witness0416 := by
  rw [← coresFast_eq]
  exact fastCoverage0416

theorem coverageSize0416 : ∀ q : Pattern,
    (cores (witness0416 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0416 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0416
#print axioms coverageSize0416

noncomputable def pairing0417 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0417 : List (Fin 4935) := templateData0417

noncomputable def witness0417 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4525) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 3225) else (if t 3 = 0 then 2981 else if t 3 = 1 then 2979 else 3226)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 1597) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 1593) else (if t 3 = 0 then 1090 else if t 3 = 1 then 1069 else 1071)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 475 else 1849) else if t 2 = 1 then (if t 3 = 0 then 490 else if t 3 = 1 then 462 else 464) else (if t 3 = 0 then 2150 else if t 3 = 1 then 467 else 469))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 1429) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 1424) else (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 990)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 3146) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3875) else (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3885)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2698) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3881) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3888 else 3889))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 175 else 2116) else if t 2 = 1 then (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 163) else (if t 3 = 0 then 1808 else if t 3 = 1 then 167 else 169)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2551) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3878) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3886 else 3887)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2879 else 2881) else if t 2 = 1 then (if t 3 = 0 then 3919 else if t 3 = 1 then 3882 else 3883) else (if t 3 = 0 then 4526 else if t 3 = 1 then 3890 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4407 else (if jt.2.val < 2 then 4409 else 4416)) else (if jt.2.val < 4 then 4408 else (if jt.2.val < 5 then 4415 else 4414))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4107 else (if jt.2.val < 2 then 4109 else 4116)) else (if jt.2.val < 4 then 4108 else (if jt.2.val < 5 then 4115 else 4114)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4029 else (if jt.2.val < 2 then 4031 else 4035)) else (if jt.2.val < 4 then 4030 else (if jt.2.val < 5 then 4034 else 4033))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4510 else (if jt.2.val < 2 then 4524 else 4512)) else (if jt.2.val < 4 then 4522 else (if jt.2.val < 5 then 4523 else 4467)))))

checked_coverage fastCoverage0417 pairing0417 template0417 witness0417

theorem coverage0417 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0417) (maskBits m))
    cores template0417 witness0417 := by
  rw [← coresFast_eq]
  exact fastCoverage0417

theorem coverageSize0417 : ∀ q : Pattern,
    (cores (witness0417 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0417 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0417
#print axioms coverageSize0417

noncomputable def pairing0418 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0418 : List (Fin 4935) := templateData0418

noncomputable def witness0418 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3062 else 3004) else if t 2 = 1 then (if t 3 = 0 then 3058 else if t 3 = 1 then 3054 else 3003) else (if t 3 = 0 then 4530 else if t 3 = 1 then 3963 else 3967)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3060 else 874) else if t 2 = 1 then (if t 3 = 0 then 3056 else if t 3 = 1 then 3052 else 862) else (if t 3 = 0 then 1648 else if t 3 = 1 then 1646 else 864)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 144 else 2129) else if t 2 = 1 then (if t 3 = 0 then 141 else if t 3 = 1 then 140 else 199) else (if t 3 = 0 then 1835 else if t 3 = 1 then 157 else 201))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3061 else 1219) else if t 2 = 1 then (if t 3 = 0 then 3057 else if t 3 = 1 then 3053 else 1207) else (if t 3 = 0 then 1329 else if t 3 = 1 then 1327 else 1209)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3059 else 3313) else if t 2 = 1 then (if t 3 = 0 then 3055 else if t 3 = 1 then 3051 else 3098) else (if t 3 = 0 then 3073 else if t 3 = 1 then 3071 else 3099)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 3091 else 3500) else if t 2 = 1 then (if t 3 = 0 then 2622 else if t 3 = 1 then 3089 else 3102) else (if t 3 = 0 then 2626 else if t 3 = 1 then 3092 else 3103))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 442 else 1838) else if t 2 = 1 then (if t 3 = 0 then 439 else if t 3 = 1 then 438 else 499) else (if t 3 = 0 then 2126 else if t 3 = 1 then 454 else 501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 3082 else 3315) else if t 2 = 1 then (if t 3 = 0 then 2470 else if t 3 = 1 then 3080 else 3100) else (if t 3 = 0 then 2474 else if t 3 = 1 then 3083 else 3101)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 3095 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2900 else if t 3 = 1 then 3094 else 3104) else (if t 3 = 0 then 2901 else if t 3 = 1 then 3096 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4314 else (if jt.2.val < 2 then 4324 else 4325)) else (if jt.2.val < 4 then 4321 else (if jt.2.val < 5 then 4323 else 4322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3384 else (if jt.2.val < 2 then 3394 else 3395)) else (if jt.2.val < 4 then 3391 else (if jt.2.val < 5 then 3393 else 3392)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4501 else (if jt.2.val < 2 then 4529 else 4504)) else (if jt.2.val < 4 then 4527 else (if jt.2.val < 5 then 4528 else 4468))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3371 else (if jt.2.val < 2 then 3373 else 3377)) else (if jt.2.val < 4 then 3372 else (if jt.2.val < 5 then 3376 else 3375)))))

checked_coverage fastCoverage0418 pairing0418 template0418 witness0418

theorem coverage0418 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0418) (maskBits m))
    cores template0418 witness0418 := by
  rw [← coresFast_eq]
  exact fastCoverage0418

theorem coverageSize0418 : ∀ q : Pattern,
    (cores (witness0418 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0418 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0418
#print axioms coverageSize0418

noncomputable def pairing0419 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0419 : List (Fin 4935) := templateData0419

noncomputable def witness0419 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2953 else 3152) else if t 2 = 1 then (if t 3 = 0 then 2960 else if t 3 = 1 then 2937 else 3329) else (if t 3 = 0 then 3860 else if t 3 = 1 then 4046 else 4532)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2951 else 859) else if t 2 = 1 then (if t 3 = 0 then 2958 else if t 3 = 1 then 2931 else 830) else (if t 3 = 0 then 1084 else if t 3 = 1 then 1046 else 1813)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2098 else 75) else if t 2 = 1 then (if t 3 = 0 then 2104 else if t 3 = 1 then 2082 else 835) else (if t 3 = 0 then 601 else if t 3 = 1 then 1051 else 1816))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2952 else 1204) else if t 2 = 1 then (if t 3 = 0 then 2959 else if t 3 = 1 then 2934 else 1180) else (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 1796)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2947 else 2949) else if t 2 = 1 then (if t 3 = 0 then 2954 else if t 3 = 1 then 2913 else 2917) else (if t 3 = 0 then 2955 else if t 3 = 1 then 2915 else 2918)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2699 else 2701) else if t 2 = 1 then (if t 3 = 0 then 2650 else if t 3 = 1 then 2923 else 2925) else (if t 3 = 0 then 2651 else if t 3 = 1 then 2924 else 2926))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1903 else 573) else if t 2 = 1 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1888 else 1182) else (if t 3 = 0 then 103 else if t 3 = 1 then 972 else 2137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2554 else 2556) else if t 2 = 1 then (if t 3 = 0 then 2502 else if t 3 = 1 then 2919 else 2921) else (if t 3 = 0 then 2503 else if t 3 = 1 then 2920 else 2922)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3196 else 3934) else if t 2 = 1 then (if t 3 = 0 then 3183 else if t 3 = 1 then 2927 else 2929) else (if t 3 = 0 then 3184 else if t 3 = 1 then 2928 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4380 else (if jt.2.val < 2 then 4382 else 4385)) else (if jt.2.val < 4 then 4381 else (if jt.2.val < 5 then 4384 else 4383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3508 else (if jt.2.val < 2 then 3510 else 3513)) else (if jt.2.val < 4 then 3509 else (if jt.2.val < 5 then 3512 else 3511)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4033 else (if jt.2.val < 2 then 4049 else 4035)) else (if jt.2.val < 4 then 4048 else (if jt.2.val < 5 then 4050 else 4029))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3375 else (if jt.2.val < 2 then 3383 else 3377)) else (if jt.2.val < 4 then 3381 else (if jt.2.val < 5 then 3382 else 3371)))))

checked_coverage fastCoverage0419 pairing0419 template0419 witness0419

theorem coverage0419 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0419) (maskBits m))
    cores template0419 witness0419 := by
  rw [← coresFast_eq]
  exact fastCoverage0419

theorem coverageSize0419 : ∀ q : Pattern,
    (cores (witness0419 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0419 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0419
#print axioms coverageSize0419

noncomputable def pairing0420 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0420 : List (Fin 4935) := templateData0420

noncomputable def witness0420 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1707 else 780) else if t 2 = 1 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1705 else 1450) else (if t 3 = 0 then 258 else if t 3 = 1 then 1353 else 2119)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1703 else if t 3 = 1 then 1699 else 778) else if t 2 = 1 then (if t 3 = 0 then 1701 else if t 3 = 1 then 1697 else 1753) else (if t 3 = 0 then 256 else if t 3 = 1 then 1747 else 1762)) else (if t 2 = 0 then (if t 3 = 0 then 4537 else if t 3 = 1 then 4064 else 3943) else if t 2 = 1 then (if t 3 = 0 then 3350 else if t 3 = 1 then 3348 else 2500) else (if t 3 = 0 then 3210 else if t 3 = 1 then 2546 else 2884))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1706 else 779) else if t 2 = 1 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1704 else 1449) else (if t 3 = 0 then 257 else if t 3 = 1 then 1352 else 2118)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1702 else if t 3 = 1 then 1698 else 777) else if t 2 = 1 then (if t 3 = 0 then 1700 else if t 3 = 1 then 1696 else 1752) else (if t 3 = 0 then 255 else if t 3 = 1 then 1746 else 1758)) else (if t 2 = 0 then (if t 3 = 0 then 1720 else if t 3 = 1 then 1718 else 781) else if t 2 = 1 then (if t 3 = 0 then 1719 else if t 3 = 1 then 1716 else 1754) else (if t 3 = 0 then 261 else if t 3 = 1 then 1748 else 1759))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 1052 else 3216) else if t 2 = 1 then (if t 3 = 0 then 836 else if t 3 = 1 then 1732 else 1452) else (if t 3 = 0 then 3942 else if t 3 = 1 then 1358 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2145 else if t 3 = 1 then 1048 else 789) else if t 2 = 1 then (if t 3 = 0 then 832 else if t 3 = 1 then 1729 else 1755) else (if t 3 = 0 then 278 else if t 3 = 1 then 1749 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 2147 else if t 3 = 1 then 1055 else 791) else if t 2 = 1 then (if t 3 = 0 then 839 else if t 3 = 1 then 1734 else 1757) else (if t 3 = 0 then 281 else if t 3 = 1 then 1751 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4380 else (if jt.2.val < 2 then 4391 else 4385)) else (if jt.2.val < 4 then 4389 else (if jt.2.val < 5 then 4390 else 4383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4494 else (if jt.2.val < 2 then 4536 else 4497)) else (if jt.2.val < 4 then 4534 else (if jt.2.val < 5 then 4535 else 4469)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2268 else (if jt.2.val < 2 then 2278 else 2279)) else (if jt.2.val < 4 then 2275 else (if jt.2.val < 5 then 2277 else 2276))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1917 else (if jt.2.val < 2 then 1923 else 1928)) else (if jt.2.val < 4 then 1922 else (if jt.2.val < 5 then 1927 else 1926)))))

checked_coverage fastCoverage0420 pairing0420 template0420 witness0420

theorem coverage0420 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0420) (maskBits m))
    cores template0420 witness0420 := by
  rw [← coresFast_eq]
  exact fastCoverage0420

theorem coverageSize0420 : ∀ q : Pattern,
    (cores (witness0420 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0420 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0420
#print axioms coverageSize0420

noncomputable def pairing0421 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0421 : List (Fin 4935) := templateData0421

noncomputable def witness0421 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 379 else 1775) else if t 2 = 1 then (if t 3 = 0 then 386 else if t 3 = 1 then 371 else 372) else (if t 3 = 0 then 2140 else if t 3 = 1 then 373 else 374)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 384 else if t 3 = 1 then 356 else 1489) else if t 2 = 1 then (if t 3 = 0 then 382 else if t 3 = 1 then 336 else 339) else (if t 3 = 0 then 928 else if t 3 = 1 then 342 else 343)) else (if t 2 = 0 then (if t 3 = 0 then 3935 else if t 3 = 1 then 3929 else 4539) else if t 2 = 1 then (if t 3 = 0 then 2740 else if t 3 = 1 then 2728 else 3203) else (if t 3 = 0 then 2985 else if t 3 = 1 then 2731 else 3205))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 375 else 1773) else if t 2 = 1 then (if t 3 = 0 then 385 else if t 3 = 1 then 363 else 365) else (if t 3 = 0 then 2139 else if t 3 = 1 then 367 else 369)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 383 else if t 3 = 1 then 346 else 1483) else if t 2 = 1 then (if t 3 = 0 then 381 else if t 3 = 1 then 318 else 322) else (if t 3 = 0 then 924 else if t 3 = 1 then 328 else 330)) else (if t 2 = 0 then (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 1484) else if t 2 = 1 then (if t 3 = 0 then 389 else if t 3 = 1 then 320 else 323) else (if t 3 = 0 then 925 else if t 3 = 1 then 329 else 331))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 894 else 2984) else if t 2 = 1 then (if t 3 = 0 then 1500 else if t 3 = 1 then 888 else 890) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1494 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 401 else if t 3 = 1 then 350 else 2157) else if t 2 = 1 then (if t 3 = 0 then 399 else if t 3 = 1 then 324 else 326) else (if t 3 = 0 then 1788 else if t 3 = 1 then 332 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 404 else if t 3 = 1 then 351 else 2158) else if t 2 = 1 then (if t 3 = 0 then 403 else if t 3 = 1 then 325 else 327) else (if t 3 = 0 then 1789 else if t 3 = 1 then 333 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4314 else (if jt.2.val < 2 then 4366 else 4325)) else (if jt.2.val < 4 then 4365 else (if jt.2.val < 5 then 4367 else 4322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4114 else (if jt.2.val < 2 then 4129 else 4116)) else (if jt.2.val < 4 then 4128 else (if jt.2.val < 5 then 4130 else 4107)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2337 else (if jt.2.val < 2 then 2339 else 2342)) else (if jt.2.val < 4 then 2338 else (if jt.2.val < 5 then 2341 else 2340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1926 else (if jt.2.val < 2 then 1940 else 1928)) else (if jt.2.val < 4 then 1938 else (if jt.2.val < 5 then 1939 else 1917)))))

checked_coverage fastCoverage0421 pairing0421 template0421 witness0421

theorem coverage0421 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0421) (maskBits m))
    cores template0421 witness0421 := by
  rw [← coresFast_eq]
  exact fastCoverage0421

theorem coverageSize0421 : ∀ q : Pattern,
    (cores (witness0421 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0421 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0421
#print axioms coverageSize0421

noncomputable def pairing0422 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0422 : List (Fin 4935) := templateData0422

noncomputable def witness0422 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 626 else 2161) else if t 2 = 1 then (if t 3 = 0 then 620 else if t 3 = 1 then 618 else 694) else (if t 3 = 0 then 1786 else if t 3 = 1 then 644 else 695)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 624 else if t 3 = 1 then 622 else 1144) else if t 2 = 1 then (if t 3 = 0 then 616 else if t 3 = 1 then 614 else 680) else (if t 3 = 0 then 1459 else if t 3 = 1 then 641 else 681)) else (if t 2 = 0 then (if t 3 = 0 then 3174 else if t 3 = 1 then 2769 else 2989) else if t 2 = 1 then (if t 3 = 0 then 3172 else if t 3 = 1 then 2766 else 2778) else (if t 3 = 0 then 4541 else if t 3 = 1 then 3945 else 3951))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 625 else 2160) else if t 2 = 1 then (if t 3 = 0 then 619 else if t 3 = 1 then 617 else 690) else (if t 3 = 0 then 1785 else if t 3 = 1 then 643 else 692)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 623 else if t 3 = 1 then 621 else 1140) else if t 2 = 1 then (if t 3 = 0 then 615 else if t 3 = 1 then 613 else 672) else (if t 3 = 0 then 1458 else if t 3 = 1 then 640 else 674)) else (if t 2 = 0 then (if t 3 = 0 then 637 else if t 3 = 1 then 636 else 1141) else if t 2 = 1 then (if t 3 = 0 then 633 else if t 3 = 1 then 632 else 673) else (if t 3 = 0 then 1463 else if t 3 = 1 then 649 else 675))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 1518 else 4542) else if t 2 = 1 then (if t 3 = 0 then 1133 else if t 3 = 1 then 1131 else 1524) else (if t 3 = 0 then 2988 else if t 3 = 1 then 1137 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 660 else if t 3 = 1 then 658 else 1824) else if t 2 = 1 then (if t 3 = 0 then 655 else if t 3 = 1 then 653 else 676) else (if t 3 = 0 then 2169 else if t 3 = 1 then 666 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 665 else if t 3 = 1 then 664 else 1825) else if t 2 = 1 then (if t 3 = 0 then 663 else if t 3 = 1 then 662 else 677) else (if t 3 = 0 then 2171 else if t 3 = 1 then 670 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4407 else (if jt.2.val < 2 then 4427 else 4416)) else (if jt.2.val < 4 then 4425 else (if jt.2.val < 5 then 4426 else 4414))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3392 else (if jt.2.val < 2 then 3428 else 3395)) else (if jt.2.val < 4 then 3426 else (if jt.2.val < 5 then 3427 else 3384)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2276 else (if jt.2.val < 2 then 2303 else 2279)) else (if jt.2.val < 4 then 2301 else (if jt.2.val < 5 then 2302 else 2268))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2250 else (if jt.2.val < 2 then 2252 else 2255)) else (if jt.2.val < 4 then 2251 else (if jt.2.val < 5 then 2254 else 2253)))))

checked_coverage fastCoverage0422 pairing0422 template0422 witness0422

theorem coverage0422 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0422) (maskBits m))
    cores template0422 witness0422 := by
  rw [← coresFast_eq]
  exact fastCoverage0422

theorem coverageSize0422 : ∀ q : Pattern,
    (cores (witness0422 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0422 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0422
#print axioms coverageSize0422

noncomputable def pairing0423 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0423 : List (Fin 4935) := templateData0423

noncomputable def witness0423 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2219 else 764) else if t 2 = 1 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2207 else 1189) else (if t 3 = 0 then 308 else if t 3 = 1 then 979 else 1802)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2213 else 742) else if t 2 = 1 then (if t 3 = 0 then 2222 else if t 3 = 1 then 2193 else 2196) else (if t 3 = 0 then 298 else if t 3 = 1 then 2195 else 2197)) else (if t 2 = 0 then (if t 3 = 0 then 2906 else if t 3 = 1 then 2690 else 3192) else if t 2 = 1 then (if t 3 = 0 then 2648 else if t 3 = 1 then 3528 else 3530) else (if t 3 = 0 then 3927 else if t 3 = 1 then 4211 else 4546))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2217 else 761) else if t 2 = 1 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2205 else 1183) else (if t 3 = 0 then 306 else if t 3 = 1 then 973 else 1799)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2211 else 736) else if t 2 = 1 then (if t 3 = 0 then 2220 else if t 3 = 1 then 2177 else 2181) else (if t 3 = 0 then 294 else if t 3 = 1 then 2179 else 2183)) else (if t 2 = 0 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2212 else 737) else if t 2 = 1 then (if t 3 = 0 then 2221 else if t 3 = 1 then 2178 else 2182) else (if t 3 = 0 then 295 else if t 3 = 1 then 2180 else 2184))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1673 else 3966) else if t 2 = 1 then (if t 3 = 0 then 1620 else if t 3 = 1 then 1889 else 1185) else (if t 3 = 0 then 3229 else if t 3 = 1 then 975 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1854 else if t 3 = 1 then 1658 else 738) else if t 2 = 1 then (if t 3 = 0 then 1614 else if t 3 = 1 then 2185 else 2189) else (if t 3 = 0 then 296 else if t 3 = 1 then 2187 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 1855 else if t 3 = 1 then 1659 else 739) else if t 2 = 1 then (if t 3 = 0 then 1615 else if t 3 = 1 then 2186 else 2190) else (if t 3 = 0 then 297 else if t 3 = 1 then 2188 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4470 else (if jt.2.val < 2 then 4544 else 4491)) else (if jt.2.val < 4 then 4543 else (if jt.2.val < 5 then 4545 else 4488))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3511 else (if jt.2.val < 2 then 3534 else 3513)) else (if jt.2.val < 4 then 3533 else (if jt.2.val < 5 then 3535 else 3508)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2340 else (if jt.2.val < 2 then 2356 else 2342)) else (if jt.2.val < 4 then 2355 else (if jt.2.val < 5 then 2357 else 2337))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2253 else (if jt.2.val < 2 then 2267 else 2255)) else (if jt.2.val < 4 then 2265 else (if jt.2.val < 5 then 2266 else 2250)))))

checked_coverage fastCoverage0423 pairing0423 template0423 witness0423

theorem coverage0423 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0423) (maskBits m))
    cores template0423 witness0423 := by
  rw [← coresFast_eq]
  exact fastCoverage0423

theorem coverageSize0423 : ∀ q : Pattern,
    (cores (witness0423 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0423 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0423
#print axioms coverageSize0423

noncomputable def pairing0424 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0424 : List (Fin 4935) := templateData0424

noncomputable def witness0424 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 3965) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3235) else (if t 3 = 0 then 3228 else if t 3 = 1 then 3227 else 2868)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1650) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1649) else (if t 3 = 0 then 1612 else if t 3 = 1 then 1610 else 1853)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1881 else 159) else if t 2 = 1 then (if t 3 = 0 then 1882 else if t 3 = 1 then 1880 else 1670) else (if t 3 = 0 then 497 else if t 3 = 1 then 1619 else 2174))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1331) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1330) else (if t 3 = 0 then 1444 else if t 3 = 1 then 1442 else 1778)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3074) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4505) else (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4518)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3270 else 3093) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4507) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4516 else 4520))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2073 else 456) else if t 2 = 1 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2072 else 1344) else (if t 3 = 0 then 197 else if t 3 = 1 then 1448 else 1781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3465 else 3084) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4506) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4515 else 4519)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 3280 else 3097) else if t 2 = 1 then (if t 3 = 0 then 4004 else if t 3 = 1 then 4499 else 4513) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4517 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4470 else (if jt.2.val < 2 then 4490 else 4491)) else (if jt.2.val < 4 then 4487 else (if jt.2.val < 5 then 4489 else 4488))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4469 else (if jt.2.val < 2 then 4496 else 4497)) else (if jt.2.val < 4 then 4493 else (if jt.2.val < 5 then 4495 else 4494)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4548 else (if jt.2.val < 2 then 4556 else 4559)) else (if jt.2.val < 4 then 4555 else (if jt.2.val < 5 then 4558 else 4557))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4549 else (if jt.2.val < 2 then 4553 else 4554)) else (if jt.2.val < 4 then 4550 else (if jt.2.val < 5 then 4552 else 4551)))))

checked_coverage fastCoverage0424 pairing0424 template0424 witness0424

theorem coverage0424 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0424) (maskBits m))
    cores template0424 witness0424 := by
  rw [← coresFast_eq]
  exact fastCoverage0424

theorem coverageSize0424 : ∀ q : Pattern,
    (cores (witness0424 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0424 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0424
#print axioms coverageSize0424

noncomputable def pairing0425 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0425 : List (Fin 4935) := templateData0425

noncomputable def witness0425 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4530) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 3234) else (if t 3 = 0 then 2981 else if t 3 = 1 then 2980 else 3242)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 1648) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 1647) else (if t 3 = 0 then 1090 else if t 3 = 1 then 1078 else 1080)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 536 else 1835) else if t 2 = 1 then (if t 3 = 0 then 539 else if t 3 = 1 then 535 else 553) else (if t 3 = 0 then 2150 else if t 3 = 1 then 595 else 597))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 1329) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 1328) else (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 999)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 3073) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3827) else (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3853)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2626) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3846) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3856 else 3857))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 33 else 2126) else if t 2 = 1 then (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 52) else (if t 3 = 0 then 1808 else if t 3 = 1 then 97 else 99)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2474) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3837) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3854 else 3855)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2899 else 2901) else if t 2 = 1 then (if t 3 = 0 then 3849 else if t 3 = 1 then 3848 else 3850) else (if t 3 = 0 then 4526 else if t 3 = 1 then 3858 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4395 else (if jt.2.val < 2 then 4405 else 4406)) else (if jt.2.val < 4 then 4402 else (if jt.2.val < 5 then 4404 else 4403))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4095 else (if jt.2.val < 2 then 4105 else 4106)) else (if jt.2.val < 4 then 4102 else (if jt.2.val < 5 then 4104 else 4103)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4082 else (if jt.2.val < 2 then 4084 else 4088)) else (if jt.2.val < 4 then 4083 else (if jt.2.val < 5 then 4087 else 4086))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4551 else (if jt.2.val < 2 then 4562 else 4554)) else (if jt.2.val < 4 then 4560 else (if jt.2.val < 5 then 4561 else 4549)))))

checked_coverage fastCoverage0425 pairing0425 template0425 witness0425

theorem coverage0425 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0425) (maskBits m))
    cores template0425 witness0425 := by
  rw [← coresFast_eq]
  exact fastCoverage0425

theorem coverageSize0425 : ∀ q : Pattern,
    (cores (witness0425 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0425 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0425
#print axioms coverageSize0425

noncomputable def pairing0426 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0426 : List (Fin 4935) := templateData0426

noncomputable def witness0426 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3156 else 3004) else if t 2 = 1 then (if t 3 = 0 then 3151 else if t 3 = 1 then 3144 else 3002) else (if t 3 = 0 then 4525 else if t 3 = 1 then 3953 else 3954)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3154 else 874) else if t 2 = 1 then (if t 3 = 0 then 3149 else if t 3 = 1 then 3138 else 853) else (if t 3 = 0 then 1597 else if t 3 = 1 then 1589 else 855)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 88 else 2129) else if t 2 = 1 then (if t 3 = 0 then 73 else if t 3 = 1 then 60 else 65) else (if t 3 = 0 then 1849 else if t 3 = 1 then 62 else 67))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3155 else 1219) else if t 2 = 1 then (if t 3 = 0 then 3150 else if t 3 = 1 then 3141 else 1198) else (if t 3 = 0 then 1429 else if t 3 = 1 then 1419 else 1200)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3153 else 3313) else if t 2 = 1 then (if t 3 = 0 then 3145 else if t 3 = 1 then 3119 else 3130) else (if t 3 = 0 then 3146 else if t 3 = 1 then 3121 else 3131)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 3165 else 3500) else if t 2 = 1 then (if t 3 = 0 then 2697 else if t 3 = 1 then 3126 else 3134) else (if t 3 = 0 then 2698 else if t 3 = 1 then 3127 else 3135))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 586 else 1838) else if t 2 = 1 then (if t 3 = 0 then 571 else if t 3 = 1 then 557 else 563) else (if t 3 = 0 then 2116 else if t 3 = 1 then 559 else 565)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 3163 else 3315) else if t 2 = 1 then (if t 3 = 0 then 2550 else if t 3 = 1 then 3123 else 3132) else (if t 3 = 0 then 2551 else if t 3 = 1 then 3124 else 3133)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 3167 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2880 else if t 3 = 1 then 3128 else 3136) else (if t 3 = 0 then 2881 else if t 3 = 1 then 3129 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4326 else (if jt.2.val < 2 then 4328 else 4335)) else (if jt.2.val < 4 then 4327 else (if jt.2.val < 5 then 4334 else 4333))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3396 else (if jt.2.val < 2 then 3398 else 3405)) else (if jt.2.val < 4 then 3397 else (if jt.2.val < 5 then 3404 else 3403)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4557 else (if jt.2.val < 2 then 4565 else 4559)) else (if jt.2.val < 4 then 4563 else (if jt.2.val < 5 then 4564 else 4548))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3305 else (if jt.2.val < 2 then 3307 else 3311)) else (if jt.2.val < 4 then 3306 else (if jt.2.val < 5 then 3310 else 3309)))))

checked_coverage fastCoverage0426 pairing0426 template0426 witness0426

theorem coverage0426 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0426) (maskBits m))
    cores template0426 witness0426 := by
  rw [← coresFast_eq]
  exact fastCoverage0426

theorem coverageSize0426 : ∀ q : Pattern,
    (cores (witness0426 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0426 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0426
#print axioms coverageSize0426

noncomputable def pairing0427 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0427 : List (Fin 4935) := templateData0427

noncomputable def witness0427 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2960 else 3106) else if t 2 = 1 then (if t 3 = 0 then 2953 else if t 3 = 1 then 2937 else 3329) else (if t 3 = 0 then 3905 else if t 3 = 1 then 4046 else 4532)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2958 else 868) else if t 2 = 1 then (if t 3 = 0 then 2951 else if t 3 = 1 then 2931 else 830) else (if t 3 = 0 then 1075 else if t 3 = 1 then 1046 else 1813)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2104 else 205) else if t 2 = 1 then (if t 3 = 0 then 2098 else if t 3 = 1 then 2082 else 835) else (if t 3 = 0 then 477 else if t 3 = 1 then 1051 else 1816))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2959 else 1213) else if t 2 = 1 then (if t 3 = 0 then 2952 else if t 3 = 1 then 2934 else 1180) else (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 1796)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2954 else 2956) else if t 2 = 1 then (if t 3 = 0 then 2947 else if t 3 = 1 then 2913 else 2917) else (if t 3 = 0 then 2948 else if t 3 = 1 then 2915 else 2918)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2650 else 2652) else if t 2 = 1 then (if t 3 = 0 then 2699 else if t 3 = 1 then 2923 else 2925) else (if t 3 = 0 then 2700 else if t 3 = 1 then 2924 else 2926))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1909 else 505) else if t 2 = 1 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1888 else 1182) else (if t 3 = 0 then 177 else if t 3 = 1 then 972 else 2137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2502 else 2504) else if t 2 = 1 then (if t 3 = 0 then 2554 else if t 3 = 1 then 2919 else 2921) else (if t 3 = 0 then 2555 else if t 3 = 1 then 2920 else 2922)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3183 else 3928) else if t 2 = 1 then (if t 3 = 0 then 3196 else if t 3 = 1 then 2927 else 2929) else (if t 3 = 0 then 3197 else if t 3 = 1 then 2928 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4380 else (if jt.2.val < 2 then 4382 else 4385)) else (if jt.2.val < 4 then 4381 else (if jt.2.val < 5 then 4384 else 4383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3508 else (if jt.2.val < 2 then 3510 else 3513)) else (if jt.2.val < 4 then 3509 else (if jt.2.val < 5 then 3512 else 3511)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4086 else (if jt.2.val < 2 then 4094 else 4088)) else (if jt.2.val < 4 then 4092 else (if jt.2.val < 5 then 4093 else 4082))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3309 else (if jt.2.val < 2 then 3332 else 3311)) else (if jt.2.val < 4 then 3331 else (if jt.2.val < 5 then 3333 else 3305)))))

checked_coverage fastCoverage0427 pairing0427 template0427 witness0427

theorem coverage0427 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0427) (maskBits m))
    cores template0427 witness0427 := by
  rw [← coresFast_eq]
  exact fastCoverage0427

theorem coverageSize0427 : ∀ q : Pattern,
    (cores (witness0427 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0427 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0427
#print axioms coverageSize0427

noncomputable def pairing0428 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0428 : List (Fin 4935) := templateData0428

noncomputable def witness0428 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1707 else 648) else if t 2 = 1 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1705 else 1353) else (if t 3 = 0 then 396 else if t 3 = 1 then 1450 else 2119)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1703 else if t 3 = 1 then 1699 else 646) else if t 2 = 1 then (if t 3 = 0 then 1701 else if t 3 = 1 then 1697 else 1747) else (if t 3 = 0 then 394 else if t 3 = 1 then 1753 else 1762)) else (if t 2 = 0 then (if t 3 = 0 then 4537 else if t 3 = 1 then 4064 else 3946) else if t 2 = 1 then (if t 3 = 0 then 3350 else if t 3 = 1 then 3348 else 2546) else (if t 3 = 0 then 3207 else if t 3 = 1 then 2500 else 2884))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1706 else 647) else if t 2 = 1 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1704 else 1352) else (if t 3 = 0 then 395 else if t 3 = 1 then 1449 else 2118)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1702 else if t 3 = 1 then 1698 else 645) else if t 2 = 1 then (if t 3 = 0 then 1700 else if t 3 = 1 then 1696 else 1746) else (if t 3 = 0 then 393 else if t 3 = 1 then 1752 else 1758)) else (if t 2 = 0 then (if t 3 = 0 then 1720 else if t 3 = 1 then 1718 else 651) else if t 2 = 1 then (if t 3 = 0 then 1719 else if t 3 = 1 then 1716 else 1748) else (if t 3 = 0 then 397 else if t 3 = 1 then 1754 else 1759))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 1052 else 3206) else if t 2 = 1 then (if t 3 = 0 then 836 else if t 3 = 1 then 1732 else 1358) else (if t 3 = 0 then 3952 else if t 3 = 1 then 1452 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2145 else if t 3 = 1 then 1048 else 668) else if t 2 = 1 then (if t 3 = 0 then 832 else if t 3 = 1 then 1729 else 1749) else (if t 3 = 0 then 405 else if t 3 = 1 then 1755 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 2147 else if t 3 = 1 then 1055 else 671) else if t 2 = 1 then (if t 3 = 0 then 839 else if t 3 = 1 then 1734 else 1751) else (if t 3 = 0 then 407 else if t 3 = 1 then 1757 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4380 else (if jt.2.val < 2 then 4391 else 4385)) else (if jt.2.val < 4 then 4389 else (if jt.2.val < 5 then 4390 else 4383))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4494 else (if jt.2.val < 2 then 4536 else 4497)) else (if jt.2.val < 4 then 4534 else (if jt.2.val < 5 then 4535 else 4469)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2376 else (if jt.2.val < 2 then 2378 else 2381)) else (if jt.2.val < 4 then 2377 else (if jt.2.val < 5 then 2380 else 2379))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1693 else (if jt.2.val < 2 then 1744 else 1745)) else (if jt.2.val < 4 then 1741 else (if jt.2.val < 5 then 1743 else 1742)))))

checked_coverage fastCoverage0428 pairing0428 template0428 witness0428

theorem coverage0428 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0428) (maskBits m))
    cores template0428 witness0428 := by
  rw [← coresFast_eq]
  exact fastCoverage0428

theorem coverageSize0428 : ∀ q : Pattern,
    (cores (witness0428 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0428 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0428
#print axioms coverageSize0428

noncomputable def pairing0429 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0429 : List (Fin 4935) := templateData0429

noncomputable def witness0429 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 224 else 1786) else if t 2 = 1 then (if t 3 = 0 then 230 else if t 3 = 1 then 222 else 254) else (if t 3 = 0 then 2140 else if t 3 = 1 then 304 else 305)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 228 else if t 3 = 1 then 220 else 1459) else if t 2 = 1 then (if t 3 = 0 then 226 else if t 3 = 1 then 218 else 251) else (if t 3 = 0 then 928 else if t 3 = 1 then 290 else 291)) else (if t 2 = 0 then (if t 3 = 0 then 3925 else if t 3 = 1 then 3923 else 4541) else if t 2 = 1 then (if t 3 = 0 then 2750 else if t 3 = 1 then 2747 else 3209) else (if t 3 = 0 then 2985 else if t 3 = 1 then 2759 else 3215))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 223 else 1785) else if t 2 = 1 then (if t 3 = 0 then 229 else if t 3 = 1 then 221 else 253) else (if t 3 = 0 then 2139 else if t 3 = 1 then 300 else 302)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 227 else if t 3 = 1 then 219 else 1458) else if t 2 = 1 then (if t 3 = 0 then 225 else if t 3 = 1 then 217 else 250) else (if t 3 = 0 then 924 else if t 3 = 1 then 282 else 284)) else (if t 2 = 0 then (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 1463) else if t 2 = 1 then (if t 3 = 0 then 242 else if t 3 = 1 then 237 else 259) else (if t 3 = 0 then 925 else if t 3 = 1 then 283 else 285))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 917 else 2988) else if t 2 = 1 then (if t 3 = 0 then 1470 else if t 3 = 1 then 915 else 921) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1476 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 270 else if t 3 = 1 then 265 else 2169) else if t 2 = 1 then (if t 3 = 0 then 268 else if t 3 = 1 then 263 else 276) else (if t 3 = 0 then 1788 else if t 3 = 1 then 286 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 275 else if t 3 = 1 then 273 else 2171) else if t 2 = 1 then (if t 3 = 0 then 274 else if t 3 = 1 then 272 else 280) else (if t 3 = 0 then 1789 else if t 3 = 1 then 287 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4326 else (if jt.2.val < 2 then 4364 else 4335)) else (if jt.2.val < 4 then 4362 else (if jt.2.val < 5 then 4363 else 4333))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4103 else (if jt.2.val < 2 then 4127 else 4106)) else (if jt.2.val < 4 then 4125 else (if jt.2.val < 5 then 4126 else 4095)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2418 else (if jt.2.val < 2 then 2420 else 2423)) else (if jt.2.val < 4 then 2419 else (if jt.2.val < 5 then 2422 else 2421))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1742 else (if jt.2.val < 2 then 1784 else 1745)) else (if jt.2.val < 4 then 1782 else (if jt.2.val < 5 then 1783 else 1693)))))

checked_coverage fastCoverage0429 pairing0429 template0429 witness0429

theorem coverage0429 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0429) (maskBits m))
    cores template0429 witness0429 := by
  rw [← coresFast_eq]
  exact fastCoverage0429

theorem coverageSize0429 : ∀ q : Pattern,
    (cores (witness0429 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0429 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0429
#print axioms coverageSize0429

noncomputable def pairing0430 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0430 : List (Fin 4935) := templateData0430

noncomputable def witness0430 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 770 else 2161) else if t 2 = 1 then (if t 3 = 0 then 763 else if t 3 = 1 then 755 else 757) else (if t 3 = 0 then 1775 else if t 3 = 1 then 756 else 758)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 768 else if t 3 = 1 then 766 else 1144) else if t 2 = 1 then (if t 3 = 0 then 740 else if t 3 = 1 then 720 else 725) else (if t 3 = 0 then 1489 else if t 3 = 1 then 722 else 726)) else (if t 2 = 0 then (if t 3 = 0 then 3198 else if t 3 = 1 then 2797 else 2989) else if t 2 = 1 then (if t 3 = 0 then 3191 else if t 3 = 1 then 2785 else 2788) else (if t 3 = 0 then 4539 else if t 3 = 1 then 3939 else 3941))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 769 else 2160) else if t 2 = 1 then (if t 3 = 0 then 759 else if t 3 = 1 then 747 else 751) else (if t 3 = 0 then 1773 else if t 3 = 1 then 749 else 753)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 767 else if t 3 = 1 then 765 else 1140) else if t 2 = 1 then (if t 3 = 0 then 732 else if t 3 = 1 then 704 else 712) else (if t 3 = 0 then 1483 else if t 3 = 1 then 706 else 714)) else (if t 2 = 0 then (if t 3 = 0 then 774 else if t 3 = 1 then 773 else 1141) else if t 2 = 1 then (if t 3 = 0 then 733 else if t 3 = 1 then 705 else 713) else (if t 3 = 0 then 1484 else if t 3 = 1 then 707 else 715))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 1548 else 4542) else if t 2 = 1 then (if t 3 = 0 then 1110 else if t 3 = 1 then 1104 else 1542) else (if t 3 = 0 then 2984 else if t 3 = 1 then 1106 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 785 else if t 3 = 1 then 783 else 1824) else if t 2 = 1 then (if t 3 = 0 then 734 else if t 3 = 1 then 708 else 716) else (if t 3 = 0 then 2157 else if t 3 = 1 then 710 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 788 else if t 3 = 1 then 787 else 1825) else if t 2 = 1 then (if t 3 = 0 then 735 else if t 3 = 1 then 709 else 717) else (if t 3 = 0 then 2158 else if t 3 = 1 then 711 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4395 else (if jt.2.val < 2 then 4429 else 4406)) else (if jt.2.val < 4 then 4428 else (if jt.2.val < 5 then 4430 else 4403))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3403 else (if jt.2.val < 2 then 3430 else 3405)) else (if jt.2.val < 4 then 3429 else (if jt.2.val < 5 then 3431 else 3396)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2379 else (if jt.2.val < 2 then 2402 else 2381)) else (if jt.2.val < 4 then 2400 else (if jt.2.val < 5 then 2401 else 2376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2151 else (if jt.2.val < 2 then 2153 else 2156)) else (if jt.2.val < 4 then 2152 else (if jt.2.val < 5 then 2155 else 2154)))))

checked_coverage fastCoverage0430 pairing0430 template0430 witness0430

theorem coverage0430 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0430) (maskBits m))
    cores template0430 witness0430 := by
  rw [← coresFast_eq]
  exact fastCoverage0430

theorem coverageSize0430 : ∀ q : Pattern,
    (cores (witness0430 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0430 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0430
#print axioms coverageSize0430

noncomputable def pairing0431 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0431 : List (Fin 4935) := templateData0431

noncomputable def witness0431 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2225 else 698) else if t 2 = 1 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2207 else 1189) else (if t 3 = 0 then 380 else if t 3 = 1 then 979 else 1802)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2222 else 688) else if t 2 = 1 then (if t 3 = 0 then 2213 else if t 3 = 1 then 2193 else 2196) else (if t 3 = 0 then 358 else if t 3 = 1 then 2195 else 2197)) else (if t 2 = 0 then (if t 3 = 0 then 2906 else if t 3 = 1 then 2648 else 3182) else if t 2 = 1 then (if t 3 = 0 then 2690 else if t 3 = 1 then 3528 else 3530) else (if t 3 = 0 then 3930 else if t 3 = 1 then 4211 else 4546))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2223 else 696) else if t 2 = 1 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2205 else 1183) else (if t 3 = 0 then 377 else if t 3 = 1 then 973 else 1799)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2220 else 684) else if t 2 = 1 then (if t 3 = 0 then 2211 else if t 3 = 1 then 2177 else 2181) else (if t 3 = 0 then 352 else if t 3 = 1 then 2179 else 2183)) else (if t 2 = 0 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2221 else 685) else if t 2 = 1 then (if t 3 = 0 then 2212 else if t 3 = 1 then 2178 else 2182) else (if t 3 = 0 then 353 else if t 3 = 1 then 2180 else 2184))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1620 else 3960) else if t 2 = 1 then (if t 3 = 0 then 1673 else if t 3 = 1 then 1889 else 1185) else (if t 3 = 0 then 3240 else if t 3 = 1 then 975 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1854 else if t 3 = 1 then 1614 else 686) else if t 2 = 1 then (if t 3 = 0 then 1658 else if t 3 = 1 then 2185 else 2189) else (if t 3 = 0 then 354 else if t 3 = 1 then 2187 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 1855 else if t 3 = 1 then 1615 else 687) else if t 2 = 1 then (if t 3 = 0 then 1659 else if t 3 = 1 then 2186 else 2190) else (if t 3 = 0 then 355 else if t 3 = 1 then 2188 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4470 else (if jt.2.val < 2 then 4544 else 4491)) else (if jt.2.val < 4 then 4543 else (if jt.2.val < 5 then 4545 else 4488))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3511 else (if jt.2.val < 2 then 3534 else 3513)) else (if jt.2.val < 4 then 3533 else (if jt.2.val < 5 then 3535 else 3508)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2421 else (if jt.2.val < 2 then 2429 else 2423)) else (if jt.2.val < 4 then 2427 else (if jt.2.val < 5 then 2428 else 2418))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2154 else (if jt.2.val < 2 then 2209 else 2156)) else (if jt.2.val < 4 then 2208 else (if jt.2.val < 5 then 2210 else 2151)))))

checked_coverage fastCoverage0431 pairing0431 template0431 witness0431

theorem coverage0431 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0431) (maskBits m))
    cores template0431 witness0431 := by
  rw [← coresFast_eq]
  exact fastCoverage0431

theorem coverageSize0431 : ∀ q : Pattern,
    (cores (witness0431 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0431 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0431
#print axioms coverageSize0431

noncomputable def pairing0432 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0432 : List (Fin 4935) := templateData0432

noncomputable def witness0432 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 3935) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2740) else (if t 3 = 0 then 3352 else if t 3 = 1 then 3350 else 3207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 489) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 488) else (if t 3 = 0 then 1882 else if t 3 = 1 then 1878 else 496)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 538 else 1120) else if t 2 = 1 then (if t 3 = 0 then 539 else if t 3 = 1 then 537 else 1114) else (if t 3 = 0 then 555 else if t 3 = 1 then 554 else 1116))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 390) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 389) else (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 397)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2715) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4019) else (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4020)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2903) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4023) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4016 else 4024))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 820 else 404) else if t 2 = 1 then (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 403) else (if t 3 = 0 then 841 else if t 3 = 1 then 839 else 407)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2723) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4021) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4003 else 4022)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2635 else 3322) else if t 2 = 1 then (if t 3 = 0 then 3849 else if t 3 = 1 then 4017 else 4025) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4018 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4431 else (if jt.2.val < 2 then 4441 else 4442)) else (if jt.2.val < 4 then 4438 else (if jt.2.val < 5 then 4440 else 4439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4233 else (if jt.2.val < 2 then 4243 else 4244)) else (if jt.2.val < 4 then 4240 else (if jt.2.val < 5 then 4242 else 4241)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4566 else (if jt.2.val < 2 then 4570 else 4571)) else (if jt.2.val < 4 then 4567 else (if jt.2.val < 5 then 4569 else 4568))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3969 else (if jt.2.val < 2 then 4006 else 4009)) else (if jt.2.val < 4 then 4005 else (if jt.2.val < 5 then 4008 else 4007)))))

checked_coverage fastCoverage0432 pairing0432 template0432 witness0432

theorem coverage0432 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0432) (maskBits m))
    cores template0432 witness0432 := by
  rw [← coresFast_eq]
  exact fastCoverage0432

theorem coverageSize0432 : ∀ q : Pattern,
    (cores (witness0432 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0432 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0432
#print axioms coverageSize0432

noncomputable def pairing0433 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0433 : List (Fin 4935) := templateData0433

noncomputable def witness0433 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4036) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2737) else (if t 3 = 0 then 3228 else if t 3 = 1 then 3225 else 3344)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 475) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 462) else (if t 3 = 0 then 1612 else if t 3 = 1 then 1593 else 464)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1075 else 477) else if t 2 = 1 then (if t 3 = 0 then 1090 else if t 3 = 1 then 1069 else 467) else (if t 3 = 0 then 1094 else if t 3 = 1 then 1071 else 469))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 376) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 364) else (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 366)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2696) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3880) else (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3881)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2700) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3888) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3885 else 3889))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 175 else 895) else if t 2 = 1 then (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 889) else (if t 3 = 0 then 197 else if t 3 = 1 then 163 else 891)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2879) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3882) else (if t 3 = 0 then 3916 else if t 3 = 1 then 3878 else 3883)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2555 else 3197) else if t 2 = 1 then (if t 3 = 0 then 4039 else if t 3 = 1 then 3886 else 3890) else (if t 3 = 0 then 4040 else if t 3 = 1 then 3887 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4407 else (if jt.2.val < 2 then 4409 else 4416)) else (if jt.2.val < 4 then 4408 else (if jt.2.val < 5 then 4415 else 4414))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4245 else (if jt.2.val < 2 then 4247 else 4250)) else (if jt.2.val < 4 then 4246 else (if jt.2.val < 5 then 4249 else 4248)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4455 else (if jt.2.val < 2 then 4457 else 4460)) else (if jt.2.val < 4 then 4456 else (if jt.2.val < 5 then 4459 else 4458))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4007 else (if jt.2.val < 2 then 4032 else 4009)) else (if jt.2.val < 4 then 4027 else (if jt.2.val < 5 then 4028 else 3969)))))

checked_coverage fastCoverage0433 pairing0433 template0433 witness0433

theorem coverage0433 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0433) (maskBits m))
    cores template0433 witness0433 := by
  rw [← coresFast_eq]
  exact fastCoverage0433

theorem coverageSize0433 : ∀ q : Pattern,
    (cores (witness0433 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0433 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0433
#print axioms coverageSize0433

noncomputable def pairing0434 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0434 : List (Fin 4935) := templateData0434

noncomputable def witness0434 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3198) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2797) else (if t 3 = 0 then 4066 else if t 3 = 1 then 4064 else 3943)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 87) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 86) else (if t 3 = 0 then 1881 else if t 3 = 1 then 1877 else 94)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 143 else 904) else if t 2 = 1 then (if t 3 = 0 then 144 else if t 3 = 1 then 142 else 898) else (if t 3 = 0 then 159 else if t 3 = 1 then 158 else 900))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 774) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 773) else (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2717) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3295) else (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3296)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2623 else 2904) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3291 else 3299) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3292 else 3300))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1040 else 788) else if t 2 = 1 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 787) else (if t 3 = 0 then 1057 else if t 3 = 1 then 1055 else 791)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2724) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3276 else 3297) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3279 else 3298)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2637 else 4045) else if t 2 = 1 then (if t 3 = 0 then 3095 else if t 3 = 1 then 3293 else 3301) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3294 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4368 else (if jt.2.val < 2 then 4378 else 4379)) else (if jt.2.val < 4 then 4375 else (if jt.2.val < 5 then 4377 else 4376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3555 else (if jt.2.val < 2 then 3565 else 3566)) else (if jt.2.val < 4 then 3562 else (if jt.2.val < 5 then 3564 else 3563)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4568 else (if jt.2.val < 2 then 4574 else 4571)) else (if jt.2.val < 4 then 4572 else (if jt.2.val < 5 then 4573 else 4566))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3243 else (if jt.2.val < 2 then 3282 else 3285)) else (if jt.2.val < 4 then 3281 else (if jt.2.val < 5 then 3284 else 3283)))))

checked_coverage fastCoverage0434 pairing0434 template0434 witness0434

theorem coverage0434 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0434) (maskBits m))
    cores template0434 witness0434 := by
  rw [← coresFast_eq]
  exact fastCoverage0434

theorem coverageSize0434 : ∀ q : Pattern,
    (cores (witness0434 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0434 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0434
#print axioms coverageSize0434

noncomputable def pairing0435 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0435 : List (Fin 4935) := templateData0435

noncomputable def witness0435 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3312) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 2794) else (if t 3 = 0 then 3959 else if t 3 = 1 then 3953 else 4060)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 73) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 60) else (if t 3 = 0 then 1611 else if t 3 = 1 then 1589 else 62)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 859 else 75) else if t 2 = 1 then (if t 3 = 0 then 874 else if t 3 = 1 then 853 else 65) else (if t 3 = 0 then 878 else if t 3 = 1 then 855 else 67))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 760) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 748) else (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 750)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2697) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3126) else (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3127)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2949 else 2701) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3130 else 3134) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3131 else 3135))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 571 else 1111) else if t 2 = 1 then (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 1105) else (if t 3 = 0 then 593 else if t 3 = 1 then 559 else 1107)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2880) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3123 else 3128) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3124 else 3129)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2556 else 3934) else if t 2 = 1 then (if t 3 = 0 then 3315 else if t 3 = 1 then 3132 else 3136) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3133 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4326 else (if jt.2.val < 2 then 4328 else 4335)) else (if jt.2.val < 4 then 4327 else (if jt.2.val < 5 then 4334 else 4333))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3567 else (if jt.2.val < 2 then 3569 else 3572)) else (if jt.2.val < 4 then 3568 else (if jt.2.val < 5 then 3571 else 3570)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4458 else (if jt.2.val < 2 then 4465 else 4460)) else (if jt.2.val < 4 then 4464 else (if jt.2.val < 5 then 4466 else 4455))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3283 else (if jt.2.val < 2 then 3308 else 3285)) else (if jt.2.val < 4 then 3303 else (if jt.2.val < 5 then 3304 else 3243)))))

checked_coverage fastCoverage0435 pairing0435 template0435 witness0435

theorem coverage0435 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0435) (maskBits m))
    cores template0435 witness0435 := by
  rw [← coresFast_eq]
  exact fastCoverage0435

theorem coverageSize0435 : ∀ q : Pattern,
    (cores (witness0435 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0435 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0435
#print axioms coverageSize0435

noncomputable def pairing0436 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0436 : List (Fin 4935) := templateData0436

noncomputable def witness0436 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 228 else 932) else if t 2 = 1 then (if t 3 = 0 then 230 else if t 3 = 1 then 226 else 928) else (if t 3 = 0 then 258 else if t 3 = 1 then 256 else 929)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 224 else if t 3 = 1 then 220 else 298) else if t 2 = 1 then (if t 3 = 0 then 222 else if t 3 = 1 then 218 else 290) else (if t 3 = 0 then 254 else if t 3 = 1 then 251 else 291)) else (if t 2 = 0 then (if t 3 = 0 then 4044 else if t 3 = 1 then 3923 else 3927) else if t 2 = 1 then (if t 3 = 0 then 2749 else if t 3 = 1 then 2747 else 2759) else (if t 3 = 0 then 3342 else if t 3 = 1 then 3209 else 3215))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 227 else 930) else if t 2 = 1 then (if t 3 = 0 then 229 else if t 3 = 1 then 225 else 924) else (if t 3 = 0 then 257 else if t 3 = 1 then 255 else 926)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 223 else if t 3 = 1 then 219 else 294) else if t 2 = 1 then (if t 3 = 0 then 221 else if t 3 = 1 then 217 else 282) else (if t 3 = 0 then 253 else if t 3 = 1 then 250 else 284)) else (if t 2 = 0 then (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 295) else if t 2 = 1 then (if t 3 = 0 then 240 else if t 3 = 1 then 237 else 283) else (if t 3 = 0 then 260 else if t 3 = 1 then 259 else 285))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 270 else 3345) else if t 2 = 1 then (if t 3 = 0 then 1470 else if t 3 = 1 then 268 else 1788) else (if t 3 = 0 then 3942 else if t 3 = 1 then 278 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 917 else if t 3 = 1 then 265 else 296) else if t 2 = 1 then (if t 3 = 0 then 915 else if t 3 = 1 then 263 else 286) else (if t 3 = 0 then 921 else if t 3 = 1 then 276 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 920 else if t 3 = 1 then 273 else 297) else if t 2 = 1 then (if t 3 = 0 then 919 else if t 3 = 1 then 272 else 287) else (if t 3 = 0 then 923 else if t 3 = 1 then 280 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4326 else (if jt.2.val < 2 then 4364 else 4335)) else (if jt.2.val < 4 then 4362 else (if jt.2.val < 5 then 4363 else 4333))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4241 else (if jt.2.val < 2 then 4256 else 4244)) else (if jt.2.val < 4 then 4254 else (if jt.2.val < 5 then 4255 else 4233)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 215 else (if jt.2.val < 2 then 249 else 252)) else (if jt.2.val < 4 then 246 else (if jt.2.val < 5 then 248 else 247))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 908 else (if jt.2.val < 2 then 910 else 913)) else (if jt.2.val < 4 then 909 else (if jt.2.val < 5 then 912 else 911)))))

checked_coverage fastCoverage0436 pairing0436 template0436 witness0436

theorem coverage0436 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0436) (maskBits m))
    cores template0436 witness0436 := by
  rw [← coresFast_eq]
  exact fastCoverage0436

theorem coverageSize0436 : ∀ q : Pattern,
    (cores (witness0436 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0436 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0436
#print axioms coverageSize0436

noncomputable def pairing0437 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0437 : List (Fin 4935) := templateData0437

noncomputable def witness0437 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 995 else 380) else if t 2 = 1 then (if t 3 = 0 then 1006 else if t 3 = 1 then 991 else 373) else (if t 3 = 0 then 1012 else if t 3 = 1 then 992 else 374)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1004 else if t 3 = 1 then 977 else 979) else if t 2 = 1 then (if t 3 = 0 then 1000 else if t 3 = 1 then 957 else 963) else (if t 3 = 0 then 1001 else if t 3 = 1 then 960 else 964)) else (if t 2 = 0 then (if t 3 = 0 then 3860 else if t 3 = 1 then 4046 else 4047) else if t 2 = 1 then (if t 3 = 0 then 2980 else if t 3 = 1 then 2970 else 2973) else (if t 3 = 0 then 3242 else if t 3 = 1 then 3338 else 3340))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 993 else 377) else if t 2 = 1 then (if t 3 = 0 then 1005 else if t 3 = 1 then 987 else 367) else (if t 3 = 0 then 1011 else if t 3 = 1 then 989 else 369)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1002 else if t 3 = 1 then 967 else 973) else if t 2 = 1 then (if t 3 = 0 then 996 else if t 3 = 1 then 939 else 949) else (if t 3 = 0 then 998 else if t 3 = 1 then 943 else 951)) else (if t 2 = 0 then (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 974) else if t 2 = 1 then (if t 3 = 0 then 997 else if t 3 = 1 then 941 else 950) else (if t 3 = 0 then 999 else if t 3 = 1 then 944 else 952))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 176 else 3240) else if t 2 = 1 then (if t 3 = 0 then 1806 else if t 3 = 1 then 166 else 1494) else (if t 3 = 0 then 4059 else if t 3 = 1 then 168 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 102 else if t 3 = 1 then 971 else 975) else if t 2 = 1 then (if t 3 = 0 then 96 else if t 3 = 1 then 945 else 953) else (if t 3 = 0 then 98 else if t 3 = 1 then 947 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 103 else if t 3 = 1 then 972 else 976) else if t 2 = 1 then (if t 3 = 0 then 97 else if t 3 = 1 then 946 else 954) else (if t 3 = 0 then 99 else if t 3 = 1 then 948 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4368 else (if jt.2.val < 2 then 4393 else 4379)) else (if jt.2.val < 4 then 4392 else (if jt.2.val < 5 then 4394 else 4376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4248 else (if jt.2.val < 2 then 4258 else 4250)) else (if jt.2.val < 4 then 4257 else (if jt.2.val < 5 then 4259 else 4245)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 933 else (if jt.2.val < 2 then 935 else 970)) else (if jt.2.val < 4 then 934 else (if jt.2.val < 5 then 969 else 942))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 911 else (if jt.2.val < 2 then 983 else 913)) else (if jt.2.val < 4 then 981 else (if jt.2.val < 5 then 982 else 908)))))

checked_coverage fastCoverage0437 pairing0437 template0437 witness0437

theorem coverage0437 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0437) (maskBits m))
    cores template0437 witness0437 := by
  rw [← coresFast_eq]
  exact fastCoverage0437

theorem coverageSize0437 : ∀ q : Pattern,
    (cores (witness0437 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0437 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0437
#print axioms coverageSize0437

noncomputable def pairing0438 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0438 : List (Fin 4935) := templateData0438

noncomputable def witness0438 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 624 else 1148) else if t 2 = 1 then (if t 3 = 0 then 626 else if t 3 = 1 then 622 else 1144) else (if t 3 = 0 then 648 else if t 3 = 1 then 646 else 1145)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 620 else if t 3 = 1 then 616 else 688) else if t 2 = 1 then (if t 3 = 0 then 618 else if t 3 = 1 then 614 else 680) else (if t 3 = 0 then 644 else if t 3 = 1 then 641 else 681)) else (if t 2 = 0 then (if t 3 = 0 then 3320 else if t 3 = 1 then 3172 else 3182) else if t 2 = 1 then (if t 3 = 0 then 2768 else if t 3 = 1 then 2766 else 2778) else (if t 3 = 0 then 4058 else if t 3 = 1 then 3945 else 3951))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 623 else 1146) else if t 2 = 1 then (if t 3 = 0 then 625 else if t 3 = 1 then 621 else 1140) else (if t 3 = 0 then 647 else if t 3 = 1 then 645 else 1142)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 619 else if t 3 = 1 then 615 else 684) else if t 2 = 1 then (if t 3 = 0 then 617 else if t 3 = 1 then 613 else 672) else (if t 3 = 0 then 643 else if t 3 = 1 then 640 else 674)) else (if t 2 = 0 then (if t 3 = 0 then 635 else if t 3 = 1 then 633 else 685) else if t 2 = 1 then (if t 3 = 0 then 634 else if t 3 = 1 then 632 else 673) else (if t 3 = 0 then 650 else if t 3 = 1 then 649 else 675))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 660 else 4061) else if t 2 = 1 then (if t 3 = 0 then 1518 else if t 3 = 1 then 658 else 1824) else (if t 3 = 0 then 3206 else if t 3 = 1 then 668 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1133 else if t 3 = 1 then 655 else 686) else if t 2 = 1 then (if t 3 = 0 then 1131 else if t 3 = 1 then 653 else 676) else (if t 3 = 0 then 1137 else if t 3 = 1 then 666 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 1136 else if t 3 = 1 then 663 else 687) else if t 2 = 1 then (if t 3 = 0 then 1135 else if t 3 = 1 then 662 else 677) else (if t 3 = 0 then 1139 else if t 3 = 1 then 670 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4407 else (if jt.2.val < 2 then 4427 else 4416)) else (if jt.2.val < 4 then 4425 else (if jt.2.val < 5 then 4426 else 4414))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3563 else (if jt.2.val < 2 then 3590 else 3566)) else (if jt.2.val < 4 then 3588 else (if jt.2.val < 5 then 3589 else 3555)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 247 else (if jt.2.val < 2 then 642 else 252)) else (if jt.2.val < 4 then 611 else (if jt.2.val < 5 then 612 else 215))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1122 else (if jt.2.val < 2 then 1124 else 1129)) else (if jt.2.val < 4 then 1123 else (if jt.2.val < 5 then 1128 else 1127)))))

checked_coverage fastCoverage0438 pairing0438 template0438 witness0438

theorem coverage0438 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0438) (maskBits m))
    cores template0438 witness0438 := by
  rw [← coresFast_eq]
  exact fastCoverage0438

theorem coverageSize0438 : ∀ q : Pattern,
    (cores (witness0438 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0438 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0438
#print axioms coverageSize0438

noncomputable def pairing0439 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0439 : List (Fin 4935) := templateData0439

noncomputable def witness0439 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1205 else 764) else if t 2 = 1 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1201 else 757) else (if t 3 = 0 then 1222 else if t 3 = 1 then 1202 else 758)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1214 else if t 3 = 1 then 1187 else 1189) else if t 2 = 1 then (if t 3 = 0 then 1210 else if t 3 = 1 then 1167 else 1172) else (if t 3 = 0 then 1211 else if t 3 = 1 then 1169 else 1173)) else (if t 2 = 0 then (if t 3 = 0 then 3106 else if t 3 = 1 then 3329 else 3330) else if t 2 = 1 then (if t 3 = 0 then 3003 else if t 3 = 1 then 2993 else 2996) else (if t 3 = 0 then 3967 else if t 3 = 1 then 4054 else 4056))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1203 else 761) else if t 2 = 1 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1197 else 751) else (if t 3 = 0 then 1221 else if t 3 = 1 then 1199 else 753)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1212 else if t 3 = 1 then 1179 else 1183) else if t 2 = 1 then (if t 3 = 0 then 1206 else if t 3 = 1 then 1151 else 1159) else (if t 3 = 0 then 1208 else if t 3 = 1 then 1153 else 1161)) else (if t 2 = 0 then (if t 3 = 0 then 1213 else if t 3 = 1 then 1180 else 1184) else if t 2 = 1 then (if t 3 = 0 then 1207 else if t 3 = 1 then 1152 else 1160) else (if t 3 = 0 then 1209 else if t 3 = 1 then 1154 else 1162))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 572 else 3966) else if t 2 = 1 then (if t 3 = 0 then 1836 else if t 3 = 1 then 562 else 1542) else (if t 3 = 0 then 3343 else if t 3 = 1 then 564 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 504 else if t 3 = 1 then 1181 else 1185) else if t 2 = 1 then (if t 3 = 0 then 498 else if t 3 = 1 then 1155 else 1163) else (if t 3 = 0 then 500 else if t 3 = 1 then 1157 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 505 else if t 3 = 1 then 1182 else 1186) else if t 2 = 1 then (if t 3 = 0 then 499 else if t 3 = 1 then 1156 else 1164) else (if t 3 = 0 then 501 else if t 3 = 1 then 1158 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4431 else (if jt.2.val < 2 then 4447 else 4442)) else (if jt.2.val < 4 then 4446 else (if jt.2.val < 5 then 4448 else 4439))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3570 else (if jt.2.val < 2 then 3592 else 3572)) else (if jt.2.val < 4 then 3591 else (if jt.2.val < 5 then 3593 else 3567)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 942 else (if jt.2.val < 2 then 1177 else 970)) else (if jt.2.val < 4 then 1176 else (if jt.2.val < 5 then 1178 else 933))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1127 else (if jt.2.val < 2 then 1193 else 1129)) else (if jt.2.val < 4 then 1191 else (if jt.2.val < 5 then 1192 else 1122)))))

checked_coverage fastCoverage0439 pairing0439 template0439 witness0439

theorem coverage0439 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0439) (maskBits m))
    cores template0439 witness0439 := by
  rw [← coresFast_eq]
  exact fastCoverage0439

theorem coverageSize0439 : ∀ q : Pattern,
    (cores (witness0439 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0439 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0439
#print axioms coverageSize0439

end Crown.CertificateData
