import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0013

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0520 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0520 : List (Fin 4935) := templateData0520

noncomputable def witness0520 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 3941) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2788) else (if t 3 = 0 then 2779 else if t 3 = 1 then 2778 else 2989)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 726) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 725) else (if t 3 = 0 then 682 else if t 3 = 1 then 680 else 1144)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2197 else 1490) else if t 2 = 1 then (if t 3 = 0 then 2200 else if t 3 = 1 then 2196 else 742) else (if t 3 = 0 then 689 else if t 3 = 1 then 688 else 1148))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 35) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 34) else (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 901)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2462) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4170) else (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4183)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2475) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4171) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4180 else 4184))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 822 else 71) else if t 2 = 1 then (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 70) else (if t 3 = 0 then 1502 else if t 3 = 1 then 202 else 2128)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2487) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4177) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4181 else 4185)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2842 else 2491) else if t 2 = 1 then (if t 3 = 0 then 4004 else if t 3 = 1 then 4164 else 4178) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4182 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4692 else (if jt.2.val < 2 then 4702 else 4703)) else (if jt.2.val < 4 then 4699 else (if jt.2.val < 5 then 4701 else 4700))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4693 else (if jt.2.val < 2 then 4697 else 4698)) else (if jt.2.val < 4 then 4694 else (if jt.2.val < 5 then 4696 else 4695)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4215 else (if jt.2.val < 2 then 4223 else 4226)) else (if jt.2.val < 4 then 4222 else (if jt.2.val < 5 then 4225 else 4224))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4216 else (if jt.2.val < 2 then 4220 else 4221)) else (if jt.2.val < 4 then 4217 else (if jt.2.val < 5 then 4219 else 4218)))))

checked_coverage fastCoverage0520 pairing0520 template0520 witness0520

theorem coverage0520 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0520) (maskBits m))
    cores template0520 witness0520 := by
  rw [← coresFast_eq]
  exact fastCoverage0520

theorem coverageSize0520 : ∀ q : Pattern,
    (cores (witness0520 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0520 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0520
#print axioms coverageSize0520

noncomputable def pairing0521 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0521 : List (Fin 4935) := templateData0521

noncomputable def witness0521 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4196) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2787) else (if t 3 = 0 then 2981 else if t 3 = 1 then 2980 else 2800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 724) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 723) else (if t 3 = 0 then 1090 else if t 3 = 1 then 1078 else 784)) else (if t 2 = 0 then (if t 3 = 0 then 1652 else if t 3 = 1 then 1648 else 2159) else if t 2 = 1 then (if t 3 = 0 then 1651 else if t 3 = 1 then 1647 else 741) else (if t 3 = 0 then 1094 else if t 3 = 1 then 1080 else 786))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 33) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 32) else (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 97)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2461) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3834) else (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3854)) else (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2474) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3837) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3853 else 3855))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 241 else 920) else if t 2 = 1 then (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 919) else (if t 3 = 0 then 2141 else if t 3 = 1 then 301 else 1477)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2899) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3848) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3856 else 3858)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2626 else 2901) else if t 2 = 1 then (if t 3 = 0 then 3847 else if t 3 = 1 then 3846 else 3850) else (if t 3 = 0 then 4192 else if t 3 = 1 then 3857 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4674 else (if jt.2.val < 2 then 4678 else 4679)) else (if jt.2.val < 4 then 4675 else (if jt.2.val < 5 then 4677 else 4676))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4396 else (if jt.2.val < 2 then 4400 else 4401)) else (if jt.2.val < 4 then 4397 else (if jt.2.val < 5 then 4399 else 4398)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4082 else (if jt.2.val < 2 then 4084 else 4088)) else (if jt.2.val < 4 then 4083 else (if jt.2.val < 5 then 4087 else 4086))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4218 else (if jt.2.val < 2 then 4229 else 4221)) else (if jt.2.val < 4 then 4227 else (if jt.2.val < 5 then 4228 else 4216)))))

checked_coverage fastCoverage0521 pairing0521 template0521 witness0521

theorem coverage0521 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0521) (maskBits m))
    cores template0521 witness0521 := by
  rw [← coresFast_eq]
  exact fastCoverage0521

theorem coverageSize0521 : ∀ q : Pattern,
    (cores (witness0521 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0521 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0521
#print axioms coverageSize0521

noncomputable def pairing0522 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0522 : List (Fin 4935) := templateData0522

noncomputable def witness0522 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2565 else 2884) else if t 2 = 1 then (if t 3 = 0 then 2560 else if t 3 = 1 then 2544 else 2546) else (if t 3 = 0 then 4190 else if t 3 = 1 then 3945 else 3946)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2563 else 1762) else if t 2 = 1 then (if t 3 = 0 then 2558 else if t 3 = 1 then 2538 else 1747) else (if t 3 = 0 then 667 else if t 3 = 1 then 641 else 646)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 291 else 929) else if t 2 = 1 then (if t 3 = 0 then 277 else if t 3 = 1 then 251 else 256) else (if t 3 = 0 then 2170 else if t 3 = 1 then 1459 else 1462))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2564 else 1915) else if t 2 = 1 then (if t 3 = 0 then 2559 else if t 3 = 1 then 2541 else 1900) else (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 153)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2562 else 2883) else if t 2 = 1 then (if t 3 = 0 then 2548 else if t 3 = 1 then 2519 else 2530) else (if t 3 = 0 then 2549 else if t 3 = 1 then 2521 else 2531)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2572 else 2886) else if t 2 = 1 then (if t 3 = 0 then 2550 else if t 3 = 1 then 2523 else 2532) else (if t 3 = 0 then 2551 else if t 3 = 1 then 2524 else 2533))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1687 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1666 else 1668) else (if t 3 = 0 then 895 else if t 3 = 1 then 151 else 155)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2576 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2878 else if t 3 = 1 then 2526 else 2534) else (if t 3 = 0 then 2879 else if t 3 = 1 then 2527 else 2535)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2579 else 4197) else if t 2 = 1 then (if t 3 = 0 then 2880 else if t 3 = 1 then 2528 else 2536) else (if t 3 = 0 then 2881 else if t 3 = 1 then 2529 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4629 else (if jt.2.val < 2 then 4631 else 4634)) else (if jt.2.val < 4 then 4630 else (if jt.2.val < 5 then 4633 else 4632))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2513 else (if jt.2.val < 2 then 2515 else 2543)) else (if jt.2.val < 4 then 2514 else (if jt.2.val < 5 then 2542 else 2522)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4224 else (if jt.2.val < 2 then 4232 else 4226)) else (if jt.2.val < 4 then 4230 else (if jt.2.val < 5 then 4231 else 4215))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2871 else (if jt.2.val < 2 then 2873 else 2877)) else (if jt.2.val < 4 then 2872 else (if jt.2.val < 5 then 2876 else 2875)))))

checked_coverage fastCoverage0522 pairing0522 template0522 witness0522

theorem coverage0522 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0522) (maskBits m))
    cores template0522 witness0522 := by
  rw [← coresFast_eq]
  exact fastCoverage0522

theorem coverageSize0522 : ∀ q : Pattern,
    (cores (witness0522 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0522 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0522
#print axioms coverageSize0522

noncomputable def pairing0523 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0523 : List (Fin 4935) := templateData0523

noncomputable def witness0523 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2960 else 2506) else if t 2 = 1 then (if t 3 = 0 then 2953 else if t 3 = 1 then 2937 else 2938) else (if t 3 = 0 then 3905 else if t 3 = 1 then 4046 else 4198)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2958 else 1756) else if t 2 = 1 then (if t 3 = 0 then 2951 else if t 3 = 1 then 2931 else 1730) else (if t 3 = 0 then 1075 else if t 3 = 1 then 1046 else 1049)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 868 else 406) else if t 2 = 1 then (if t 3 = 0 then 859 else if t 3 = 1 then 830 else 833) else (if t 3 = 0 then 1599 else if t 3 = 1 then 1813 else 2146))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2959 else 1909) else if t 2 = 1 then (if t 3 = 0 then 2952 else if t 3 = 1 then 2934 else 1888) else (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 972)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2954 else 2502) else if t 2 = 1 then (if t 3 = 0 then 2947 else if t 3 = 1 then 2913 else 2919) else (if t 3 = 0 then 2948 else if t 3 = 1 then 2915 else 2920)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2956 else 2504) else if t 2 = 1 then (if t 3 = 0 then 2949 else if t 3 = 1 then 2917 else 2921) else (if t 3 = 0 then 2950 else if t 3 = 1 then 2918 else 2922))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2224 else 1621) else if t 2 = 1 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2206 else 1890) else (if t 3 = 0 then 378 else if t 3 = 1 then 974 else 976)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2650 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2699 else if t 3 = 1 then 2923 else 2927) else (if t 3 = 0 then 2700 else if t 3 = 1 then 2924 else 2928)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2652 else 3928) else if t 2 = 1 then (if t 3 = 0 then 2701 else if t 3 = 1 then 2925 else 2929) else (if t 3 = 0 then 2702 else if t 3 = 1 then 2926 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4659 else (if jt.2.val < 2 then 4661 else 4664)) else (if jt.2.val < 4 then 4660 else (if jt.2.val < 5 then 4663 else 4662))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2907 else (if jt.2.val < 2 then 2909 else 2936)) else (if jt.2.val < 4 then 2908 else (if jt.2.val < 5 then 2935 else 2916)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4086 else (if jt.2.val < 2 then 4094 else 4088)) else (if jt.2.val < 4 then 4092 else (if jt.2.val < 5 then 4093 else 4082))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2875 else (if jt.2.val < 2 then 2945 else 2877)) else (if jt.2.val < 4 then 2944 else (if jt.2.val < 5 then 2946 else 2871)))))

checked_coverage fastCoverage0523 pairing0523 template0523 witness0523

theorem coverage0523 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0523) (maskBits m))
    cores template0523 witness0523 := by
  rw [← coresFast_eq]
  exact fastCoverage0523

theorem coverageSize0523 : ∀ q : Pattern,
    (cores (witness0523 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0523 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0523
#print axioms coverageSize0523

noncomputable def pairing0524 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0524 : List (Fin 4935) := templateData0524

noncomputable def witness0524 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1510) else if t 2 = 1 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 48) else (if t 3 = 0 then 195 else if t 3 = 1 then 193 else 904)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 450) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2090) else (if t 3 = 0 then 1447 else if t 3 = 1 then 2101 else 2107)) else (if t 2 = 0 then (if t 3 = 0 then 4213 else if t 3 = 1 then 4211 else 3930) else if t 2 = 1 then (if t 3 = 0 then 3531 else if t 3 = 1 then 3528 else 2690) else (if t 3 = 0 then 2649 else if t 3 = 1 then 2648 else 2906))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1509) else if t 2 = 1 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 47) else (if t 3 = 0 then 194 else if t 3 = 1 then 192 else 903)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 449) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2089) else (if t 3 = 0 then 1446 else if t 3 = 1 then 2100 else 2106)) else (if t 2 = 0 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 455) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2091) else (if t 3 = 0 then 1448 else if t 3 = 1 then 2102 else 2108))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 1815 else 2739) else if t 2 = 1 then (if t 3 = 0 then 836 else if t 3 = 1 then 834 else 74) else (if t 3 = 0 then 3952 else if t 3 = 1 then 204 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1050 else 476) else if t 2 = 1 then (if t 3 = 0 then 1732 else if t 3 = 1 then 2081 else 2097) else (if t 3 = 0 then 1452 else if t 3 = 1 then 2103 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 1057 else if t 3 = 1 then 1056 else 479) else if t 2 = 1 then (if t 3 = 0 then 1735 else if t 3 = 1 then 2083 else 2099) else (if t 3 = 0 then 1454 else if t 3 = 1 then 2105 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4659 else (if jt.2.val < 2 then 4670 else 4664)) else (if jt.2.val < 4 then 4668 else (if jt.2.val < 5 then 4669 else 4662))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4695 else (if jt.2.val < 2 then 4706 else 4698)) else (if jt.2.val < 4 then 4704 else (if jt.2.val < 5 then 4705 else 4693)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2412 else (if jt.2.val < 2 then 2414 else 2417)) else (if jt.2.val < 4 then 2413 else (if jt.2.val < 5 then 2416 else 2415))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2233 else (if jt.2.val < 2 then 2237 else 2238)) else (if jt.2.val < 4 then 2234 else (if jt.2.val < 5 then 2236 else 2235)))))

checked_coverage fastCoverage0524 pairing0524 template0524 witness0524

theorem coverage0524 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0524) (maskBits m))
    cores template0524 witness0524 := by
  rw [← coresFast_eq]
  exact fastCoverage0524

theorem coverageSize0524 : ∀ q : Pattern,
    (cores (witness0524 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0524 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0524
#print axioms coverageSize0524

noncomputable def pairing0525 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0525 : List (Fin 4935) := templateData0525

noncomputable def witness0525 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 2125) else if t 2 = 1 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 46) else (if t 3 = 0 then 1012 else if t 3 = 1 then 1001 else 101)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 448) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1339) else (if t 3 = 0 then 1777 else if t 3 = 1 then 1370 else 1371)) else (if t 2 = 0 then (if t 3 = 0 then 3965 else if t 3 = 1 then 3963 else 4205) else if t 2 = 1 then (if t 3 = 0 then 3235 else if t 3 = 1 then 3232 else 2689) else (if t 3 = 0 then 2868 else if t 3 = 1 then 2860 else 2722))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 2124) else if t 2 = 1 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 45) else (if t 3 = 0 then 1011 else if t 3 = 1 then 998 else 98)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 447) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1338) else (if t 3 = 0 then 1776 else if t 3 = 1 then 1362 else 1364)) else (if t 2 = 0 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 454) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1343) else (if t 3 = 0 then 1778 else if t 3 = 1 then 1363 else 1365))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1785 else 2988) else if t 2 = 1 then (if t 3 = 0 then 257 else if t 3 = 1 then 253 else 921) else (if t 3 = 0 then 4206 else if t 3 = 1 then 302 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 647 else if t 3 = 1 then 643 else 1137) else if t 2 = 1 then (if t 3 = 0 then 1352 else if t 3 = 1 then 1349 else 1356) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1366 else 1368)) else (if t 2 = 0 then (if t 3 = 0 then 652 else if t 3 = 1 then 650 else 1139) else if t 2 = 1 then (if t 3 = 0 then 1355 else if t 3 = 1 then 1354 else 1360) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1367 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4629 else (if jt.2.val < 2 then 4637 else 4634)) else (if jt.2.val < 4 then 4635 else (if jt.2.val < 5 then 4636 else 4632))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4398 else (if jt.2.val < 2 then 4421 else 4401)) else (if jt.2.val < 4 then 4419 else (if jt.2.val < 5 then 4420 else 4396)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2382 else (if jt.2.val < 2 then 2384 else 2387)) else (if jt.2.val < 4 then 2383 else (if jt.2.val < 5 then 2386 else 2385))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2235 else (if jt.2.val < 2 then 2246 else 2238)) else (if jt.2.val < 4 then 2244 else (if jt.2.val < 5 then 2245 else 2233)))))

checked_coverage fastCoverage0525 pairing0525 template0525 witness0525

theorem coverage0525 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0525) (maskBits m))
    cores template0525 witness0525 := by
  rw [← coresFast_eq]
  exact fastCoverage0525

theorem coverageSize0525 : ∀ q : Pattern,
    (cores (witness0525 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0525 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0525
#print axioms coverageSize0525

noncomputable def pairing0526 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0526 : List (Fin 4935) := templateData0526

noncomputable def witness0526 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 579 else 1116) else if t 2 = 1 then (if t 3 = 0 then 574 else if t 3 = 1 then 552 else 554) else (if t 3 = 0 then 2117 else if t 3 = 1 then 1537 else 1538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 581 else if t 3 = 1 then 577 else 1114) else if t 2 = 1 then (if t 3 = 0 then 566 else if t 3 = 1 then 532 else 537) else (if t 3 = 0 then 567 else if t 3 = 1 then 534 else 538)) else (if t 2 = 0 then (if t 3 = 0 then 2760 else if t 3 = 1 then 2759 else 2985) else if t 2 = 1 then (if t 3 = 0 then 2756 else if t 3 = 1 then 2747 else 2750) else (if t 3 = 0 then 4207 else if t 3 = 1 then 3923 else 3925))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 578 else 1115) else if t 2 = 1 then (if t 3 = 0 then 570 else if t 3 = 1 then 544 else 548) else (if t 3 = 0 then 2115 else if t 3 = 1 then 1531 else 1535)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 580 else if t 3 = 1 then 576 else 1113) else if t 2 = 1 then (if t 3 = 0 then 556 else if t 3 = 1 then 515 else 524) else (if t 3 = 0 then 558 else if t 3 = 1 then 517 else 526)) else (if t 2 = 0 then (if t 3 = 0 then 586 else if t 3 = 1 then 584 else 1117) else if t 2 = 1 then (if t 3 = 0 then 557 else if t 3 = 1 then 516 else 525) else (if t 3 = 0 then 559 else if t 3 = 1 then 518 else 527))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 596 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1110 else if t 3 = 1 then 546 else 550) else (if t 3 = 0 then 2984 else if t 3 = 1 then 1833 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1548 else if t 3 = 1 then 594 else 2148) else if t 2 = 1 then (if t 3 = 0 then 1104 else if t 3 = 1 then 520 else 528) else (if t 3 = 0 then 1106 else if t 3 = 1 then 522 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 1550 else if t 3 = 1 then 598 else 2149) else if t 2 = 1 then (if t 3 = 0 then 1105 else if t 3 = 1 then 521 else 529) else (if t 3 = 0 then 1107 else if t 3 = 1 then 523 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4674 else (if jt.2.val < 2 then 4690 else 4679)) else (if jt.2.val < 4 then 4689 else (if jt.2.val < 5 then 4691 else 4676))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2522 else (if jt.2.val < 2 then 2753 else 2543)) else (if jt.2.val < 4 then 2752 else (if jt.2.val < 5 then 2754 else 2513)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2415 else (if jt.2.val < 2 then 2426 else 2417)) else (if jt.2.val < 4 then 2424 else (if jt.2.val < 5 then 2425 else 2412))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1095 else (if jt.2.val < 2 then 1097 else 1103)) else (if jt.2.val < 4 then 1096 else (if jt.2.val < 5 then 1102 else 1101)))))

checked_coverage fastCoverage0526 pairing0526 template0526 witness0526

theorem coverage0526 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0526) (maskBits m))
    cores template0526 witness0526 := by
  rw [← coresFast_eq]
  exact fastCoverage0526

theorem coverageSize0526 : ∀ q : Pattern,
    (cores (witness0526 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0526 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0526
#print axioms coverageSize0526

noncomputable def pairing0527 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0527 : List (Fin 4935) := templateData0527

noncomputable def witness0527 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1214 else 506) else if t 2 = 1 then (if t 3 = 0 then 1205 else if t 3 = 1 then 1187 else 1188) else (if t 3 = 0 then 1433 else if t 3 = 1 then 1801 else 2138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1210 else 502) else if t 2 = 1 then (if t 3 = 0 then 1201 else if t 3 = 1 then 1167 else 1170) else (if t 3 = 0 then 1202 else if t 3 = 1 then 1169 else 1171)) else (if t 2 = 0 then (if t 3 = 0 then 3004 else if t 3 = 1 then 3003 else 2743) else if t 2 = 1 then (if t 3 = 0 then 3002 else if t 3 = 1 then 2993 else 2995) else (if t 3 = 0 then 3954 else if t 3 = 1 then 4054 else 4203))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1212 else 504) else if t 2 = 1 then (if t 3 = 0 then 1203 else if t 3 = 1 then 1179 else 1181) else (if t 3 = 0 then 1430 else if t 3 = 1 then 1795 else 2136)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1206 else 498) else if t 2 = 1 then (if t 3 = 0 then 1197 else if t 3 = 1 then 1151 else 1155) else (if t 3 = 0 then 1199 else if t 3 = 1 then 1153 else 1157)) else (if t 2 = 0 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1207 else 499) else if t 2 = 1 then (if t 3 = 0 then 1198 else if t 3 = 1 then 1152 else 1156) else (if t 3 = 0 then 1200 else if t 3 = 1 then 1154 else 1158))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 696 else 3960) else if t 2 = 1 then (if t 3 = 0 then 761 else if t 3 = 1 then 1183 else 1185) else (if t 3 = 0 then 2796 else if t 3 = 1 then 1799 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2160 else if t 3 = 1 then 690 else 1524) else if t 2 = 1 then (if t 3 = 0 then 751 else if t 3 = 1 then 1159 else 1163) else (if t 3 = 0 then 753 else if t 3 = 1 then 1161 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 2162 else if t 3 = 1 then 691 else 1525) else if t 2 = 1 then (if t 3 = 0 then 752 else if t 3 = 1 then 1160 else 1164) else (if t 3 = 0 then 754 else if t 3 = 1 then 1162 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4692 else (if jt.2.val < 2 then 4708 else 4703)) else (if jt.2.val < 4 then 4707 else (if jt.2.val < 5 then 4709 else 4700))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2916 else (if jt.2.val < 2 then 2999 else 2936)) else (if jt.2.val < 4 then 2998 else (if jt.2.val < 5 then 3000 else 2907)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2385 else (if jt.2.val < 2 then 2405 else 2387)) else (if jt.2.val < 4 then 2403 else (if jt.2.val < 5 then 2404 else 2382))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1101 else (if jt.2.val < 2 then 1195 else 1103)) else (if jt.2.val < 4 then 1194 else (if jt.2.val < 5 then 1196 else 1095)))))

checked_coverage fastCoverage0527 pairing0527 template0527 witness0527

theorem coverage0527 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0527) (maskBits m))
    cores template0527 witness0527 := by
  rw [← coresFast_eq]
  exact fastCoverage0527

theorem coverageSize0527 : ∀ q : Pattern,
    (cores (witness0527 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0527 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0527
#print axioms coverageSize0527

noncomputable def pairing0528 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0528 : List (Fin 4935) := templateData0528

noncomputable def witness0528 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 3860) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2980) else (if t 3 = 0 then 3236 else if t 3 = 1 then 3234 else 3242)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 1084) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 1078) else (if t 3 = 0 then 1651 else if t 3 = 1 then 1647 else 1080)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 724 else 790) else if t 2 = 1 then (if t 3 = 0 then 727 else if t 3 = 1 then 723 else 784) else (if t 3 = 0 then 743 else if t 3 = 1 then 741 else 786))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 1003) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 997) else (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 999)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2955) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3852) else (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3853)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2503) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3854) else (if t 3 = 0 then 3838 else if t 3 = 1 then 3837 else 3855))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 241 else 307) else if t 2 = 1 then (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 301) else (if t 3 = 0 then 262 else if t 3 = 1 then 260 else 303)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2651) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3856) else (if t 3 = 0 then 3847 else if t 3 = 1 then 3846 else 3857)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2899 else 3184) else if t 2 = 1 then (if t 3 = 0 then 3849 else if t 3 = 1 then 3848 else 3858) else (if t 3 = 0 then 3851 else if t 3 = 1 then 3850 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4674 else (if jt.2.val < 2 then 4678 else 4679)) else (if jt.2.val < 4 then 4675 else (if jt.2.val < 5 then 4677 else 4676))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3805 else (if jt.2.val < 2 then 3833 else 3835)) else (if jt.2.val < 4 then 3830 else (if jt.2.val < 5 then 3832 else 3831)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4449 else (if jt.2.val < 2 then 4453 else 4454)) else (if jt.2.val < 4 then 4450 else (if jt.2.val < 5 then 4452 else 4451))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3798 else (if jt.2.val < 2 then 3800 else 3803)) else (if jt.2.val < 4 then 3799 else (if jt.2.val < 5 then 3802 else 3801)))))

checked_coverage fastCoverage0528 pairing0528 template0528 witness0528

theorem coverage0528 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0528) (maskBits m))
    cores template0528 witness0528 := by
  rw [← coresFast_eq]
  exact fastCoverage0528

theorem coverageSize0528 : ∀ q : Pattern,
    (cores (witness0528 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0528 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0528
#print axioms coverageSize0528

noncomputable def pairing0529 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0529 : List (Fin 4935) := templateData0529

noncomputable def witness0529 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 3905) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2979) else (if t 3 = 0 then 3228 else if t 3 = 1 then 3225 else 3226)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 1075) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 1069) else (if t 3 = 0 then 1612 else if t 3 = 1 then 1593 else 1071)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 667 else 669) else if t 2 = 1 then (if t 3 = 0 then 682 else if t 3 = 1 then 654 else 659) else (if t 3 = 0 then 689 else if t 3 = 1 then 656 else 661))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 994) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 988) else (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 990)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2948) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3884) else (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3885)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2555) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3886) else (if t 3 = 0 then 3916 else if t 3 = 1 then 3878 else 3887))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 376 else 378) else if t 2 = 1 then (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 368) else (if t 3 = 0 then 398 else if t 3 = 1 then 366 else 370)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2700) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3888) else (if t 3 = 0 then 3918 else if t 3 = 1 then 3881 else 3889)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2879 else 3197) else if t 2 = 1 then (if t 3 = 0 then 3919 else if t 3 = 1 then 3882 else 3890) else (if t 3 = 0 then 3920 else if t 3 = 1 then 3883 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4680 else (if jt.2.val < 2 then 4682 else 4685)) else (if jt.2.val < 4 then 4681 else (if jt.2.val < 5 then 4684 else 4683))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3867 else (if jt.2.val < 2 then 3869 else 3897)) else (if jt.2.val < 4 then 3868 else (if jt.2.val < 5 then 3896 else 3876)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4455 else (if jt.2.val < 2 then 4457 else 4460)) else (if jt.2.val < 4 then 4456 else (if jt.2.val < 5 then 4459 else 4458))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3801 else (if jt.2.val < 2 then 3863 else 3803)) else (if jt.2.val < 4 then 3861 else (if jt.2.val < 5 then 3862 else 3798)))))

checked_coverage fastCoverage0529 pairing0529 template0529 witness0529

theorem coverage0529 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0529) (maskBits m))
    cores template0529 witness0529 := by
  rw [← coresFast_eq]
  exact fastCoverage0529

theorem coverageSize0529 : ∀ q : Pattern,
    (cores (witness0529 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0529 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0529
#print axioms coverageSize0529

noncomputable def pairing0530 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0530 : List (Fin 4935) := templateData0530

noncomputable def witness0530 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3106) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 3003) else (if t 3 = 0 then 3965 else if t 3 = 1 then 3963 else 3967)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 868) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 862) else (if t 3 = 0 then 1650 else if t 3 = 1 then 1646 else 864)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 341 else 406) else if t 2 = 1 then (if t 3 = 0 then 344 else if t 3 = 1 then 340 else 400) else (if t 3 = 0 then 359 else if t 3 = 1 then 357 else 402))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 1213) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 1207) else (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 1209)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2956) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3098) else (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3099)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2504) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3080 else 3100) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3083 else 3101))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 635 else 697) else if t 2 = 1 then (if t 3 = 0 then 638 else if t 3 = 1 then 634 else 691) else (if t 3 = 0 then 652 else if t 3 = 1 then 650 else 693)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2622 else 2652) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3089 else 3102) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3092 else 3103)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2900 else 3928) else if t 2 = 1 then (if t 3 = 0 then 3095 else if t 3 = 1 then 3094 else 3104) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3096 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4611 else (if jt.2.val < 2 then 4615 else 4616)) else (if jt.2.val < 4 then 4612 else (if jt.2.val < 5 then 4614 else 4613))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3049 else (if jt.2.val < 2 then 3079 else 3081)) else (if jt.2.val < 4 then 3076 else (if jt.2.val < 5 then 3078 else 3077)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4451 else (if jt.2.val < 2 then 4463 else 4454)) else (if jt.2.val < 4 then 4461 else (if jt.2.val < 5 then 4462 else 4449))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3042 else (if jt.2.val < 2 then 3044 else 3047)) else (if jt.2.val < 4 then 3043 else (if jt.2.val < 5 then 3046 else 3045)))))

checked_coverage fastCoverage0530 pairing0530 template0530 witness0530

theorem coverage0530 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0530) (maskBits m))
    cores template0530 witness0530 := by
  rw [← coresFast_eq]
  exact fastCoverage0530

theorem coverageSize0530 : ∀ q : Pattern,
    (cores (witness0530 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0530 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0530
#print axioms coverageSize0530

noncomputable def pairing0531 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0531 : List (Fin 4935) := templateData0531

noncomputable def witness0531 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3152) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 3002) else (if t 3 = 0 then 3959 else if t 3 = 1 then 3953 else 3954)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 859) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 853) else (if t 3 = 0 then 1611 else if t 3 = 1 then 1589 else 855)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 277 else 279) else if t 2 = 1 then (if t 3 = 0 then 292 else if t 3 = 1 then 264 else 269) else (if t 3 = 0 then 299 else if t 3 = 1 then 266 else 271))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 1204) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 1198) else (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 1200)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2949) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3130) else (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3131)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2556) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3123 else 3132) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3124 else 3133))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 760 else 762) else if t 2 = 1 then (if t 3 = 0 then 775 else if t 3 = 1 then 748 else 752) else (if t 3 = 0 then 782 else if t 3 = 1 then 750 else 754)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2697 else 2701) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3126 else 3134) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3127 else 3135)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2880 else 3934) else if t 2 = 1 then (if t 3 = 0 then 3167 else if t 3 = 1 then 3128 else 3136) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3129 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4617 else (if jt.2.val < 2 then 4619 else 4622)) else (if jt.2.val < 4 then 4618 else (if jt.2.val < 5 then 4621 else 4620))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3113 else (if jt.2.val < 2 then 3115 else 3143)) else (if jt.2.val < 4 then 3114 else (if jt.2.val < 5 then 3142 else 3122)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4458 else (if jt.2.val < 2 then 4465 else 4460)) else (if jt.2.val < 4 then 4464 else (if jt.2.val < 5 then 4466 else 4455))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3045 else (if jt.2.val < 2 then 3109 else 3047)) else (if jt.2.val < 4 then 3107 else (if jt.2.val < 5 then 3108 else 3042)))))

checked_coverage fastCoverage0531 pairing0531 template0531 witness0531

theorem coverage0531 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0531) (maskBits m))
    cores template0531 witness0531 := by
  rw [← coresFast_eq]
  exact fastCoverage0531

theorem coverageSize0531 : ∀ q : Pattern,
    (cores (witness0531 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0531 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0531
#print axioms coverageSize0531

noncomputable def pairing0532 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0532 : List (Fin 4935) := templateData0532

noncomputable def witness0532 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 16 else 104) else if t 2 = 1 then (if t 3 = 0 then 22 else if t 3 = 1 then 14 else 100) else (if t 3 = 0 then 50 else if t 3 = 1 then 46 else 101)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 20 else if t 3 = 1 then 12 else 94) else if t 2 = 1 then (if t 3 = 0 then 18 else if t 3 = 1 then 10 else 86) else (if t 3 = 0 then 48 else if t 3 = 1 then 43 else 87)) else (if t 2 = 0 then (if t 3 = 0 then 3941 else if t 3 = 1 then 3939 else 3943) else if t 2 = 1 then (if t 3 = 0 then 2788 else if t 3 = 1 then 2785 else 2797) else (if t 3 = 0 then 3192 else if t 3 = 1 then 3191 else 3198))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 15 else 102) else if t 2 = 1 then (if t 3 = 0 then 21 else if t 3 = 1 then 13 else 96) else (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 98)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 19 else if t 3 = 1 then 11 else 90) else if t 2 = 1 then (if t 3 = 0 then 17 else if t 3 = 1 then 9 else 78) else (if t 3 = 0 then 47 else if t 3 = 1 then 42 else 80)) else (if t 2 = 0 then (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 91) else if t 2 = 1 then (if t 3 = 0 then 34 else if t 3 = 1 then 29 else 79) else (if t 3 = 0 then 53 else if t 3 = 1 then 51 else 81))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 917 else 3229) else if t 2 = 1 then (if t 3 = 0 then 1470 else if t 3 = 1 then 915 else 1476) else (if t 3 = 0 then 3942 else if t 3 = 1 then 921 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 66 else if t 3 = 1 then 61 else 92) else if t 2 = 1 then (if t 3 = 0 then 64 else if t 3 = 1 then 59 else 82) else (if t 3 = 0 then 74 else if t 3 = 1 then 72 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 71 else if t 3 = 1 then 69 else 93) else if t 2 = 1 then (if t 3 = 0 then 70 else if t 3 = 1 then 68 else 83) else (if t 3 = 0 then 77 else if t 3 = 1 then 76 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4617 else (if jt.2.val < 2 then 4643 else 4622)) else (if jt.2.val < 4 then 4641 else (if jt.2.val < 5 then 4642 else 4620))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3831 else (if jt.2.val < 2 then 3940 else 3835)) else (if jt.2.val < 4 then 3937 else (if jt.2.val < 5 then 3938 else 3805)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 7 else (if jt.2.val < 2 then 41 else 44)) else (if jt.2.val < 4 then 38 else (if jt.2.val < 5 then 40 else 39))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 0 else (if jt.2.val < 2 then 2 else 5)) else (if jt.2.val < 4 then 1 else (if jt.2.val < 5 then 4 else 3)))))

checked_coverage fastCoverage0532 pairing0532 template0532 witness0532

theorem coverage0532 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0532) (maskBits m))
    cores template0532 witness0532 := by
  rw [← coresFast_eq]
  exact fastCoverage0532

theorem coverageSize0532 : ∀ q : Pattern,
    (cores (witness0532 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0532 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0532
#print axioms coverageSize0532

noncomputable def pairing0533 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0533 : List (Fin 4935) := templateData0533

noncomputable def witness0533 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 178 else 179) else if t 2 = 1 then (if t 3 = 0 then 185 else if t 3 = 1 then 170 else 172) else (if t 3 = 0 then 195 else if t 3 = 1 then 171 else 173)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 183 else if t 3 = 1 then 156 else 158) else if t 2 = 1 then (if t 3 = 0 then 181 else if t 3 = 1 then 136 else 142) else (if t 3 = 0 then 193 else if t 3 = 1 then 139 else 143)) else (if t 2 = 0 then (if t 3 = 0 then 3951 else if t 3 = 1 then 3945 else 3946) else if t 2 = 1 then (if t 3 = 0 then 2778 else if t 3 = 1 then 2766 else 2769) else (if t 3 = 0 then 3182 else if t 3 = 1 then 3172 else 3174))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 174 else 176) else if t 2 = 1 then (if t 3 = 0 then 184 else if t 3 = 1 then 160 else 166) else (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 168)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 182 else if t 3 = 1 then 146 else 152) else if t 2 = 1 then (if t 3 = 0 then 180 else if t 3 = 1 then 117 else 128) else (if t 3 = 0 then 192 else if t 3 = 1 then 121 else 130)) else (if t 2 = 0 then (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 153) else if t 2 = 1 then (if t 3 = 0 then 188 else if t 3 = 1 then 119 else 129) else (if t 3 = 0 then 196 else if t 3 = 1 then 122 else 131))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 894 else 3240) else if t 2 = 1 then (if t 3 = 0 then 1500 else if t 3 = 1 then 888 else 1494) else (if t 3 = 0 then 3952 else if t 3 = 1 then 890 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 200 else if t 3 = 1 then 150 else 154) else if t 2 = 1 then (if t 3 = 0 then 198 else if t 3 = 1 then 124 else 132) else (if t 3 = 0 then 204 else if t 3 = 1 then 126 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 203 else if t 3 = 1 then 151 else 155) else if t 2 = 1 then (if t 3 = 0 then 202 else if t 3 = 1 then 125 else 133) else (if t 3 = 0 then 206 else if t 3 = 1 then 127 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4611 else (if jt.2.val < 2 then 4645 else 4616)) else (if jt.2.val < 4 then 4644 else (if jt.2.val < 5 then 4646 else 4613))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3876 else (if jt.2.val < 2 then 3948 else 3897)) else (if jt.2.val < 4 then 3947 else (if jt.2.val < 5 then 3949 else 3867)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 111 else (if jt.2.val < 2 then 113 else 149)) else (if jt.2.val < 4 then 112 else (if jt.2.val < 5 then 148 else 120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3 else (if jt.2.val < 2 then 107 else 5)) else (if jt.2.val < 4 then 105 else (if jt.2.val < 5 then 106 else 0)))))

checked_coverage fastCoverage0533 pairing0533 template0533 witness0533

theorem coverage0533 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0533) (maskBits m))
    cores template0533 witness0533 := by
  rw [← coresFast_eq]
  exact fastCoverage0533

theorem coverageSize0533 : ∀ q : Pattern,
    (cores (witness0533 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0533 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0533
#print axioms coverageSize0533

noncomputable def pairing0534 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0534 : List (Fin 4935) := templateData0534

noncomputable def witness0534 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 424 else 506) else if t 2 = 1 then (if t 3 = 0 then 430 else if t 3 = 1 then 422 else 502) else (if t 3 = 0 then 452 else if t 3 = 1 then 448 else 503)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 428 else if t 3 = 1 then 420 else 496) else if t 2 = 1 then (if t 3 = 0 then 426 else if t 3 = 1 then 418 else 488) else (if t 3 = 0 then 450 else if t 3 = 1 then 445 else 489)) else (if t 2 = 0 then (if t 3 = 0 then 3205 else if t 3 = 1 then 3203 else 3207) else if t 2 = 1 then (if t 3 = 0 then 2731 else if t 3 = 1 then 2728 else 2740) else (if t 3 = 0 then 3930 else if t 3 = 1 then 3929 else 3935))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 423 else 504) else if t 2 = 1 then (if t 3 = 0 then 429 else if t 3 = 1 then 421 else 498) else (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 500)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 427 else if t 3 = 1 then 419 else 492) else if t 2 = 1 then (if t 3 = 0 then 425 else if t 3 = 1 then 417 else 480) else (if t 3 = 0 then 449 else if t 3 = 1 then 444 else 482)) else (if t 2 = 0 then (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 493) else if t 2 = 1 then (if t 3 = 0 then 440 else if t 3 = 1 then 436 else 481) else (if t 3 = 0 then 455 else if t 3 = 1 then 453 else 483))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 1133 else 3960) else if t 2 = 1 then (if t 3 = 0 then 1518 else if t 3 = 1 then 1131 else 1524) else (if t 3 = 0 then 3206 else if t 3 = 1 then 1137 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 468 else if t 3 = 1 then 463 else 494) else if t 2 = 1 then (if t 3 = 0 then 466 else if t 3 = 1 then 461 else 484) else (if t 3 = 0 then 476 else if t 3 = 1 then 474 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 473 else if t 3 = 1 then 471 else 495) else if t 2 = 1 then (if t 3 = 0 then 472 else if t 3 = 1 then 470 else 485) else (if t 3 = 0 then 479 else if t 3 = 1 then 478 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4680 else (if jt.2.val < 2 then 4688 else 4685)) else (if jt.2.val < 4 then 4686 else (if jt.2.val < 5 then 4687 else 4683))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3077 else (if jt.2.val < 2 then 3204 else 3081)) else (if jt.2.val < 4 then 3201 else (if jt.2.val < 5 then 3202 else 3049)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 39 else (if jt.2.val < 2 then 446 else 44)) else (if jt.2.val < 4 then 414 else (if jt.2.val < 5 then 415 else 7))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 408 else (if jt.2.val < 2 then 410 else 413)) else (if jt.2.val < 4 then 409 else (if jt.2.val < 5 then 412 else 411)))))

checked_coverage fastCoverage0534 pairing0534 template0534 witness0534

theorem coverage0534 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0534) (maskBits m))
    cores template0534 witness0534 := by
  rw [← coresFast_eq]
  exact fastCoverage0534

theorem coverageSize0534 : ∀ q : Pattern,
    (cores (witness0534 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0534 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0534
#print axioms coverageSize0534

noncomputable def pairing0535 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0535 : List (Fin 4935) := templateData0535

noncomputable def witness0535 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 574 else 575) else if t 2 = 1 then (if t 3 = 0 then 581 else if t 3 = 1 then 566 else 568) else (if t 3 = 0 then 591 else if t 3 = 1 then 567 else 569)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 579 else if t 3 = 1 then 552 else 554) else if t 2 = 1 then (if t 3 = 0 then 577 else if t 3 = 1 then 532 else 537) else (if t 3 = 0 then 589 else if t 3 = 1 then 534 else 538)) else (if t 2 = 0 then (if t 3 = 0 then 3215 else if t 3 = 1 then 3209 else 3210) else if t 2 = 1 then (if t 3 = 0 then 2759 else if t 3 = 1 then 2747 else 2750) else (if t 3 = 0 then 3927 else if t 3 = 1 then 3923 else 3925))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 570 else 572) else if t 2 = 1 then (if t 3 = 0 then 580 else if t 3 = 1 then 556 else 562) else (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 564)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 578 else if t 3 = 1 then 544 else 548) else if t 2 = 1 then (if t 3 = 0 then 576 else if t 3 = 1 then 515 else 524) else (if t 3 = 0 then 588 else if t 3 = 1 then 517 else 526)) else (if t 2 = 0 then (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 549) else if t 2 = 1 then (if t 3 = 0 then 584 else if t 3 = 1 then 516 else 525) else (if t 3 = 0 then 592 else if t 3 = 1 then 518 else 527))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 1110 else 3966) else if t 2 = 1 then (if t 3 = 0 then 1548 else if t 3 = 1 then 1104 else 1542) else (if t 3 = 0 then 3216 else if t 3 = 1 then 1106 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 596 else if t 3 = 1 then 546 else 550) else if t 2 = 1 then (if t 3 = 0 then 594 else if t 3 = 1 then 520 else 528) else (if t 3 = 0 then 600 else if t 3 = 1 then 522 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 599 else if t 3 = 1 then 547 else 551) else if t 2 = 1 then (if t 3 = 0 then 598 else if t 3 = 1 then 521 else 529) else (if t 3 = 0 then 602 else if t 3 = 1 then 523 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4674 else (if jt.2.val < 2 then 4690 else 4679)) else (if jt.2.val < 4 then 4689 else (if jt.2.val < 5 then 4691 else 4676))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3122 else (if jt.2.val < 2 then 3212 else 3143)) else (if jt.2.val < 4 then 3211 else (if jt.2.val < 5 then 3213 else 3113)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 120 else (if jt.2.val < 2 then 542 else 149)) else (if jt.2.val < 4 then 541 else (if jt.2.val < 5 then 543 else 111))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 411 else (if jt.2.val < 2 then 509 else 413)) else (if jt.2.val < 4 then 507 else (if jt.2.val < 5 then 508 else 408)))))

checked_coverage fastCoverage0535 pairing0535 template0535 witness0535

theorem coverage0535 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0535) (maskBits m))
    cores template0535 witness0535 := by
  rw [← coresFast_eq]
  exact fastCoverage0535

theorem coverageSize0535 : ∀ q : Pattern,
    (cores (witness0535 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0535 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0535
#print axioms coverageSize0535

noncomputable def pairing0536 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0536 : List (Fin 4935) := templateData0536

noncomputable def witness0536 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 3959) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3227) else (if t 3 = 0 then 3236 else if t 3 = 1 then 3235 else 2868)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1611) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1610) else (if t 3 = 0 then 1651 else if t 3 = 1 then 1649 else 1853)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2199 else 299) else if t 2 = 1 then (if t 3 = 0 then 2200 else if t 3 = 1 then 2198 else 1616) else (if t 3 = 0 then 743 else if t 3 = 1 then 1661 else 1856))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1443) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1442) else (if t 3 = 0 then 1332 else if t 3 = 1 then 1330 else 1778)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3161) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4514) else (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4518)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3465 else 3164) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4515) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4506 else 4519))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1722 else 782) else if t 2 = 1 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1721 else 1451) else (if t 3 = 0 then 262 else if t 3 = 1 then 1355 else 2120)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3270 else 3166) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4516) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4507 else 4520)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 3280 else 3168) else if t 2 = 1 then (if t 3 = 0 then 4004 else if t 3 = 1 then 4499 else 4517) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4513 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4710 else (if jt.2.val < 2 then 4720 else 4721)) else (if jt.2.val < 4 then 4717 else (if jt.2.val < 5 then 4719 else 4718))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4711 else (if jt.2.val < 2 then 4715 else 4716)) else (if jt.2.val < 4 then 4712 else (if jt.2.val < 5 then 4714 else 4713)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4468 else (if jt.2.val < 2 then 4503 else 4504)) else (if jt.2.val < 4 then 4500 else (if jt.2.val < 5 then 4502 else 4501))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4467 else (if jt.2.val < 2 then 4509 else 4512)) else (if jt.2.val < 4 then 4508 else (if jt.2.val < 5 then 4511 else 4510)))))

checked_coverage fastCoverage0536 pairing0536 template0536 witness0536

theorem coverage0536 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0536) (maskBits m))
    cores template0536 witness0536 := by
  rw [← coresFast_eq]
  exact fastCoverage0536

theorem coverageSize0536 : ∀ q : Pattern,
    (cores (witness0536 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0536 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0536
#print axioms coverageSize0536

noncomputable def pairing0537 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0537 : List (Fin 4935) := templateData0537

noncomputable def witness0537 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4525) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 3225) else (if t 3 = 0 then 2981 else if t 3 = 1 then 2979 else 3226)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 1597) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 1593) else (if t 3 = 0 then 1090 else if t 3 = 1 then 1069 else 1071)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 667 else 2170) else if t 2 = 1 then (if t 3 = 0 then 682 else if t 3 = 1 then 654 else 656) else (if t 3 = 0 then 1826 else if t 3 = 1 then 659 else 661))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 1429) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 1424) else (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 990)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 3146) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3875) else (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3885)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2551) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3878) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3886 else 3887))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 376 else 1774) else if t 2 = 1 then (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 366) else (if t 3 = 0 then 2141 else if t 3 = 1 then 368 else 370)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2698) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3881) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3888 else 3889)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2879 else 2881) else if t 2 = 1 then (if t 3 = 0 then 3919 else if t 3 = 1 then 3882 else 3883) else (if t 3 = 0 then 4526 else if t 3 = 1 then 3890 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4680 else (if jt.2.val < 2 then 4682 else 4685)) else (if jt.2.val < 4 then 4681 else (if jt.2.val < 5 then 4684 else 4683))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3867 else (if jt.2.val < 2 then 3869 else 3897)) else (if jt.2.val < 4 then 3868 else (if jt.2.val < 5 then 3896 else 3876)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4029 else (if jt.2.val < 2 then 4031 else 4035)) else (if jt.2.val < 4 then 4030 else (if jt.2.val < 5 then 4034 else 4033))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4510 else (if jt.2.val < 2 then 4524 else 4512)) else (if jt.2.val < 4 then 4522 else (if jt.2.val < 5 then 4523 else 4467)))))

checked_coverage fastCoverage0537 pairing0537 template0537 witness0537

theorem coverage0537 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0537) (maskBits m))
    cores template0537 witness0537 := by
  rw [← coresFast_eq]
  exact fastCoverage0537

theorem coverageSize0537 : ∀ q : Pattern,
    (cores (witness0537 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0537 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0537
#print axioms coverageSize0537

noncomputable def pairing0538 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0538 : List (Fin 4935) := templateData0538

noncomputable def witness0538 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3062 else 3004) else if t 2 = 1 then (if t 3 = 0 then 3058 else if t 3 = 1 then 3054 else 3003) else (if t 3 = 0 then 4530 else if t 3 = 1 then 3963 else 3967)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3060 else 874) else if t 2 = 1 then (if t 3 = 0 then 3056 else if t 3 = 1 then 3052 else 862) else (if t 3 = 0 then 1648 else if t 3 = 1 then 1646 else 864)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 344 else 1790) else if t 2 = 1 then (if t 3 = 0 then 341 else if t 3 = 1 then 340 else 400) else (if t 3 = 0 then 2159 else if t 3 = 1 then 357 else 402))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3061 else 1219) else if t 2 = 1 then (if t 3 = 0 then 3057 else if t 3 = 1 then 3053 else 1207) else (if t 3 = 0 then 1329 else if t 3 = 1 then 1327 else 1209)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3059 else 3313) else if t 2 = 1 then (if t 3 = 0 then 3055 else if t 3 = 1 then 3051 else 3098) else (if t 3 = 0 then 3073 else if t 3 = 1 then 3071 else 3099)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 3082 else 3315) else if t 2 = 1 then (if t 3 = 0 then 2470 else if t 3 = 1 then 3080 else 3100) else (if t 3 = 0 then 2474 else if t 3 = 1 then 3083 else 3101))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 638 else 2162) else if t 2 = 1 then (if t 3 = 0 then 635 else if t 3 = 1 then 634 else 691) else (if t 3 = 0 then 1787 else if t 3 = 1 then 650 else 693)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 3091 else 3500) else if t 2 = 1 then (if t 3 = 0 then 2622 else if t 3 = 1 then 3089 else 3102) else (if t 3 = 0 then 2626 else if t 3 = 1 then 3092 else 3103)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 3095 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2900 else if t 3 = 1 then 3094 else 3104) else (if t 3 = 0 then 2901 else if t 3 = 1 then 3096 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4611 else (if jt.2.val < 2 then 4615 else 4616)) else (if jt.2.val < 4 then 4612 else (if jt.2.val < 5 then 4614 else 4613))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3049 else (if jt.2.val < 2 then 3079 else 3081)) else (if jt.2.val < 4 then 3076 else (if jt.2.val < 5 then 3078 else 3077)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4501 else (if jt.2.val < 2 then 4529 else 4504)) else (if jt.2.val < 4 then 4527 else (if jt.2.val < 5 then 4528 else 4468))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3371 else (if jt.2.val < 2 then 3373 else 3377)) else (if jt.2.val < 4 then 3372 else (if jt.2.val < 5 then 3376 else 3375)))))

checked_coverage fastCoverage0538 pairing0538 template0538 witness0538

theorem coverage0538 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0538) (maskBits m))
    cores template0538 witness0538 := by
  rw [← coresFast_eq]
  exact fastCoverage0538

theorem coverageSize0538 : ∀ q : Pattern,
    (cores (witness0538 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0538 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0538
#print axioms coverageSize0538

noncomputable def pairing0539 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0539 : List (Fin 4935) := templateData0539

noncomputable def witness0539 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2953 else 3152) else if t 2 = 1 then (if t 3 = 0 then 2960 else if t 3 = 1 then 2937 else 3329) else (if t 3 = 0 then 3860 else if t 3 = 1 then 4046 else 4532)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2951 else 859) else if t 2 = 1 then (if t 3 = 0 then 2958 else if t 3 = 1 then 2931 else 830) else (if t 3 = 0 then 1084 else if t 3 = 1 then 1046 else 1813)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1750 else 279) else if t 2 = 1 then (if t 3 = 0 then 1756 else if t 3 = 1 then 1730 else 833) else (if t 3 = 0 then 790 else if t 3 = 1 then 1049 else 2146))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2952 else 1204) else if t 2 = 1 then (if t 3 = 0 then 2959 else if t 3 = 1 then 2934 else 1180) else (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 1796)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2947 else 2949) else if t 2 = 1 then (if t 3 = 0 then 2954 else if t 3 = 1 then 2913 else 2917) else (if t 3 = 0 then 2955 else if t 3 = 1 then 2915 else 2918)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2554 else 2556) else if t 2 = 1 then (if t 3 = 0 then 2502 else if t 3 = 1 then 2919 else 2921) else (if t 3 = 0 then 2503 else if t 3 = 1 then 2920 else 2922))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2218 else 762) else if t 2 = 1 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2206 else 1184) else (if t 3 = 0 then 307 else if t 3 = 1 then 974 else 1800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2699 else 2701) else if t 2 = 1 then (if t 3 = 0 then 2650 else if t 3 = 1 then 2923 else 2925) else (if t 3 = 0 then 2651 else if t 3 = 1 then 2924 else 2926)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3196 else 3934) else if t 2 = 1 then (if t 3 = 0 then 3183 else if t 3 = 1 then 2927 else 2929) else (if t 3 = 0 then 3184 else if t 3 = 1 then 2928 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4659 else (if jt.2.val < 2 then 4661 else 4664)) else (if jt.2.val < 4 then 4660 else (if jt.2.val < 5 then 4663 else 4662))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3323 else (if jt.2.val < 2 then 3325 else 3328)) else (if jt.2.val < 4 then 3324 else (if jt.2.val < 5 then 3327 else 3326)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4033 else (if jt.2.val < 2 then 4049 else 4035)) else (if jt.2.val < 4 then 4048 else (if jt.2.val < 5 then 4050 else 4029))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3375 else (if jt.2.val < 2 then 3383 else 3377)) else (if jt.2.val < 4 then 3381 else (if jt.2.val < 5 then 3382 else 3371)))))

checked_coverage fastCoverage0539 pairing0539 template0539 witness0539

theorem coverage0539 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0539) (maskBits m))
    cores template0539 witness0539 := by
  rw [← coresFast_eq]
  exact fastCoverage0539

theorem coverageSize0539 : ∀ q : Pattern,
    (cores (witness0539 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0539 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0539
#print axioms coverageSize0539

noncomputable def pairing0540 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0540 : List (Fin 4935) := templateData0540

noncomputable def witness0540 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2058 else 591) else if t 2 = 1 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2056 else 1447) else (if t 3 = 0 then 50 else if t 3 = 1 then 1342 else 1780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2054 else if t 3 = 1 then 2050 else 589) else if t 2 = 1 then (if t 3 = 0 then 2052 else if t 3 = 1 then 2048 else 2101) else (if t 3 = 0 then 48 else if t 3 = 1 then 2090 else 2107)) else (if t 2 = 0 then (if t 3 = 0 then 4546 else if t 3 = 1 then 4211 else 3927) else if t 2 = 1 then (if t 3 = 0 then 3530 else if t 3 = 1 then 3528 else 2648) else (if t 3 = 0 then 3192 else if t 3 = 1 then 2690 else 2906))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2057 else 590) else if t 2 = 1 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2055 else 1446) else (if t 3 = 0 then 49 else if t 3 = 1 then 1341 else 1779)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2053 else if t 3 = 1 then 2049 else 588) else if t 2 = 1 then (if t 3 = 0 then 2051 else if t 3 = 1 then 2047 else 2100) else (if t 3 = 0 then 47 else if t 3 = 1 then 2089 else 2106)) else (if t 2 = 0 then (if t 3 = 0 then 2071 else if t 3 = 1 then 2069 else 592) else if t 2 = 1 then (if t 3 = 0 then 2070 else if t 3 = 1 then 2067 else 2102) else (if t 3 = 0 then 53 else if t 3 = 1 then 2091 else 2108))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 1052 else 3216) else if t 2 = 1 then (if t 3 = 0 then 836 else if t 3 = 1 then 1732 else 1452) else (if t 3 = 0 then 3942 else if t 3 = 1 then 1358 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1815 else if t 3 = 1 then 1050 else 600) else if t 2 = 1 then (if t 3 = 0 then 834 else if t 3 = 1 then 2081 else 2103) else (if t 3 = 0 then 74 else if t 3 = 1 then 2097 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 1818 else if t 3 = 1 then 1056 else 602) else if t 2 = 1 then (if t 3 = 0 then 840 else if t 3 = 1 then 2083 else 2105) else (if t 3 = 0 then 77 else if t 3 = 1 then 2099 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4659 else (if jt.2.val < 2 then 4670 else 4664)) else (if jt.2.val < 4 then 4668 else (if jt.2.val < 5 then 4669 else 4662))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4713 else (if jt.2.val < 2 then 4724 else 4716)) else (if jt.2.val < 4 then 4722 else (if jt.2.val < 5 then 4723 else 4711)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2322 else (if jt.2.val < 2 then 2332 else 2333)) else (if jt.2.val < 4 then 2329 else (if jt.2.val < 5 then 2331 else 2330))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2232 else (if jt.2.val < 2 then 2240 else 2243)) else (if jt.2.val < 4 then 2239 else (if jt.2.val < 5 then 2242 else 2241)))))

checked_coverage fastCoverage0540 pairing0540 template0540 witness0540

theorem coverage0540 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0540) (maskBits m))
    cores template0540 witness0540 := by
  rw [← coresFast_eq]
  exact fastCoverage0540

theorem coverageSize0540 : ∀ q : Pattern,
    (cores (witness0540 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0540 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0540
#print axioms coverageSize0540

noncomputable def pairing0541 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0541 : List (Fin 4935) := templateData0541

noncomputable def witness0541 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 178 else 2117) else if t 2 = 1 then (if t 3 = 0 then 185 else if t 3 = 1 then 170 else 171) else (if t 3 = 0 then 1807 else if t 3 = 1 then 172 else 173)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 183 else if t 3 = 1 then 156 else 1537) else if t 2 = 1 then (if t 3 = 0 then 181 else if t 3 = 1 then 136 else 139) else (if t 3 = 0 then 898 else if t 3 = 1 then 142 else 143)) else (if t 2 = 0 then (if t 3 = 0 then 3951 else if t 3 = 1 then 3945 else 4541) else if t 2 = 1 then (if t 3 = 0 then 2778 else if t 3 = 1 then 2766 else 3172) else (if t 3 = 0 then 2989 else if t 3 = 1 then 2769 else 3174))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 174 else 2115) else if t 2 = 1 then (if t 3 = 0 then 184 else if t 3 = 1 then 160 else 162) else (if t 3 = 0 then 1806 else if t 3 = 1 then 166 else 168)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 182 else if t 3 = 1 then 146 else 1531) else if t 2 = 1 then (if t 3 = 0 then 180 else if t 3 = 1 then 117 else 121) else (if t 3 = 0 then 897 else if t 3 = 1 then 128 else 130)) else (if t 2 = 0 then (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 1532) else if t 2 = 1 then (if t 3 = 0 then 188 else if t 3 = 1 then 119 else 122) else (if t 3 = 0 then 901 else if t 3 = 1 then 129 else 131))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 894 else 2984) else if t 2 = 1 then (if t 3 = 0 then 1500 else if t 3 = 1 then 888 else 890) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1494 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 200 else if t 3 = 1 then 150 else 1833) else if t 2 = 1 then (if t 3 = 0 then 198 else if t 3 = 1 then 124 else 126) else (if t 3 = 0 then 2127 else if t 3 = 1 then 132 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 203 else if t 3 = 1 then 151 else 1834) else if t 2 = 1 then (if t 3 = 0 then 202 else if t 3 = 1 then 125 else 127) else (if t 3 = 0 then 2128 else if t 3 = 1 then 133 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4611 else (if jt.2.val < 2 then 4645 else 4616)) else (if jt.2.val < 4 then 4644 else (if jt.2.val < 5 then 4646 else 4613))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3876 else (if jt.2.val < 2 then 3948 else 3897)) else (if jt.2.val < 4 then 3947 else (if jt.2.val < 5 then 3949 else 3867)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2295 else (if jt.2.val < 2 then 2297 else 2300)) else (if jt.2.val < 4 then 2296 else (if jt.2.val < 5 then 2299 else 2298))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2241 else (if jt.2.val < 2 then 2249 else 2243)) else (if jt.2.val < 4 then 2247 else (if jt.2.val < 5 then 2248 else 2232)))))

checked_coverage fastCoverage0541 pairing0541 template0541 witness0541

theorem coverage0541 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0541) (maskBits m))
    cores template0541 witness0541 := by
  rw [← coresFast_eq]
  exact fastCoverage0541

theorem coverageSize0541 : ∀ q : Pattern,
    (cores (witness0541 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0541 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0541
#print axioms coverageSize0541

noncomputable def pairing0542 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0542 : List (Fin 4935) := templateData0542

noncomputable def witness0542 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 430 else 1837) else if t 2 = 1 then (if t 3 = 0 then 424 else if t 3 = 1 then 422 else 502) else (if t 3 = 0 then 2125 else if t 3 = 1 then 448 else 503)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 428 else if t 3 = 1 then 426 else 1114) else if t 2 = 1 then (if t 3 = 0 then 420 else if t 3 = 1 then 418 else 488) else (if t 3 = 0 then 1507 else if t 3 = 1 then 445 else 489)) else (if t 2 = 0 then (if t 3 = 0 then 3205 else if t 3 = 1 then 2731 else 2985) else if t 2 = 1 then (if t 3 = 0 then 3203 else if t 3 = 1 then 2728 else 2740) else (if t 3 = 0 then 4539 else if t 3 = 1 then 3929 else 3935))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 429 else 1836) else if t 2 = 1 then (if t 3 = 0 then 423 else if t 3 = 1 then 421 else 498) else (if t 3 = 0 then 2124 else if t 3 = 1 then 447 else 500)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 427 else if t 3 = 1 then 425 else 1113) else if t 2 = 1 then (if t 3 = 0 then 419 else if t 3 = 1 then 417 else 480) else (if t 3 = 0 then 1506 else if t 3 = 1 then 444 else 482)) else (if t 2 = 0 then (if t 3 = 0 then 441 else if t 3 = 1 then 440 else 1117) else if t 2 = 1 then (if t 3 = 0 then 437 else if t 3 = 1 then 436 else 481) else (if t 3 = 0 then 1511 else if t 3 = 1 then 453 else 483))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 1518 else 4542) else if t 2 = 1 then (if t 3 = 0 then 1133 else if t 3 = 1 then 1131 else 1524) else (if t 3 = 0 then 2988 else if t 3 = 1 then 1137 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 468 else if t 3 = 1 then 466 else 2148) else if t 2 = 1 then (if t 3 = 0 then 463 else if t 3 = 1 then 461 else 484) else (if t 3 = 0 then 1848 else if t 3 = 1 then 474 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 473 else if t 3 = 1 then 472 else 2149) else if t 2 = 1 then (if t 3 = 0 then 471 else if t 3 = 1 then 470 else 485) else (if t 3 = 0 then 1850 else if t 3 = 1 then 478 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4680 else (if jt.2.val < 2 then 4688 else 4685)) else (if jt.2.val < 4 then 4686 else (if jt.2.val < 5 then 4687 else 4683))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3077 else (if jt.2.val < 2 then 3204 else 3081)) else (if jt.2.val < 4 then 3201 else (if jt.2.val < 5 then 3202 else 3049)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2330 else (if jt.2.val < 2 then 2345 else 2333)) else (if jt.2.val < 4 then 2343 else (if jt.2.val < 5 then 2344 else 2322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1950 else (if jt.2.val < 2 then 1952 else 1955)) else (if jt.2.val < 4 then 1951 else (if jt.2.val < 5 then 1954 else 1953)))))

checked_coverage fastCoverage0542 pairing0542 template0542 witness0542

theorem coverage0542 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0542) (maskBits m))
    cores template0542 witness0542 := by
  rw [← coresFast_eq]
  exact fastCoverage0542

theorem coverageSize0542 : ∀ q : Pattern,
    (cores (witness0542 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0542 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0542
#print axioms coverageSize0542

noncomputable def pairing0543 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0543 : List (Fin 4935) := templateData0543

noncomputable def witness0543 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1904 else 575) else if t 2 = 1 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1891 else 1188) else (if t 3 = 0 then 104 else if t 3 = 1 then 978 else 2138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1901 else 554) else if t 2 = 1 then (if t 3 = 0 then 1907 else if t 3 = 1 then 1875 else 1878) else (if t 3 = 0 then 94 else if t 3 = 1 then 1877 else 1879)) else (if t 2 = 0 then (if t 3 = 0 then 2884 else if t 3 = 1 then 2546 else 3210) else if t 2 = 1 then (if t 3 = 0 then 2500 else if t 3 = 1 then 3348 else 3350) else (if t 3 = 0 then 3943 else if t 3 = 1 then 4064 else 4537))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1902 else 572) else if t 2 = 1 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1887 else 1181) else (if t 3 = 0 then 102 else if t 3 = 1 then 971 else 2136)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1899 else 548) else if t 2 = 1 then (if t 3 = 0 then 1905 else if t 3 = 1 then 1859 else 1863) else (if t 3 = 0 then 90 else if t 3 = 1 then 1861 else 1865)) else (if t 2 = 0 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1900 else 549) else if t 2 = 1 then (if t 3 = 0 then 1906 else if t 3 = 1 then 1860 else 1864) else (if t 3 = 0 then 91 else if t 3 = 1 then 1862 else 1866))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1673 else 3966) else if t 2 = 1 then (if t 3 = 0 then 1620 else if t 3 = 1 then 1889 else 1185) else (if t 3 = 0 then 3229 else if t 3 = 1 then 975 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2172 else if t 3 = 1 then 1667 else 550) else if t 2 = 1 then (if t 3 = 0 then 1617 else if t 3 = 1 then 1867 else 1871) else (if t 3 = 0 then 92 else if t 3 = 1 then 1869 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 2173 else if t 3 = 1 then 1668 else 551) else if t 2 = 1 then (if t 3 = 0 then 1618 else if t 3 = 1 then 1868 else 1872) else (if t 3 = 0 then 93 else if t 3 = 1 then 1870 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4710 else (if jt.2.val < 2 then 4726 else 4721)) else (if jt.2.val < 4 then 4725 else (if jt.2.val < 5 then 4727 else 4718))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3326 else (if jt.2.val < 2 then 3354 else 3328)) else (if jt.2.val < 4 then 3353 else (if jt.2.val < 5 then 3355 else 3323)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2298 else (if jt.2.val < 2 then 2320 else 2300)) else (if jt.2.val < 4 then 2319 else (if jt.2.val < 5 then 2321 else 2295))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1953 else (if jt.2.val < 2 then 1970 else 1955)) else (if jt.2.val < 4 then 1967 else (if jt.2.val < 5 then 1968 else 1950)))))

checked_coverage fastCoverage0543 pairing0543 template0543 witness0543

theorem coverage0543 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0543) (maskBits m))
    cores template0543 witness0543 := by
  rw [← coresFast_eq]
  exact fastCoverage0543

theorem coverageSize0543 : ∀ q : Pattern,
    (cores (witness0543 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0543 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0543
#print axioms coverageSize0543

noncomputable def pairing0544 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0544 : List (Fin 4935) := templateData0544

noncomputable def witness0544 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 3965) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3235) else (if t 3 = 0 then 3228 else if t 3 = 1 then 3227 else 2868)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1650) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1649) else (if t 3 = 0 then 1612 else if t 3 = 1 then 1610 else 1853)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2199 else 359) else if t 2 = 1 then (if t 3 = 0 then 2200 else if t 3 = 1 then 2198 else 1661) else (if t 3 = 0 then 689 else if t 3 = 1 then 1616 else 1856))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1331) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1330) else (if t 3 = 0 then 1444 else if t 3 = 1 then 1442 else 1778)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3074) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4505) else (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4518)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3465 else 3084) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4506) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4515 else 4519))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1722 else 652) else if t 2 = 1 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1721 else 1355) else (if t 3 = 0 then 398 else if t 3 = 1 then 1451 else 2120)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3270 else 3093) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4507) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4516 else 4520)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 3280 else 3097) else if t 2 = 1 then (if t 3 = 0 then 4004 else if t 3 = 1 then 4499 else 4513) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4517 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4710 else (if jt.2.val < 2 then 4720 else 4721)) else (if jt.2.val < 4 then 4717 else (if jt.2.val < 5 then 4719 else 4718))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4711 else (if jt.2.val < 2 then 4715 else 4716)) else (if jt.2.val < 4 then 4712 else (if jt.2.val < 5 then 4714 else 4713)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4548 else (if jt.2.val < 2 then 4556 else 4559)) else (if jt.2.val < 4 then 4555 else (if jt.2.val < 5 then 4558 else 4557))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4549 else (if jt.2.val < 2 then 4553 else 4554)) else (if jt.2.val < 4 then 4550 else (if jt.2.val < 5 then 4552 else 4551)))))

checked_coverage fastCoverage0544 pairing0544 template0544 witness0544

theorem coverage0544 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0544) (maskBits m))
    cores template0544 witness0544 := by
  rw [← coresFast_eq]
  exact fastCoverage0544

theorem coverageSize0544 : ∀ q : Pattern,
    (cores (witness0544 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0544 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0544
#print axioms coverageSize0544

noncomputable def pairing0545 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0545 : List (Fin 4935) := templateData0545

noncomputable def witness0545 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4530) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 3234) else (if t 3 = 0 then 2981 else if t 3 = 1 then 2980 else 3242)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 1648) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 1647) else (if t 3 = 0 then 1090 else if t 3 = 1 then 1078 else 1080)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 724 else 2159) else if t 2 = 1 then (if t 3 = 0 then 727 else if t 3 = 1 then 723 else 741) else (if t 3 = 0 then 1826 else if t 3 = 1 then 784 else 786))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 1329) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 1328) else (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 999)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 3073) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3827) else (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3853)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2474) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3837) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3854 else 3855))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 241 else 1787) else if t 2 = 1 then (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 260) else (if t 3 = 0 then 2141 else if t 3 = 1 then 301 else 303)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2626) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3846) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3856 else 3857)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2899 else 2901) else if t 2 = 1 then (if t 3 = 0 then 3849 else if t 3 = 1 then 3848 else 3850) else (if t 3 = 0 then 4526 else if t 3 = 1 then 3858 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4674 else (if jt.2.val < 2 then 4678 else 4679)) else (if jt.2.val < 4 then 4675 else (if jt.2.val < 5 then 4677 else 4676))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3805 else (if jt.2.val < 2 then 3833 else 3835)) else (if jt.2.val < 4 then 3830 else (if jt.2.val < 5 then 3832 else 3831)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4082 else (if jt.2.val < 2 then 4084 else 4088)) else (if jt.2.val < 4 then 4083 else (if jt.2.val < 5 then 4087 else 4086))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4551 else (if jt.2.val < 2 then 4562 else 4554)) else (if jt.2.val < 4 then 4560 else (if jt.2.val < 5 then 4561 else 4549)))))

checked_coverage fastCoverage0545 pairing0545 template0545 witness0545

theorem coverage0545 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0545) (maskBits m))
    cores template0545 witness0545 := by
  rw [← coresFast_eq]
  exact fastCoverage0545

theorem coverageSize0545 : ∀ q : Pattern,
    (cores (witness0545 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0545 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0545
#print axioms coverageSize0545

noncomputable def pairing0546 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0546 : List (Fin 4935) := templateData0546

noncomputable def witness0546 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3156 else 3004) else if t 2 = 1 then (if t 3 = 0 then 3151 else if t 3 = 1 then 3144 else 3002) else (if t 3 = 0 then 4525 else if t 3 = 1 then 3953 else 3954)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3154 else 874) else if t 2 = 1 then (if t 3 = 0 then 3149 else if t 3 = 1 then 3138 else 853) else (if t 3 = 0 then 1597 else if t 3 = 1 then 1589 else 855)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 292 else 1790) else if t 2 = 1 then (if t 3 = 0 then 277 else if t 3 = 1 then 264 else 269) else (if t 3 = 0 then 2170 else if t 3 = 1 then 266 else 271))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3155 else 1219) else if t 2 = 1 then (if t 3 = 0 then 3150 else if t 3 = 1 then 3141 else 1198) else (if t 3 = 0 then 1429 else if t 3 = 1 then 1419 else 1200)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3153 else 3313) else if t 2 = 1 then (if t 3 = 0 then 3145 else if t 3 = 1 then 3119 else 3130) else (if t 3 = 0 then 3146 else if t 3 = 1 then 3121 else 3131)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 3163 else 3315) else if t 2 = 1 then (if t 3 = 0 then 2550 else if t 3 = 1 then 3123 else 3132) else (if t 3 = 0 then 2551 else if t 3 = 1 then 3124 else 3133))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 775 else 2162) else if t 2 = 1 then (if t 3 = 0 then 760 else if t 3 = 1 then 748 else 752) else (if t 3 = 0 then 1774 else if t 3 = 1 then 750 else 754)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 3165 else 3500) else if t 2 = 1 then (if t 3 = 0 then 2697 else if t 3 = 1 then 3126 else 3134) else (if t 3 = 0 then 2698 else if t 3 = 1 then 3127 else 3135)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 3167 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2880 else if t 3 = 1 then 3128 else 3136) else (if t 3 = 0 then 2881 else if t 3 = 1 then 3129 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4617 else (if jt.2.val < 2 then 4619 else 4622)) else (if jt.2.val < 4 then 4618 else (if jt.2.val < 5 then 4621 else 4620))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3113 else (if jt.2.val < 2 then 3115 else 3143)) else (if jt.2.val < 4 then 3114 else (if jt.2.val < 5 then 3142 else 3122)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4557 else (if jt.2.val < 2 then 4565 else 4559)) else (if jt.2.val < 4 then 4563 else (if jt.2.val < 5 then 4564 else 4548))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3305 else (if jt.2.val < 2 then 3307 else 3311)) else (if jt.2.val < 4 then 3306 else (if jt.2.val < 5 then 3310 else 3309)))))

checked_coverage fastCoverage0546 pairing0546 template0546 witness0546

theorem coverage0546 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0546) (maskBits m))
    cores template0546 witness0546 := by
  rw [← coresFast_eq]
  exact fastCoverage0546

theorem coverageSize0546 : ∀ q : Pattern,
    (cores (witness0546 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0546 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0546
#print axioms coverageSize0546

noncomputable def pairing0547 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0547 : List (Fin 4935) := templateData0547

noncomputable def witness0547 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2960 else 3106) else if t 2 = 1 then (if t 3 = 0 then 2953 else if t 3 = 1 then 2937 else 3329) else (if t 3 = 0 then 3905 else if t 3 = 1 then 4046 else 4532)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2958 else 868) else if t 2 = 1 then (if t 3 = 0 then 2951 else if t 3 = 1 then 2931 else 830) else (if t 3 = 0 then 1075 else if t 3 = 1 then 1046 else 1813)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1756 else 406) else if t 2 = 1 then (if t 3 = 0 then 1750 else if t 3 = 1 then 1730 else 833) else (if t 3 = 0 then 669 else if t 3 = 1 then 1049 else 2146))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2959 else 1213) else if t 2 = 1 then (if t 3 = 0 then 2952 else if t 3 = 1 then 2934 else 1180) else (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 1796)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2954 else 2956) else if t 2 = 1 then (if t 3 = 0 then 2947 else if t 3 = 1 then 2913 else 2917) else (if t 3 = 0 then 2948 else if t 3 = 1 then 2915 else 2918)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2502 else 2504) else if t 2 = 1 then (if t 3 = 0 then 2554 else if t 3 = 1 then 2919 else 2921) else (if t 3 = 0 then 2555 else if t 3 = 1 then 2920 else 2922))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2224 else 697) else if t 2 = 1 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2206 else 1184) else (if t 3 = 0 then 378 else if t 3 = 1 then 974 else 1800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2650 else 2652) else if t 2 = 1 then (if t 3 = 0 then 2699 else if t 3 = 1 then 2923 else 2925) else (if t 3 = 0 then 2700 else if t 3 = 1 then 2924 else 2926)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3183 else 3928) else if t 2 = 1 then (if t 3 = 0 then 3196 else if t 3 = 1 then 2927 else 2929) else (if t 3 = 0 then 3197 else if t 3 = 1 then 2928 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4659 else (if jt.2.val < 2 then 4661 else 4664)) else (if jt.2.val < 4 then 4660 else (if jt.2.val < 5 then 4663 else 4662))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3323 else (if jt.2.val < 2 then 3325 else 3328)) else (if jt.2.val < 4 then 3324 else (if jt.2.val < 5 then 3327 else 3326)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4086 else (if jt.2.val < 2 then 4094 else 4088)) else (if jt.2.val < 4 then 4092 else (if jt.2.val < 5 then 4093 else 4082))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3309 else (if jt.2.val < 2 then 3332 else 3311)) else (if jt.2.val < 4 then 3331 else (if jt.2.val < 5 then 3333 else 3305)))))

checked_coverage fastCoverage0547 pairing0547 template0547 witness0547

theorem coverage0547 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0547) (maskBits m))
    cores template0547 witness0547 := by
  rw [← coresFast_eq]
  exact fastCoverage0547

theorem coverageSize0547 : ∀ q : Pattern,
    (cores (witness0547 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0547 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0547
#print axioms coverageSize0547

noncomputable def pairing0548 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0548 : List (Fin 4935) := templateData0548

noncomputable def witness0548 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2058 else 452) else if t 2 = 1 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2056 else 1342) else (if t 3 = 0 then 195 else if t 3 = 1 then 1447 else 1780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2054 else if t 3 = 1 then 2050 else 450) else if t 2 = 1 then (if t 3 = 0 then 2052 else if t 3 = 1 then 2048 else 2090) else (if t 3 = 0 then 193 else if t 3 = 1 then 2101 else 2107)) else (if t 2 = 0 then (if t 3 = 0 then 4546 else if t 3 = 1 then 4211 else 3930) else if t 2 = 1 then (if t 3 = 0 then 3530 else if t 3 = 1 then 3528 else 2690) else (if t 3 = 0 then 3182 else if t 3 = 1 then 2648 else 2906))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2057 else 451) else if t 2 = 1 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2055 else 1341) else (if t 3 = 0 then 194 else if t 3 = 1 then 1446 else 1779)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2053 else if t 3 = 1 then 2049 else 449) else if t 2 = 1 then (if t 3 = 0 then 2051 else if t 3 = 1 then 2047 else 2089) else (if t 3 = 0 then 192 else if t 3 = 1 then 2100 else 2106)) else (if t 2 = 0 then (if t 3 = 0 then 2071 else if t 3 = 1 then 2069 else 455) else if t 2 = 1 then (if t 3 = 0 then 2070 else if t 3 = 1 then 2067 else 2091) else (if t 3 = 0 then 196 else if t 3 = 1 then 2102 else 2108))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 1052 else 3206) else if t 2 = 1 then (if t 3 = 0 then 836 else if t 3 = 1 then 1732 else 1358) else (if t 3 = 0 then 3952 else if t 3 = 1 then 1452 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1815 else if t 3 = 1 then 1050 else 476) else if t 2 = 1 then (if t 3 = 0 then 834 else if t 3 = 1 then 2081 else 2097) else (if t 3 = 0 then 204 else if t 3 = 1 then 2103 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 1818 else if t 3 = 1 then 1056 else 479) else if t 2 = 1 then (if t 3 = 0 then 840 else if t 3 = 1 then 2083 else 2099) else (if t 3 = 0 then 206 else if t 3 = 1 then 2105 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4659 else (if jt.2.val < 2 then 4670 else 4664)) else (if jt.2.val < 4 then 4668 else (if jt.2.val < 5 then 4669 else 4662))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4713 else (if jt.2.val < 2 then 4724 else 4716)) else (if jt.2.val < 4 then 4722 else (if jt.2.val < 5 then 4723 else 4711)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2412 else (if jt.2.val < 2 then 2414 else 2417)) else (if jt.2.val < 4 then 2413 else (if jt.2.val < 5 then 2416 else 2415))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2044 else (if jt.2.val < 2 then 2087 else 2088)) else (if jt.2.val < 4 then 2084 else (if jt.2.val < 5 then 2086 else 2085)))))

checked_coverage fastCoverage0548 pairing0548 template0548 witness0548

theorem coverage0548 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0548) (maskBits m))
    cores template0548 witness0548 := by
  rw [← coresFast_eq]
  exact fastCoverage0548

theorem coverageSize0548 : ∀ q : Pattern,
    (cores (witness0548 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0548 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0548
#print axioms coverageSize0548

noncomputable def pairing0549 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0549 : List (Fin 4935) := templateData0549

noncomputable def witness0549 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 16 else 2125) else if t 2 = 1 then (if t 3 = 0 then 22 else if t 3 = 1 then 14 else 46) else (if t 3 = 0 then 1807 else if t 3 = 1 then 100 else 101)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 20 else if t 3 = 1 then 12 else 1507) else if t 2 = 1 then (if t 3 = 0 then 18 else if t 3 = 1 then 10 else 43) else (if t 3 = 0 then 898 else if t 3 = 1 then 86 else 87)) else (if t 2 = 0 then (if t 3 = 0 then 3941 else if t 3 = 1 then 3939 else 4539) else if t 2 = 1 then (if t 3 = 0 then 2788 else if t 3 = 1 then 2785 else 3191) else (if t 3 = 0 then 2989 else if t 3 = 1 then 2797 else 3198))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 15 else 2124) else if t 2 = 1 then (if t 3 = 0 then 21 else if t 3 = 1 then 13 else 45) else (if t 3 = 0 then 1806 else if t 3 = 1 then 96 else 98)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 19 else if t 3 = 1 then 11 else 1506) else if t 2 = 1 then (if t 3 = 0 then 17 else if t 3 = 1 then 9 else 42) else (if t 3 = 0 then 897 else if t 3 = 1 then 78 else 80)) else (if t 2 = 0 then (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 1511) else if t 2 = 1 then (if t 3 = 0 then 34 else if t 3 = 1 then 29 else 51) else (if t 3 = 0 then 901 else if t 3 = 1 then 79 else 81))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 917 else 2988) else if t 2 = 1 then (if t 3 = 0 then 1470 else if t 3 = 1 then 915 else 921) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1476 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 66 else if t 3 = 1 then 61 else 1848) else if t 2 = 1 then (if t 3 = 0 then 64 else if t 3 = 1 then 59 else 72) else (if t 3 = 0 then 2127 else if t 3 = 1 then 82 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 71 else if t 3 = 1 then 69 else 1850) else if t 2 = 1 then (if t 3 = 0 then 70 else if t 3 = 1 then 68 else 76) else (if t 3 = 0 then 2128 else if t 3 = 1 then 83 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4617 else (if jt.2.val < 2 then 4643 else 4622)) else (if jt.2.val < 4 then 4641 else (if jt.2.val < 5 then 4642 else 4620))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3831 else (if jt.2.val < 2 then 3940 else 3835)) else (if jt.2.val < 4 then 3937 else (if jt.2.val < 5 then 3938 else 3805)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2394 else (if jt.2.val < 2 then 2396 else 2399)) else (if jt.2.val < 4 then 2395 else (if jt.2.val < 5 then 2398 else 2397))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2085 else (if jt.2.val < 2 then 2123 else 2088)) else (if jt.2.val < 4 then 2121 else (if jt.2.val < 5 then 2122 else 2044)))))

checked_coverage fastCoverage0549 pairing0549 template0549 witness0549

theorem coverage0549 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0549) (maskBits m))
    cores template0549 witness0549 := by
  rw [← coresFast_eq]
  exact fastCoverage0549

theorem coverageSize0549 : ∀ q : Pattern,
    (cores (witness0549 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0549 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0549
#print axioms coverageSize0549

noncomputable def pairing0550 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0550 : List (Fin 4935) := templateData0550

noncomputable def witness0550 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 581 else 1837) else if t 2 = 1 then (if t 3 = 0 then 574 else if t 3 = 1 then 566 else 568) else (if t 3 = 0 then 2117 else if t 3 = 1 then 567 else 569)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 579 else if t 3 = 1 then 577 else 1114) else if t 2 = 1 then (if t 3 = 0 then 552 else if t 3 = 1 then 532 else 537) else (if t 3 = 0 then 1537 else if t 3 = 1 then 534 else 538)) else (if t 2 = 0 then (if t 3 = 0 then 3215 else if t 3 = 1 then 2759 else 2985) else if t 2 = 1 then (if t 3 = 0 then 3209 else if t 3 = 1 then 2747 else 2750) else (if t 3 = 0 then 4541 else if t 3 = 1 then 3923 else 3925))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 580 else 1836) else if t 2 = 1 then (if t 3 = 0 then 570 else if t 3 = 1 then 556 else 562) else (if t 3 = 0 then 2115 else if t 3 = 1 then 558 else 564)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 578 else if t 3 = 1 then 576 else 1113) else if t 2 = 1 then (if t 3 = 0 then 544 else if t 3 = 1 then 515 else 524) else (if t 3 = 0 then 1531 else if t 3 = 1 then 517 else 526)) else (if t 2 = 0 then (if t 3 = 0 then 585 else if t 3 = 1 then 584 else 1117) else if t 2 = 1 then (if t 3 = 0 then 545 else if t 3 = 1 then 516 else 525) else (if t 3 = 0 then 1532 else if t 3 = 1 then 518 else 527))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 1548 else 4542) else if t 2 = 1 then (if t 3 = 0 then 1110 else if t 3 = 1 then 1104 else 1542) else (if t 3 = 0 then 2984 else if t 3 = 1 then 1106 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 596 else if t 3 = 1 then 594 else 2148) else if t 2 = 1 then (if t 3 = 0 then 546 else if t 3 = 1 then 520 else 528) else (if t 3 = 0 then 1833 else if t 3 = 1 then 522 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 599 else if t 3 = 1 then 598 else 2149) else if t 2 = 1 then (if t 3 = 0 then 547 else if t 3 = 1 then 521 else 529) else (if t 3 = 0 then 1834 else if t 3 = 1 then 523 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4674 else (if jt.2.val < 2 then 4690 else 4679)) else (if jt.2.val < 4 then 4689 else (if jt.2.val < 5 then 4691 else 4676))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3122 else (if jt.2.val < 2 then 3212 else 3143)) else (if jt.2.val < 4 then 3211 else (if jt.2.val < 5 then 3213 else 3113)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2415 else (if jt.2.val < 2 then 2426 else 2417)) else (if jt.2.val < 4 then 2424 else (if jt.2.val < 5 then 2425 else 2412))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1827 else (if jt.2.val < 2 then 1829 else 1832)) else (if jt.2.val < 4 then 1828 else (if jt.2.val < 5 then 1831 else 1830)))))

checked_coverage fastCoverage0550 pairing0550 template0550 witness0550

theorem coverage0550 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0550) (maskBits m))
    cores template0550 witness0550 := by
  rw [← coresFast_eq]
  exact fastCoverage0550

theorem coverageSize0550 : ∀ q : Pattern,
    (cores (witness0550 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0550 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0550
#print axioms coverageSize0550

noncomputable def pairing0551 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0551 : List (Fin 4935) := templateData0551

noncomputable def witness0551 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1910 else 506) else if t 2 = 1 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1891 else 1188) else (if t 3 = 0 then 179 else if t 3 = 1 then 978 else 2138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1907 else 496) else if t 2 = 1 then (if t 3 = 0 then 1901 else if t 3 = 1 then 1875 else 1878) else (if t 3 = 0 then 158 else if t 3 = 1 then 1877 else 1879)) else (if t 2 = 0 then (if t 3 = 0 then 2884 else if t 3 = 1 then 2500 else 3207) else if t 2 = 1 then (if t 3 = 0 then 2546 else if t 3 = 1 then 3348 else 3350) else (if t 3 = 0 then 3946 else if t 3 = 1 then 4064 else 4537))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1908 else 504) else if t 2 = 1 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1887 else 1181) else (if t 3 = 0 then 176 else if t 3 = 1 then 971 else 2136)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1905 else 492) else if t 2 = 1 then (if t 3 = 0 then 1899 else if t 3 = 1 then 1859 else 1863) else (if t 3 = 0 then 152 else if t 3 = 1 then 1861 else 1865)) else (if t 2 = 0 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1906 else 493) else if t 2 = 1 then (if t 3 = 0 then 1900 else if t 3 = 1 then 1860 else 1864) else (if t 3 = 0 then 153 else if t 3 = 1 then 1862 else 1866))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1620 else 3960) else if t 2 = 1 then (if t 3 = 0 then 1673 else if t 3 = 1 then 1889 else 1185) else (if t 3 = 0 then 3240 else if t 3 = 1 then 975 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2172 else if t 3 = 1 then 1617 else 494) else if t 2 = 1 then (if t 3 = 0 then 1667 else if t 3 = 1 then 1867 else 1871) else (if t 3 = 0 then 154 else if t 3 = 1 then 1869 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 2173 else if t 3 = 1 then 1618 else 495) else if t 2 = 1 then (if t 3 = 0 then 1668 else if t 3 = 1 then 1868 else 1872) else (if t 3 = 0 then 155 else if t 3 = 1 then 1870 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4710 else (if jt.2.val < 2 then 4726 else 4721)) else (if jt.2.val < 4 then 4725 else (if jt.2.val < 5 then 4727 else 4718))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3326 else (if jt.2.val < 2 then 3354 else 3328)) else (if jt.2.val < 4 then 3353 else (if jt.2.val < 5 then 3355 else 3323)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2397 else (if jt.2.val < 2 then 2411 else 2399)) else (if jt.2.val < 4 then 2409 else (if jt.2.val < 5 then 2410 else 2394))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1830 else (if jt.2.val < 2 then 1897 else 1832)) else (if jt.2.val < 4 then 1896 else (if jt.2.val < 5 then 1898 else 1827)))))

checked_coverage fastCoverage0551 pairing0551 template0551 witness0551

theorem coverage0551 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0551) (maskBits m))
    cores template0551 witness0551 := by
  rw [← coresFast_eq]
  exact fastCoverage0551

theorem coverageSize0551 : ∀ q : Pattern,
    (cores (witness0551 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0551 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0551
#print axioms coverageSize0551

noncomputable def pairing0552 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0552 : List (Fin 4935) := templateData0552

noncomputable def witness0552 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 3951) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2778) else (if t 3 = 0 then 3532 else if t 3 = 1 then 3530 else 3182)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 681) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 680) else (if t 3 = 0 then 2200 else if t 3 = 1 then 2196 else 688)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 726 else 1145) else if t 2 = 1 then (if t 3 = 0 then 727 else if t 3 = 1 then 725 else 1144) else (if t 3 = 0 then 743 else if t 3 = 1 then 742 else 1148))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 189) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 188) else (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 196)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2570) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4179) else (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4180)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2885) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4183) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4171 else 4184))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 822 else 203) else if t 2 = 1 then (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 202) else (if t 3 = 0 then 841 else if t 3 = 1 then 840 else 206)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2578) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4181) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4164 else 4182)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2487 else 3507) else if t 2 = 1 then (if t 3 = 0 then 3849 else if t 3 = 1 then 4177 else 4185) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4178 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4692 else (if jt.2.val < 2 then 4702 else 4703)) else (if jt.2.val < 4 then 4699 else (if jt.2.val < 5 then 4701 else 4700))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4260 else (if jt.2.val < 2 then 4270 else 4271)) else (if jt.2.val < 4 then 4267 else (if jt.2.val < 5 then 4269 else 4268)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4728 else (if jt.2.val < 2 then 4732 else 4733)) else (if jt.2.val < 4 then 4729 else (if jt.2.val < 5 then 4731 else 4730))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4131 else (if jt.2.val < 2 then 4173 else 4176)) else (if jt.2.val < 4 then 4172 else (if jt.2.val < 5 then 4175 else 4174)))))

checked_coverage fastCoverage0552 pairing0552 template0552 witness0552

theorem coverage0552 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0552) (maskBits m))
    cores template0552 witness0552 := by
  rw [← coresFast_eq]
  exact fastCoverage0552

theorem coverageSize0552 : ∀ q : Pattern,
    (cores (witness0552 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0552 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0552
#print axioms coverageSize0552

noncomputable def pairing0553 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0553 : List (Fin 4935) := templateData0553

noncomputable def witness0553 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4190) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2775) else (if t 3 = 0 then 3228 else if t 3 = 1 then 3225 else 3524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 667) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 654) else (if t 3 = 0 then 1612 else if t 3 = 1 then 1593 else 656)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1075 else 669) else if t 2 = 1 then (if t 3 = 0 then 1090 else if t 3 = 1 then 1069 else 659) else (if t 3 = 0 then 1094 else if t 3 = 1 then 1071 else 661))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 175) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 161) else (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 163)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2549) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3877) else (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3878)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2555) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3886) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3885 else 3887))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 376 else 895) else if t 2 = 1 then (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 889) else (if t 3 = 0 then 398 else if t 3 = 1 then 366 else 891)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2879) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3882) else (if t 3 = 0 then 3918 else if t 3 = 1 then 3881 else 3883)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2700 else 3197) else if t 2 = 1 then (if t 3 = 0 then 4191 else if t 3 = 1 then 3888 else 3890) else (if t 3 = 0 then 4192 else if t 3 = 1 then 3889 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4680 else (if jt.2.val < 2 then 4682 else 4685)) else (if jt.2.val < 4 then 4681 else (if jt.2.val < 5 then 4684 else 4683))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4245 else (if jt.2.val < 2 then 4247 else 4250)) else (if jt.2.val < 4 then 4246 else (if jt.2.val < 5 then 4249 else 4248)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4455 else (if jt.2.val < 2 then 4457 else 4460)) else (if jt.2.val < 4 then 4456 else (if jt.2.val < 5 then 4459 else 4458))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4174 else (if jt.2.val < 2 then 4189 else 4176)) else (if jt.2.val < 4 then 4187 else (if jt.2.val < 5 then 4188 else 4131)))))

checked_coverage fastCoverage0553 pairing0553 template0553 witness0553

theorem coverage0553 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0553) (maskBits m))
    cores template0553 witness0553 := by
  rw [← coresFast_eq]
  exact fastCoverage0553

theorem coverageSize0553 : ∀ q : Pattern,
    (cores (witness0553 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0553 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0553
#print axioms coverageSize0553

noncomputable def pairing0554 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0554 : List (Fin 4935) := templateData0554

noncomputable def witness0554 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3215) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2759) else (if t 3 = 0 then 4213 else if t 3 = 1 then 4211 else 3927)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 291) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 290) else (if t 3 = 0 then 2199 else if t 3 = 1 then 2195 else 298)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 343 else 929) else if t 2 = 1 then (if t 3 = 0 then 344 else if t 3 = 1 then 342 else 928) else (if t 3 = 0 then 359 else if t 3 = 1 then 358 else 932))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 585) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 584) else (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 592)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2572) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3488) else (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3489)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2471 else 2886) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3479 else 3492) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3480 else 3493))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1042 else 599) else if t 2 = 1 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1041 else 598) else (if t 3 = 0 then 1057 else if t 3 = 1 then 1056 else 602)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2838 else 2579) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3472 else 3490) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3473 else 3491)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2489 else 4197) else if t 2 = 1 then (if t 3 = 0 then 3095 else if t 3 = 1 then 3486 else 3494) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3487 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4647 else (if jt.2.val < 2 then 4657 else 4658)) else (if jt.2.val < 4 then 4654 else (if jt.2.val < 5 then 4656 else 4655))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3600 else (if jt.2.val < 2 then 3610 else 3611)) else (if jt.2.val < 4 then 3607 else (if jt.2.val < 5 then 3609 else 3608)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4730 else (if jt.2.val < 2 then 4736 else 4733)) else (if jt.2.val < 4 then 4734 else (if jt.2.val < 5 then 4735 else 4728))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3438 else (if jt.2.val < 2 then 3482 else 3485)) else (if jt.2.val < 4 then 3481 else (if jt.2.val < 5 then 3484 else 3483)))))

checked_coverage fastCoverage0554 pairing0554 template0554 witness0554

theorem coverage0554 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0554) (maskBits m))
    cores template0554 witness0554 := by
  rw [← coresFast_eq]
  exact fastCoverage0554

theorem coverageSize0554 : ∀ q : Pattern,
    (cores (witness0554 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0554 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0554
#print axioms coverageSize0554

noncomputable def pairing0555 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0555 : List (Fin 4935) := templateData0555

noncomputable def witness0555 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3499) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 2756) else (if t 3 = 0 then 3959 else if t 3 = 1 then 3953 else 4207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 277) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 264) else (if t 3 = 0 then 1611 else if t 3 = 1 then 1589 else 266)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 859 else 279) else if t 2 = 1 then (if t 3 = 0 then 874 else if t 3 = 1 then 853 else 269) else (if t 3 = 0 then 878 else if t 3 = 1 then 855 else 271))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 571) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 557) else (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 559)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2550) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3123) else (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3124)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2949 else 2556) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3130 else 3132) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3131 else 3133))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 760 else 1111) else if t 2 = 1 then (if t 3 = 0 then 775 else if t 3 = 1 then 748 else 1105) else (if t 3 = 0 then 782 else if t 3 = 1 then 750 else 1107)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2697 else 2880) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3126 else 3128) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3127 else 3129)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2701 else 3934) else if t 2 = 1 then (if t 3 = 0 then 3500 else if t 3 = 1 then 3134 else 3136) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3135 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4617 else (if jt.2.val < 2 then 4619 else 4622)) else (if jt.2.val < 4 then 4618 else (if jt.2.val < 5 then 4621 else 4620))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3567 else (if jt.2.val < 2 then 3569 else 3572)) else (if jt.2.val < 4 then 3568 else (if jt.2.val < 5 then 3571 else 3570)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4458 else (if jt.2.val < 2 then 4465 else 4460)) else (if jt.2.val < 4 then 4464 else (if jt.2.val < 5 then 4466 else 4455))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3483 else (if jt.2.val < 2 then 3498 else 3485)) else (if jt.2.val < 4 then 3496 else (if jt.2.val < 5 then 3497 else 3438)))))

checked_coverage fastCoverage0555 pairing0555 template0555 witness0555

theorem coverage0555 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0555) (maskBits m))
    cores template0555 witness0555 := by
  rw [← coresFast_eq]
  exact fastCoverage0555

theorem coverageSize0555 : ∀ q : Pattern,
    (cores (witness0555 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0555 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0555
#print axioms coverageSize0555

noncomputable def pairing0556 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0556 : List (Fin 4935) := templateData0556

noncomputable def witness0556 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 20 else 900) else if t 2 = 1 then (if t 3 = 0 then 22 else if t 3 = 1 then 18 else 898) else (if t 3 = 0 then 50 else if t 3 = 1 then 48 else 904)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 16 else if t 3 = 1 then 12 else 94) else if t 2 = 1 then (if t 3 = 0 then 14 else if t 3 = 1 then 10 else 86) else (if t 3 = 0 then 46 else if t 3 = 1 then 43 else 87)) else (if t 2 = 0 then (if t 3 = 0 then 4196 else if t 3 = 1 then 3939 else 3943) else if t 2 = 1 then (if t 3 = 0 then 2787 else if t 3 = 1 then 2785 else 2797) else (if t 3 = 0 then 3522 else if t 3 = 1 then 3191 else 3198))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 19 else 899) else if t 2 = 1 then (if t 3 = 0 then 21 else if t 3 = 1 then 17 else 897) else (if t 3 = 0 then 49 else if t 3 = 1 then 47 else 903)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 15 else if t 3 = 1 then 11 else 90) else if t 2 = 1 then (if t 3 = 0 then 13 else if t 3 = 1 then 9 else 78) else (if t 3 = 0 then 45 else if t 3 = 1 then 42 else 80)) else (if t 2 = 0 then (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 91) else if t 2 = 1 then (if t 3 = 0 then 32 else if t 3 = 1 then 29 else 79) else (if t 3 = 0 then 52 else if t 3 = 1 then 51 else 81))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 66 else 3525) else if t 2 = 1 then (if t 3 = 0 then 1470 else if t 3 = 1 then 64 else 2127) else (if t 3 = 0 then 3942 else if t 3 = 1 then 74 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 917 else if t 3 = 1 then 61 else 92) else if t 2 = 1 then (if t 3 = 0 then 915 else if t 3 = 1 then 59 else 82) else (if t 3 = 0 then 921 else if t 3 = 1 then 72 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 920 else if t 3 = 1 then 69 else 93) else if t 2 = 1 then (if t 3 = 0 then 919 else if t 3 = 1 then 68 else 83) else (if t 3 = 0 then 923 else if t 3 = 1 then 76 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4617 else (if jt.2.val < 2 then 4643 else 4622)) else (if jt.2.val < 4 then 4641 else (if jt.2.val < 5 then 4642 else 4620))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4268 else (if jt.2.val < 2 then 4277 else 4271)) else (if jt.2.val < 4 then 4275 else (if jt.2.val < 5 then 4276 else 4260)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 7 else (if jt.2.val < 2 then 41 else 44)) else (if jt.2.val < 4 then 38 else (if jt.2.val < 5 then 40 else 39))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1238 else (if jt.2.val < 2 then 1240 else 1243)) else (if jt.2.val < 4 then 1239 else (if jt.2.val < 5 then 1242 else 1241)))))

checked_coverage fastCoverage0556 pairing0556 template0556 witness0556

theorem coverage0556 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0556) (maskBits m))
    cores template0556 witness0556 := by
  rw [← coresFast_eq]
  exact fastCoverage0556

theorem coverageSize0556 : ∀ q : Pattern,
    (cores (witness0556 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0556 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0556
#print axioms coverageSize0556

noncomputable def pairing0557 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0557 : List (Fin 4935) := templateData0557

noncomputable def witness0557 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 995 else 179) else if t 2 = 1 then (if t 3 = 0 then 1006 else if t 3 = 1 then 991 else 172) else (if t 3 = 0 then 1012 else if t 3 = 1 then 992 else 173)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1004 else if t 3 = 1 then 977 else 978) else if t 2 = 1 then (if t 3 = 0 then 1000 else if t 3 = 1 then 957 else 961) else (if t 3 = 0 then 1001 else if t 3 = 1 then 960 else 962)) else (if t 2 = 0 then (if t 3 = 0 then 3860 else if t 3 = 1 then 4046 else 4198) else if t 2 = 1 then (if t 3 = 0 then 2980 else if t 3 = 1 then 2970 else 2972) else (if t 3 = 0 then 3242 else if t 3 = 1 then 3338 else 3520))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 993 else 176) else if t 2 = 1 then (if t 3 = 0 then 1005 else if t 3 = 1 then 987 else 166) else (if t 3 = 0 then 1011 else if t 3 = 1 then 989 else 168)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1002 else if t 3 = 1 then 967 else 971) else if t 2 = 1 then (if t 3 = 0 then 996 else if t 3 = 1 then 939 else 945) else (if t 3 = 0 then 998 else if t 3 = 1 then 943 else 947)) else (if t 2 = 0 then (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 972) else if t 2 = 1 then (if t 3 = 0 then 997 else if t 3 = 1 then 941 else 946) else (if t 3 = 0 then 999 else if t 3 = 1 then 944 else 948))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 377 else 3240) else if t 2 = 1 then (if t 3 = 0 then 2139 else if t 3 = 1 then 367 else 1494) else (if t 3 = 0 then 4206 else if t 3 = 1 then 369 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 306 else if t 3 = 1 then 973 else 975) else if t 2 = 1 then (if t 3 = 0 then 300 else if t 3 = 1 then 949 else 953) else (if t 3 = 0 then 302 else if t 3 = 1 then 951 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 307 else if t 3 = 1 then 974 else 976) else if t 2 = 1 then (if t 3 = 0 then 301 else if t 3 = 1 then 950 else 954) else (if t 3 = 0 then 303 else if t 3 = 1 then 952 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4647 else (if jt.2.val < 2 then 4672 else 4658)) else (if jt.2.val < 4 then 4671 else (if jt.2.val < 5 then 4673 else 4655))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4248 else (if jt.2.val < 2 then 4258 else 4250)) else (if jt.2.val < 4 then 4257 else (if jt.2.val < 5 then 4259 else 4245)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 933 else (if jt.2.val < 2 then 935 else 970)) else (if jt.2.val < 4 then 934 else (if jt.2.val < 5 then 969 else 942))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1241 else (if jt.2.val < 2 then 1258 else 1243)) else (if jt.2.val < 4 then 1254 else (if jt.2.val < 5 then 1255 else 1238)))))

checked_coverage fastCoverage0557 pairing0557 template0557 witness0557

theorem coverage0557 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0557) (maskBits m))
    cores template0557 witness0557 := by
  rw [← coresFast_eq]
  exact fastCoverage0557

theorem coverageSize0557 : ∀ q : Pattern,
    (cores (witness0557 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0557 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0557
#print axioms coverageSize0557

noncomputable def pairing0558 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0558 : List (Fin 4935) := templateData0558

noncomputable def witness0558 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 428 else 1116) else if t 2 = 1 then (if t 3 = 0 then 430 else if t 3 = 1 then 426 else 1114) else (if t 3 = 0 then 452 else if t 3 = 1 then 450 else 1120)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 424 else if t 3 = 1 then 420 else 496) else if t 2 = 1 then (if t 3 = 0 then 422 else if t 3 = 1 then 418 else 488) else (if t 3 = 0 then 448 else if t 3 = 1 then 445 else 489)) else (if t 2 = 0 then (if t 3 = 0 then 3505 else if t 3 = 1 then 3203 else 3207) else if t 2 = 1 then (if t 3 = 0 then 2730 else if t 3 = 1 then 2728 else 2740) else (if t 3 = 0 then 4205 else if t 3 = 1 then 3929 else 3935))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 427 else 1115) else if t 2 = 1 then (if t 3 = 0 then 429 else if t 3 = 1 then 425 else 1113) else (if t 3 = 0 then 451 else if t 3 = 1 then 449 else 1119)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 423 else if t 3 = 1 then 419 else 492) else if t 2 = 1 then (if t 3 = 0 then 421 else if t 3 = 1 then 417 else 480) else (if t 3 = 0 then 447 else if t 3 = 1 then 444 else 482)) else (if t 2 = 0 then (if t 3 = 0 then 439 else if t 3 = 1 then 437 else 493) else if t 2 = 1 then (if t 3 = 0 then 438 else if t 3 = 1 then 436 else 481) else (if t 3 = 0 then 454 else if t 3 = 1 then 453 else 483))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 468 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1518 else if t 3 = 1 then 466 else 2148) else (if t 3 = 0 then 3206 else if t 3 = 1 then 476 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1133 else if t 3 = 1 then 463 else 494) else if t 2 = 1 then (if t 3 = 0 then 1131 else if t 3 = 1 then 461 else 484) else (if t 3 = 0 then 1137 else if t 3 = 1 then 474 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 1136 else if t 3 = 1 then 471 else 495) else if t 2 = 1 then (if t 3 = 0 then 1135 else if t 3 = 1 then 470 else 485) else (if t 3 = 0 then 1139 else if t 3 = 1 then 478 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4680 else (if jt.2.val < 2 then 4688 else 4685)) else (if jt.2.val < 4 then 4686 else (if jt.2.val < 5 then 4687 else 4683))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3608 else (if jt.2.val < 2 then 3623 else 3611)) else (if jt.2.val < 4 then 3621 else (if jt.2.val < 5 then 3622 else 3600)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 39 else (if jt.2.val < 2 then 446 else 44)) else (if jt.2.val < 4 then 414 else (if jt.2.val < 5 then 415 else 7))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1272 else (if jt.2.val < 2 then 1274 else 1279)) else (if jt.2.val < 4 then 1273 else (if jt.2.val < 5 then 1278 else 1277)))))

checked_coverage fastCoverage0558 pairing0558 template0558 witness0558

theorem coverage0558 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0558) (maskBits m))
    cores template0558 witness0558 := by
  rw [← coresFast_eq]
  exact fastCoverage0558

theorem coverageSize0558 : ∀ q : Pattern,
    (cores (witness0558 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0558 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0558
#print axioms coverageSize0558

noncomputable def pairing0559 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0559 : List (Fin 4935) := templateData0559

noncomputable def witness0559 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1205 else 575) else if t 2 = 1 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1201 else 568) else (if t 3 = 0 then 1222 else if t 3 = 1 then 1202 else 569)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1214 else if t 3 = 1 then 1187 else 1188) else if t 2 = 1 then (if t 3 = 0 then 1210 else if t 3 = 1 then 1167 else 1170) else (if t 3 = 0 then 1211 else if t 3 = 1 then 1169 else 1171)) else (if t 2 = 0 then (if t 3 = 0 then 3106 else if t 3 = 1 then 3329 else 3514) else if t 2 = 1 then (if t 3 = 0 then 3003 else if t 3 = 1 then 2993 else 2995) else (if t 3 = 0 then 3967 else if t 3 = 1 then 4054 else 4203))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1203 else 572) else if t 2 = 1 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1197 else 562) else (if t 3 = 0 then 1221 else if t 3 = 1 then 1199 else 564)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1212 else if t 3 = 1 then 1179 else 1181) else if t 2 = 1 then (if t 3 = 0 then 1206 else if t 3 = 1 then 1151 else 1155) else (if t 3 = 0 then 1208 else if t 3 = 1 then 1153 else 1157)) else (if t 2 = 0 then (if t 3 = 0 then 1213 else if t 3 = 1 then 1180 else 1182) else if t 2 = 1 then (if t 3 = 0 then 1207 else if t 3 = 1 then 1152 else 1156) else (if t 3 = 0 then 1209 else if t 3 = 1 then 1154 else 1158))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 761 else 3966) else if t 2 = 1 then (if t 3 = 0 then 2160 else if t 3 = 1 then 751 else 1542) else (if t 3 = 0 then 3523 else if t 3 = 1 then 753 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 696 else if t 3 = 1 then 1183 else 1185) else if t 2 = 1 then (if t 3 = 0 then 690 else if t 3 = 1 then 1159 else 1163) else (if t 3 = 0 then 692 else if t 3 = 1 then 1161 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 697 else if t 3 = 1 then 1184 else 1186) else if t 2 = 1 then (if t 3 = 0 then 691 else if t 3 = 1 then 1160 else 1164) else (if t 3 = 0 then 693 else if t 3 = 1 then 1162 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4692 else (if jt.2.val < 2 then 4708 else 4703)) else (if jt.2.val < 4 then 4707 else (if jt.2.val < 5 then 4709 else 4700))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3570 else (if jt.2.val < 2 then 3592 else 3572)) else (if jt.2.val < 4 then 3591 else (if jt.2.val < 5 then 3593 else 3567)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 942 else (if jt.2.val < 2 then 1177 else 970)) else (if jt.2.val < 4 then 1176 else (if jt.2.val < 5 then 1178 else 933))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1277 else (if jt.2.val < 2 then 1294 else 1279)) else (if jt.2.val < 4 then 1292 else (if jt.2.val < 5 then 1293 else 1272)))))

checked_coverage fastCoverage0559 pairing0559 template0559 witness0559

theorem coverage0559 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0559) (maskBits m))
    cores template0559 witness0559 := by
  rw [← coresFast_eq]
  exact fastCoverage0559

theorem coverageSize0559 : ∀ q : Pattern,
    (cores (witness0559 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0559 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0559
#print axioms coverageSize0559

end Crown.CertificateData
