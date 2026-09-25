import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0008

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0320 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0320 : List (Fin 4935) := templateData0320

noncomputable def witness0320 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 3951) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2778) else (if t 3 = 0 then 2997 else if t 3 = 1 then 2996 else 2781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 681) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 680) else (if t 3 = 0 then 1174 else if t 3 = 1 then 1172 else 694)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 726 else 1145) else if t 2 = 1 then (if t 3 = 0 then 727 else if t 3 = 1 then 725 else 1144) else (if t 3 = 0 then 1544 else if t 3 = 1 then 757 else 2161))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 189) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 188) else (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 202)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2570) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4179) else (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4181)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2885) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4183) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4177 else 4185))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1547) else if t 2 = 1 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 196) else (if t 3 = 0 then 841 else if t 3 = 1 then 840 else 206)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2574) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4180) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4164 else 4182)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2475 else 2887) else if t 2 = 1 then (if t 3 = 0 then 3838 else if t 3 = 1 then 4171 else 4184) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4178 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4134 else (if jt.2.val < 2 then 4154 else 4156)) else (if jt.2.val < 4 then 4151 else (if jt.2.val < 5 then 4153 else 4152))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4260 else (if jt.2.val < 2 then 4270 else 4271)) else (if jt.2.val < 4 then 4267 else (if jt.2.val < 5 then 4269 else 4268)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4261 else (if jt.2.val < 2 then 4265 else 4266)) else (if jt.2.val < 4 then 4262 else (if jt.2.val < 5 then 4264 else 4263))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4131 else (if jt.2.val < 2 then 4173 else 4176)) else (if jt.2.val < 4 then 4172 else (if jt.2.val < 5 then 4175 else 4174)))))

checked_coverage fastCoverage0320 pairing0320 template0320 witness0320

theorem coverage0320 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0320) (maskBits m))
    cores template0320 witness0320 := by
  rw [← coresFast_eq]
  exact fastCoverage0320

theorem coverageSize0320 : ∀ q : Pattern,
    (cores (witness0320 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0320 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0320
#print axioms coverageSize0320

noncomputable def pairing0321 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0321 : List (Fin 4935) := templateData0321

noncomputable def witness0321 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4190) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2775) else (if t 3 = 0 then 2741 else if t 3 = 1 then 2737 else 2987)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 667) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 654) else (if t 3 = 0 then 490 else if t 3 = 1 then 462 else 1132)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1075 else 669) else if t 2 = 1 then (if t 3 = 0 then 1090 else if t 3 = 1 then 1069 else 659) else (if t 3 = 0 then 2150 else if t 3 = 1 then 467 else 1519))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 175) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 161) else (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 889)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2549) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3877) else (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3882)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2555) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3886) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3888 else 3890))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 2116) else if t 2 = 1 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 163) else (if t 3 = 0 then 398 else if t 3 = 1 then 366 else 891)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2551) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3878) else (if t 3 = 0 then 3918 else if t 3 = 1 then 3881 else 3883)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2950 else 2557) else if t 2 = 1 then (if t 3 = 0 then 4038 else if t 3 = 1 then 3885 else 3887) else (if t 3 = 0 then 4192 else if t 3 = 1 then 3889 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3870 else (if jt.2.val < 2 then 3872 else 3894)) else (if jt.2.val < 4 then 3871 else (if jt.2.val < 5 then 3893 else 3874))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4245 else (if jt.2.val < 2 then 4247 else 4250)) else (if jt.2.val < 4 then 4246 else (if jt.2.val < 5 then 4249 else 4248)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3864 else (if jt.2.val < 2 then 3866 else 3901)) else (if jt.2.val < 4 then 3865 else (if jt.2.val < 5 then 3900 else 3879))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4174 else (if jt.2.val < 2 then 4189 else 4176)) else (if jt.2.val < 4 then 4187 else (if jt.2.val < 5 then 4188 else 4131)))))

checked_coverage fastCoverage0321 pairing0321 template0321 witness0321

theorem coverage0321 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0321) (maskBits m))
    cores template0321 witness0321 := by
  rw [← coresFast_eq]
  exact fastCoverage0321

theorem coverageSize0321 : ∀ q : Pattern,
    (cores (witness0321 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0321 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0321
#print axioms coverageSize0321

noncomputable def pairing0322 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0322 : List (Fin 4935) := templateData0322

noncomputable def witness0322 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2817 else 2577) else if t 2 = 1 then (if t 3 = 0 then 2813 else if t 3 = 1 then 2809 else 2860) else (if t 3 = 0 then 4203 else if t 3 = 1 then 4054 else 3967)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2815 else 1372) else if t 2 = 1 then (if t 3 = 0 then 2811 else if t 3 = 1 then 2807 else 1370) else (if t 3 = 0 then 1171 else if t 3 = 1 then 1169 else 1211)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1416 else 2119) else if t 2 = 1 then (if t 3 = 0 then 1415 else if t 3 = 1 then 1414 else 1777) else (if t 3 = 0 then 569 else if t 3 = 1 then 1202 else 1222))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2816 else 1687) else if t 2 = 1 then (if t 3 = 0 then 2812 else if t 3 = 1 then 2808 else 1685) else (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 866)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2814 else 2576) else if t 2 = 1 then (if t 3 = 0 then 2810 else if t 3 = 1 then 2806 else 2859) else (if t 3 = 0 then 2828 else if t 3 = 1 then 2826 else 2861)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2484 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2632 else if t 3 = 1 then 2854 else 2864) else (if t 3 = 0 then 2635 else if t 3 = 1 then 2856 else 2865))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1042 else 599) else if t 2 = 1 then (if t 3 = 0 then 1040 else if t 3 = 1 then 1038 else 1082) else (if t 3 = 0 then 2147 else if t 3 = 1 then 1817 else 1691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2838 else 2579) else if t 2 = 1 then (if t 3 = 0 then 2837 else if t 3 = 1 then 2835 else 2862) else (if t 3 = 0 then 2841 else if t 3 = 1 then 2840 else 2863)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2489 else 4197) else if t 2 = 1 then (if t 3 = 0 then 2637 else if t 3 = 1 then 2857 else 2866) else (if t 3 = 0 then 2639 else if t 3 = 1 then 2858 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3762 else (if jt.2.val < 2 then 3772 else 3773)) else (if jt.2.val < 4 then 3769 else (if jt.2.val < 5 then 3771 else 3770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3575 else (if jt.2.val < 2 then 3580 else 3581)) else (if jt.2.val < 4 then 3577 else (if jt.2.val < 5 then 3579 else 3578)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4263 else (if jt.2.val < 2 then 4274 else 4266)) else (if jt.2.val < 4 then 4272 else (if jt.2.val < 5 then 4273 else 4261))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3006 else (if jt.2.val < 2 then 3012 else 3015)) else (if jt.2.val < 4 then 3011 else (if jt.2.val < 5 then 3014 else 3013)))))

checked_coverage fastCoverage0322 pairing0322 template0322 witness0322

theorem coverage0322 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0322) (maskBits m))
    cores template0322 witness0322 := by
  rw [← coresFast_eq]
  exact fastCoverage0322

theorem coverageSize0322 : ∀ q : Pattern,
    (cores (witness0322 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0322 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0322
#print axioms coverageSize0322

noncomputable def pairing0323 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0323 : List (Fin 4935) := templateData0323

noncomputable def witness0323 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2705 else 2882) else if t 2 = 1 then (if t 3 = 0 then 2710 else if t 3 = 1 then 2688 else 2689) else (if t 3 = 0 then 3935 else if t 3 = 1 then 3929 else 4205)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2703 else 1357) else if t 2 = 1 then (if t 3 = 0 then 2708 else if t 3 = 1 then 2682 else 1339) else (if t 3 = 0 then 489 else if t 3 = 1 then 445 else 448)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2098 else 1359) else if t 2 = 1 then (if t 3 = 0 then 2107 else if t 3 = 1 then 2090 else 1342) else (if t 3 = 0 then 1120 else if t 3 = 1 then 450 else 452))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2704 else 1672) else if t 2 = 1 then (if t 3 = 0 then 2709 else if t 3 = 1 then 2685 else 1657) else (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 351)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2695 else 2878) else if t 2 = 1 then (if t 3 = 0 then 2707 else if t 3 = 1 then 2664 else 2670) else (if t 3 = 0 then 2715 else if t 3 = 1 then 2666 else 2671)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2699 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2902 else if t 3 = 1 then 2674 else 2678) else (if t 3 = 0 then 2903 else if t 3 = 1 then 2675 else 2679))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 760 else 1111) else if t 2 = 1 then (if t 3 = 0 then 774 else if t 3 = 1 then 733 else 735) else (if t 3 = 0 then 1499 else if t 3 = 1 then 1484 else 2158)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2697 else 2880) else if t 2 = 1 then (if t 3 = 0 then 2717 else if t 3 = 1 then 2668 else 2672) else (if t 3 = 0 then 2719 else if t 3 = 1 then 2669 else 2673)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2701 else 3934) else if t 2 = 1 then (if t 3 = 0 then 2904 else if t 3 = 1 then 2676 else 2680) else (if t 3 = 0 then 2905 else if t 3 = 1 then 2677 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3726 else (if jt.2.val < 2 then 3728 else 3735)) else (if jt.2.val < 4 then 3727 else (if jt.2.val < 5 then 3734 else 3733))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3615 else (if jt.2.val < 2 then 3617 else 3620)) else (if jt.2.val < 4 then 3616 else (if jt.2.val < 5 then 3619 else 3618)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3879 else (if jt.2.val < 2 then 3932 else 3901)) else (if jt.2.val < 4 then 3931 else (if jt.2.val < 5 then 3933 else 3864))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3013 else (if jt.2.val < 2 then 3033 else 3015)) else (if jt.2.val < 4 then 3027 else (if jt.2.val < 5 then 3028 else 3006)))))

checked_coverage fastCoverage0323 pairing0323 template0323 witness0323

theorem coverage0323 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0323) (maskBits m))
    cores template0323 witness0323 := by
  rw [← coresFast_eq]
  exact fastCoverage0323

theorem coverageSize0323 : ∀ q : Pattern,
    (cores (witness0323 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0323 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0323
#print axioms coverageSize0323

noncomputable def pairing0324 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0324 : List (Fin 4935) := templateData0324

noncomputable def witness0324 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 20 else 900) else if t 2 = 1 then (if t 3 = 0 then 22 else if t 3 = 1 then 18 else 898) else (if t 3 = 0 then 1471 else if t 3 = 1 then 65 else 2129)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 16 else if t 3 = 1 then 12 else 94) else if t 2 = 1 then (if t 3 = 0 then 14 else if t 3 = 1 then 10 else 86) else (if t 3 = 0 then 916 else if t 3 = 1 then 60 else 88)) else (if t 2 = 0 then (if t 3 = 0 then 4196 else if t 3 = 1 then 3939 else 3943) else if t 2 = 1 then (if t 3 = 0 then 2787 else if t 3 = 1 then 2785 else 2797) else (if t 3 = 0 then 2983 else if t 3 = 1 then 2794 else 2798))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 19 else 899) else if t 2 = 1 then (if t 3 = 0 then 21 else if t 3 = 1 then 17 else 897) else (if t 3 = 0 then 1470 else if t 3 = 1 then 64 else 2127)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 15 else if t 3 = 1 then 11 else 90) else if t 2 = 1 then (if t 3 = 0 then 13 else if t 3 = 1 then 9 else 78) else (if t 3 = 0 then 915 else if t 3 = 1 then 59 else 82)) else (if t 2 = 0 then (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 91) else if t 2 = 1 then (if t 3 = 0 then 32 else if t 3 = 1 then 29 else 79) else (if t 3 = 0 then 919 else if t 3 = 1 then 68 else 83))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 1509 else 2986) else if t 2 = 1 then (if t 3 = 0 then 49 else if t 3 = 1 then 47 else 903) else (if t 3 = 0 then 3942 else if t 3 = 1 then 74 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2124 else if t 3 = 1 then 1506 else 1521) else if t 2 = 1 then (if t 3 = 0 then 45 else if t 3 = 1 then 42 else 80) else (if t 3 = 0 then 921 else if t 3 = 1 then 72 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 2126 else if t 3 = 1 then 1511 else 1522) else if t 2 = 1 then (if t 3 = 0 then 52 else if t 3 = 1 then 51 else 81) else (if t 3 = 0 then 923 else if t 3 = 1 then 76 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3726 else (if jt.2.val < 2 then 3743 else 3735)) else (if jt.2.val < 4 then 3741 else (if jt.2.val < 5 then 3742 else 3733))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4268 else (if jt.2.val < 2 then 4277 else 4271)) else (if jt.2.val < 4 then 4275 else (if jt.2.val < 5 then 4276 else 4260)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1997 else (if jt.2.val < 2 then 2002 else 2003)) else (if jt.2.val < 4 then 1999 else (if jt.2.val < 5 then 2001 else 2000))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1238 else (if jt.2.val < 2 then 1240 else 1243)) else (if jt.2.val < 4 then 1239 else (if jt.2.val < 5 then 1242 else 1241)))))

checked_coverage fastCoverage0324 pairing0324 template0324 witness0324

theorem coverage0324 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0324) (maskBits m))
    cores template0324 witness0324 := by
  rw [← coresFast_eq]
  exact fastCoverage0324

theorem coverageSize0324 : ∀ q : Pattern,
    (cores (witness0324 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0324 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0324
#print axioms coverageSize0324

noncomputable def pairing0325 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0325 : List (Fin 4935) := templateData0325

noncomputable def witness0325 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 995 else 179) else if t 2 = 1 then (if t 3 = 0 then 1006 else if t 3 = 1 then 991 else 172) else (if t 3 = 0 then 2140 else if t 3 = 1 then 373 else 1496)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1004 else if t 3 = 1 then 977 else 978) else if t 2 = 1 then (if t 3 = 0 then 1000 else if t 3 = 1 then 957 else 961) else (if t 3 = 0 then 304 else if t 3 = 1 then 963 else 965)) else (if t 2 = 0 then (if t 3 = 0 then 3860 else if t 3 = 1 then 4046 else 4198) else if t 2 = 1 then (if t 3 = 0 then 2980 else if t 3 = 1 then 2970 else 2972) else (if t 3 = 0 then 2762 else if t 3 = 1 then 2973 else 2974))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 993 else 176) else if t 2 = 1 then (if t 3 = 0 then 1005 else if t 3 = 1 then 987 else 166) else (if t 3 = 0 then 2139 else if t 3 = 1 then 367 else 1494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1002 else if t 3 = 1 then 967 else 971) else if t 2 = 1 then (if t 3 = 0 then 996 else if t 3 = 1 then 939 else 945) else (if t 3 = 0 then 300 else if t 3 = 1 then 949 else 953)) else (if t 2 = 0 then (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 972) else if t 2 = 1 then (if t 3 = 0 then 997 else if t 3 = 1 then 941 else 946) else (if t 3 = 0 then 301 else if t 3 = 1 then 950 else 954))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1430 else 2758) else if t 2 = 1 then (if t 3 = 0 then 1011 else if t 3 = 1 then 989 else 168) else (if t 3 = 0 then 4206 else if t 3 = 1 then 369 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1374 else if t 3 = 1 then 1795 else 2136) else if t 2 = 1 then (if t 3 = 0 then 998 else if t 3 = 1 then 943 else 947) else (if t 3 = 0 then 302 else if t 3 = 1 then 951 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 1375 else if t 3 = 1 then 1796 else 2137) else if t 2 = 1 then (if t 3 = 0 then 999 else if t 3 = 1 then 944 else 948) else (if t 3 = 0 then 303 else if t 3 = 1 then 952 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3762 else (if jt.2.val < 2 then 3793 else 3773)) else (if jt.2.val < 4 then 3792 else (if jt.2.val < 5 then 3794 else 3770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4248 else (if jt.2.val < 2 then 4258 else 4250)) else (if jt.2.val < 4 then 4257 else (if jt.2.val < 5 then 4259 else 4245)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2130 else (if jt.2.val < 2 then 2132 else 2135)) else (if jt.2.val < 4 then 2131 else (if jt.2.val < 5 then 2134 else 2133))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1241 else (if jt.2.val < 2 then 1258 else 1243)) else (if jt.2.val < 4 then 1254 else (if jt.2.val < 5 then 1255 else 1238)))))

checked_coverage fastCoverage0325 pairing0325 template0325 witness0325

theorem coverage0325 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0325) (maskBits m))
    cores template0325 witness0325 := by
  rw [← coresFast_eq]
  exact fastCoverage0325

theorem coverageSize0325 : ∀ q : Pattern,
    (cores (witness0325 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0325 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0325
#print axioms coverageSize0325

noncomputable def pairing0326 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0326 : List (Fin 4935) := templateData0326

noncomputable def witness0326 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1574 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1570 else 1853) else (if t 3 = 0 then 271 else if t 3 = 1 then 855 else 878)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1566 else 1619) else if t 2 = 1 then (if t 3 = 0 then 1564 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 266 else if t 3 = 1 then 1589 else 1611)) else (if t 2 = 0 then (if t 3 = 0 then 2898 else if t 3 = 1 then 2482 else 2501) else if t 2 = 1 then (if t 3 = 0 then 2630 else if t 3 = 1 then 3219 else 3227) else (if t 3 = 0 then 4207 else if t 3 = 1 then 3953 else 3959))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1573 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1569 else 1851) else (if t 3 = 0 then 270 else if t 3 = 1 then 854 else 876)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1565 else 1617) else if t 2 = 1 then (if t 3 = 0 then 1563 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 265 else if t 3 = 1 then 1588 else 1604)) else (if t 2 = 0 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1582 else 1618) else if t 2 = 1 then (if t 3 = 0 then 1581 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 273 else if t 3 = 1 then 1591 else 1605))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 468 else 4208) else if t 2 = 1 then (if t 3 = 0 then 660 else if t 3 = 1 then 1070 else 1092) else (if t 3 = 0 then 2777 else if t 3 = 1 then 1598 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1133 else if t 3 = 1 then 463 else 494) else if t 2 = 1 then (if t 3 = 0 then 655 else if t 3 = 1 then 1592 else 1606) else (if t 3 = 0 then 2169 else if t 3 = 1 then 1596 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 1136 else if t 3 = 1 then 471 else 495) else if t 2 = 1 then (if t 3 = 0 then 663 else if t 3 = 1 then 1595 else 1607) else (if t 3 = 0 then 2171 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3870 else (if jt.2.val < 2 then 3957 else 3894)) else (if jt.2.val < 4 then 3955 else (if jt.2.val < 5 then 3956 else 3874))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3578 else (if jt.2.val < 2 then 3596 else 3581)) else (if jt.2.val < 4 then 3594 else (if jt.2.val < 5 then 3595 else 3575)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2000 else (if jt.2.val < 2 then 2035 else 2003)) else (if jt.2.val < 4 then 2031 else (if jt.2.val < 5 then 2032 else 1997))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2163 else (if jt.2.val < 2 then 2165 else 2168)) else (if jt.2.val < 4 then 2164 else (if jt.2.val < 5 then 2167 else 2166)))))

checked_coverage fastCoverage0326 pairing0326 template0326 witness0326

theorem coverage0326 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0326) (maskBits m))
    cores template0326 witness0326 := by
  rw [← coresFast_eq]
  exact fastCoverage0326

theorem coverageSize0326 : ∀ q : Pattern,
    (cores (witness0326 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0326 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0326
#print axioms coverageSize0326

noncomputable def pairing0327 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0327 : List (Fin 4935) := templateData0327

noncomputable def witness0327 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2219 else 1676) else if t 2 = 1 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2213 else 1661) else (if t 3 = 0 then 932 else if t 3 = 1 then 358 else 359)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2207 else 1892) else if t 2 = 1 then (if t 3 = 0 then 2222 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 298 else if t 3 = 1 then 2195 else 2199)) else (if t 2 = 0 then (if t 3 = 0 then 2654 else if t 3 = 1 then 2939 else 2940) else if t 2 = 1 then (if t 3 = 0 then 2648 else if t 3 = 1 then 3528 else 3531) else (if t 3 = 0 then 3927 else if t 3 = 1 then 4211 else 4213))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2217 else 1673) else if t 2 = 1 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2211 else 1658) else (if t 3 = 0 then 930 else if t 3 = 1 then 352 else 354)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2205 else 1889) else if t 2 = 1 then (if t 3 = 0 then 2220 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 294 else if t 3 = 1 then 2179 else 2187)) else (if t 2 = 0 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2206 else 1890) else if t 2 = 1 then (if t 3 = 0 then 2221 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 295 else if t 3 = 1 then 2180 else 2188))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 761 else 3966) else if t 2 = 1 then (if t 3 = 0 then 1146 else if t 3 = 1 then 736 else 738) else (if t 3 = 0 then 2990 else if t 3 = 1 then 1487 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 696 else if t 3 = 1 then 1183 else 1185) else if t 2 = 1 then (if t 3 = 0 then 684 else if t 3 = 1 then 2181 else 2189) else (if t 3 = 0 then 1473 else if t 3 = 1 then 2183 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 697 else if t 3 = 1 then 1184 else 1186) else if t 2 = 1 then (if t 3 = 0 then 685 else if t 3 = 1 then 2182 else 2190) else (if t 3 = 0 then 1474 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4134 else (if jt.2.val < 2 then 4210 else 4156)) else (if jt.2.val < 4 then 4209 else (if jt.2.val < 5 then 4212 else 4152))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3618 else (if jt.2.val < 2 then 3625 else 3620)) else (if jt.2.val < 4 then 3624 else (if jt.2.val < 5 then 3626 else 3615)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2133 else (if jt.2.val < 2 then 2203 else 2135)) else (if jt.2.val < 4 then 2202 else (if jt.2.val < 5 then 2204 else 2130))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2166 else (if jt.2.val < 2 then 2216 else 2168)) else (if jt.2.val < 4 then 2214 else (if jt.2.val < 5 then 2215 else 2163)))))

checked_coverage fastCoverage0327 pairing0327 template0327 witness0327

theorem coverage0327 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0327) (maskBits m))
    cores template0327 witness0327 := by
  rw [← coresFast_eq]
  exact fastCoverage0327

theorem coverageSize0327 : ∀ q : Pattern,
    (cores (witness0327 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0327 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0327
#print axioms coverageSize0327

noncomputable def pairing0328 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0328 : List (Fin 4935) := templateData0328

noncomputable def witness0328 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 4056) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2996) else (if t 3 = 0 then 2779 else if t 3 = 1 then 2778 else 2781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 1173) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 1172) else (if t 3 = 0 then 682 else if t 3 = 1 then 680 else 694)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 726 else 758) else if t 2 = 1 then (if t 3 = 0 then 727 else if t 3 = 1 then 725 else 757) else (if t 3 = 0 then 1826 else if t 3 = 1 then 1144 else 2161))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 822) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 821) else (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 202)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2829) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4163) else (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4181)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2487) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4177) else (if t 3 = 0 then 4039 else if t 3 = 1 then 4183 else 4185))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1818) else if t 2 = 1 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 840) else (if t 3 = 0 then 197 else if t 3 = 1 then 196 else 206)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2842) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4164) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4180 else 4182)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2475 else 2491) else if t 2 = 1 then (if t 3 = 0 then 3838 else if t 3 = 1 then 4171 else 4178) else (if t 3 = 0 then 4040 else if t 3 = 1 then 4184 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4134 else (if jt.2.val < 2 then 4154 else 4156)) else (if jt.2.val < 4 then 4151 else (if jt.2.val < 5 then 4153 else 4152))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4260 else (if jt.2.val < 2 then 4270 else 4271)) else (if jt.2.val < 4 then 4267 else (if jt.2.val < 5 then 4269 else 4268)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4215 else (if jt.2.val < 2 then 4223 else 4226)) else (if jt.2.val < 4 then 4222 else (if jt.2.val < 5 then 4225 else 4224))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4278 else (if jt.2.val < 2 then 4282 else 4283)) else (if jt.2.val < 4 then 4279 else (if jt.2.val < 5 then 4281 else 4280)))))

checked_coverage fastCoverage0328 pairing0328 template0328 witness0328

theorem coverage0328 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0328) (maskBits m))
    cores template0328 witness0328 := by
  rw [← coresFast_eq]
  exact fastCoverage0328

theorem coverageSize0328 : ∀ q : Pattern,
    (cores (witness0328 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0328 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0328
#print axioms coverageSize0328

noncomputable def pairing0329 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0329 : List (Fin 4935) := templateData0329

noncomputable def witness0329 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 4203) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2995) else (if t 3 = 0 then 2741 else if t 3 = 1 then 2740 else 2743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 1171) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 1170) else (if t 3 = 0 then 490 else if t 3 = 1 then 488 else 502)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 538 else 569) else if t 2 = 1 then (if t 3 = 0 then 539 else if t 3 = 1 then 537 else 568) else (if t 3 = 0 then 2150 else if t 3 = 1 then 1114 else 1837))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 820) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 819) else (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 403)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2828) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4000) else (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4021)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2635) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4017) else (if t 3 = 0 then 4191 else if t 3 = 1 then 4023 else 4025))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 2147) else if t 2 = 1 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 839) else (if t 3 = 0 then 398 else if t 3 = 1 then 397 else 407)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2841) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4003) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4020 else 4022)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2627 else 2639) else if t 2 = 1 then (if t 3 = 0 then 3847 else if t 3 = 1 then 4016 else 4018) else (if t 3 = 0 then 4192 else if t 3 = 1 then 4024 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3972 else (if jt.2.val < 2 then 3992 else 3994)) else (if jt.2.val < 4 then 3989 else (if jt.2.val < 5 then 3991 else 3990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4233 else (if jt.2.val < 2 then 4243 else 4244)) else (if jt.2.val < 4 then 4240 else (if jt.2.val < 5 then 4242 else 4241)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4068 else (if jt.2.val < 2 then 4074 else 4079)) else (if jt.2.val < 4 then 4073 else (if jt.2.val < 5 then 4078 else 4077))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4280 else (if jt.2.val < 2 then 4286 else 4283)) else (if jt.2.val < 4 then 4284 else (if jt.2.val < 5 then 4285 else 4278)))))

checked_coverage fastCoverage0329 pairing0329 template0329 witness0329

theorem coverage0329 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0329) (maskBits m))
    cores template0329 witness0329 := by
  rw [← coresFast_eq]
  exact fastCoverage0329

theorem coverageSize0329 : ∀ q : Pattern,
    (cores (witness0329 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0329 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0329
#print axioms coverageSize0329

noncomputable def pairing0330 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0330 : List (Fin 4935) := templateData0330

noncomputable def witness0330 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2565 else 2577) else if t 2 = 1 then (if t 3 = 0 then 2560 else if t 3 = 1 then 2544 else 2545) else (if t 3 = 0 then 4190 else if t 3 = 1 then 3945 else 4058)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2563 else 1372) else if t 2 = 1 then (if t 3 = 0 then 2558 else if t 3 = 1 then 2538 else 1350) else (if t 3 = 0 then 667 else if t 3 = 1 then 641 else 644)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1762 else 2119) else if t 2 = 1 then (if t 3 = 0 then 1750 else if t 3 = 1 then 1747 else 1353) else (if t 3 = 0 then 669 else if t 3 = 1 then 646 else 648))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2564 else 1687) else if t 2 = 1 then (if t 3 = 0 then 2559 else if t 3 = 1 then 2541 else 1666) else (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 151)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2562 else 2576) else if t 2 = 1 then (if t 3 = 0 then 2548 else if t 3 = 1 then 2519 else 2526) else (if t 3 = 0 then 2549 else if t 3 = 1 then 2521 else 2527)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2883 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2554 else if t 3 = 1 then 2530 else 2534) else (if t 3 = 0 then 2555 else if t 3 = 1 then 2531 else 2535))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 585 else 599) else if t 2 = 1 then (if t 3 = 0 then 571 else if t 3 = 1 then 545 else 547) else (if t 3 = 0 then 2116 else if t 3 = 1 then 1532 else 1834)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2572 else 2579) else if t 2 = 1 then (if t 3 = 0 then 2550 else if t 3 = 1 then 2523 else 2528) else (if t 3 = 0 then 2551 else if t 3 = 1 then 2524 else 2529)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2886 else 4197) else if t 2 = 1 then (if t 3 = 0 then 2556 else if t 3 = 1 then 2532 else 2536) else (if t 3 = 0 then 2557 else if t 3 = 1 then 2533 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3702 else (if jt.2.val < 2 then 3704 else 3711)) else (if jt.2.val < 4 then 3703 else (if jt.2.val < 5 then 3710 else 3709))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3582 else (if jt.2.val < 2 then 3584 else 3587)) else (if jt.2.val < 4 then 3583 else (if jt.2.val < 5 then 3586 else 3585)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4224 else (if jt.2.val < 2 then 4232 else 4226)) else (if jt.2.val < 4 then 4230 else (if jt.2.val < 5 then 4231 else 4215))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2510 else (if jt.2.val < 2 then 2512 else 2553)) else (if jt.2.val < 4 then 2511 else (if jt.2.val < 5 then 2552 else 2525)))))

checked_coverage fastCoverage0330 pairing0330 template0330 witness0330

theorem coverage0330 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0330) (maskBits m))
    cores template0330 witness0330 := by
  rw [← coresFast_eq]
  exact fastCoverage0330

theorem coverageSize0330 : ∀ q : Pattern,
    (cores (witness0330 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0330 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0330
#print axioms coverageSize0330

noncomputable def pairing0331 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 6 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0331 : List (Fin 4935) := templateData0331

noncomputable def witness0331 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2710 else 2722) else if t 2 = 1 then (if t 3 = 0 then 2705 else if t 3 = 1 then 2688 else 2689) else (if t 3 = 0 then 4036 else if t 3 = 1 then 3929 else 4205)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2708 else 1371) else if t 2 = 1 then (if t 3 = 0 then 2703 else if t 3 = 1 then 2682 else 1339) else (if t 3 = 0 then 475 else if t 3 = 1 then 445 else 448)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2107 else 1780) else if t 2 = 1 then (if t 3 = 0 then 2098 else if t 3 = 1 then 2090 else 1342) else (if t 3 = 0 then 477 else if t 3 = 1 then 450 else 452))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2709 else 1686) else if t 2 = 1 then (if t 3 = 0 then 2704 else if t 3 = 1 then 2685 else 1657) else (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 351)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2707 else 2721) else if t 2 = 1 then (if t 3 = 0 then 2695 else if t 3 = 1 then 2664 else 2670) else (if t 3 = 0 then 2696 else if t 3 = 1 then 2666 else 2671)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2902 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2699 else if t 3 = 1 then 2674 else 2678) else (if t 3 = 0 then 2700 else if t 3 = 1 then 2675 else 2679))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 774 else 788) else if t 2 = 1 then (if t 3 = 0 then 760 else if t 3 = 1 then 733 else 735) else (if t 3 = 0 then 1774 else if t 3 = 1 then 1484 else 2158)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2717 else 2724) else if t 2 = 1 then (if t 3 = 0 then 2697 else if t 3 = 1 then 2668 else 2672) else (if t 3 = 0 then 2698 else if t 3 = 1 then 2669 else 2673)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2904 else 4045) else if t 2 = 1 then (if t 3 = 0 then 2701 else if t 3 = 1 then 2676 else 2680) else (if t 3 = 0 then 2702 else if t 3 = 1 then 2677 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3726 else (if jt.2.val < 2 then 3728 else 3735)) else (if jt.2.val < 4 then 3727 else (if jt.2.val < 5 then 3734 else 3733))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3615 else (if jt.2.val < 2 then 3617 else 3620)) else (if jt.2.val < 4 then 3616 else (if jt.2.val < 5 then 3619 else 3618)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4077 else (if jt.2.val < 2 then 4091 else 4079)) else (if jt.2.val < 4 then 4089 else (if jt.2.val < 5 then 4090 else 4068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2525 else (if jt.2.val < 2 then 2693 else 2553)) else (if jt.2.val < 4 then 2692 else (if jt.2.val < 5 then 2694 else 2510)))))

checked_coverage fastCoverage0331 pairing0331 template0331 witness0331

theorem coverage0331 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0331) (maskBits m))
    cores template0331 witness0331 := by
  rw [← coresFast_eq]
  exact fastCoverage0331

theorem coverageSize0331 : ∀ q : Pattern,
    (cores (witness0331 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0331 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0331
#print axioms coverageSize0331

noncomputable def pairing0332 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0332 : List (Fin 4935) := templateData0332

noncomputable def witness0332 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 20 else 67) else if t 2 = 1 then (if t 3 = 0 then 22 else if t 3 = 1 then 18 else 65) else (if t 3 = 0 then 1807 else if t 3 = 1 then 898 else 2129)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 16 else if t 3 = 1 then 12 else 62) else if t 2 = 1 then (if t 3 = 0 then 14 else if t 3 = 1 then 10 else 60) else (if t 3 = 0 then 100 else if t 3 = 1 then 86 else 88)) else (if t 2 = 0 then (if t 3 = 0 then 4196 else if t 3 = 1 then 3939 else 4060) else if t 2 = 1 then (if t 3 = 0 then 2787 else if t 3 = 1 then 2785 else 2794) else (if t 3 = 0 then 2800 else if t 3 = 1 then 2797 else 2798))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 19 else 66) else if t 2 = 1 then (if t 3 = 0 then 21 else if t 3 = 1 then 17 else 64) else (if t 3 = 0 then 1806 else if t 3 = 1 then 897 else 2127)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 15 else if t 3 = 1 then 11 else 61) else if t 2 = 1 then (if t 3 = 0 then 13 else if t 3 = 1 then 9 else 59) else (if t 3 = 0 then 96 else if t 3 = 1 then 78 else 82)) else (if t 2 = 0 then (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 69) else if t 2 = 1 then (if t 3 = 0 then 32 else if t 3 = 1 then 29 else 68) else (if t 3 = 0 then 97 else if t 3 = 1 then 79 else 83))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 1509 else 2739) else if t 2 = 1 then (if t 3 = 0 then 49 else if t 3 = 1 then 47 else 74) else (if t 3 = 0 then 4059 else if t 3 = 1 then 903 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2124 else if t 3 = 1 then 1506 else 1848) else if t 2 = 1 then (if t 3 = 0 then 45 else if t 3 = 1 then 42 else 72) else (if t 3 = 0 then 98 else if t 3 = 1 then 80 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 2126 else if t 3 = 1 then 1511 else 1850) else if t 2 = 1 then (if t 3 = 0 then 52 else if t 3 = 1 then 51 else 76) else (if t 3 = 0 then 99 else if t 3 = 1 then 81 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3726 else (if jt.2.val < 2 then 3743 else 3735)) else (if jt.2.val < 4 then 3741 else (if jt.2.val < 5 then 3742 else 3733))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4268 else (if jt.2.val < 2 then 4277 else 4271)) else (if jt.2.val < 4 then 4275 else (if jt.2.val < 5 then 4276 else 4260)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2394 else (if jt.2.val < 2 then 2396 else 2399)) else (if jt.2.val < 4 then 2395 else (if jt.2.val < 5 then 2398 else 2397))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 6 else (if jt.2.val < 2 then 58 else 63)) else (if jt.2.val < 4 then 55 else (if jt.2.val < 5 then 57 else 56)))))

checked_coverage fastCoverage0332 pairing0332 template0332 witness0332

theorem coverage0332 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0332) (maskBits m))
    cores template0332 witness0332 := by
  rw [← coresFast_eq]
  exact fastCoverage0332

theorem coverageSize0332 : ∀ q : Pattern,
    (cores (witness0332 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0332 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0332
#print axioms coverageSize0332

noncomputable def pairing0333 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0333 : List (Fin 4935) := templateData0333

noncomputable def witness0333 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 228 else 271) else if t 2 = 1 then (if t 3 = 0 then 230 else if t 3 = 1 then 226 else 269) else (if t 3 = 0 then 2140 else if t 3 = 1 then 928 else 1790)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 224 else if t 3 = 1 then 220 else 266) else if t 2 = 1 then (if t 3 = 0 then 222 else if t 3 = 1 then 218 else 264) else (if t 3 = 0 then 304 else if t 3 = 1 then 290 else 292)) else (if t 2 = 0 then (if t 3 = 0 then 4044 else if t 3 = 1 then 3923 else 4207) else if t 2 = 1 then (if t 3 = 0 then 2749 else if t 3 = 1 then 2747 else 2756) else (if t 3 = 0 then 2762 else if t 3 = 1 then 2759 else 2760))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 227 else 270) else if t 2 = 1 then (if t 3 = 0 then 229 else if t 3 = 1 then 225 else 268) else (if t 3 = 0 then 2139 else if t 3 = 1 then 924 else 1788)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 223 else if t 3 = 1 then 219 else 265) else if t 2 = 1 then (if t 3 = 0 then 221 else if t 3 = 1 then 217 else 263) else (if t 3 = 0 then 300 else if t 3 = 1 then 282 else 286)) else (if t 2 = 0 then (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 273) else if t 2 = 1 then (if t 3 = 0 then 240 else if t 3 = 1 then 237 else 272) else (if t 3 = 0 then 301 else if t 3 = 1 then 283 else 287))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1461 else 2777) else if t 2 = 1 then (if t 3 = 0 then 257 else if t 3 = 1 then 255 else 278) else (if t 3 = 0 then 4206 else if t 3 = 1 then 926 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1785 else if t 3 = 1 then 1458 else 2169) else if t 2 = 1 then (if t 3 = 0 then 253 else if t 3 = 1 then 250 else 276) else (if t 3 = 0 then 302 else if t 3 = 1 then 284 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 1787 else if t 3 = 1 then 1463 else 2171) else if t 2 = 1 then (if t 3 = 0 then 260 else if t 3 = 1 then 259 else 280) else (if t 3 = 0 then 303 else if t 3 = 1 then 285 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3702 else (if jt.2.val < 2 then 3755 else 3711)) else (if jt.2.val < 4 then 3753 else (if jt.2.val < 5 then 3754 else 3709))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4241 else (if jt.2.val < 2 then 4256 else 4244)) else (if jt.2.val < 4 then 4254 else (if jt.2.val < 5 then 4255 else 4233)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2418 else (if jt.2.val < 2 then 2420 else 2423)) else (if jt.2.val < 4 then 2419 else (if jt.2.val < 5 then 2422 else 2421))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 56 else (if jt.2.val < 2 then 267 else 63)) else (if jt.2.val < 4 then 213 else (if jt.2.val < 5 then 214 else 6)))))

checked_coverage fastCoverage0333 pairing0333 template0333 witness0333

theorem coverage0333 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0333) (maskBits m))
    cores template0333 witness0333 := by
  rw [← coresFast_eq]
  exact fastCoverage0333

theorem coverageSize0333 : ∀ q : Pattern,
    (cores (witness0333 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0333 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0333
#print axioms coverageSize0333

noncomputable def pairing0334 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0334 : List (Fin 4935) := templateData0334

noncomputable def witness0334 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1912 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1901 else 1670) else (if t 3 = 0 then 179 else if t 3 = 1 then 158 else 159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1907 else 1619) else if t 2 = 1 then (if t 3 = 0 then 1891 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 978 else if t 3 = 1 then 1877 else 1881)) else (if t 2 = 0 then (if t 3 = 0 then 2506 else if t 3 = 1 then 2500 else 2501) else if t 2 = 1 then (if t 3 = 0 then 2938 else if t 3 = 1 then 3348 else 3351) else (if t 3 = 0 then 4198 else if t 3 = 1 then 4064 else 4066))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1911 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1899 else 1667) else (if t 3 = 0 then 176 else if t 3 = 1 then 152 else 154)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1905 else 1617) else if t 2 = 1 then (if t 3 = 0 then 1887 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 971 else if t 3 = 1 then 1861 else 1869)) else (if t 2 = 0 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1906 else 1618) else if t 2 = 1 then (if t 3 = 0 then 1888 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 972 else if t 3 = 1 then 1862 else 1870))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 1115 else 4208) else if t 2 = 1 then (if t 3 = 0 then 572 else if t 3 = 1 then 548 else 550) else (if t 3 = 0 then 2758 else if t 3 = 1 then 1535 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 504 else if t 3 = 1 then 492 else 494) else if t 2 = 1 then (if t 3 = 0 then 1181 else if t 3 = 1 then 1863 else 1871) else (if t 3 = 0 then 2136 else if t 3 = 1 then 1865 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 505 else if t 3 = 1 then 493 else 495) else if t 2 = 1 then (if t 3 = 0 then 1182 else if t 3 = 1 then 1864 else 1872) else (if t 3 = 0 then 2137 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3972 else (if jt.2.val < 2 then 4063 else 3994)) else (if jt.2.val < 4 then 4062 else (if jt.2.val < 5 then 4065 else 3990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3585 else (if jt.2.val < 2 then 3598 else 3587)) else (if jt.2.val < 4 then 3597 else (if jt.2.val < 5 then 3599 else 3582)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2397 else (if jt.2.val < 2 then 2411 else 2399)) else (if jt.2.val < 4 then 2409 else (if jt.2.val < 5 then 2410 else 2394))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2367 else (if jt.2.val < 2 then 2369 else 2372)) else (if jt.2.val < 4 then 2368 else (if jt.2.val < 5 then 2371 else 2370)))))

checked_coverage fastCoverage0334 pairing0334 template0334 witness0334

theorem coverage0334 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0334) (maskBits m))
    cores template0334 witness0334 := by
  rw [← coresFast_eq]
  exact fastCoverage0334

theorem coverageSize0334 : ∀ q : Pattern,
    (cores (witness0334 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0334 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0334
#print axioms coverageSize0334

noncomputable def pairing0335 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 6)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0335 : List (Fin 4935) := templateData0335

noncomputable def witness0335 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2228 else 1856) else if t 2 = 1 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2213 else 1661) else (if t 3 = 0 then 380 else if t 3 = 1 then 358 else 359)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2222 else 1616) else if t 2 = 1 then (if t 3 = 0 then 2207 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 979 else if t 3 = 1 then 2195 else 2199)) else (if t 2 = 0 then (if t 3 = 0 then 2654 else if t 3 = 1 then 2648 else 2649) else if t 2 = 1 then (if t 3 = 0 then 2939 else if t 3 = 1 then 3528 else 3531) else (if t 3 = 0 then 4047 else if t 3 = 1 then 4211 else 4213))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2226 else 1854) else if t 2 = 1 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2211 else 1658) else (if t 3 = 0 then 377 else if t 3 = 1 then 352 else 354)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2220 else 1614) else if t 2 = 1 then (if t 3 = 0 then 2205 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 973 else if t 3 = 1 then 2179 else 2187)) else (if t 2 = 0 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2221 else 1615) else if t 2 = 1 then (if t 3 = 0 then 2206 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 974 else if t 3 = 1 then 2180 else 2188))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 1146 else 4061) else if t 2 = 1 then (if t 3 = 0 then 761 else if t 3 = 1 then 736 else 738) else (if t 3 = 0 then 2796 else if t 3 = 1 then 1487 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 696 else if t 3 = 1 then 684 else 686) else if t 2 = 1 then (if t 3 = 0 then 1183 else if t 3 = 1 then 2181 else 2189) else (if t 3 = 0 then 1799 else if t 3 = 1 then 2183 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 697 else if t 3 = 1 then 685 else 687) else if t 2 = 1 then (if t 3 = 0 then 1184 else if t 3 = 1 then 2182 else 2190) else (if t 3 = 0 then 1800 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4134 else (if jt.2.val < 2 then 4210 else 4156)) else (if jt.2.val < 4 then 4209 else (if jt.2.val < 5 then 4212 else 4152))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3618 else (if jt.2.val < 2 then 3625 else 3620)) else (if jt.2.val < 4 then 3624 else (if jt.2.val < 5 then 3626 else 3615)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2421 else (if jt.2.val < 2 then 2429 else 2423)) else (if jt.2.val < 4 then 2427 else (if jt.2.val < 5 then 2428 else 2418))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2370 else (if jt.2.val < 2 then 2374 else 2372)) else (if jt.2.val < 4 then 2373 else (if jt.2.val < 5 then 2375 else 2367)))))

checked_coverage fastCoverage0335 pairing0335 template0335 witness0335

theorem coverage0335 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0335) (maskBits m))
    cores template0335 witness0335 := by
  rw [← coresFast_eq]
  exact fastCoverage0335

theorem coverageSize0335 : ∀ q : Pattern,
    (cores (witness0335 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0335 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0335
#print axioms coverageSize0335

noncomputable def pairing0336 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0336 : List (Fin 4935) := templateData0336

noncomputable def witness0336 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 3925) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2750) else (if t 3 = 0 then 2997 else if t 3 = 1 then 2995 else 2757)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 538) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 537) else (if t 3 = 0 then 1174 else if t 3 = 1 then 1170 else 568)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 489 else 1120) else if t 2 = 1 then (if t 3 = 0 then 490 else if t 3 = 1 then 488 else 1114) else (if t 3 = 0 then 1526 else if t 3 = 1 then 502 else 1837))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 243) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 242) else (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 274)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2614) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4015) else (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4017)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2903) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4023) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4021 else 4025))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 1464) else if t 2 = 1 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 261) else (if t 3 = 0 then 841 else if t 3 = 1 then 839 else 281)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2627) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4016) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4003 else 4018)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2719 else 2905) else if t 2 = 1 then (if t 3 = 0 then 3918 else if t 3 = 1 then 4020 else 4024) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4022 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3972 else (if jt.2.val < 2 then 3992 else 3994)) else (if jt.2.val < 4 then 3989 else (if jt.2.val < 5 then 3991 else 3990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4287 else (if jt.2.val < 2 then 4289 else 4292)) else (if jt.2.val < 4 then 4288 else (if jt.2.val < 5 then 4291 else 4290)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4234 else (if jt.2.val < 2 then 4238 else 4239)) else (if jt.2.val < 4 then 4235 else (if jt.2.val < 5 then 4237 else 4236))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4069 else (if jt.2.val < 2 then 4075 else 4076)) else (if jt.2.val < 4 then 4070 else (if jt.2.val < 5 then 4072 else 4071)))))

checked_coverage fastCoverage0336 pairing0336 template0336 witness0336

theorem coverage0336 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0336) (maskBits m))
    cores template0336 witness0336 := by
  rw [← coresFast_eq]
  exact fastCoverage0336

theorem coverageSize0336 : ∀ q : Pattern,
    (cores (witness0336 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0336 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0336
#print axioms coverageSize0336

noncomputable def pairing0337 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0337 : List (Fin 4935) := templateData0337

noncomputable def witness0337 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4044) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2749) else (if t 3 = 0 then 2789 else if t 3 = 1 then 2787 else 2983)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 536) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 535) else (if t 3 = 0 then 727 else if t 3 = 1 then 723 else 1108)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1084 else 601) else if t 2 = 1 then (if t 3 = 0 then 1090 else if t 3 = 1 then 1078 else 595) else (if t 3 = 0 then 1826 else if t 3 = 1 then 784 else 1549))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 241) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 240) else (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 919)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2613) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3843) else (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3848)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2651) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3856) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3854 else 3858))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 1787) else if t 2 = 1 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 260) else (if t 3 = 0 then 54 else if t 3 = 1 then 52 else 923)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2626) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3846) else (if t 3 = 0 then 3838 else if t 3 = 1 then 3837 else 3850)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2957 else 2653) else if t 2 = 1 then (if t 3 = 0 then 4038 else if t 3 = 1 then 3853 else 3857) else (if t 3 = 0 then 4040 else if t 3 = 1 then 3855 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3806 else (if jt.2.val < 2 then 3826 else 3828)) else (if jt.2.val < 4 then 3823 else (if jt.2.val < 5 then 3825 else 3824))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4293 else (if jt.2.val < 2 then 4295 else 4298)) else (if jt.2.val < 4 then 4294 else (if jt.2.val < 5 then 4297 else 4296)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4096 else (if jt.2.val < 2 then 4100 else 4101)) else (if jt.2.val < 4 then 4097 else (if jt.2.val < 5 then 4099 else 4098))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4071 else (if jt.2.val < 2 then 4085 else 4076)) else (if jt.2.val < 4 then 4080 else (if jt.2.val < 5 then 4081 else 4069)))))

checked_coverage fastCoverage0337 pairing0337 template0337 witness0337

theorem coverage0337 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0337) (maskBits m))
    cores template0337 witness0337 := by
  rw [← coresFast_eq]
  exact fastCoverage0337

theorem coverageSize0337 : ∀ q : Pattern,
    (cores (witness0337 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0337 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0337
#print axioms coverageSize0337

noncomputable def pairing0338 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0338 : List (Fin 4935) := templateData0338

noncomputable def witness0338 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2813 else 2633) else if t 2 = 1 then (if t 3 = 0 then 2817 else if t 3 = 1 then 2809 else 2855) else (if t 3 = 0 then 4056 else if t 3 = 1 then 4054 else 3954)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2811 else 1415) else if t 2 = 1 then (if t 3 = 0 then 2815 else if t 3 = 1 then 2807 else 1414) else (if t 3 = 0 then 1173 else if t 3 = 1 then 1169 else 1202)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1371 else 1780) else if t 2 = 1 then (if t 3 = 0 then 1372 else if t 3 = 1 then 1370 else 1777) else (if t 3 = 0 then 695 else if t 3 = 1 then 1211 else 1222))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2812 else 1585) else if t 2 = 1 then (if t 3 = 0 then 2816 else if t 3 = 1 then 2808 else 1584) else (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 857)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2810 else 2632) else if t 2 = 1 then (if t 3 = 0 then 2814 else if t 3 = 1 then 2806 else 2854) else (if t 3 = 0 then 2829 else if t 3 = 1 then 2826 else 2856)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2721 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2576 else if t 3 = 1 then 2859 else 2864) else (if t 3 = 0 then 2578 else if t 3 = 1 then 2861 else 2865))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1040 else 665) else if t 2 = 1 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1073) else (if t 3 = 0 then 1818 else if t 3 = 1 then 1817 else 1601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2637) else if t 2 = 1 then (if t 3 = 0 then 2838 else if t 3 = 1 then 2835 else 2857) else (if t 3 = 0 then 2842 else if t 3 = 1 then 2840 else 2858)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2724 else 4045) else if t 2 = 1 then (if t 3 = 0 then 2579 else if t 3 = 1 then 2862 else 2866) else (if t 3 = 0 then 2580 else if t 3 = 1 then 2863 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3762 else (if jt.2.val < 2 then 3772 else 3773)) else (if jt.2.val < 4 then 3769 else (if jt.2.val < 5 then 3771 else 3770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3648 else (if jt.2.val < 2 then 3650 else 3653)) else (if jt.2.val < 4 then 3649 else (if jt.2.val < 5 then 3652 else 3651)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4236 else (if jt.2.val < 2 then 4253 else 4239)) else (if jt.2.val < 4 then 4251 else (if jt.2.val < 5 then 4252 else 4234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3007 else (if jt.2.val < 2 then 3016 else 3017)) else (if jt.2.val < 4 then 3008 else (if jt.2.val < 5 then 3010 else 3009)))))

checked_coverage fastCoverage0338 pairing0338 template0338 witness0338

theorem coverage0338 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0338) (maskBits m))
    cores template0338 witness0338 := by
  rw [← coresFast_eq]
  exact fastCoverage0338

theorem coverageSize0338 : ∀ q : Pattern,
    (cores (witness0338 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0338 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0338
#print axioms coverageSize0338

noncomputable def pairing0339 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0339 : List (Fin 4935) := templateData0339

noncomputable def witness0339 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2446 else 2898) else if t 2 = 1 then (if t 3 = 0 then 2450 else if t 3 = 1 then 2442 else 2482) else (if t 3 = 0 then 3941 else if t 3 = 1 then 3939 else 4060)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2444 else 1413) else if t 2 = 1 then (if t 3 = 0 then 2448 else if t 3 = 1 then 2440 else 1412) else (if t 3 = 0 then 726 else if t 3 = 1 then 722 else 756)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1756 else 1453) else if t 2 = 1 then (if t 3 = 0 then 1762 else if t 3 = 1 then 1753 else 1450) else (if t 3 = 0 then 1145 else if t 3 = 1 then 778 else 780))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2445 else 1583) else if t 2 = 1 then (if t 3 = 0 then 2449 else if t 3 = 1 then 2441 else 1582) else (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 69)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2443 else 2897) else if t 2 = 1 then (if t 3 = 0 then 2447 else if t 3 = 1 then 2439 else 2481) else (if t 3 = 0 then 2462 else if t 3 = 1 then 2459 else 2486)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2502 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2883 else if t 3 = 1 then 2492 else 2496) else (if t 3 = 0 then 2885 else if t 3 = 1 then 2493 else 2497))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 439 else 1136) else if t 2 = 1 then (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 471) else (if t 3 = 0 then 1512 else if t 3 = 1 then 1511 else 1850)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2900) else if t 2 = 1 then (if t 3 = 0 then 2471 else if t 3 = 1 then 2468 else 2488) else (if t 3 = 0 then 2475 else if t 3 = 1 then 2473 else 2490)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2504 else 3928) else if t 2 = 1 then (if t 3 = 0 then 2886 else if t 3 = 1 then 2494 else 2498) else (if t 3 = 0 then 2887 else if t 3 = 1 then 2495 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3690 else (if jt.2.val < 2 then 3700 else 3701)) else (if jt.2.val < 4 then 3697 else (if jt.2.val < 5 then 3699 else 3698))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3654 else (if jt.2.val < 2 then 3656 else 3659)) else (if jt.2.val < 4 then 3655 else (if jt.2.val < 5 then 3658 else 3657)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4098 else (if jt.2.val < 2 then 4121 else 4101)) else (if jt.2.val < 4 then 4119 else (if jt.2.val < 5 then 4120 else 4096))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3009 else (if jt.2.val < 2 then 3026 else 3017)) else (if jt.2.val < 4 then 3018 else (if jt.2.val < 5 then 3019 else 3007)))))

checked_coverage fastCoverage0339 pairing0339 template0339 witness0339

theorem coverage0339 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0339) (maskBits m))
    cores template0339 witness0339 := by
  rw [← coresFast_eq]
  exact fastCoverage0339

theorem coverageSize0339 : ∀ q : Pattern,
    (cores (witness0339 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0339 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0339
#print axioms coverageSize0339

noncomputable def pairing0340 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0340 : List (Fin 4935) := templateData0340

noncomputable def witness0340 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 384 else 932) else if t 2 = 1 then (if t 3 = 0 then 386 else if t 3 = 1 then 382 else 928) else (if t 3 = 0 then 1501 else if t 3 = 1 then 400 else 1790)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 379 else if t 3 = 1 then 356 else 358) else if t 2 = 1 then (if t 3 = 0 then 371 else if t 3 = 1 then 336 else 342) else (if t 3 = 0 then 892 else if t 3 = 1 then 340 else 344)) else (if t 2 = 0 then (if t 3 = 0 then 4036 else if t 3 = 1 then 3929 else 3930) else if t 2 = 1 then (if t 3 = 0 then 2737 else if t 3 = 1 then 2728 else 2731) else (if t 3 = 0 then 2987 else if t 3 = 1 then 2730 else 2732))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 383 else 930) else if t 2 = 1 then (if t 3 = 0 then 385 else if t 3 = 1 then 381 else 924) else (if t 3 = 0 then 1500 else if t 3 = 1 then 399 else 1788)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 375 else if t 3 = 1 then 346 else 352) else if t 2 = 1 then (if t 3 = 0 then 363 else if t 3 = 1 then 318 else 328) else (if t 3 = 0 then 888 else if t 3 = 1 then 324 else 332)) else (if t 2 = 0 then (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 353) else if t 2 = 1 then (if t 3 = 0 then 364 else if t 3 = 1 then 320 else 329) else (if t 3 = 0 then 889 else if t 3 = 1 then 325 else 333))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1497 else 2990) else if t 2 = 1 then (if t 3 = 0 then 395 else if t 3 = 1 then 393 else 926) else (if t 3 = 0 then 3952 else if t 3 = 1 then 405 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1773 else if t 3 = 1 then 1483 else 1487) else if t 2 = 1 then (if t 3 = 0 then 365 else if t 3 = 1 then 322 else 330) else (if t 3 = 0 then 890 else if t 3 = 1 then 326 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 1774 else if t 3 = 1 then 1484 else 1488) else if t 2 = 1 then (if t 3 = 0 then 366 else if t 3 = 1 then 323 else 331) else (if t 3 = 0 then 891 else if t 3 = 1 then 327 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3690 else (if jt.2.val < 2 then 3757 else 3701)) else (if jt.2.val < 4 then 3756 else (if jt.2.val < 5 then 3758 else 3698))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4290 else (if jt.2.val < 2 then 4301 else 4292)) else (if jt.2.val < 4 then 4299 else (if jt.2.val < 5 then 4300 else 4287)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1479 else (if jt.2.val < 2 then 1481 else 1486)) else (if jt.2.val < 4 then 1480 else (if jt.2.val < 5 then 1485 else 1482))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1247 else (if jt.2.val < 2 then 1249 else 1253)) else (if jt.2.val < 4 then 1248 else (if jt.2.val < 5 then 1252 else 1250)))))

checked_coverage fastCoverage0340 pairing0340 template0340 witness0340

theorem coverage0340 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0340) (maskBits m))
    cores template0340 witness0340 := by
  rw [← coresFast_eq]
  exact fastCoverage0340

theorem coverageSize0340 : ∀ q : Pattern,
    (cores (witness0340 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0340 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0340
#print axioms coverageSize0340

noncomputable def pairing0341 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0341 : List (Fin 4935) := templateData0341

noncomputable def witness0341 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 1004 else 308) else if t 2 = 1 then (if t 3 = 0 then 1006 else if t 3 = 1 then 1000 else 304) else (if t 3 = 0 then 1807 else if t 3 = 1 then 100 else 1478)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 995 else if t 3 = 1 then 977 else 979) else if t 2 = 1 then (if t 3 = 0 then 991 else if t 3 = 1 then 957 else 963) else (if t 3 = 0 then 172 else if t 3 = 1 then 961 else 965)) else (if t 2 = 0 then (if t 3 = 0 then 3905 else if t 3 = 1 then 4046 else 4047) else if t 2 = 1 then (if t 3 = 0 then 2979 else if t 3 = 1 then 2970 else 2973) else (if t 3 = 0 then 2776 else if t 3 = 1 then 2972 else 2974))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 1002 else 306) else if t 2 = 1 then (if t 3 = 0 then 1005 else if t 3 = 1 then 996 else 300) else (if t 3 = 0 then 1806 else if t 3 = 1 then 96 else 1476)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 993 else if t 3 = 1 then 967 else 973) else if t 2 = 1 then (if t 3 = 0 then 987 else if t 3 = 1 then 939 else 949) else (if t 3 = 0 then 166 else if t 3 = 1 then 945 else 953)) else (if t 2 = 0 then (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 974) else if t 2 = 1 then (if t 3 = 0 then 988 else if t 3 = 1 then 941 else 950) else (if t 3 = 0 then 167 else if t 3 = 1 then 946 else 954))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1374 else 2782) else if t 2 = 1 then (if t 3 = 0 then 1011 else if t 3 = 1 then 998 else 302) else (if t 3 = 0 then 4059 else if t 3 = 1 then 98 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1430 else if t 3 = 1 then 1795 else 1799) else if t 2 = 1 then (if t 3 = 0 then 989 else if t 3 = 1 then 943 else 951) else (if t 3 = 0 then 168 else if t 3 = 1 then 947 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 1431 else if t 3 = 1 then 1796 else 1800) else if t 2 = 1 then (if t 3 = 0 then 990 else if t 3 = 1 then 944 else 952) else (if t 3 = 0 then 169 else if t 3 = 1 then 948 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3762 else (if jt.2.val < 2 then 3793 else 3773)) else (if jt.2.val < 4 then 3792 else (if jt.2.val < 5 then 3794 else 3770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4296 else (if jt.2.val < 2 then 4304 else 4298)) else (if jt.2.val < 4 then 4302 else (if jt.2.val < 5 then 4303 else 4293)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1791 else (if jt.2.val < 2 then 1793 else 1798)) else (if jt.2.val < 4 then 1792 else (if jt.2.val < 5 then 1797 else 1794))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1250 else (if jt.2.val < 2 then 1257 else 1253)) else (if jt.2.val < 4 then 1256 else (if jt.2.val < 5 then 1259 else 1247)))))

checked_coverage fastCoverage0341 pairing0341 template0341 witness0341

theorem coverage0341 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0341) (maskBits m))
    cores template0341 witness0341 := by
  rw [← coresFast_eq]
  exact fastCoverage0341

theorem coverageSize0341 : ∀ q : Pattern,
    (cores (witness0341 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0341 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0341
#print axioms coverageSize0341

noncomputable def pairing0342 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0342 : List (Fin 4935) := templateData0342

noncomputable def witness0342 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1680 else 1856) else if t 2 = 1 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1678 else 1853) else (if t 3 = 0 then 201 else if t 3 = 1 then 864 else 878)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1660 else 1661) else if t 2 = 1 then (if t 3 = 0 then 1669 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 157 else if t 3 = 1 then 1646 else 1650)) else (if t 2 = 0 then (if t 3 = 0 then 2882 else if t 3 = 1 then 2689 else 2691) else if t 2 = 1 then (if t 3 = 0 then 2545 else if t 3 = 1 then 3232 else 3235) else (if t 3 = 0 then 4058 else if t 3 = 1 then 3963 else 3965))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1679 else 1854) else if t 2 = 1 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1677 else 1851) else (if t 3 = 0 then 200 else if t 3 = 1 then 863 else 876)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1656 else 1658) else if t 2 = 1 then (if t 3 = 0 then 1665 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 150 else if t 3 = 1 then 1630 else 1638)) else (if t 2 = 0 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1657 else 1659) else if t 2 = 1 then (if t 3 = 0 then 1666 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 151 else if t 3 = 1 then 1631 else 1639))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 785 else 4061) else if t 2 = 1 then (if t 3 = 0 then 596 else if t 3 = 1 then 1079 else 1092) else (if t 3 = 0 then 2763 else if t 3 = 1 then 1689 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1110 else if t 3 = 1 then 734 else 738) else if t 2 = 1 then (if t 3 = 0 then 546 else if t 3 = 1 then 1632 else 1640) else (if t 3 = 0 then 1833 else if t 3 = 1 then 1634 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 1111 else if t 3 = 1 then 735 else 739) else if t 2 = 1 then (if t 3 = 0 then 547 else if t 3 = 1 then 1633 else 1641) else (if t 3 = 0 then 1834 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3806 else (if jt.2.val < 2 then 3962 else 3828)) else (if jt.2.val < 4 then 3961 else (if jt.2.val < 5 then 3964 else 3824))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3651 else (if jt.2.val < 2 then 3668 else 3653)) else (if jt.2.val < 4 then 3666 else (if jt.2.val < 5 then 3667 else 3648)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1482 else (if jt.2.val < 2 then 1654 else 1486)) else (if jt.2.val < 4 then 1653 else (if jt.2.val < 5 then 1655 else 1479))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1956 else (if jt.2.val < 2 then 1958 else 1963)) else (if jt.2.val < 4 then 1957 else (if jt.2.val < 5 then 1962 else 1961)))))

checked_coverage fastCoverage0342 pairing0342 template0342 witness0342

theorem coverage0342 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0342) (maskBits m))
    cores template0342 witness0342 := by
  rw [← coresFast_eq]
  exact fastCoverage0342

theorem coverageSize0342 : ∀ q : Pattern,
    (cores (witness0342 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0342 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0342
#print axioms coverageSize0342

noncomputable def pairing0343 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0343 : List (Fin 4935) := templateData0343

noncomputable def witness0343 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1910 else 1622) else if t 2 = 1 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1907 else 1619) else (if t 3 = 0 then 900 else if t 3 = 1 then 94 else 95)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1891 else 1892) else if t 2 = 1 then (if t 3 = 0 then 1901 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 158 else if t 3 = 1 then 1877 else 1881)) else (if t 2 = 0 then (if t 3 = 0 then 2561 else if t 3 = 1 then 2938 else 2940) else if t 2 = 1 then (if t 3 = 0 then 2546 else if t 3 = 1 then 3348 else 3351) else (if t 3 = 0 then 3946 else if t 3 = 1 then 4064 else 4066))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1908 else 1620) else if t 2 = 1 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1905 else 1617) else (if t 3 = 0 then 899 else if t 3 = 1 then 90 else 92)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1887 else 1889) else if t 2 = 1 then (if t 3 = 0 then 1899 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 152 else if t 3 = 1 then 1861 else 1869)) else (if t 2 = 0 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1888 else 1890) else if t 2 = 1 then (if t 3 = 0 then 1900 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 153 else if t 3 = 1 then 1862 else 1870))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 504 else 3960) else if t 2 = 1 then (if t 3 = 0 then 1115 else if t 3 = 1 then 492 else 494) else (if t 3 = 0 then 2986 else if t 3 = 1 then 1521 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 572 else if t 3 = 1 then 1181 else 1185) else if t 2 = 1 then (if t 3 = 0 then 548 else if t 3 = 1 then 1863 else 1871) else (if t 3 = 0 then 1535 else if t 3 = 1 then 1865 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 573 else if t 3 = 1 then 1182 else 1186) else if t 2 = 1 then (if t 3 = 0 then 549 else if t 3 = 1 then 1864 else 1872) else (if t 3 = 0 then 1536 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3972 else (if jt.2.val < 2 then 4063 else 3994)) else (if jt.2.val < 4 then 4062 else (if jt.2.val < 5 then 4065 else 3990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3657 else (if jt.2.val < 2 then 3671 else 3659)) else (if jt.2.val < 4 then 3669 else (if jt.2.val < 5 then 3670 else 3654)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1794 else (if jt.2.val < 2 then 1885 else 1798)) else (if jt.2.val < 4 then 1884 else (if jt.2.val < 5 then 1886 else 1791))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1961 else (if jt.2.val < 2 then 1966 else 1963)) else (if jt.2.val < 4 then 1965 else (if jt.2.val < 5 then 1969 else 1956)))))

checked_coverage fastCoverage0343 pairing0343 template0343 witness0343

theorem coverage0343 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0343) (maskBits m))
    cores template0343 witness0343 := by
  rw [← coresFast_eq]
  exact fastCoverage0343

theorem coverageSize0343 : ∀ q : Pattern,
    (cores (witness0343 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0343 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0343
#print axioms coverageSize0343

noncomputable def pairing0344 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0344 : List (Fin 4935) := templateData0344

noncomputable def witness0344 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 3941) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2788) else (if t 3 = 0 then 2997 else if t 3 = 1 then 2996 else 2795)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 726) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 725) else (if t 3 = 0 then 1174 else if t 3 = 1 then 1172 else 757)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 681 else 1145) else if t 2 = 1 then (if t 3 = 0 then 682 else if t 3 = 1 then 680 else 1144) else (if t 3 = 0 then 1526 else if t 3 = 1 then 694 else 2161))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 35) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 34) else (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 70)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2462) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4170) else (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4177)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2885) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4183) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4181 else 4185))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1512) else if t 2 = 1 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 53) else (if t 3 = 0 then 841 else if t 3 = 1 then 840 else 77)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2475) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4171) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4164 else 4178)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2574 else 2887) else if t 2 = 1 then (if t 3 = 0 then 3916 else if t 3 = 1 then 4180 else 4184) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4182 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4134 else (if jt.2.val < 2 then 4154 else 4156)) else (if jt.2.val < 4 then 4151 else (if jt.2.val < 5 then 4153 else 4152))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4305 else (if jt.2.val < 2 then 4307 else 4310)) else (if jt.2.val < 4 then 4306 else (if jt.2.val < 5 then 4309 else 4308)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4261 else (if jt.2.val < 2 then 4265 else 4266)) else (if jt.2.val < 4 then 4262 else (if jt.2.val < 5 then 4264 else 4263))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4216 else (if jt.2.val < 2 then 4220 else 4221)) else (if jt.2.val < 4 then 4217 else (if jt.2.val < 5 then 4219 else 4218)))))

checked_coverage fastCoverage0344 pairing0344 template0344 witness0344

theorem coverage0344 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0344) (maskBits m))
    cores template0344 witness0344 := by
  rw [← coresFast_eq]
  exact fastCoverage0344

theorem coverageSize0344 : ∀ q : Pattern,
    (cores (witness0344 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0344 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0344
#print axioms coverageSize0344

noncomputable def pairing0345 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0345 : List (Fin 4935) := templateData0345

noncomputable def witness0345 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4196) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2787) else (if t 3 = 0 then 2751 else if t 3 = 1 then 2749 else 2983)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 724) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 723) else (if t 3 = 0 then 539 else if t 3 = 1 then 535 else 1108)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1084 else 790) else if t 2 = 1 then (if t 3 = 0 then 1090 else if t 3 = 1 then 1078 else 784) else (if t 3 = 0 then 2150 else if t 3 = 1 then 595 else 1549))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 33) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 32) else (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 919)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2461) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3834) else (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3848)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2503) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3854) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3856 else 3858))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 2126) else if t 2 = 1 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 52) else (if t 3 = 0 then 262 else if t 3 = 1 then 260 else 923)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2474) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3837) else (if t 3 = 0 then 3847 else if t 3 = 1 then 3846 else 3850)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2957 else 2505) else if t 2 = 1 then (if t 3 = 0 then 4038 else if t 3 = 1 then 3853 else 3855) else (if t 3 = 0 then 4192 else if t 3 = 1 then 3857 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3806 else (if jt.2.val < 2 then 3826 else 3828)) else (if jt.2.val < 4 then 3823 else (if jt.2.val < 5 then 3825 else 3824))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4293 else (if jt.2.val < 2 then 4295 else 4298)) else (if jt.2.val < 4 then 4294 else (if jt.2.val < 5 then 4297 else 4296)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3804 else (if jt.2.val < 2 then 3842 else 3844)) else (if jt.2.val < 4 then 3839 else (if jt.2.val < 5 then 3841 else 3840))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4218 else (if jt.2.val < 2 then 4229 else 4221)) else (if jt.2.val < 4 then 4227 else (if jt.2.val < 5 then 4228 else 4216)))))

checked_coverage fastCoverage0345 pairing0345 template0345 witness0345

theorem coverage0345 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0345) (maskBits m))
    cores template0345 witness0345 := by
  rw [← coresFast_eq]
  exact fastCoverage0345

theorem coverageSize0345 : ∀ q : Pattern,
    (cores (witness0345 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0345 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0345
#print axioms coverageSize0345

noncomputable def pairing0346 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0346 : List (Fin 4935) := templateData0346

noncomputable def witness0346 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2817 else 2485) else if t 2 = 1 then (if t 3 = 0 then 2813 else if t 3 = 1 then 2809 else 2855) else (if t 3 = 0 then 4203 else if t 3 = 1 then 4054 else 3954)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2815 else 1416) else if t 2 = 1 then (if t 3 = 0 then 2811 else if t 3 = 1 then 2807 else 1414) else (if t 3 = 0 then 1171 else if t 3 = 1 then 1169 else 1202)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1372 else 2119) else if t 2 = 1 then (if t 3 = 0 then 1371 else if t 3 = 1 then 1370 else 1777) else (if t 3 = 0 then 503 else if t 3 = 1 then 1211 else 1222))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2816 else 1586) else if t 2 = 1 then (if t 3 = 0 then 2812 else if t 3 = 1 then 2808 else 1584) else (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 857)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2814 else 2484) else if t 2 = 1 then (if t 3 = 0 then 2810 else if t 3 = 1 then 2806 else 2854) else (if t 3 = 0 then 2828 else if t 3 = 1 then 2826 else 2856)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2576 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2721 else if t 3 = 1 then 2859 else 2864) else (if t 3 = 0 then 2723 else if t 3 = 1 then 2861 else 2865))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1042 else 473) else if t 2 = 1 then (if t 3 = 0 then 1040 else if t 3 = 1 then 1038 else 1073) else (if t 3 = 0 then 2147 else if t 3 = 1 then 1817 else 1601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2838 else 2489) else if t 2 = 1 then (if t 3 = 0 then 2837 else if t 3 = 1 then 2835 else 2857) else (if t 3 = 0 then 2841 else if t 3 = 1 then 2840 else 2858)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2579 else 4197) else if t 2 = 1 then (if t 3 = 0 then 2724 else if t 3 = 1 then 2862 else 2866) else (if t 3 = 0 then 2725 else if t 3 = 1 then 2863 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3762 else (if jt.2.val < 2 then 3772 else 3773)) else (if jt.2.val < 4 then 3769 else (if jt.2.val < 5 then 3771 else 3770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3648 else (if jt.2.val < 2 then 3650 else 3653)) else (if jt.2.val < 4 then 3649 else (if jt.2.val < 5 then 3652 else 3651)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4263 else (if jt.2.val < 2 then 4274 else 4266)) else (if jt.2.val < 4 then 4272 else (if jt.2.val < 5 then 4273 else 4261))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2803 else (if jt.2.val < 2 then 2852 else 2853)) else (if jt.2.val < 4 then 2849 else (if jt.2.val < 5 then 2851 else 2850)))))

checked_coverage fastCoverage0346 pairing0346 template0346 witness0346

theorem coverage0346 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0346) (maskBits m))
    cores template0346 witness0346 := by
  rw [← coresFast_eq]
  exact fastCoverage0346

theorem coverageSize0346 : ∀ q : Pattern,
    (cores (witness0346 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0346 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0346
#print axioms coverageSize0346

noncomputable def pairing0347 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0347 : List (Fin 4935) := templateData0347

noncomputable def witness0347 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2598 else 2898) else if t 2 = 1 then (if t 3 = 0 then 2602 else if t 3 = 1 then 2594 else 2630) else (if t 3 = 0 then 3925 else if t 3 = 1 then 3923 else 4207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2596 else 1413) else if t 2 = 1 then (if t 3 = 0 then 2600 else if t 3 = 1 then 2592 else 1411) else (if t 3 = 0 then 538 else if t 3 = 1 then 534 else 567)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2104 else 1453) else if t 2 = 1 then (if t 3 = 0 then 2107 else if t 3 = 1 then 2101 else 1447) else (if t 3 = 0 then 1120 else if t 3 = 1 then 589 else 591))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2597 else 1583) else if t 2 = 1 then (if t 3 = 0 then 2601 else if t 3 = 1 then 2593 else 1581) else (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 273)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2595 else 2897) else if t 2 = 1 then (if t 3 = 0 then 2599 else if t 3 = 1 then 2591 else 2629) else (if t 3 = 0 then 2614 else if t 3 = 1 then 2611 else 2634)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2650 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2902 else if t 3 = 1 then 2640 else 2644) else (if t 3 = 0 then 2903 else if t 3 = 1 then 2641 else 2645))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 635 else 1136) else if t 2 = 1 then (if t 3 = 0 then 637 else if t 3 = 1 then 633 else 663) else (if t 3 = 0 then 1464 else if t 3 = 1 then 1463 else 2171)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2622 else 2900) else if t 2 = 1 then (if t 3 = 0 then 2623 else if t 3 = 1 then 2620 else 2636) else (if t 3 = 0 then 2627 else if t 3 = 1 then 2625 else 2638)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2652 else 3928) else if t 2 = 1 then (if t 3 = 0 then 2904 else if t 3 = 1 then 2642 else 2646) else (if t 3 = 0 then 2905 else if t 3 = 1 then 2643 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3714 else (if jt.2.val < 2 then 3724 else 3725)) else (if jt.2.val < 4 then 3721 else (if jt.2.val < 5 then 3723 else 3722))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3678 else (if jt.2.val < 2 then 3680 else 3683)) else (if jt.2.val < 4 then 3679 else (if jt.2.val < 5 then 3682 else 3681)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3840 else (if jt.2.val < 2 then 3924 else 3844)) else (if jt.2.val < 4 then 3921 else (if jt.2.val < 5 then 3922 else 3804))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2850 else (if jt.2.val < 2 then 2896 else 2853)) else (if jt.2.val < 4 then 2888 else (if jt.2.val < 5 then 2889 else 2803)))))

checked_coverage fastCoverage0347 pairing0347 template0347 witness0347

theorem coverage0347 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0347) (maskBits m))
    cores template0347 witness0347 := by
  rw [← coresFast_eq]
  exact fastCoverage0347

theorem coverageSize0347 : ∀ q : Pattern,
    (cores (witness0347 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0347 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0347
#print axioms coverageSize0347

noncomputable def pairing0348 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0348 : List (Fin 4935) := templateData0348

noncomputable def witness0348 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 183 else 900) else if t 2 = 1 then (if t 3 = 0 then 185 else if t 3 = 1 then 181 else 898) else (if t 3 = 0 then 1501 else if t 3 = 1 then 199 else 2129)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 178 else if t 3 = 1 then 156 else 158) else if t 2 = 1 then (if t 3 = 0 then 170 else if t 3 = 1 then 136 else 142) else (if t 3 = 0 then 892 else if t 3 = 1 then 140 else 144)) else (if t 2 = 0 then (if t 3 = 0 then 4190 else if t 3 = 1 then 3945 else 3946) else if t 2 = 1 then (if t 3 = 0 then 2775 else if t 3 = 1 then 2766 else 2769) else (if t 3 = 0 then 2987 else if t 3 = 1 then 2768 else 2770))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 182 else 899) else if t 2 = 1 then (if t 3 = 0 then 184 else if t 3 = 1 then 180 else 897) else (if t 3 = 0 then 1500 else if t 3 = 1 then 198 else 2127)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 174 else if t 3 = 1 then 146 else 152) else if t 2 = 1 then (if t 3 = 0 then 160 else if t 3 = 1 then 117 else 128) else (if t 3 = 0 then 888 else if t 3 = 1 then 124 else 132)) else (if t 2 = 0 then (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 153) else if t 2 = 1 then (if t 3 = 0 then 161 else if t 3 = 1 then 119 else 129) else (if t 3 = 0 then 889 else if t 3 = 1 then 125 else 133))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 1545 else 2986) else if t 2 = 1 then (if t 3 = 0 then 194 else if t 3 = 1 then 192 else 903) else (if t 3 = 0 then 3952 else if t 3 = 1 then 204 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2115 else if t 3 = 1 then 1531 else 1535) else if t 2 = 1 then (if t 3 = 0 then 162 else if t 3 = 1 then 121 else 130) else (if t 3 = 0 then 890 else if t 3 = 1 then 126 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 2116 else if t 3 = 1 then 1532 else 1536) else if t 2 = 1 then (if t 3 = 0 then 163 else if t 3 = 1 then 122 else 131) else (if t 3 = 0 then 891 else if t 3 = 1 then 127 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3714 else (if jt.2.val < 2 then 3745 else 3725)) else (if jt.2.val < 4 then 3744 else (if jt.2.val < 5 then 3746 else 3722))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4308 else (if jt.2.val < 2 then 4313 else 4310)) else (if jt.2.val < 4 then 4311 else (if jt.2.val < 5 then 4312 else 4305)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2004 else (if jt.2.val < 2 then 2006 else 2009)) else (if jt.2.val < 4 then 2005 else (if jt.2.val < 5 then 2008 else 2007))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 881 else (if jt.2.val < 2 then 883 else 887)) else (if jt.2.val < 4 then 882 else (if jt.2.val < 5 then 886 else 885)))))

checked_coverage fastCoverage0348 pairing0348 template0348 witness0348

theorem coverage0348 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0348) (maskBits m))
    cores template0348 witness0348 := by
  rw [← coresFast_eq]
  exact fastCoverage0348

theorem coverageSize0348 : ∀ q : Pattern,
    (cores (witness0348 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0348 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0348
#print axioms coverageSize0348

noncomputable def pairing0349 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0349 : List (Fin 4935) := templateData0349

noncomputable def witness0349 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 1004 else 104) else if t 2 = 1 then (if t 3 = 0 then 1006 else if t 3 = 1 then 1000 else 100) else (if t 3 = 0 then 2140 else if t 3 = 1 then 304 else 1478)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 995 else if t 3 = 1 then 977 else 978) else if t 2 = 1 then (if t 3 = 0 then 991 else if t 3 = 1 then 957 else 961) else (if t 3 = 0 then 373 else if t 3 = 1 then 963 else 965)) else (if t 2 = 0 then (if t 3 = 0 then 3905 else if t 3 = 1 then 4046 else 4198) else if t 2 = 1 then (if t 3 = 0 then 2979 else if t 3 = 1 then 2970 else 2972) else (if t 3 = 0 then 2738 else if t 3 = 1 then 2973 else 2974))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 1002 else 102) else if t 2 = 1 then (if t 3 = 0 then 1005 else if t 3 = 1 then 996 else 96) else (if t 3 = 0 then 2139 else if t 3 = 1 then 300 else 1476)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 993 else if t 3 = 1 then 967 else 971) else if t 2 = 1 then (if t 3 = 0 then 987 else if t 3 = 1 then 939 else 945) else (if t 3 = 0 then 367 else if t 3 = 1 then 949 else 953)) else (if t 2 = 0 then (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 972) else if t 2 = 1 then (if t 3 = 0 then 988 else if t 3 = 1 then 941 else 946) else (if t 3 = 0 then 368 else if t 3 = 1 then 950 else 954))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1374 else 2744) else if t 2 = 1 then (if t 3 = 0 then 1011 else if t 3 = 1 then 998 else 98) else (if t 3 = 0 then 4206 else if t 3 = 1 then 302 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1430 else if t 3 = 1 then 1795 else 2136) else if t 2 = 1 then (if t 3 = 0 then 989 else if t 3 = 1 then 943 else 947) else (if t 3 = 0 then 369 else if t 3 = 1 then 951 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 1431 else if t 3 = 1 then 1796 else 2137) else if t 2 = 1 then (if t 3 = 0 then 990 else if t 3 = 1 then 944 else 948) else (if t 3 = 0 then 370 else if t 3 = 1 then 952 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3762 else (if jt.2.val < 2 then 3793 else 3773)) else (if jt.2.val < 4 then 3792 else (if jt.2.val < 5 then 3794 else 3770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4296 else (if jt.2.val < 2 then 4304 else 4298)) else (if jt.2.val < 4 then 4302 else (if jt.2.val < 5 then 4303 else 4293)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2130 else (if jt.2.val < 2 then 2132 else 2135)) else (if jt.2.val < 4 then 2131 else (if jt.2.val < 5 then 2134 else 2133))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 885 else (if jt.2.val < 2 then 985 else 887)) else (if jt.2.val < 4 then 984 else (if jt.2.val < 5 then 986 else 881)))))

checked_coverage fastCoverage0349 pairing0349 template0349 witness0349

theorem coverage0349 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0349) (maskBits m))
    cores template0349 witness0349 := by
  rw [← coresFast_eq]
  exact fastCoverage0349

theorem coverageSize0349 : ∀ q : Pattern,
    (cores (witness0349 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0349 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0349
#print axioms coverageSize0349

noncomputable def pairing0350 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0350 : List (Fin 4935) := templateData0350

noncomputable def witness0350 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1682 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1678 else 1853) else (if t 3 = 0 then 402 else if t 3 = 1 then 864 else 878)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1669 else 1670) else if t 2 = 1 then (if t 3 = 0 then 1660 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 357 else if t 3 = 1 then 1646 else 1650)) else (if t 2 = 0 then (if t 3 = 0 then 2882 else if t 3 = 1 then 2545 else 2547) else if t 2 = 1 then (if t 3 = 0 then 2689 else if t 3 = 1 then 3232 else 3235) else (if t 3 = 0 then 4205 else if t 3 = 1 then 3963 else 3965))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1681 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1677 else 1851) else (if t 3 = 0 then 401 else if t 3 = 1 then 863 else 876)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1665 else 1667) else if t 2 = 1 then (if t 3 = 0 then 1656 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 350 else if t 3 = 1 then 1630 else 1638)) else (if t 2 = 0 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1666 else 1668) else if t 2 = 1 then (if t 3 = 0 then 1657 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 351 else if t 3 = 1 then 1631 else 1639))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 596 else 4208) else if t 2 = 1 then (if t 3 = 0 then 785 else if t 3 = 1 then 1079 else 1092) else (if t 3 = 0 then 2801 else if t 3 = 1 then 1689 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1110 else if t 3 = 1 then 546 else 550) else if t 2 = 1 then (if t 3 = 0 then 734 else if t 3 = 1 then 1632 else 1640) else (if t 3 = 0 then 2157 else if t 3 = 1 then 1634 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 1111 else if t 3 = 1 then 547 else 551) else if t 2 = 1 then (if t 3 = 0 then 735 else if t 3 = 1 then 1633 else 1641) else (if t 3 = 0 then 2158 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3806 else (if jt.2.val < 2 then 3962 else 3828)) else (if jt.2.val < 4 then 3961 else (if jt.2.val < 5 then 3964 else 3824))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3651 else (if jt.2.val < 2 then 3668 else 3653)) else (if jt.2.val < 4 then 3666 else (if jt.2.val < 5 then 3667 else 3648)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2007 else (if jt.2.val < 2 then 2041 else 2009)) else (if jt.2.val < 4 then 2040 else (if jt.2.val < 5 then 2042 else 2004))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2256 else (if jt.2.val < 2 then 2258 else 2261)) else (if jt.2.val < 4 then 2257 else (if jt.2.val < 5 then 2260 else 2259)))))

checked_coverage fastCoverage0350 pairing0350 template0350 witness0350

theorem coverage0350 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0350) (maskBits m))
    cores template0350 witness0350 := by
  rw [← coresFast_eq]
  exact fastCoverage0350

theorem coverageSize0350 : ∀ q : Pattern,
    (cores (witness0350 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0350 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0350
#print axioms coverageSize0350

noncomputable def pairing0351 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0351 : List (Fin 4935) := templateData0351

noncomputable def witness0351 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2225 else 1622) else if t 2 = 1 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2222 else 1616) else (if t 3 = 0 then 932 else if t 3 = 1 then 298 else 299)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2207 else 1892) else if t 2 = 1 then (if t 3 = 0 then 2213 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 358 else if t 3 = 1 then 2195 else 2199)) else (if t 2 = 0 then (if t 3 = 0 then 2706 else if t 3 = 1 then 2939 else 2940) else if t 2 = 1 then (if t 3 = 0 then 2690 else if t 3 = 1 then 3528 else 3531) else (if t 3 = 0 then 3930 else if t 3 = 1 then 4211 else 4213))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2223 else 1620) else if t 2 = 1 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2220 else 1614) else (if t 3 = 0 then 930 else if t 3 = 1 then 294 else 296)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2205 else 1889) else if t 2 = 1 then (if t 3 = 0 then 2211 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 352 else if t 3 = 1 then 2179 else 2187)) else (if t 2 = 0 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2206 else 1890) else if t 2 = 1 then (if t 3 = 0 then 2212 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 353 else if t 3 = 1 then 2180 else 2188))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 696 else 3960) else if t 2 = 1 then (if t 3 = 0 then 1146 else if t 3 = 1 then 684 else 686) else (if t 3 = 0 then 2990 else if t 3 = 1 then 1473 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 761 else if t 3 = 1 then 1183 else 1185) else if t 2 = 1 then (if t 3 = 0 then 736 else if t 3 = 1 then 2181 else 2189) else (if t 3 = 0 then 1487 else if t 3 = 1 then 2183 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 762 else if t 3 = 1 then 1184 else 1186) else if t 2 = 1 then (if t 3 = 0 then 737 else if t 3 = 1 then 2182 else 2190) else (if t 3 = 0 then 1488 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4134 else (if jt.2.val < 2 then 4210 else 4156)) else (if jt.2.val < 4 then 4209 else (if jt.2.val < 5 then 4212 else 4152))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3681 else (if jt.2.val < 2 then 3689 else 3683)) else (if jt.2.val < 4 then 3687 else (if jt.2.val < 5 then 3688 else 3678)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2133 else (if jt.2.val < 2 then 2203 else 2135)) else (if jt.2.val < 4 then 2202 else (if jt.2.val < 5 then 2204 else 2130))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2259 else (if jt.2.val < 2 then 2263 else 2261)) else (if jt.2.val < 4 then 2262 else (if jt.2.val < 5 then 2264 else 2256)))))

checked_coverage fastCoverage0351 pairing0351 template0351 witness0351

theorem coverage0351 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0351) (maskBits m))
    cores template0351 witness0351 := by
  rw [← coresFast_eq]
  exact fastCoverage0351

theorem coverageSize0351 : ∀ q : Pattern,
    (cores (witness0351 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0351 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0351
#print axioms coverageSize0351

noncomputable def pairing0352 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0352 : List (Fin 4935) := templateData0352

noncomputable def witness0352 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 4056) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2996) else (if t 3 = 0 then 2789 else if t 3 = 1 then 2788 else 2795)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 1173) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 1172) else (if t 3 = 0 then 727 else if t 3 = 1 then 725 else 757)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 681 else 695) else if t 2 = 1 then (if t 3 = 0 then 682 else if t 3 = 1 then 680 else 694) else (if t 3 = 0 then 1826 else if t 3 = 1 then 1144 else 2161))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 822) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 821) else (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 70)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2829) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4163) else (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4177)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2578) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4181) else (if t 3 = 0 then 4039 else if t 3 = 1 then 4183 else 4185))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1818) else if t 2 = 1 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 840) else (if t 3 = 0 then 54 else if t 3 = 1 then 53 else 77)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2842) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4164) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4171 else 4178)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2574 else 2580) else if t 2 = 1 then (if t 3 = 0 then 3916 else if t 3 = 1 then 4180 else 4182) else (if t 3 = 0 then 4040 else if t 3 = 1 then 4184 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4134 else (if jt.2.val < 2 then 4154 else 4156)) else (if jt.2.val < 4 then 4151 else (if jt.2.val < 5 then 4153 else 4152))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4305 else (if jt.2.val < 2 then 4307 else 4310)) else (if jt.2.val < 4 then 4306 else (if jt.2.val < 5 then 4309 else 4308)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4132 else (if jt.2.val < 2 then 4168 else 4169)) else (if jt.2.val < 4 then 4165 else (if jt.2.val < 5 then 4167 else 4166))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4278 else (if jt.2.val < 2 then 4282 else 4283)) else (if jt.2.val < 4 then 4279 else (if jt.2.val < 5 then 4281 else 4280)))))

checked_coverage fastCoverage0352 pairing0352 template0352 witness0352

theorem coverage0352 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0352) (maskBits m))
    cores template0352 witness0352 := by
  rw [← coresFast_eq]
  exact fastCoverage0352

theorem coverageSize0352 : ∀ q : Pattern,
    (cores (witness0352 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0352 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0352
#print axioms coverageSize0352

noncomputable def pairing0353 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0353 : List (Fin 4935) := templateData0353

noncomputable def witness0353 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 4203) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2995) else (if t 3 = 0 then 2751 else if t 3 = 1 then 2750 else 2757)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 1171) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 1170) else (if t 3 = 0 then 539 else if t 3 = 1 then 537 else 568)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 489 else 503) else if t 2 = 1 then (if t 3 = 0 then 490 else if t 3 = 1 then 488 else 502) else (if t 3 = 0 then 2150 else if t 3 = 1 then 1114 else 1837))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 820) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 819) else (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 274)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2828) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4000) else (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4017)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2723) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4021) else (if t 3 = 0 then 4191 else if t 3 = 1 then 4023 else 4025))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 2147) else if t 2 = 1 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 839) else (if t 3 = 0 then 262 else if t 3 = 1 then 261 else 281)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2841) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4003) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4016 else 4018)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2719 else 2725) else if t 2 = 1 then (if t 3 = 0 then 3918 else if t 3 = 1 then 4020 else 4022) else (if t 3 = 0 then 4192 else if t 3 = 1 then 4024 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3972 else (if jt.2.val < 2 then 3992 else 3994)) else (if jt.2.val < 4 then 3989 else (if jt.2.val < 5 then 3991 else 3990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4287 else (if jt.2.val < 2 then 4289 else 4292)) else (if jt.2.val < 4 then 4288 else (if jt.2.val < 5 then 4291 else 4290)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3970 else (if jt.2.val < 2 then 4013 else 4014)) else (if jt.2.val < 4 then 4010 else (if jt.2.val < 5 then 4012 else 4011))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4280 else (if jt.2.val < 2 then 4286 else 4283)) else (if jt.2.val < 4 then 4284 else (if jt.2.val < 5 then 4285 else 4278)))))

checked_coverage fastCoverage0353 pairing0353 template0353 witness0353

theorem coverage0353 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0353) (maskBits m))
    cores template0353 witness0353 := by
  rw [← coresFast_eq]
  exact fastCoverage0353

theorem coverageSize0353 : ∀ q : Pattern,
    (cores (witness0353 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0353 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0353
#print axioms coverageSize0353

noncomputable def pairing0354 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0354 : List (Fin 4935) := templateData0354

noncomputable def witness0354 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2450 else 2485) else if t 2 = 1 then (if t 3 = 0 then 2446 else if t 3 = 1 then 2442 else 2482) else (if t 3 = 0 then 4196 else if t 3 = 1 then 3939 else 4060)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2448 else 1416) else if t 2 = 1 then (if t 3 = 0 then 2444 else if t 3 = 1 then 2440 else 1412) else (if t 3 = 0 then 724 else if t 3 = 1 then 722 else 756)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1762 else 2119) else if t 2 = 1 then (if t 3 = 0 then 1756 else if t 3 = 1 then 1753 else 1450) else (if t 3 = 0 then 790 else if t 3 = 1 then 778 else 780))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2449 else 1586) else if t 2 = 1 then (if t 3 = 0 then 2445 else if t 3 = 1 then 2441 else 1582) else (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 69)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2447 else 2484) else if t 2 = 1 then (if t 3 = 0 then 2443 else if t 3 = 1 then 2439 else 2481) else (if t 3 = 0 then 2461 else if t 3 = 1 then 2459 else 2486)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2883 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2502 else if t 3 = 1 then 2492 else 2496) else (if t 3 = 0 then 2503 else if t 3 = 1 then 2493 else 2497))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 441 else 473) else if t 2 = 1 then (if t 3 = 0 then 439 else if t 3 = 1 then 437 else 471) else (if t 3 = 0 then 2126 else if t 3 = 1 then 1511 else 1850)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2471 else 2489) else if t 2 = 1 then (if t 3 = 0 then 2470 else if t 3 = 1 then 2468 else 2488) else (if t 3 = 0 then 2474 else if t 3 = 1 then 2473 else 2490)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2886 else 4197) else if t 2 = 1 then (if t 3 = 0 then 2504 else if t 3 = 1 then 2494 else 2498) else (if t 3 = 0 then 2505 else if t 3 = 1 then 2495 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3690 else (if jt.2.val < 2 then 3700 else 3701)) else (if jt.2.val < 4 then 3697 else (if jt.2.val < 5 then 3699 else 3698))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3654 else (if jt.2.val < 2 then 3656 else 3659)) else (if jt.2.val < 4 then 3655 else (if jt.2.val < 5 then 3658 else 3657)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4166 else (if jt.2.val < 2 then 4195 else 4169)) else (if jt.2.val < 4 then 4193 else (if jt.2.val < 5 then 4194 else 4132))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2436 else (if jt.2.val < 2 then 2480 else 2483)) else (if jt.2.val < 4 then 2477 else (if jt.2.val < 5 then 2479 else 2478)))))

checked_coverage fastCoverage0354 pairing0354 template0354 witness0354

theorem coverage0354 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0354) (maskBits m))
    cores template0354 witness0354 := by
  rw [← coresFast_eq]
  exact fastCoverage0354

theorem coverageSize0354 : ∀ q : Pattern,
    (cores (witness0354 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0354 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0354
#print axioms coverageSize0354

noncomputable def pairing0355 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 7 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0355 : List (Fin 4935) := templateData0355

noncomputable def witness0355 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2602 else 2633) else if t 2 = 1 then (if t 3 = 0 then 2598 else if t 3 = 1 then 2594 else 2630) else (if t 3 = 0 then 4044 else if t 3 = 1 then 3923 else 4207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2600 else 1415) else if t 2 = 1 then (if t 3 = 0 then 2596 else if t 3 = 1 then 2592 else 1411) else (if t 3 = 0 then 536 else if t 3 = 1 then 534 else 567)) else (if t 2 = 0 then (if t 3 = 0 then 2111 else if t 3 = 1 then 2107 else 1780) else if t 2 = 1 then (if t 3 = 0 then 2104 else if t 3 = 1 then 2101 else 1447) else (if t 3 = 0 then 601 else if t 3 = 1 then 589 else 591))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2601 else 1585) else if t 2 = 1 then (if t 3 = 0 then 2597 else if t 3 = 1 then 2593 else 1581) else (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 273)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2599 else 2632) else if t 2 = 1 then (if t 3 = 0 then 2595 else if t 3 = 1 then 2591 else 2629) else (if t 3 = 0 then 2613 else if t 3 = 1 then 2611 else 2634)) else (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2902 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2650 else if t 3 = 1 then 2640 else 2644) else (if t 3 = 0 then 2651 else if t 3 = 1 then 2641 else 2645))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 637 else 665) else if t 2 = 1 then (if t 3 = 0 then 635 else if t 3 = 1 then 633 else 663) else (if t 3 = 0 then 1787 else if t 3 = 1 then 1463 else 2171)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2623 else 2637) else if t 2 = 1 then (if t 3 = 0 then 2622 else if t 3 = 1 then 2620 else 2636) else (if t 3 = 0 then 2626 else if t 3 = 1 then 2625 else 2638)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2904 else 4045) else if t 2 = 1 then (if t 3 = 0 then 2652 else if t 3 = 1 then 2642 else 2646) else (if t 3 = 0 then 2653 else if t 3 = 1 then 2643 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3714 else (if jt.2.val < 2 then 3724 else 3725)) else (if jt.2.val < 4 then 3721 else (if jt.2.val < 5 then 3723 else 3722))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3678 else (if jt.2.val < 2 then 3680 else 3683)) else (if jt.2.val < 4 then 3679 else (if jt.2.val < 5 then 3682 else 3681)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4011 else (if jt.2.val < 2 then 4043 else 4014)) else (if jt.2.val < 4 then 4041 else (if jt.2.val < 5 then 4042 else 3970))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2478 else (if jt.2.val < 2 then 2631 else 2483)) else (if jt.2.val < 4 then 2587 else (if jt.2.val < 5 then 2588 else 2436)))))

checked_coverage fastCoverage0355 pairing0355 template0355 witness0355

theorem coverage0355 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0355) (maskBits m))
    cores template0355 witness0355 := by
  rw [← coresFast_eq]
  exact fastCoverage0355

theorem coverageSize0355 : ∀ q : Pattern,
    (cores (witness0355 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0355 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0355
#print axioms coverageSize0355

noncomputable def pairing0356 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0356 : List (Fin 4935) := templateData0356

noncomputable def witness0356 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 183 else 201) else if t 2 = 1 then (if t 3 = 0 then 185 else if t 3 = 1 then 181 else 199) else (if t 3 = 0 then 1807 else if t 3 = 1 then 898 else 2129)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 178 else if t 3 = 1 then 156 else 157) else if t 2 = 1 then (if t 3 = 0 then 170 else if t 3 = 1 then 136 else 140) else (if t 3 = 0 then 172 else if t 3 = 1 then 142 else 144)) else (if t 2 = 0 then (if t 3 = 0 then 4190 else if t 3 = 1 then 3945 else 4058) else if t 2 = 1 then (if t 3 = 0 then 2775 else if t 3 = 1 then 2766 else 2768) else (if t 3 = 0 then 2776 else if t 3 = 1 then 2769 else 2770))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 182 else 200) else if t 2 = 1 then (if t 3 = 0 then 184 else if t 3 = 1 then 180 else 198) else (if t 3 = 0 then 1806 else if t 3 = 1 then 897 else 2127)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 174 else if t 3 = 1 then 146 else 150) else if t 2 = 1 then (if t 3 = 0 then 160 else if t 3 = 1 then 117 else 124) else (if t 3 = 0 then 166 else if t 3 = 1 then 128 else 132)) else (if t 2 = 0 then (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 151) else if t 2 = 1 then (if t 3 = 0 then 161 else if t 3 = 1 then 119 else 125) else (if t 3 = 0 then 167 else if t 3 = 1 then 129 else 133))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 1545 else 2763) else if t 2 = 1 then (if t 3 = 0 then 194 else if t 3 = 1 then 192 else 204) else (if t 3 = 0 then 4059 else if t 3 = 1 then 903 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2115 else if t 3 = 1 then 1531 else 1833) else if t 2 = 1 then (if t 3 = 0 then 162 else if t 3 = 1 then 121 else 126) else (if t 3 = 0 then 168 else if t 3 = 1 then 130 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 2116 else if t 3 = 1 then 1532 else 1834) else if t 2 = 1 then (if t 3 = 0 then 163 else if t 3 = 1 then 122 else 127) else (if t 3 = 0 then 169 else if t 3 = 1 then 131 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3714 else (if jt.2.val < 2 then 3745 else 3725)) else (if jt.2.val < 4 then 3744 else (if jt.2.val < 5 then 3746 else 3722))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4308 else (if jt.2.val < 2 then 4313 else 4310)) else (if jt.2.val < 4 then 4311 else (if jt.2.val < 5 then 4312 else 4305)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2295 else (if jt.2.val < 2 then 2297 else 2300)) else (if jt.2.val < 4 then 2296 else (if jt.2.val < 5 then 2299 else 2298))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 108 else (if jt.2.val < 2 then 110 else 165)) else (if jt.2.val < 4 then 109 else (if jt.2.val < 5 then 164 else 123)))))

checked_coverage fastCoverage0356 pairing0356 template0356 witness0356

theorem coverage0356 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0356) (maskBits m))
    cores template0356 witness0356 := by
  rw [← coresFast_eq]
  exact fastCoverage0356

theorem coverageSize0356 : ∀ q : Pattern,
    (cores (witness0356 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0356 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0356
#print axioms coverageSize0356

noncomputable def pairing0357 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0357 : List (Fin 4935) := templateData0357

noncomputable def witness0357 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 384 else 402) else if t 2 = 1 then (if t 3 = 0 then 386 else if t 3 = 1 then 382 else 400) else (if t 3 = 0 then 2140 else if t 3 = 1 then 928 else 1790)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 379 else if t 3 = 1 then 356 else 357) else if t 2 = 1 then (if t 3 = 0 then 371 else if t 3 = 1 then 336 else 340) else (if t 3 = 0 then 373 else if t 3 = 1 then 342 else 344)) else (if t 2 = 0 then (if t 3 = 0 then 4036 else if t 3 = 1 then 3929 else 4205) else if t 2 = 1 then (if t 3 = 0 then 2737 else if t 3 = 1 then 2728 else 2730) else (if t 3 = 0 then 2738 else if t 3 = 1 then 2731 else 2732))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 383 else 401) else if t 2 = 1 then (if t 3 = 0 then 385 else if t 3 = 1 then 381 else 399) else (if t 3 = 0 then 2139 else if t 3 = 1 then 924 else 1788)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 375 else if t 3 = 1 then 346 else 350) else if t 2 = 1 then (if t 3 = 0 then 363 else if t 3 = 1 then 318 else 324) else (if t 3 = 0 then 367 else if t 3 = 1 then 328 else 332)) else (if t 2 = 0 then (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 351) else if t 2 = 1 then (if t 3 = 0 then 364 else if t 3 = 1 then 320 else 325) else (if t 3 = 0 then 368 else if t 3 = 1 then 329 else 333))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1497 else 2801) else if t 2 = 1 then (if t 3 = 0 then 395 else if t 3 = 1 then 393 else 405) else (if t 3 = 0 then 4206 else if t 3 = 1 then 926 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1773 else if t 3 = 1 then 1483 else 2157) else if t 2 = 1 then (if t 3 = 0 then 365 else if t 3 = 1 then 322 else 326) else (if t 3 = 0 then 369 else if t 3 = 1 then 330 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 1774 else if t 3 = 1 then 1484 else 2158) else if t 2 = 1 then (if t 3 = 0 then 366 else if t 3 = 1 then 323 else 327) else (if t 3 = 0 then 370 else if t 3 = 1 then 331 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3690 else (if jt.2.val < 2 then 3757 else 3701)) else (if jt.2.val < 4 then 3756 else (if jt.2.val < 5 then 3758 else 3698))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4290 else (if jt.2.val < 2 then 4301 else 4292)) else (if jt.2.val < 4 then 4299 else (if jt.2.val < 5 then 4300 else 4287)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2337 else (if jt.2.val < 2 then 2339 else 2342)) else (if jt.2.val < 4 then 2338 else (if jt.2.val < 5 then 2341 else 2340))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 123 else (if jt.2.val < 2 then 361 else 165)) else (if jt.2.val < 4 then 360 else (if jt.2.val < 5 then 362 else 108)))))

checked_coverage fastCoverage0357 pairing0357 template0357 witness0357

theorem coverage0357 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0357) (maskBits m))
    cores template0357 witness0357 := by
  rw [← coresFast_eq]
  exact fastCoverage0357

theorem coverageSize0357 : ∀ q : Pattern,
    (cores (witness0357 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0357 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0357
#print axioms coverageSize0357

noncomputable def pairing0358 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0358 : List (Fin 4935) := templateData0358

noncomputable def witness0358 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1912 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1907 else 1619) else (if t 3 = 0 then 104 else if t 3 = 1 then 94 else 95)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1901 else 1670) else if t 2 = 1 then (if t 3 = 0 then 1891 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 978 else if t 3 = 1 then 1877 else 1881)) else (if t 2 = 0 then (if t 3 = 0 then 2561 else if t 3 = 1 then 2546 else 2547) else if t 2 = 1 then (if t 3 = 0 then 2938 else if t 3 = 1 then 3348 else 3351) else (if t 3 = 0 then 4198 else if t 3 = 1 then 4064 else 4066))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1911 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1905 else 1617) else (if t 3 = 0 then 102 else if t 3 = 1 then 90 else 92)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1899 else 1667) else if t 2 = 1 then (if t 3 = 0 then 1887 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 971 else if t 3 = 1 then 1861 else 1869)) else (if t 2 = 0 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1900 else 1668) else if t 2 = 1 then (if t 3 = 0 then 1888 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 972 else if t 3 = 1 then 1862 else 1870))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 1115 else 4208) else if t 2 = 1 then (if t 3 = 0 then 504 else if t 3 = 1 then 492 else 494) else (if t 3 = 0 then 2744 else if t 3 = 1 then 1521 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 572 else if t 3 = 1 then 548 else 550) else if t 2 = 1 then (if t 3 = 0 then 1181 else if t 3 = 1 then 1863 else 1871) else (if t 3 = 0 then 2136 else if t 3 = 1 then 1865 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 573 else if t 3 = 1 then 549 else 551) else if t 2 = 1 then (if t 3 = 0 then 1182 else if t 3 = 1 then 1864 else 1872) else (if t 3 = 0 then 2137 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3972 else (if jt.2.val < 2 then 4063 else 3994)) else (if jt.2.val < 4 then 4062 else (if jt.2.val < 5 then 4065 else 3990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3657 else (if jt.2.val < 2 then 3671 else 3659)) else (if jt.2.val < 4 then 3669 else (if jt.2.val < 5 then 3670 else 3654)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2298 else (if jt.2.val < 2 then 2320 else 2300)) else (if jt.2.val < 4 then 2319 else (if jt.2.val < 5 then 2321 else 2295))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2367 else (if jt.2.val < 2 then 2369 else 2372)) else (if jt.2.val < 4 then 2368 else (if jt.2.val < 5 then 2371 else 2370)))))

checked_coverage fastCoverage0358 pairing0358 template0358 witness0358

theorem coverage0358 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0358) (maskBits m))
    cores template0358 witness0358 := by
  rw [← coresFast_eq]
  exact fastCoverage0358

theorem coverageSize0358 : ∀ q : Pattern,
    (cores (witness0358 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0358 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0358
#print axioms coverageSize0358

noncomputable def pairing0359 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 7)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0359 : List (Fin 4935) := templateData0359

noncomputable def witness0359 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2228 else 1856) else if t 2 = 1 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2222 else 1616) else (if t 3 = 0 then 308 else if t 3 = 1 then 298 else 299)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2213 else 1661) else if t 2 = 1 then (if t 3 = 0 then 2207 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 979 else if t 3 = 1 then 2195 else 2199)) else (if t 2 = 0 then (if t 3 = 0 then 2706 else if t 3 = 1 then 2690 else 2691) else if t 2 = 1 then (if t 3 = 0 then 2939 else if t 3 = 1 then 3528 else 3531) else (if t 3 = 0 then 4047 else if t 3 = 1 then 4211 else 4213))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2226 else 1854) else if t 2 = 1 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2220 else 1614) else (if t 3 = 0 then 306 else if t 3 = 1 then 294 else 296)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2211 else 1658) else if t 2 = 1 then (if t 3 = 0 then 2205 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 973 else if t 3 = 1 then 2179 else 2187)) else (if t 2 = 0 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2212 else 1659) else if t 2 = 1 then (if t 3 = 0 then 2206 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 974 else if t 3 = 1 then 2180 else 2188))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 1146 else 4061) else if t 2 = 1 then (if t 3 = 0 then 696 else if t 3 = 1 then 684 else 686) else (if t 3 = 0 then 2782 else if t 3 = 1 then 1473 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 761 else if t 3 = 1 then 736 else 738) else if t 2 = 1 then (if t 3 = 0 then 1183 else if t 3 = 1 then 2181 else 2189) else (if t 3 = 0 then 1799 else if t 3 = 1 then 2183 else 2191)) else (if t 2 = 0 then (if t 3 = 0 then 762 else if t 3 = 1 then 737 else 739) else if t 2 = 1 then (if t 3 = 0 then 1184 else if t 3 = 1 then 2182 else 2190) else (if t 3 = 0 then 1800 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4134 else (if jt.2.val < 2 then 4210 else 4156)) else (if jt.2.val < 4 then 4209 else (if jt.2.val < 5 then 4212 else 4152))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3681 else (if jt.2.val < 2 then 3689 else 3683)) else (if jt.2.val < 4 then 3687 else (if jt.2.val < 5 then 3688 else 3678)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2340 else (if jt.2.val < 2 then 2356 else 2342)) else (if jt.2.val < 4 then 2355 else (if jt.2.val < 5 then 2357 else 2337))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2370 else (if jt.2.val < 2 then 2374 else 2372)) else (if jt.2.val < 4 then 2373 else (if jt.2.val < 5 then 2375 else 2367)))))

checked_coverage fastCoverage0359 pairing0359 template0359 witness0359

theorem coverage0359 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0359) (maskBits m))
    cores template0359 witness0359 := by
  rw [← coresFast_eq]
  exact fastCoverage0359

theorem coverageSize0359 : ∀ q : Pattern,
    (cores (witness0359 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0359 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0359
#print axioms coverageSize0359

end Crown.CertificateData
