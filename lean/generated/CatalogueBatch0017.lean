import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0016

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0640 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0640 : List (Fin 4935) := templateData0640

noncomputable def witness0640 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 4056) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2996) else (if t 3 = 0 then 2779 else if t 3 = 1 then 2778 else 2781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 1173) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 1172) else (if t 3 = 0 then 682 else if t 3 = 1 then 680 else 694)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2197 else 1802) else if t 2 = 1 then (if t 3 = 0 then 2200 else if t 3 = 1 then 2196 else 1189) else (if t 3 = 0 then 689 else if t 3 = 1 then 688 else 698))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 822) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 821) else (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 202)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2829) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4163) else (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4181)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2842) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4164) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4180 else 4182))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 35 else 71) else if t 2 = 1 then (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 70) else (if t 3 = 0 then 1808 else if t 3 = 1 then 901 else 2128)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2487) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4177) else (if t 3 = 0 then 4039 else if t 3 = 1 then 4183 else 4185)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2475 else 2491) else if t 2 = 1 then (if t 3 = 0 then 3838 else if t 3 = 1 then 4171 else 4178) else (if t 3 = 0 then 4040 else if t 3 = 1 then 4184 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4827 else (if jt.2.val < 2 then 4831 else 4832)) else (if jt.2.val < 4 then 4828 else (if jt.2.val < 5 then 4830 else 4829))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4693 else (if jt.2.val < 2 then 4697 else 4698)) else (if jt.2.val < 4 then 4694 else (if jt.2.val < 5 then 4696 else 4695)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4215 else (if jt.2.val < 2 then 4223 else 4226)) else (if jt.2.val < 4 then 4222 else (if jt.2.val < 5 then 4225 else 4224))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4278 else (if jt.2.val < 2 then 4282 else 4283)) else (if jt.2.val < 4 then 4279 else (if jt.2.val < 5 then 4281 else 4280)))))

checked_coverage fastCoverage0640 pairing0640 template0640 witness0640

theorem coverage0640 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0640) (maskBits m))
    cores template0640 witness0640 := by
  rw [← coresFast_eq]
  exact fastCoverage0640

theorem coverageSize0640 : ∀ q : Pattern,
    (cores (witness0640 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0640 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0640
#print axioms coverageSize0640

noncomputable def pairing0641 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0641 : List (Fin 4935) := templateData0641

noncomputable def witness0641 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 4203) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2995) else (if t 3 = 0 then 2741 else if t 3 = 1 then 2740 else 2743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 1171) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 1170) else (if t 3 = 0 then 490 else if t 3 = 1 then 488 else 502)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1879 else 2138) else if t 2 = 1 then (if t 3 = 0 then 1882 else if t 3 = 1 then 1878 else 1188) else (if t 3 = 0 then 497 else if t 3 = 1 then 496 else 506))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 820) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 819) else (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 403)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2828) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4000) else (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4021)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2841) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4003) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4020 else 4022))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 243 else 275) else if t 2 = 1 then (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 274) else (if t 3 = 0 then 2141 else if t 3 = 1 then 925 else 1789)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2635) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4017) else (if t 3 = 0 then 4191 else if t 3 = 1 then 4023 else 4025)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2627 else 2639) else if t 2 = 1 then (if t 3 = 0 then 3847 else if t 3 = 1 then 4016 else 4018) else (if t 3 = 0 then 4192 else if t 3 = 1 then 4024 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4809 else (if jt.2.val < 2 then 4813 else 4814)) else (if jt.2.val < 4 then 4810 else (if jt.2.val < 5 then 4812 else 4811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4432 else (if jt.2.val < 2 then 4436 else 4437)) else (if jt.2.val < 4 then 4433 else (if jt.2.val < 5 then 4435 else 4434)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4068 else (if jt.2.val < 2 then 4074 else 4079)) else (if jt.2.val < 4 then 4073 else (if jt.2.val < 5 then 4078 else 4077))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4280 else (if jt.2.val < 2 then 4286 else 4283)) else (if jt.2.val < 4 then 4284 else (if jt.2.val < 5 then 4285 else 4278)))))

checked_coverage fastCoverage0641 pairing0641 template0641 witness0641

theorem coverage0641 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0641) (maskBits m))
    cores template0641 witness0641 := by
  rw [← coresFast_eq]
  exact fastCoverage0641

theorem coverageSize0641 : ∀ q : Pattern,
    (cores (witness0641 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0641 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0641
#print axioms coverageSize0641

noncomputable def pairing0642 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0642 : List (Fin 4935) := templateData0642

noncomputable def witness0642 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2565 else 2577) else if t 2 = 1 then (if t 3 = 0 then 2560 else if t 3 = 1 then 2544 else 2545) else (if t 3 = 0 then 4190 else if t 3 = 1 then 3945 else 4058)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2563 else 1372) else if t 2 = 1 then (if t 3 = 0 then 2558 else if t 3 = 1 then 2538 else 1350) else (if t 3 = 0 then 667 else if t 3 = 1 then 641 else 644)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 291 else 305) else if t 2 = 1 then (if t 3 = 0 then 277 else if t 3 = 1 then 251 else 254) else (if t 3 = 0 then 2170 else if t 3 = 1 then 1459 else 1786))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2564 else 1687) else if t 2 = 1 then (if t 3 = 0 then 2559 else if t 3 = 1 then 2541 else 1666) else (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 151)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2562 else 2576) else if t 2 = 1 then (if t 3 = 0 then 2548 else if t 3 = 1 then 2519 else 2526) else (if t 3 = 0 then 2549 else if t 3 = 1 then 2521 else 2527)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2572 else 2579) else if t 2 = 1 then (if t 3 = 0 then 2550 else if t 3 = 1 then 2523 else 2528) else (if t 3 = 0 then 2551 else if t 3 = 1 then 2524 else 2529))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1915 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1900 else 1668) else (if t 3 = 0 then 177 else if t 3 = 1 then 153 else 155)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2883 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2554 else if t 3 = 1 then 2530 else 2534) else (if t 3 = 0 then 2555 else if t 3 = 1 then 2531 else 2535)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2886 else 4197) else if t 2 = 1 then (if t 3 = 0 then 2556 else if t 3 = 1 then 2532 else 2536) else (if t 3 = 0 then 2557 else if t 3 = 1 then 2533 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4773 else (if jt.2.val < 2 then 4775 else 4778)) else (if jt.2.val < 4 then 4774 else (if jt.2.val < 5 then 4777 else 4776))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2513 else (if jt.2.val < 2 then 2515 else 2543)) else (if jt.2.val < 4 then 2514 else (if jt.2.val < 5 then 2542 else 2522)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4224 else (if jt.2.val < 2 then 4232 else 4226)) else (if jt.2.val < 4 then 4230 else (if jt.2.val < 5 then 4231 else 4215))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2510 else (if jt.2.val < 2 then 2512 else 2553)) else (if jt.2.val < 4 then 2511 else (if jt.2.val < 5 then 2552 else 2525)))))

checked_coverage fastCoverage0642 pairing0642 template0642 witness0642

theorem coverage0642 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0642) (maskBits m))
    cores template0642 witness0642 := by
  rw [← coresFast_eq]
  exact fastCoverage0642

theorem coverageSize0642 : ∀ q : Pattern,
    (cores (witness0642 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0642 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0642
#print axioms coverageSize0642

noncomputable def pairing0643 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0643 : List (Fin 4935) := templateData0643

noncomputable def witness0643 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2710 else 2722) else if t 2 = 1 then (if t 3 = 0 then 2705 else if t 3 = 1 then 2688 else 2689) else (if t 3 = 0 then 4036 else if t 3 = 1 then 3929 else 4205)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2708 else 1371) else if t 2 = 1 then (if t 3 = 0 then 2703 else if t 3 = 1 then 2682 else 1339) else (if t 3 = 0 then 475 else if t 3 = 1 then 445 else 448)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 87 else 101) else if t 2 = 1 then (if t 3 = 0 then 73 else if t 3 = 1 then 43 else 46) else (if t 3 = 0 then 1849 else if t 3 = 1 then 1507 else 2125))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2709 else 1686) else if t 2 = 1 then (if t 3 = 0 then 2704 else if t 3 = 1 then 2685 else 1657) else (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 351)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2707 else 2721) else if t 2 = 1 then (if t 3 = 0 then 2695 else if t 3 = 1 then 2664 else 2670) else (if t 3 = 0 then 2696 else if t 3 = 1 then 2666 else 2671)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2717 else 2724) else if t 2 = 1 then (if t 3 = 0 then 2697 else if t 3 = 1 then 2668 else 2672) else (if t 3 = 0 then 2698 else if t 3 = 1 then 2669 else 2673))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2227 else 1855) else if t 2 = 1 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2212 else 1659) else (if t 3 = 0 then 378 else if t 3 = 1 then 353 else 355)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2902 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2699 else if t 3 = 1 then 2674 else 2678) else (if t 3 = 0 then 2700 else if t 3 = 1 then 2675 else 2679)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2904 else 4045) else if t 2 = 1 then (if t 3 = 0 then 2701 else if t 3 = 1 then 2676 else 2680) else (if t 3 = 0 then 2702 else if t 3 = 1 then 2677 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4797 else (if jt.2.val < 2 then 4799 else 4802)) else (if jt.2.val < 4 then 4798 else (if jt.2.val < 5 then 4801 else 4800))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2658 else (if jt.2.val < 2 then 2660 else 2687)) else (if jt.2.val < 4 then 2659 else (if jt.2.val < 5 then 2686 else 2667)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4077 else (if jt.2.val < 2 then 4091 else 4079)) else (if jt.2.val < 4 then 4089 else (if jt.2.val < 5 then 4090 else 4068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2525 else (if jt.2.val < 2 then 2693 else 2553)) else (if jt.2.val < 4 then 2692 else (if jt.2.val < 5 then 2694 else 2510)))))

checked_coverage fastCoverage0643 pairing0643 template0643 witness0643

theorem coverage0643 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0643) (maskBits m))
    cores template0643 witness0643 := by
  rw [← coresFast_eq]
  exact fastCoverage0643

theorem coverageSize0643 : ∀ q : Pattern,
    (cores (witness0643 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0643 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0643
#print axioms coverageSize0643

noncomputable def pairing0644 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0644 : List (Fin 4935) := templateData0644

noncomputable def witness0644 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1816) else if t 2 = 1 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 835) else (if t 3 = 0 then 195 else if t 3 = 1 then 193 else 205)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 1051) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2082) else (if t 3 = 0 then 1447 else if t 3 = 1 then 2101 else 2104)) else (if t 2 = 0 then (if t 3 = 0 then 4213 else if t 3 = 1 then 4211 else 4047) else if t 2 = 1 then (if t 3 = 0 then 3531 else if t 3 = 1 then 3528 else 2939) else (if t 3 = 0 then 2649 else if t 3 = 1 then 2648 else 2654))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1815) else if t 2 = 1 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 834) else (if t 3 = 0 then 194 else if t 3 = 1 then 192 else 204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 1050) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2081) else (if t 3 = 0 then 1446 else if t 3 = 1 then 2100 else 2103)) else (if t 2 = 0 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 1056) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2083) else (if t 3 = 0 then 1448 else if t 3 = 1 then 2102 else 2105))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 1509 else 2739) else if t 2 = 1 then (if t 3 = 0 then 49 else if t 3 = 1 then 47 else 74) else (if t 3 = 0 then 4059 else if t 3 = 1 then 903 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 451 else if t 3 = 1 then 449 else 476) else if t 2 = 1 then (if t 3 = 0 then 1341 else if t 3 = 1 then 2089 else 2097) else (if t 3 = 0 then 1779 else if t 3 = 1 then 2106 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 456 else if t 3 = 1 then 455 else 479) else if t 2 = 1 then (if t 3 = 0 then 1344 else if t 3 = 1 then 2091 else 2099) else (if t 3 = 0 then 1781 else if t 3 = 1 then 2108 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4797 else (if jt.2.val < 2 then 4805 else 4802)) else (if jt.2.val < 4 then 4803 else (if jt.2.val < 5 then 4804 else 4800))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4695 else (if jt.2.val < 2 then 4706 else 4698)) else (if jt.2.val < 4 then 4704 else (if jt.2.val < 5 then 4705 else 4693)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2412 else (if jt.2.val < 2 then 2414 else 2417)) else (if jt.2.val < 4 then 2413 else (if jt.2.val < 5 then 2416 else 2415))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2358 else (if jt.2.val < 2 then 2362 else 2363)) else (if jt.2.val < 4 then 2359 else (if jt.2.val < 5 then 2361 else 2360)))))

checked_coverage fastCoverage0644 pairing0644 template0644 witness0644

theorem coverage0644 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0644) (maskBits m))
    cores template0644 witness0644 := by
  rw [← coresFast_eq]
  exact fastCoverage0644

theorem coverageSize0644 : ∀ q : Pattern,
    (cores (witness0644 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0644 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0644
#print axioms coverageSize0644

noncomputable def pairing0645 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0645 : List (Fin 4935) := templateData0645

noncomputable def witness0645 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 2146) else if t 2 = 1 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 833) else (if t 3 = 0 then 396 else if t 3 = 1 then 394 else 406)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 1049) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1730) else (if t 3 = 0 then 1450 else if t 3 = 1 then 1753 else 1756)) else (if t 2 = 0 then (if t 3 = 0 then 4066 else if t 3 = 1 then 4064 else 4198) else if t 2 = 1 then (if t 3 = 0 then 3351 else if t 3 = 1 then 3348 else 2938) else (if t 3 = 0 then 2501 else if t 3 = 1 then 2500 else 2506))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 2145) else if t 2 = 1 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 832) else (if t 3 = 0 then 395 else if t 3 = 1 then 393 else 405)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 1048) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1729) else (if t 3 = 0 then 1449 else if t 3 = 1 then 1752 else 1755)) else (if t 2 = 0 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 1055) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1734) else (if t 3 = 0 then 1451 else if t 3 = 1 then 1754 else 1757))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1461 else 2777) else if t 2 = 1 then (if t 3 = 0 then 257 else if t 3 = 1 then 255 else 278) else (if t 3 = 0 then 4206 else if t 3 = 1 then 926 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 647 else if t 3 = 1 then 645 else 668) else if t 2 = 1 then (if t 3 = 0 then 1352 else if t 3 = 1 then 1746 else 1749) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1758 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 652 else if t 3 = 1 then 651 else 671) else if t 2 = 1 then (if t 3 = 0 then 1355 else if t 3 = 1 then 1748 else 1751) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1759 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4773 else (if jt.2.val < 2 then 4781 else 4778)) else (if jt.2.val < 4 then 4779 else (if jt.2.val < 5 then 4780 else 4776))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4434 else (if jt.2.val < 2 then 4445 else 4437)) else (if jt.2.val < 4 then 4443 else (if jt.2.val < 5 then 4444 else 4432)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2376 else (if jt.2.val < 2 then 2378 else 2381)) else (if jt.2.val < 4 then 2377 else (if jt.2.val < 5 then 2380 else 2379))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2360 else (if jt.2.val < 2 then 2366 else 2363)) else (if jt.2.val < 4 then 2364 else (if jt.2.val < 5 then 2365 else 2358)))))

checked_coverage fastCoverage0645 pairing0645 template0645 witness0645

theorem coverage0645 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0645) (maskBits m))
    cores template0645 witness0645 := by
  rw [← coresFast_eq]
  exact fastCoverage0645

theorem coverageSize0645 : ∀ q : Pattern,
    (cores (witness0645 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0645 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0645
#print axioms coverageSize0645

noncomputable def pairing0646 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0646 : List (Fin 4935) := templateData0646

noncomputable def witness0646 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 579 else 597) else if t 2 = 1 then (if t 3 = 0 then 574 else if t 3 = 1 then 552 else 553) else (if t 3 = 0 then 2117 else if t 3 = 1 then 1537 else 1835)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 581 else if t 3 = 1 then 577 else 595) else if t 2 = 1 then (if t 3 = 0 then 566 else if t 3 = 1 then 532 else 535) else (if t 3 = 0 then 567 else if t 3 = 1 then 534 else 536)) else (if t 2 = 0 then (if t 3 = 0 then 2760 else if t 3 = 1 then 2759 else 2762) else if t 2 = 1 then (if t 3 = 0 then 2756 else if t 3 = 1 then 2747 else 2749) else (if t 3 = 0 then 4207 else if t 3 = 1 then 3923 else 4044))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 578 else 596) else if t 2 = 1 then (if t 3 = 0 then 570 else if t 3 = 1 then 544 else 546) else (if t 3 = 0 then 2115 else if t 3 = 1 then 1531 else 1833)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 580 else if t 3 = 1 then 576 else 594) else if t 2 = 1 then (if t 3 = 0 then 556 else if t 3 = 1 then 515 else 520) else (if t 3 = 0 then 558 else if t 3 = 1 then 517 else 522)) else (if t 2 = 0 then (if t 3 = 0 then 586 else if t 3 = 1 then 584 else 598) else if t 2 = 1 then (if t 3 = 0 then 557 else if t 3 = 1 then 516 else 521) else (if t 3 = 0 then 559 else if t 3 = 1 then 518 else 523))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 1115 else 4208) else if t 2 = 1 then (if t 3 = 0 then 572 else if t 3 = 1 then 548 else 550) else (if t 3 = 0 then 2758 else if t 3 = 1 then 1535 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1836 else if t 3 = 1 then 1113 else 2148) else if t 2 = 1 then (if t 3 = 0 then 562 else if t 3 = 1 then 524 else 528) else (if t 3 = 0 then 564 else if t 3 = 1 then 526 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 1838 else if t 3 = 1 then 1117 else 2149) else if t 2 = 1 then (if t 3 = 0 then 563 else if t 3 = 1 then 525 else 529) else (if t 3 = 0 then 565 else if t 3 = 1 then 527 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4809 else (if jt.2.val < 2 then 4825 else 4814)) else (if jt.2.val < 4 then 4824 else (if jt.2.val < 5 then 4826 else 4811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2522 else (if jt.2.val < 2 then 2753 else 2543)) else (if jt.2.val < 4 then 2752 else (if jt.2.val < 5 then 2754 else 2513)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2415 else (if jt.2.val < 2 then 2426 else 2417)) else (if jt.2.val < 4 then 2424 else (if jt.2.val < 5 then 2425 else 2412))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 510 else (if jt.2.val < 2 then 512 else 561)) else (if jt.2.val < 4 then 511 else (if jt.2.val < 5 then 560 else 519)))))

checked_coverage fastCoverage0646 pairing0646 template0646 witness0646

theorem coverage0646 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0646) (maskBits m))
    cores template0646 witness0646 := by
  rw [← coresFast_eq]
  exact fastCoverage0646

theorem coverageSize0646 : ∀ q : Pattern,
    (cores (witness0646 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0646 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0646
#print axioms coverageSize0646

noncomputable def pairing0647 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0647 : List (Fin 4935) := templateData0647

noncomputable def witness0647 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 768 else 786) else if t 2 = 1 then (if t 3 = 0 then 763 else if t 3 = 1 then 740 else 741) else (if t 3 = 0 then 1775 else if t 3 = 1 then 1489 else 2159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 770 else if t 3 = 1 then 766 else 784) else if t 2 = 1 then (if t 3 = 0 then 755 else if t 3 = 1 then 720 else 723) else (if t 3 = 0 then 756 else if t 3 = 1 then 722 else 724)) else (if t 2 = 0 then (if t 3 = 0 then 2798 else if t 3 = 1 then 2797 else 2800) else if t 2 = 1 then (if t 3 = 0 then 2794 else if t 3 = 1 then 2785 else 2787) else (if t 3 = 0 then 4060 else if t 3 = 1 then 3939 else 4196))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 767 else 785) else if t 2 = 1 then (if t 3 = 0 then 759 else if t 3 = 1 then 732 else 734) else (if t 3 = 0 then 1773 else if t 3 = 1 then 1483 else 2157)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 769 else if t 3 = 1 then 765 else 783) else if t 2 = 1 then (if t 3 = 0 then 747 else if t 3 = 1 then 704 else 708) else (if t 3 = 0 then 749 else if t 3 = 1 then 706 else 710)) else (if t 2 = 0 then (if t 3 = 0 then 775 else if t 3 = 1 then 773 else 787) else if t 2 = 1 then (if t 3 = 0 then 748 else if t 3 = 1 then 705 else 709) else (if t 3 = 0 then 750 else if t 3 = 1 then 707 else 711))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 1146 else 4061) else if t 2 = 1 then (if t 3 = 0 then 761 else if t 3 = 1 then 736 else 738) else (if t 3 = 0 then 2796 else if t 3 = 1 then 1487 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2160 else if t 3 = 1 then 1140 else 1824) else if t 2 = 1 then (if t 3 = 0 then 751 else if t 3 = 1 then 712 else 716) else (if t 3 = 0 then 753 else if t 3 = 1 then 714 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 2162 else if t 3 = 1 then 1141 else 1825) else if t 2 = 1 then (if t 3 = 0 then 752 else if t 3 = 1 then 713 else 717) else (if t 3 = 0 then 754 else if t 3 = 1 then 715 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4827 else (if jt.2.val < 2 then 4834 else 4832)) else (if jt.2.val < 4 then 4833 else (if jt.2.val < 5 then 4835 else 4829))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2667 else (if jt.2.val < 2 then 2791 else 2687)) else (if jt.2.val < 4 then 2790 else (if jt.2.val < 5 then 2792 else 2658)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2379 else (if jt.2.val < 2 then 2402 else 2381)) else (if jt.2.val < 4 then 2400 else (if jt.2.val < 5 then 2401 else 2376))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 519 else (if jt.2.val < 2 then 745 else 561)) else (if jt.2.val < 4 then 744 else (if jt.2.val < 5 then 746 else 510)))))

checked_coverage fastCoverage0647 pairing0647 template0647 witness0647

theorem coverage0647 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0647) (maskBits m))
    cores template0647 witness0647 := by
  rw [← coresFast_eq]
  exact fastCoverage0647

theorem coverageSize0647 : ∀ q : Pattern,
    (cores (witness0647 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0647 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0647
#print axioms coverageSize0647

noncomputable def pairing0648 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0648 : List (Fin 4935) := templateData0648

noncomputable def witness0648 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 3935) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2740) else (if t 3 = 0 then 3352 else if t 3 = 1 then 3350 else 3207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 489) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 488) else (if t 3 = 0 then 1882 else if t 3 = 1 then 1878 else 496)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1171 else 503) else if t 2 = 1 then (if t 3 = 0 then 1174 else if t 3 = 1 then 1170 else 502) else (if t 3 = 0 then 1190 else if t 3 = 1 then 1188 else 506))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 390) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 389) else (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 397)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2715) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4019) else (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4020)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2723) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4021) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4003 else 4022))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 243 else 931) else if t 2 = 1 then (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 925) else (if t 3 = 0 then 262 else if t 3 = 1 then 261 else 927)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2903) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4023) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4016 else 4024)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2635 else 3322) else if t 2 = 1 then (if t 3 = 0 then 3849 else if t 3 = 1 then 4017 else 4025) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4018 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4809 else (if jt.2.val < 2 then 4813 else 4814)) else (if jt.2.val < 4 then 4810 else (if jt.2.val < 5 then 4812 else 4811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3971 else (if jt.2.val < 2 then 3999 else 4001)) else (if jt.2.val < 4 then 3996 else (if jt.2.val < 5 then 3998 else 3997)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4566 else (if jt.2.val < 2 then 4570 else 4571)) else (if jt.2.val < 4 then 4567 else (if jt.2.val < 5 then 4569 else 4568))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3969 else (if jt.2.val < 2 then 4006 else 4009)) else (if jt.2.val < 4 then 4005 else (if jt.2.val < 5 then 4008 else 4007)))))

checked_coverage fastCoverage0648 pairing0648 template0648 witness0648

theorem coverage0648 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0648) (maskBits m))
    cores template0648 witness0648 := by
  rw [← coresFast_eq]
  exact fastCoverage0648

theorem coverageSize0648 : ∀ q : Pattern,
    (cores (witness0648 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0648 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0648
#print axioms coverageSize0648

noncomputable def pairing0649 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0649 : List (Fin 4935) := templateData0649

noncomputable def witness0649 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4036) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2737) else (if t 3 = 0 then 3228 else if t 3 = 1 then 3225 else 3344)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 475) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 462) else (if t 3 = 0 then 1612 else if t 3 = 1 then 1593 else 464)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 667 else 1138) else if t 2 = 1 then (if t 3 = 0 then 682 else if t 3 = 1 then 654 else 1132) else (if t 3 = 0 then 689 else if t 3 = 1 then 656 else 1134))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 376) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 364) else (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 366)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2696) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3880) else (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3881)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2879) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3882) else (if t 3 = 0 then 3916 else if t 3 = 1 then 3878 else 3883))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 994 else 378) else if t 2 = 1 then (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 368) else (if t 3 = 0 then 1013 else if t 3 = 1 then 990 else 370)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2700) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3888) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3885 else 3889)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2555 else 3197) else if t 2 = 1 then (if t 3 = 0 then 4039 else if t 3 = 1 then 3886 else 3890) else (if t 3 = 0 then 4040 else if t 3 = 1 then 3887 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4815 else (if jt.2.val < 2 then 4817 else 4820)) else (if jt.2.val < 4 then 4816 else (if jt.2.val < 5 then 4819 else 4818))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3867 else (if jt.2.val < 2 then 3869 else 3897)) else (if jt.2.val < 4 then 3868 else (if jt.2.val < 5 then 3896 else 3876)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4455 else (if jt.2.val < 2 then 4457 else 4460)) else (if jt.2.val < 4 then 4456 else (if jt.2.val < 5 then 4459 else 4458))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4007 else (if jt.2.val < 2 then 4032 else 4009)) else (if jt.2.val < 4 then 4027 else (if jt.2.val < 5 then 4028 else 3969)))))

checked_coverage fastCoverage0649 pairing0649 template0649 witness0649

theorem coverage0649 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0649) (maskBits m))
    cores template0649 witness0649 := by
  rw [← coresFast_eq]
  exact fastCoverage0649

theorem coverageSize0649 : ∀ q : Pattern,
    (cores (witness0649 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0649 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0649
#print axioms coverageSize0649

noncomputable def pairing0650 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0650 : List (Fin 4935) := templateData0650

noncomputable def witness0650 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3198) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2797) else (if t 3 = 0 then 4066 else if t 3 = 1 then 4064 else 3943)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 87) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 86) else (if t 3 = 0 then 1881 else if t 3 = 1 then 1877 else 94)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 962 else 101) else if t 2 = 1 then (if t 3 = 0 then 965 else if t 3 = 1 then 961 else 100) else (if t 3 = 0 then 980 else if t 3 = 1 then 978 else 104))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 774) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 773) else (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2717) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3295) else (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3296)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2724) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3276 else 3297) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3279 else 3298))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 637 else 1147) else if t 2 = 1 then (if t 3 = 0 then 638 else if t 3 = 1 then 636 else 1141) else (if t 3 = 0 then 652 else if t 3 = 1 then 651 else 1143)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2623 else 2904) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3291 else 3299) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3292 else 3300)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2637 else 4045) else if t 2 = 1 then (if t 3 = 0 then 3095 else if t 3 = 1 then 3293 else 3301) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3294 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4755 else (if jt.2.val < 2 then 4759 else 4760)) else (if jt.2.val < 4 then 4756 else (if jt.2.val < 5 then 4758 else 4757))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3245 else (if jt.2.val < 2 then 3275 else 3277)) else (if jt.2.val < 4 then 3272 else (if jt.2.val < 5 then 3274 else 3273)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4568 else (if jt.2.val < 2 then 4574 else 4571)) else (if jt.2.val < 4 then 4572 else (if jt.2.val < 5 then 4573 else 4566))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3243 else (if jt.2.val < 2 then 3282 else 3285)) else (if jt.2.val < 4 then 3281 else (if jt.2.val < 5 then 3284 else 3283)))))

checked_coverage fastCoverage0650 pairing0650 template0650 witness0650

theorem coverage0650 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0650) (maskBits m))
    cores template0650 witness0650 := by
  rw [← coresFast_eq]
  exact fastCoverage0650

theorem coverageSize0650 : ∀ q : Pattern,
    (cores (witness0650 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0650 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0650
#print axioms coverageSize0650

noncomputable def pairing0651 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0651 : List (Fin 4935) := templateData0651

noncomputable def witness0651 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3312) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 2794) else (if t 3 = 0 then 3959 else if t 3 = 1 then 3953 else 4060)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 73) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 60) else (if t 3 = 0 then 1611 else if t 3 = 1 then 1589 else 62)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 277 else 922) else if t 2 = 1 then (if t 3 = 0 then 292 else if t 3 = 1 then 264 else 916) else (if t 3 = 0 then 299 else if t 3 = 1 then 266 else 918))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 760) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 748) else (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 750)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2697) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3126) else (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3127)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2880) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3123 else 3128) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3124 else 3129))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1204 else 762) else if t 2 = 1 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1198 else 752) else (if t 3 = 0 then 1223 else if t 3 = 1 then 1200 else 754)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2949 else 2701) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3130 else 3134) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3131 else 3135)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2556 else 3934) else if t 2 = 1 then (if t 3 = 0 then 3315 else if t 3 = 1 then 3132 else 3136) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3133 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4761 else (if jt.2.val < 2 then 4763 else 4766)) else (if jt.2.val < 4 then 4762 else (if jt.2.val < 5 then 4765 else 4764))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3113 else (if jt.2.val < 2 then 3115 else 3143)) else (if jt.2.val < 4 then 3114 else (if jt.2.val < 5 then 3142 else 3122)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4458 else (if jt.2.val < 2 then 4465 else 4460)) else (if jt.2.val < 4 then 4464 else (if jt.2.val < 5 then 4466 else 4455))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3283 else (if jt.2.val < 2 then 3308 else 3285)) else (if jt.2.val < 4 then 3303 else (if jt.2.val < 5 then 3304 else 3243)))))

checked_coverage fastCoverage0651 pairing0651 template0651 witness0651

theorem coverage0651 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0651) (maskBits m))
    cores template0651 witness0651 := by
  rw [← coresFast_eq]
  exact fastCoverage0651

theorem coverageSize0651 : ∀ q : Pattern,
    (cores (witness0651 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0651 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0651
#print axioms coverageSize0651

noncomputable def pairing0652 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0652 : List (Fin 4935) := templateData0652

noncomputable def witness0652 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 803 else 402) else if t 2 = 1 then (if t 3 = 0 then 809 else if t 3 = 1 then 801 else 400) else (if t 3 = 0 then 837 else if t 3 = 1 then 833 else 406)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 807 else if t 3 = 1 then 799 else 864) else if t 2 = 1 then (if t 3 = 0 then 805 else if t 3 = 1 then 797 else 862) else (if t 3 = 0 then 835 else if t 3 = 1 then 830 else 868)) else (if t 2 = 0 then (if t 3 = 0 then 4056 else if t 3 = 1 then 4054 else 3967) else if t 2 = 1 then (if t 3 = 0 then 2996 else if t 3 = 1 then 2993 else 3003) else (if t 3 = 0 then 3330 else if t 3 = 1 then 3329 else 3106))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 802 else 401) else if t 2 = 1 then (if t 3 = 0 then 808 else if t 3 = 1 then 800 else 399) else (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 405)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 806 else if t 3 = 1 then 798 else 863) else if t 2 = 1 then (if t 3 = 0 then 804 else if t 3 = 1 then 796 else 861) else (if t 3 = 0 then 834 else if t 3 = 1 then 829 else 867)) else (if t 2 = 0 then (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 866) else if t 2 = 1 then (if t 3 = 0 then 821 else if t 3 = 1 then 816 else 865) else (if t 3 = 0 then 840 else if t 3 = 1 then 838 else 869))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 270 else 3345) else if t 2 = 1 then (if t 3 = 0 then 1470 else if t 3 = 1 then 268 else 1788) else (if t 3 = 0 then 3942 else if t 3 = 1 then 278 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 66 else if t 3 = 1 then 854 else 876) else if t 2 = 1 then (if t 3 = 0 then 64 else if t 3 = 1 then 852 else 870) else (if t 3 = 0 then 74 else if t 3 = 1 then 858 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 71 else if t 3 = 1 then 857 else 877) else if t 2 = 1 then (if t 3 = 0 then 70 else if t 3 = 1 then 856 else 871) else (if t 3 = 0 then 77 else if t 3 = 1 then 860 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4761 else (if jt.2.val < 2 then 4787 else 4766)) else (if jt.2.val < 4 then 4785 else (if jt.2.val < 5 then 4786 else 4764))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3997 else (if jt.2.val < 2 then 4055 else 4001)) else (if jt.2.val < 4 then 4052 else (if jt.2.val < 5 then 4053 else 3971)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 794 else (if jt.2.val < 2 then 828 else 831)) else (if jt.2.val < 4 then 825 else (if jt.2.val < 5 then 827 else 826))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 792 else (if jt.2.val < 2 then 843 else 846)) else (if jt.2.val < 4 then 842 else (if jt.2.val < 5 then 845 else 844)))))

checked_coverage fastCoverage0652 pairing0652 template0652 witness0652

theorem coverage0652 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0652) (maskBits m))
    cores template0652 witness0652 := by
  rw [← coresFast_eq]
  exact fastCoverage0652

theorem coverageSize0652 : ∀ q : Pattern,
    (cores (witness0652 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0652 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0652
#print axioms coverageSize0652

noncomputable def pairing0653 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0653 : List (Fin 4935) := templateData0653

noncomputable def witness0653 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 178 else 896) else if t 2 = 1 then (if t 3 = 0 then 185 else if t 3 = 1 then 170 else 892) else (if t 3 = 0 then 195 else if t 3 = 1 then 171 else 893)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 183 else if t 3 = 1 then 156 else 157) else if t 2 = 1 then (if t 3 = 0 then 181 else if t 3 = 1 then 136 else 140) else (if t 3 = 0 then 193 else if t 3 = 1 then 139 else 141)) else (if t 2 = 0 then (if t 3 = 0 then 3951 else if t 3 = 1 then 3945 else 4058) else if t 2 = 1 then (if t 3 = 0 then 2778 else if t 3 = 1 then 2766 else 2768) else (if t 3 = 0 then 3182 else if t 3 = 1 then 3172 else 3320))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 174 else 894) else if t 2 = 1 then (if t 3 = 0 then 184 else if t 3 = 1 then 160 else 888) else (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 890)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 182 else if t 3 = 1 then 146 else 150) else if t 2 = 1 then (if t 3 = 0 then 180 else if t 3 = 1 then 117 else 124) else (if t 3 = 0 then 192 else if t 3 = 1 then 121 else 126)) else (if t 2 = 0 then (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 151) else if t 2 = 1 then (if t 3 = 0 then 188 else if t 3 = 1 then 119 else 125) else (if t 3 = 0 then 196 else if t 3 = 1 then 122 else 127))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 176 else 3240) else if t 2 = 1 then (if t 3 = 0 then 1806 else if t 3 = 1 then 166 else 1494) else (if t 3 = 0 then 4059 else if t 3 = 1 then 168 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 899 else if t 3 = 1 then 152 else 154) else if t 2 = 1 then (if t 3 = 0 then 897 else if t 3 = 1 then 128 else 132) else (if t 3 = 0 then 903 else if t 3 = 1 then 130 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 902 else if t 3 = 1 then 153 else 155) else if t 2 = 1 then (if t 3 = 0 then 901 else if t 3 = 1 then 129 else 133) else (if t 3 = 0 then 905 else if t 3 = 1 then 131 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4755 else (if jt.2.val < 2 then 4789 else 4760)) else (if jt.2.val < 4 then 4788 else (if jt.2.val < 5 then 4790 else 4757))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3876 else (if jt.2.val < 2 then 3948 else 3897)) else (if jt.2.val < 4 then 3947 else (if jt.2.val < 5 then 3949 else 3867)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 111 else (if jt.2.val < 2 then 113 else 149)) else (if jt.2.val < 4 then 112 else (if jt.2.val < 5 then 148 else 120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 844 else (if jt.2.val < 2 then 884 else 846)) else (if jt.2.val < 4 then 879 else (if jt.2.val < 5 then 880 else 792)))))

checked_coverage fastCoverage0653 pairing0653 template0653 witness0653

theorem coverage0653 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0653) (maskBits m))
    cores template0653 witness0653 := by
  rw [← coresFast_eq]
  exact fastCoverage0653

theorem coverageSize0653 : ∀ q : Pattern,
    (cores (witness0653 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0653 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0653
#print axioms coverageSize0653

noncomputable def pairing0654 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0654 : List (Fin 4935) := templateData0654

noncomputable def witness0654 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1025 else 786) else if t 2 = 1 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1023 else 784) else (if t 3 = 0 then 1053 else if t 3 = 1 then 1049 else 790)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1021 else 1080) else if t 2 = 1 then (if t 3 = 0 then 1027 else if t 3 = 1 then 1019 else 1078) else (if t 3 = 0 then 1051 else if t 3 = 1 then 1046 else 1084)) else (if t 2 = 0 then (if t 3 = 0 then 3340 else if t 3 = 1 then 3338 else 3242) else if t 2 = 1 then (if t 3 = 0 then 2973 else if t 3 = 1 then 2970 else 2980) else (if t 3 = 0 then 4047 else if t 3 = 1 then 4046 else 3860))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1024 else 785) else if t 2 = 1 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1022 else 783) else (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 789)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1020 else 1079) else if t 2 = 1 then (if t 3 = 0 then 1026 else if t 3 = 1 then 1018 else 1077) else (if t 3 = 0 then 1050 else if t 3 = 1 then 1045 else 1083)) else (if t 2 = 0 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1082) else if t 2 = 1 then (if t 3 = 0 then 1041 else if t 3 = 1 then 1037 else 1081) else (if t 3 = 0 then 1056 else if t 3 = 1 then 1054 else 1085))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 660 else 4061) else if t 2 = 1 then (if t 3 = 0 then 1518 else if t 3 = 1 then 658 else 1824) else (if t 3 = 0 then 3206 else if t 3 = 1 then 668 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 468 else if t 3 = 1 then 1070 else 1092) else if t 2 = 1 then (if t 3 = 0 then 466 else if t 3 = 1 then 1068 else 1086) else (if t 3 = 0 then 476 else if t 3 = 1 then 1074 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 473 else if t 3 = 1 then 1073 else 1093) else if t 2 = 1 then (if t 3 = 0 then 472 else if t 3 = 1 then 1072 else 1087) else (if t 3 = 0 then 479 else if t 3 = 1 then 1076 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4815 else (if jt.2.val < 2 then 4823 else 4820)) else (if jt.2.val < 4 then 4821 else (if jt.2.val < 5 then 4822 else 4818))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3273 else (if jt.2.val < 2 then 3339 else 3277)) else (if jt.2.val < 4 then 3336 else (if jt.2.val < 5 then 3337 else 3245)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 826 else (if jt.2.val < 2 then 1047 else 831)) else (if jt.2.val < 4 then 1014 else (if jt.2.val < 5 then 1015 else 794))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1016 else (if jt.2.val < 2 then 1059 else 1062)) else (if jt.2.val < 4 then 1058 else (if jt.2.val < 5 then 1061 else 1060)))))

checked_coverage fastCoverage0654 pairing0654 template0654 witness0654

theorem coverage0654 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0654) (maskBits m))
    cores template0654 witness0654 := by
  rw [← coresFast_eq]
  exact fastCoverage0654

theorem coverageSize0654 : ∀ q : Pattern,
    (cores (witness0654 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0654 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0654
#print axioms coverageSize0654

noncomputable def pairing0655 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0655 : List (Fin 4935) := templateData0655

noncomputable def witness0655 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 574 else 1112) else if t 2 = 1 then (if t 3 = 0 then 581 else if t 3 = 1 then 566 else 1108) else (if t 3 = 0 then 591 else if t 3 = 1 then 567 else 1109)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 579 else if t 3 = 1 then 552 else 553) else if t 2 = 1 then (if t 3 = 0 then 577 else if t 3 = 1 then 532 else 535) else (if t 3 = 0 then 589 else if t 3 = 1 then 534 else 536)) else (if t 2 = 0 then (if t 3 = 0 then 3215 else if t 3 = 1 then 3209 else 3342) else if t 2 = 1 then (if t 3 = 0 then 2759 else if t 3 = 1 then 2747 else 2749) else (if t 3 = 0 then 3927 else if t 3 = 1 then 3923 else 4044))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 570 else 1110) else if t 2 = 1 then (if t 3 = 0 then 580 else if t 3 = 1 then 556 else 1104) else (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 1106)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 578 else if t 3 = 1 then 544 else 546) else if t 2 = 1 then (if t 3 = 0 then 576 else if t 3 = 1 then 515 else 520) else (if t 3 = 0 then 588 else if t 3 = 1 then 517 else 522)) else (if t 2 = 0 then (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 547) else if t 2 = 1 then (if t 3 = 0 then 584 else if t 3 = 1 then 516 else 521) else (if t 3 = 0 then 592 else if t 3 = 1 then 518 else 523))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 572 else 3966) else if t 2 = 1 then (if t 3 = 0 then 1836 else if t 3 = 1 then 562 else 1542) else (if t 3 = 0 then 3343 else if t 3 = 1 then 564 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1115 else if t 3 = 1 then 548 else 550) else if t 2 = 1 then (if t 3 = 0 then 1113 else if t 3 = 1 then 524 else 528) else (if t 3 = 0 then 1119 else if t 3 = 1 then 526 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 1118 else if t 3 = 1 then 549 else 551) else if t 2 = 1 then (if t 3 = 0 then 1117 else if t 3 = 1 then 525 else 529) else (if t 3 = 0 then 1121 else if t 3 = 1 then 527 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4809 else (if jt.2.val < 2 then 4825 else 4814)) else (if jt.2.val < 4 then 4824 else (if jt.2.val < 5 then 4826 else 4811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3122 else (if jt.2.val < 2 then 3212 else 3143)) else (if jt.2.val < 4 then 3211 else (if jt.2.val < 5 then 3213 else 3113)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 120 else (if jt.2.val < 2 then 542 else 149)) else (if jt.2.val < 4 then 541 else (if jt.2.val < 5 then 543 else 111))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1060 else (if jt.2.val < 2 then 1100 else 1062)) else (if jt.2.val < 4 then 1098 else (if jt.2.val < 5 then 1099 else 1016)))))

checked_coverage fastCoverage0655 pairing0655 template0655 witness0655

theorem coverage0655 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0655) (maskBits m))
    cores template0655 witness0655 := by
  rw [← coresFast_eq]
  exact fastCoverage0655

theorem coverageSize0655 : ∀ q : Pattern,
    (cores (witness0655 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0655 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0655
#print axioms coverageSize0655

noncomputable def pairing0656 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0656 : List (Fin 4935) := templateData0656

noncomputable def witness0656 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 3959) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3227) else (if t 3 = 0 then 3352 else if t 3 = 1 then 3351 else 2501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1611) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1610) else (if t 3 = 0 then 1882 else if t 3 = 1 then 1880 else 1619)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2199 else 299) else if t 2 = 1 then (if t 3 = 0 then 2200 else if t 3 = 1 then 2198 else 1616) else (if t 3 = 0 then 1190 else if t 3 = 1 then 1892 else 1622))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1443) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1442) else (if t 3 = 0 then 1723 else if t 3 = 1 then 1721 else 1451)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3161) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4514) else (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4516)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3465 else 3164) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4515) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4499 else 4517))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1331 else 1223) else if t 2 = 1 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1330 else 1778) else (if t 3 = 0 then 262 else if t 3 = 1 then 1355 else 2120)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3074 else 3314) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4518) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4507 else 4520)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 3084 else 3316) else if t 2 = 1 then (if t 3 = 0 then 3838 else if t 3 = 1 then 4506 else 4519) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4513 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4836 else (if jt.2.val < 2 then 4840 else 4841)) else (if jt.2.val < 4 then 4837 else (if jt.2.val < 5 then 4839 else 4838))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4711 else (if jt.2.val < 2 then 4715 else 4716)) else (if jt.2.val < 4 then 4712 else (if jt.2.val < 5 then 4714 else 4713)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4576 else (if jt.2.val < 2 then 4580 else 4581)) else (if jt.2.val < 4 then 4577 else (if jt.2.val < 5 then 4579 else 4578))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4467 else (if jt.2.val < 2 then 4509 else 4512)) else (if jt.2.val < 4 then 4508 else (if jt.2.val < 5 then 4511 else 4510)))))

checked_coverage fastCoverage0656 pairing0656 template0656 witness0656

theorem coverage0656 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0656) (maskBits m))
    cores template0656 witness0656 := by
  rw [← coresFast_eq]
  exact fastCoverage0656

theorem coverageSize0656 : ∀ q : Pattern,
    (cores (witness0656 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0656 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0656
#print axioms coverageSize0656

noncomputable def pairing0657 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0657 : List (Fin 4935) := templateData0657

noncomputable def witness0657 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4525) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 3225) else (if t 3 = 0 then 2741 else if t 3 = 1 then 2737 else 3344)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 1597) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 1593) else (if t 3 = 0 then 490 else if t 3 = 1 then 462 else 464)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 667 else 2170) else if t 2 = 1 then (if t 3 = 0 then 682 else if t 3 = 1 then 654 else 656) else (if t 3 = 0 then 1526 else if t 3 = 1 then 1132 else 1134))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 1429) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 1424) else (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 366)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 3146) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3875) else (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3881)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2551) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3878) else (if t 3 = 0 then 3919 else if t 3 = 1 then 3882 else 3883))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 994 else 1431) else if t 2 = 1 then (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 990) else (if t 3 = 0 then 2141 else if t 3 = 1 then 368 else 370)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2950) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3885) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3888 else 3889)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2555 else 2557) else if t 2 = 1 then (if t 3 = 0 then 4039 else if t 3 = 1 then 3886 else 3887) else (if t 3 = 0 then 4526 else if t 3 = 1 then 3890 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4815 else (if jt.2.val < 2 then 4817 else 4820)) else (if jt.2.val < 4 then 4816 else (if jt.2.val < 5 then 4819 else 4818))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3867 else (if jt.2.val < 2 then 3869 else 3897)) else (if jt.2.val < 4 then 3868 else (if jt.2.val < 5 then 3896 else 3876)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3864 else (if jt.2.val < 2 then 3866 else 3901)) else (if jt.2.val < 4 then 3865 else (if jt.2.val < 5 then 3900 else 3879))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4510 else (if jt.2.val < 2 then 4524 else 4512)) else (if jt.2.val < 4 then 4522 else (if jt.2.val < 5 then 4523 else 4467)))))

checked_coverage fastCoverage0657 pairing0657 template0657 witness0657

theorem coverage0657 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0657) (maskBits m))
    cores template0657 witness0657 := by
  rw [← coresFast_eq]
  exact fastCoverage0657

theorem coverageSize0657 : ∀ q : Pattern,
    (cores (witness0657 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0657 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0657
#print axioms coverageSize0657

noncomputable def pairing0658 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0658 : List (Fin 4935) := templateData0658

noncomputable def witness0658 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3258 else 2798) else if t 2 = 1 then (if t 3 = 0 then 3254 else if t 3 = 1 then 3250 else 2797) else (if t 3 = 0 then 4537 else if t 3 = 1 then 4064 else 3943)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3256 else 88) else if t 2 = 1 then (if t 3 = 0 then 3252 else if t 3 = 1 then 3248 else 86) else (if t 3 = 0 then 1879 else if t 3 = 1 then 1877 else 94)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 965 else 1478) else if t 2 = 1 then (if t 3 = 0 then 962 else if t 3 = 1 then 961 else 100) else (if t 3 = 0 then 2138 else if t 3 = 1 then 978 else 104))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3257 else 775) else if t 2 = 1 then (if t 3 = 0 then 3253 else if t 3 = 1 then 3249 else 773) else (if t 3 = 0 then 1720 else if t 3 = 1 then 1718 else 781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3255 else 3165) else if t 2 = 1 then (if t 3 = 0 then 3251 else if t 3 = 1 then 3247 else 3295) else (if t 3 = 0 then 3269 else if t 3 = 1 then 3267 else 3296)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 3278 else 3167) else if t 2 = 1 then (if t 3 = 0 then 2837 else if t 3 = 1 then 3276 else 3297) else (if t 3 = 0 then 2841 else if t 3 = 1 then 3279 else 3298))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 638 else 2162) else if t 2 = 1 then (if t 3 = 0 then 637 else if t 3 = 1 then 636 else 1141) else (if t 3 = 0 then 1464 else if t 3 = 1 then 651 else 1143)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 3091 else 3500) else if t 2 = 1 then (if t 3 = 0 then 2623 else if t 3 = 1 then 3291 else 3299) else (if t 3 = 0 then 2627 else if t 3 = 1 then 3292 else 3300)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 3095 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2637 else if t 3 = 1 then 3293 else 3301) else (if t 3 = 0 then 2639 else if t 3 = 1 then 3294 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4755 else (if jt.2.val < 2 then 4759 else 4760)) else (if jt.2.val < 4 then 4756 else (if jt.2.val < 5 then 4758 else 4757))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3245 else (if jt.2.val < 2 then 3275 else 3277)) else (if jt.2.val < 4 then 3272 else (if jt.2.val < 5 then 3274 else 3273)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4578 else (if jt.2.val < 2 then 4589 else 4581)) else (if jt.2.val < 4 then 4587 else (if jt.2.val < 5 then 4588 else 4576))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3357 else (if jt.2.val < 2 then 3363 else 3368)) else (if jt.2.val < 4 then 3362 else (if jt.2.val < 5 then 3367 else 3366)))))

checked_coverage fastCoverage0658 pairing0658 template0658 witness0658

theorem coverage0658 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0658) (maskBits m))
    cores template0658 witness0658 := by
  rw [← coresFast_eq]
  exact fastCoverage0658

theorem coverageSize0658 : ∀ q : Pattern,
    (cores (witness0658 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0658 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0658
#print axioms coverageSize0658

noncomputable def pairing0659 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0659 : List (Fin 4935) := templateData0659

noncomputable def witness0659 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2705 else 3312) else if t 2 = 1 then (if t 3 = 0 then 2710 else if t 3 = 1 then 2688 else 3191) else (if t 3 = 0 then 3935 else if t 3 = 1 then 3929 else 4539)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2703 else 73) else if t 2 = 1 then (if t 3 = 0 then 2708 else if t 3 = 1 then 2682 else 43) else (if t 3 = 0 then 489 else if t 3 = 1 then 445 else 1507)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1357 else 922) else if t 2 = 1 then (if t 3 = 0 then 1371 else if t 3 = 1 then 1339 else 46) else (if t 3 = 0 then 503 else if t 3 = 1 then 448 else 2125))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2704 else 760) else if t 2 = 1 then (if t 3 = 0 then 2709 else if t 3 = 1 then 2685 else 733) else (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 1484)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2695 else 2697) else if t 2 = 1 then (if t 3 = 0 then 2707 else if t 3 = 1 then 2664 else 2668) else (if t 3 = 0 then 2715 else if t 3 = 1 then 2666 else 2669)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2878 else 2880) else if t 2 = 1 then (if t 3 = 0 then 2721 else if t 3 = 1 then 2670 else 2672) else (if t 3 = 0 then 2723 else if t 3 = 1 then 2671 else 2673))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2218 else 762) else if t 2 = 1 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2212 else 737) else (if t 3 = 0 then 931 else if t 3 = 1 then 353 else 1488)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2699 else 2701) else if t 2 = 1 then (if t 3 = 0 then 2902 else if t 3 = 1 then 2674 else 2676) else (if t 3 = 0 then 2903 else if t 3 = 1 then 2675 else 2677)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3196 else 3934) else if t 2 = 1 then (if t 3 = 0 then 3321 else if t 3 = 1 then 2678 else 2680) else (if t 3 = 0 then 3322 else if t 3 = 1 then 2679 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4797 else (if jt.2.val < 2 then 4799 else 4802)) else (if jt.2.val < 4 then 4798 else (if jt.2.val < 5 then 4801 else 4800))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3185 else (if jt.2.val < 2 then 3187 else 3190)) else (if jt.2.val < 4 then 3186 else (if jt.2.val < 5 then 3189 else 3188)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3879 else (if jt.2.val < 2 then 3932 else 3901)) else (if jt.2.val < 4 then 3931 else (if jt.2.val < 5 then 3933 else 3864))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3366 else (if jt.2.val < 2 then 3380 else 3368)) else (if jt.2.val < 4 then 3378 else (if jt.2.val < 5 then 3379 else 3357)))))

checked_coverage fastCoverage0659 pairing0659 template0659 witness0659

theorem coverage0659 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0659) (maskBits m))
    cores template0659 witness0659 := by
  rw [← coresFast_eq]
  exact fastCoverage0659

theorem coverageSize0659 : ∀ q : Pattern,
    (cores (witness0659 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0659 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0659
#print axioms coverageSize0659

noncomputable def pairing0660 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0660 : List (Fin 4935) := templateData0660

noncomputable def witness0660 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2058 else 591) else if t 2 = 1 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2056 else 1447) else (if t 3 = 0 then 837 else if t 3 = 1 then 1733 else 1453)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2054 else if t 3 = 1 then 2050 else 589) else if t 2 = 1 then (if t 3 = 0 then 2052 else if t 3 = 1 then 2048 else 2101) else (if t 3 = 0 then 835 else if t 3 = 1 then 2082 else 2104)) else (if t 2 = 0 then (if t 3 = 0 then 4546 else if t 3 = 1 then 4211 else 3927) else if t 2 = 1 then (if t 3 = 0 then 3530 else if t 3 = 1 then 3528 else 2648) else (if t 3 = 0 then 3330 else if t 3 = 1 then 2939 else 2654))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2057 else 590) else if t 2 = 1 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2055 else 1446) else (if t 3 = 0 then 836 else if t 3 = 1 then 1732 else 1452)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2053 else if t 3 = 1 then 2049 else 588) else if t 2 = 1 then (if t 3 = 0 then 2051 else if t 3 = 1 then 2047 else 2100) else (if t 3 = 0 then 834 else if t 3 = 1 then 2081 else 2103)) else (if t 2 = 0 then (if t 3 = 0 then 2071 else if t 3 = 1 then 2069 else 592) else if t 2 = 1 then (if t 3 = 0 then 2070 else if t 3 = 1 then 2067 else 2102) else (if t 3 = 0 then 840 else if t 3 = 1 then 2083 else 2105))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 451 else 3343) else if t 2 = 1 then (if t 3 = 0 then 49 else if t 3 = 1 then 1341 else 1779) else (if t 3 = 0 then 3942 else if t 3 = 1 then 1358 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1509 else if t 3 = 1 then 449 else 1119) else if t 2 = 1 then (if t 3 = 0 then 47 else if t 3 = 1 then 2089 else 2106) else (if t 3 = 0 then 74 else if t 3 = 1 then 2097 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 1512 else if t 3 = 1 then 455 else 1121) else if t 2 = 1 then (if t 3 = 0 then 53 else if t 3 = 1 then 2091 else 2108) else (if t 3 = 0 then 77 else if t 3 = 1 then 2099 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4797 else (if jt.2.val < 2 then 4805 else 4802)) else (if jt.2.val < 4 then 4803 else (if jt.2.val < 5 then 4804 else 4800))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4713 else (if jt.2.val < 2 then 4724 else 4716)) else (if jt.2.val < 4 then 4722 else (if jt.2.val < 5 then 4723 else 4711)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2045 else (if jt.2.val < 2 then 2079 else 2080)) else (if jt.2.val < 4 then 2076 else (if jt.2.val < 5 then 2078 else 2077))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2232 else (if jt.2.val < 2 then 2240 else 2243)) else (if jt.2.val < 4 then 2239 else (if jt.2.val < 5 then 2242 else 2241)))))

checked_coverage fastCoverage0660 pairing0660 template0660 witness0660

theorem coverage0660 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0660) (maskBits m))
    cores template0660 witness0660 := by
  rw [← coresFast_eq]
  exact fastCoverage0660

theorem coverageSize0660 : ∀ q : Pattern,
    (cores (witness0660 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0660 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0660
#print axioms coverageSize0660

noncomputable def pairing0661 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0661 : List (Fin 4935) := templateData0661

noncomputable def witness0661 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 178 else 2117) else if t 2 = 1 then (if t 3 = 0 then 185 else if t 3 = 1 then 170 else 171) else (if t 3 = 0 then 1501 else if t 3 = 1 then 892 else 893)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 183 else if t 3 = 1 then 156 else 1537) else if t 2 = 1 then (if t 3 = 0 then 181 else if t 3 = 1 then 136 else 139) else (if t 3 = 0 then 199 else if t 3 = 1 then 140 else 141)) else (if t 2 = 0 then (if t 3 = 0 then 3951 else if t 3 = 1 then 3945 else 4541) else if t 2 = 1 then (if t 3 = 0 then 2778 else if t 3 = 1 then 2766 else 3172) else (if t 3 = 0 then 2781 else if t 3 = 1 then 2768 else 3320))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 174 else 2115) else if t 2 = 1 then (if t 3 = 0 then 184 else if t 3 = 1 then 160 else 162) else (if t 3 = 0 then 1500 else if t 3 = 1 then 888 else 890)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 182 else if t 3 = 1 then 146 else 1531) else if t 2 = 1 then (if t 3 = 0 then 180 else if t 3 = 1 then 117 else 121) else (if t 3 = 0 then 198 else if t 3 = 1 then 124 else 126)) else (if t 2 = 0 then (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 1532) else if t 2 = 1 then (if t 3 = 0 then 188 else if t 3 = 1 then 119 else 122) else (if t 3 = 0 then 202 else if t 3 = 1 then 125 else 127))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 176 else 2758) else if t 2 = 1 then (if t 3 = 0 then 1806 else if t 3 = 1 then 166 else 168) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1494 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 899 else if t 3 = 1 then 152 else 1535) else if t 2 = 1 then (if t 3 = 0 then 897 else if t 3 = 1 then 128 else 130) else (if t 3 = 0 then 2127 else if t 3 = 1 then 132 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 902 else if t 3 = 1 then 153 else 1536) else if t 2 = 1 then (if t 3 = 0 then 901 else if t 3 = 1 then 129 else 131) else (if t 3 = 0 then 2128 else if t 3 = 1 then 133 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4755 else (if jt.2.val < 2 then 4789 else 4760)) else (if jt.2.val < 4 then 4788 else (if jt.2.val < 5 then 4790 else 4757))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3876 else (if jt.2.val < 2 then 3948 else 3897)) else (if jt.2.val < 4 then 3947 else (if jt.2.val < 5 then 3949 else 3867)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2004 else (if jt.2.val < 2 then 2006 else 2009)) else (if jt.2.val < 4 then 2005 else (if jt.2.val < 5 then 2008 else 2007))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2241 else (if jt.2.val < 2 then 2249 else 2243)) else (if jt.2.val < 4 then 2247 else (if jt.2.val < 5 then 2248 else 2232)))))

checked_coverage fastCoverage0661 pairing0661 template0661 witness0661

theorem coverage0661 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0661) (maskBits m))
    cores template0661 witness0661 := by
  rw [← coresFast_eq]
  exact fastCoverage0661

theorem coverageSize0661 : ∀ q : Pattern,
    (cores (witness0661 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0661 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0661
#print axioms coverageSize0661

noncomputable def pairing0662 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 3)))) (by decide +kernel)

noncomputable def template0662 : List (Fin 4935) := templateData0662

noncomputable def witness0662 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1031 else 1549) else if t 2 = 1 then (if t 3 = 0 then 1025 else if t 3 = 1 then 1023 else 784) else (if t 3 = 0 then 2146 else if t 3 = 1 then 1049 else 790)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1027 else 595) else if t 2 = 1 then (if t 3 = 0 then 1021 else if t 3 = 1 then 1019 else 1078) else (if t 3 = 0 then 1813 else if t 3 = 1 then 1046 else 1084)) else (if t 2 = 0 then (if t 3 = 0 then 3340 else if t 3 = 1 then 2973 else 2762) else if t 2 = 1 then (if t 3 = 0 then 3338 else if t 3 = 1 then 2970 else 2980) else (if t 3 = 0 then 4532 else if t 3 = 1 then 4046 else 3860))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1030 else 1548) else if t 2 = 1 then (if t 3 = 0 then 1024 else if t 3 = 1 then 1022 else 783) else (if t 3 = 0 then 2145 else if t 3 = 1 then 1048 else 789)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1026 else 594) else if t 2 = 1 then (if t 3 = 0 then 1020 else if t 3 = 1 then 1018 else 1077) else (if t 3 = 0 then 1812 else if t 3 = 1 then 1045 else 1083)) else (if t 2 = 0 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1041 else 598) else if t 2 = 1 then (if t 3 = 0 then 1038 else if t 3 = 1 then 1037 else 1081) else (if t 3 = 0 then 1817 else if t 3 = 1 then 1054 else 1085))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 1518 else 4542) else if t 2 = 1 then (if t 3 = 0 then 660 else if t 3 = 1 then 658 else 1824) else (if t 3 = 0 then 2777 else if t 3 = 1 then 668 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 468 else if t 3 = 1 then 466 else 2148) else if t 2 = 1 then (if t 3 = 0 then 1070 else if t 3 = 1 then 1068 else 1086) else (if t 3 = 0 then 1598 else if t 3 = 1 then 1074 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 473 else if t 3 = 1 then 472 else 2149) else if t 2 = 1 then (if t 3 = 0 then 1073 else if t 3 = 1 then 1072 else 1087) else (if t 3 = 0 then 1601 else if t 3 = 1 then 1076 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4815 else (if jt.2.val < 2 then 4823 else 4820)) else (if jt.2.val < 4 then 4821 else (if jt.2.val < 5 then 4822 else 4818))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3273 else (if jt.2.val < 2 then 3339 else 3277)) else (if jt.2.val < 4 then 3336 else (if jt.2.val < 5 then 3337 else 3245)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2077 else (if jt.2.val < 2 then 2144 else 2080)) else (if jt.2.val < 4 then 2142 else (if jt.2.val < 5 then 2143 else 2045))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1944 else (if jt.2.val < 2 then 1946 else 1949)) else (if jt.2.val < 4 then 1945 else (if jt.2.val < 5 then 1948 else 1947)))))

checked_coverage fastCoverage0662 pairing0662 template0662 witness0662

theorem coverage0662 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0662) (maskBits m))
    cores template0662 witness0662 := by
  rw [← coresFast_eq]
  exact fastCoverage0662

theorem coverageSize0662 : ∀ q : Pattern,
    (cores (witness0662 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0662 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0662
#print axioms coverageSize0662

noncomputable def pairing0663 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 7)))) (by decide +kernel)

noncomputable def template0663 : List (Fin 4935) := templateData0663

noncomputable def witness0663 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1675 else 1112) else if t 2 = 1 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1660 else 741) else (if t 3 = 0 then 402 else if t 3 = 1 then 357 else 2159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1669 else 553) else if t 2 = 1 then (if t 3 = 0 then 1678 else if t 3 = 1 then 1644 else 1647) else (if t 3 = 0 then 864 else if t 3 = 1 then 1646 else 1648)) else (if t 2 = 0 then (if t 3 = 0 then 2577 else if t 3 = 1 then 2545 else 3342) else if t 2 = 1 then (if t 3 = 0 then 2860 else if t 3 = 1 then 3232 else 3234) else (if t 3 = 0 then 3967 else if t 3 = 1 then 3963 else 4530))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1671 else 1110) else if t 2 = 1 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1656 else 734) else (if t 3 = 0 then 401 else if t 3 = 1 then 350 else 2157)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1665 else 546) else if t 2 = 1 then (if t 3 = 0 then 1677 else if t 3 = 1 then 1628 else 1632) else (if t 3 = 0 then 863 else if t 3 = 1 then 1630 else 1634)) else (if t 2 = 0 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1666 else 547) else if t 2 = 1 then (if t 3 = 0 then 1685 else if t 3 = 1 then 1629 else 1633) else (if t 3 = 0 then 866 else if t 3 = 1 then 1631 else 1635))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1673 else 3966) else if t 2 = 1 then (if t 3 = 0 then 1854 else if t 3 = 1 then 1658 else 738) else (if t 3 = 0 then 3345 else if t 3 = 1 then 354 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2172 else if t 3 = 1 then 1667 else 550) else if t 2 = 1 then (if t 3 = 0 then 1851 else if t 3 = 1 then 1636 else 1640) else (if t 3 = 0 then 876 else if t 3 = 1 then 1638 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 2173 else if t 3 = 1 then 1668 else 551) else if t 2 = 1 then (if t 3 = 0 then 1852 else if t 3 = 1 then 1637 else 1641) else (if t 3 = 0 then 877 else if t 3 = 1 then 1639 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4836 else (if jt.2.val < 2 then 4843 else 4841)) else (if jt.2.val < 4 then 4842 else (if jt.2.val < 5 then 4844 else 4838))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3188 else (if jt.2.val < 2 then 3238 else 3190)) else (if jt.2.val < 4 then 3237 else (if jt.2.val < 5 then 3239 else 3185)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2007 else (if jt.2.val < 2 then 2041 else 2009)) else (if jt.2.val < 4 then 2040 else (if jt.2.val < 5 then 2042 else 2004))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1947 else (if jt.2.val < 2 then 1964 else 1949)) else (if jt.2.val < 4 then 1959 else (if jt.2.val < 5 then 1960 else 1944)))))

checked_coverage fastCoverage0663 pairing0663 template0663 witness0663

theorem coverage0663 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0663) (maskBits m))
    cores template0663 witness0663 := by
  rw [← coresFast_eq]
  exact fastCoverage0663

theorem coverageSize0663 : ∀ q : Pattern,
    (cores (witness0663 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0663 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0663
#print axioms coverageSize0663

noncomputable def pairing0664 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0664 : List (Fin 4935) := templateData0664

noncomputable def witness0664 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 4066) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3351) else (if t 3 = 0 then 3228 else if t 3 = 1 then 3227 else 2501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1881) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1880) else (if t 3 = 0 then 1612 else if t 3 = 1 then 1610 else 1619)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2199 else 980) else if t 2 = 1 then (if t 3 = 0 then 2200 else if t 3 = 1 then 2198 else 1892) else (if t 3 = 0 then 689 else if t 3 = 1 then 1616 else 1622))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1722) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1721) else (if t 3 = 0 then 1444 else if t 3 = 1 then 1442 else 1451)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3270) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4498) else (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4516)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3465 else 3280) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4499) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4515 else 4517))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1331 else 652) else if t 2 = 1 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1330 else 1355) else (if t 3 = 0 then 1013 else if t 3 = 1 then 1778 else 2120)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3074 else 3093) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4507) else (if t 3 = 0 then 4038 else if t 3 = 1 then 4518 else 4520)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 3084 else 3097) else if t 2 = 1 then (if t 3 = 0 then 3838 else if t 3 = 1 then 4506 else 4513) else (if t 3 = 0 then 4040 else if t 3 = 1 then 4519 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4836 else (if jt.2.val < 2 then 4840 else 4841)) else (if jt.2.val < 4 then 4837 else (if jt.2.val < 5 then 4839 else 4838))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4711 else (if jt.2.val < 2 then 4715 else 4716)) else (if jt.2.val < 4 then 4712 else (if jt.2.val < 5 then 4714 else 4713)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4548 else (if jt.2.val < 2 then 4556 else 4559)) else (if jt.2.val < 4 then 4555 else (if jt.2.val < 5 then 4558 else 4557))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4593 else (if jt.2.val < 2 then 4597 else 4598)) else (if jt.2.val < 4 then 4594 else (if jt.2.val < 5 then 4596 else 4595)))))

checked_coverage fastCoverage0664 pairing0664 template0664 witness0664

theorem coverage0664 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0664) (maskBits m))
    cores template0664 witness0664 := by
  rw [← coresFast_eq]
  exact fastCoverage0664

theorem coverageSize0664 : ∀ q : Pattern,
    (cores (witness0664 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0664 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0664
#print axioms coverageSize0664

noncomputable def pairing0665 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0665 : List (Fin 4935) := templateData0665

noncomputable def witness0665 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 4537) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 3350) else (if t 3 = 0 then 2741 else if t 3 = 1 then 2740 else 3207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 1879) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 1878) else (if t 3 = 0 then 490 else if t 3 = 1 then 488 else 496)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1171 else 2138) else if t 2 = 1 then (if t 3 = 0 then 1174 else if t 3 = 1 then 1170 else 1188) else (if t 3 = 0 then 1526 else if t 3 = 1 then 502 else 506))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 1720) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 1719) else (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 397)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 3269) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 3993) else (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4020)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2841) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4003) else (if t 3 = 0 then 3919 else if t 3 = 1 then 4021 else 4022))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 243 else 1464) else if t 2 = 1 then (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 261) else (if t 3 = 0 then 2141 else if t 3 = 1 then 925 else 927)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2627) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4016) else (if t 3 = 0 then 4191 else if t 3 = 1 then 4023 else 4024)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2635 else 2639) else if t 2 = 1 then (if t 3 = 0 then 3849 else if t 3 = 1 then 4017 else 4018) else (if t 3 = 0 then 4526 else if t 3 = 1 then 4025 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4809 else (if jt.2.val < 2 then 4813 else 4814)) else (if jt.2.val < 4 then 4810 else (if jt.2.val < 5 then 4812 else 4811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3971 else (if jt.2.val < 2 then 3999 else 4001)) else (if jt.2.val < 4 then 3996 else (if jt.2.val < 5 then 3998 else 3997)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4068 else (if jt.2.val < 2 then 4074 else 4079)) else (if jt.2.val < 4 then 4073 else (if jt.2.val < 5 then 4078 else 4077))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4595 else (if jt.2.val < 2 then 4601 else 4598)) else (if jt.2.val < 4 then 4599 else (if jt.2.val < 5 then 4600 else 4593)))))

checked_coverage fastCoverage0665 pairing0665 template0665 witness0665

theorem coverage0665 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0665) (maskBits m))
    cores template0665 witness0665 := by
  rw [← coresFast_eq]
  exact fastCoverage0665

theorem coverageSize0665 : ∀ q : Pattern,
    (cores (witness0665 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0665 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0665
#print axioms coverageSize0665

noncomputable def pairing0666 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0666 : List (Fin 4935) := templateData0666

noncomputable def witness0666 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3156 else 2798) else if t 2 = 1 then (if t 3 = 0 then 3151 else if t 3 = 1 then 3144 else 2794) else (if t 3 = 0 then 4525 else if t 3 = 1 then 3953 else 4060)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3154 else 88) else if t 2 = 1 then (if t 3 = 0 then 3149 else if t 3 = 1 then 3138 else 60) else (if t 3 = 0 then 1597 else if t 3 = 1 then 1589 else 62)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 292 else 1478) else if t 2 = 1 then (if t 3 = 0 then 277 else if t 3 = 1 then 264 else 916) else (if t 3 = 0 then 2170 else if t 3 = 1 then 266 else 918))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3155 else 775) else if t 2 = 1 then (if t 3 = 0 then 3150 else if t 3 = 1 then 3141 else 748) else (if t 3 = 0 then 1429 else if t 3 = 1 then 1419 else 750)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3153 else 3165) else if t 2 = 1 then (if t 3 = 0 then 3145 else if t 3 = 1 then 3119 else 3126) else (if t 3 = 0 then 3146 else if t 3 = 1 then 3121 else 3127)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 3163 else 3167) else if t 2 = 1 then (if t 3 = 0 then 2550 else if t 3 = 1 then 3123 else 3128) else (if t 3 = 0 then 2551 else if t 3 = 1 then 3124 else 3129))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1219 else 2162) else if t 2 = 1 then (if t 3 = 0 then 1204 else if t 3 = 1 then 1198 else 752) else (if t 3 = 0 then 1431 else if t 3 = 1 then 1200 else 754)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 3313 else 3500) else if t 2 = 1 then (if t 3 = 0 then 2949 else if t 3 = 1 then 3130 else 3134) else (if t 3 = 0 then 2950 else if t 3 = 1 then 3131 else 3135)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 3315 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2556 else if t 3 = 1 then 3132 else 3136) else (if t 3 = 0 then 2557 else if t 3 = 1 then 3133 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4761 else (if jt.2.val < 2 then 4763 else 4766)) else (if jt.2.val < 4 then 4762 else (if jt.2.val < 5 then 4765 else 4764))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3113 else (if jt.2.val < 2 then 3115 else 3143)) else (if jt.2.val < 4 then 3114 else (if jt.2.val < 5 then 3142 else 3122)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4557 else (if jt.2.val < 2 then 4565 else 4559)) else (if jt.2.val < 4 then 4563 else (if jt.2.val < 5 then 4564 else 4548))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3110 else (if jt.2.val < 2 then 3112 else 3148)) else (if jt.2.val < 4 then 3111 else (if jt.2.val < 5 then 3147 else 3125)))))

checked_coverage fastCoverage0666 pairing0666 template0666 witness0666

theorem coverage0666 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0666) (maskBits m))
    cores template0666 witness0666 := by
  rw [← coresFast_eq]
  exact fastCoverage0666

theorem coverageSize0666 : ∀ q : Pattern,
    (cores (witness0666 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0666 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0666
#print axioms coverageSize0666

noncomputable def pairing0667 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0667 : List (Fin 4935) := templateData0667

noncomputable def witness0667 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2710 else 3198) else if t 2 = 1 then (if t 3 = 0 then 2705 else if t 3 = 1 then 2688 else 3191) else (if t 3 = 0 then 4036 else if t 3 = 1 then 3929 else 4539)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2708 else 87) else if t 2 = 1 then (if t 3 = 0 then 2703 else if t 3 = 1 then 2682 else 43) else (if t 3 = 0 then 475 else if t 3 = 1 then 445 else 1507)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1371 else 101) else if t 2 = 1 then (if t 3 = 0 then 1357 else if t 3 = 1 then 1339 else 46) else (if t 3 = 0 then 1138 else if t 3 = 1 then 448 else 2125))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2709 else 774) else if t 2 = 1 then (if t 3 = 0 then 2704 else if t 3 = 1 then 2685 else 733) else (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 1484)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2707 else 2717) else if t 2 = 1 then (if t 3 = 0 then 2695 else if t 3 = 1 then 2664 else 2668) else (if t 3 = 0 then 2696 else if t 3 = 1 then 2666 else 2669)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2721 else 2724) else if t 2 = 1 then (if t 3 = 0 then 2878 else if t 3 = 1 then 2670 else 2672) else (if t 3 = 0 then 2879 else if t 3 = 1 then 2671 else 2673))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2227 else 1147) else if t 2 = 1 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2212 else 737) else (if t 3 = 0 then 378 else if t 3 = 1 then 353 else 1488)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2902 else 2904) else if t 2 = 1 then (if t 3 = 0 then 2699 else if t 3 = 1 then 2674 else 2676) else (if t 3 = 0 then 2700 else if t 3 = 1 then 2675 else 2677)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3321 else 4045) else if t 2 = 1 then (if t 3 = 0 then 3196 else if t 3 = 1 then 2678 else 2680) else (if t 3 = 0 then 3197 else if t 3 = 1 then 2679 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4797 else (if jt.2.val < 2 then 4799 else 4802)) else (if jt.2.val < 4 then 4798 else (if jt.2.val < 5 then 4801 else 4800))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3185 else (if jt.2.val < 2 then 3187 else 3190)) else (if jt.2.val < 4 then 3186 else (if jt.2.val < 5 then 3189 else 3188)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4077 else (if jt.2.val < 2 then 4091 else 4079)) else (if jt.2.val < 4 then 4089 else (if jt.2.val < 5 then 4090 else 4068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3125 else (if jt.2.val < 2 then 3194 else 3148)) else (if jt.2.val < 4 then 3193 else (if jt.2.val < 5 then 3195 else 3110)))))

checked_coverage fastCoverage0667 pairing0667 template0667 witness0667

theorem coverage0667 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0667) (maskBits m))
    cores template0667 witness0667 := by
  rw [← coresFast_eq]
  exact fastCoverage0667

theorem coverageSize0667 : ∀ q : Pattern,
    (cores (witness0667 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0667 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0667
#print axioms coverageSize0667

noncomputable def pairing0668 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0668 : List (Fin 4935) := templateData0668

noncomputable def witness0668 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2058 else 1053) else if t 2 = 1 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2056 else 1733) else (if t 3 = 0 then 195 else if t 3 = 1 then 1447 else 1453)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2054 else if t 3 = 1 then 2050 else 1051) else if t 2 = 1 then (if t 3 = 0 then 2052 else if t 3 = 1 then 2048 else 2082) else (if t 3 = 0 then 193 else if t 3 = 1 then 2101 else 2104)) else (if t 2 = 0 then (if t 3 = 0 then 4546 else if t 3 = 1 then 4211 else 4047) else if t 2 = 1 then (if t 3 = 0 then 3530 else if t 3 = 1 then 3528 else 2939) else (if t 3 = 0 then 3182 else if t 3 = 1 then 2648 else 2654))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2057 else 1052) else if t 2 = 1 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2055 else 1732) else (if t 3 = 0 then 194 else if t 3 = 1 then 1446 else 1452)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2053 else if t 3 = 1 then 2049 else 1050) else if t 2 = 1 then (if t 3 = 0 then 2051 else if t 3 = 1 then 2047 else 2081) else (if t 3 = 0 then 192 else if t 3 = 1 then 2100 else 2103)) else (if t 2 = 0 then (if t 3 = 0 then 2071 else if t 3 = 1 then 2069 else 1056) else if t 2 = 1 then (if t 3 = 0 then 2070 else if t 3 = 1 then 2067 else 2083) else (if t 3 = 0 then 196 else if t 3 = 1 then 2102 else 2105))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 451 else 3206) else if t 2 = 1 then (if t 3 = 0 then 49 else if t 3 = 1 then 1341 else 1358) else (if t 3 = 0 then 4059 else if t 3 = 1 then 1779 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1509 else if t 3 = 1 then 449 else 476) else if t 2 = 1 then (if t 3 = 0 then 47 else if t 3 = 1 then 2089 else 2097) else (if t 3 = 0 then 903 else if t 3 = 1 then 2106 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 1512 else if t 3 = 1 then 455 else 479) else if t 2 = 1 then (if t 3 = 0 then 53 else if t 3 = 1 then 2091 else 2099) else (if t 3 = 0 then 905 else if t 3 = 1 then 2108 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4797 else (if jt.2.val < 2 then 4805 else 4802)) else (if jt.2.val < 4 then 4803 else (if jt.2.val < 5 then 4804 else 4800))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4713 else (if jt.2.val < 2 then 4724 else 4716)) else (if jt.2.val < 4 then 4722 else (if jt.2.val < 5 then 4723 else 4711)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2412 else (if jt.2.val < 2 then 2414 else 2417)) else (if jt.2.val < 4 then 2413 else (if jt.2.val < 5 then 2416 else 2415))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2323 else (if jt.2.val < 2 then 2327 else 2328)) else (if jt.2.val < 4 then 2324 else (if jt.2.val < 5 then 2326 else 2325)))))

checked_coverage fastCoverage0668 pairing0668 template0668 witness0668

theorem coverage0668 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0668) (maskBits m))
    cores template0668 witness0668 := by
  rw [← coresFast_eq]
  exact fastCoverage0668

theorem coverageSize0668 : ∀ q : Pattern,
    (cores (witness0668 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0668 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0668
#print axioms coverageSize0668

noncomputable def pairing0669 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0669 : List (Fin 4935) := templateData0669

noncomputable def witness0669 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 803 else 2146) else if t 2 = 1 then (if t 3 = 0 then 809 else if t 3 = 1 then 801 else 833) else (if t 3 = 0 then 1501 else if t 3 = 1 then 400 else 406)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 807 else if t 3 = 1 then 799 else 1813) else if t 2 = 1 then (if t 3 = 0 then 805 else if t 3 = 1 then 797 else 830) else (if t 3 = 0 then 199 else if t 3 = 1 then 862 else 868)) else (if t 2 = 0 then (if t 3 = 0 then 4056 else if t 3 = 1 then 4054 else 4532) else if t 2 = 1 then (if t 3 = 0 then 2996 else if t 3 = 1 then 2993 else 3329) else (if t 3 = 0 then 2781 else if t 3 = 1 then 3003 else 3106))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 802 else 2145) else if t 2 = 1 then (if t 3 = 0 then 808 else if t 3 = 1 then 800 else 832) else (if t 3 = 0 then 1500 else if t 3 = 1 then 399 else 405)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 806 else if t 3 = 1 then 798 else 1812) else if t 2 = 1 then (if t 3 = 0 then 804 else if t 3 = 1 then 796 else 829) else (if t 3 = 0 then 198 else if t 3 = 1 then 861 else 867)) else (if t 2 = 0 then (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 1817) else if t 2 = 1 then (if t 3 = 0 then 821 else if t 3 = 1 then 816 else 838) else (if t 3 = 0 then 202 else if t 3 = 1 then 865 else 869))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 270 else 2777) else if t 2 = 1 then (if t 3 = 0 then 1470 else if t 3 = 1 then 268 else 278) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1788 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 66 else if t 3 = 1 then 854 else 1598) else if t 2 = 1 then (if t 3 = 0 then 64 else if t 3 = 1 then 852 else 858) else (if t 3 = 0 then 2127 else if t 3 = 1 then 870 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 71 else if t 3 = 1 then 857 else 1601) else if t 2 = 1 then (if t 3 = 0 then 70 else if t 3 = 1 then 856 else 860) else (if t 3 = 0 then 2128 else if t 3 = 1 then 871 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4761 else (if jt.2.val < 2 then 4787 else 4766)) else (if jt.2.val < 4 then 4785 else (if jt.2.val < 5 then 4786 else 4764))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3997 else (if jt.2.val < 2 then 4055 else 4001)) else (if jt.2.val < 4 then 4052 else (if jt.2.val < 5 then 4053 else 3971)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2388 else (if jt.2.val < 2 then 2390 else 2393)) else (if jt.2.val < 4 then 2389 else (if jt.2.val < 5 then 2392 else 2391))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2325 else (if jt.2.val < 2 then 2336 else 2328)) else (if jt.2.val < 4 then 2334 else (if jt.2.val < 5 then 2335 else 2323)))))

checked_coverage fastCoverage0669 pairing0669 template0669 witness0669

theorem coverage0669 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0669) (maskBits m))
    cores template0669 witness0669 := by
  rw [← coresFast_eq]
  exact fastCoverage0669

theorem coverageSize0669 : ∀ q : Pattern,
    (cores (witness0669 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0669 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0669
#print axioms coverageSize0669

noncomputable def pairing0670 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0670 : List (Fin 4935) := templateData0670

noncomputable def witness0670 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 581 else 1549) else if t 2 = 1 then (if t 3 = 0 then 574 else if t 3 = 1 then 566 else 1108) else (if t 3 = 0 then 2117 else if t 3 = 1 then 567 else 1109)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 579 else if t 3 = 1 then 577 else 595) else if t 2 = 1 then (if t 3 = 0 then 552 else if t 3 = 1 then 532 else 535) else (if t 3 = 0 then 1537 else if t 3 = 1 then 534 else 536)) else (if t 2 = 0 then (if t 3 = 0 then 3215 else if t 3 = 1 then 2759 else 2762) else if t 2 = 1 then (if t 3 = 0 then 3209 else if t 3 = 1 then 2747 else 2749) else (if t 3 = 0 then 4541 else if t 3 = 1 then 3923 else 4044))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 580 else 1548) else if t 2 = 1 then (if t 3 = 0 then 570 else if t 3 = 1 then 556 else 1104) else (if t 3 = 0 then 2115 else if t 3 = 1 then 558 else 1106)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 578 else if t 3 = 1 then 576 else 594) else if t 2 = 1 then (if t 3 = 0 then 544 else if t 3 = 1 then 515 else 520) else (if t 3 = 0 then 1531 else if t 3 = 1 then 517 else 522)) else (if t 2 = 0 then (if t 3 = 0 then 585 else if t 3 = 1 then 584 else 598) else if t 2 = 1 then (if t 3 = 0 then 545 else if t 3 = 1 then 516 else 521) else (if t 3 = 0 then 1532 else if t 3 = 1 then 518 else 523))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 1836 else 4542) else if t 2 = 1 then (if t 3 = 0 then 572 else if t 3 = 1 then 562 else 1542) else (if t 3 = 0 then 2758 else if t 3 = 1 then 564 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1115 else if t 3 = 1 then 1113 else 2148) else if t 2 = 1 then (if t 3 = 0 then 548 else if t 3 = 1 then 524 else 528) else (if t 3 = 0 then 1535 else if t 3 = 1 then 526 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 1118 else if t 3 = 1 then 1117 else 2149) else if t 2 = 1 then (if t 3 = 0 then 549 else if t 3 = 1 then 525 else 529) else (if t 3 = 0 then 1536 else if t 3 = 1 then 527 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4809 else (if jt.2.val < 2 then 4825 else 4814)) else (if jt.2.val < 4 then 4824 else (if jt.2.val < 5 then 4826 else 4811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3122 else (if jt.2.val < 2 then 3212 else 3143)) else (if jt.2.val < 4 then 3211 else (if jt.2.val < 5 then 3213 else 3113)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2415 else (if jt.2.val < 2 then 2426 else 2417)) else (if jt.2.val < 4 then 2424 else (if jt.2.val < 5 then 2425 else 2412))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1527 else (if jt.2.val < 2 then 1529 else 1534)) else (if jt.2.val < 4 then 1528 else (if jt.2.val < 5 then 1533 else 1530)))))

checked_coverage fastCoverage0670 pairing0670 template0670 witness0670

theorem coverage0670 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0670) (maskBits m))
    cores template0670 witness0670 := by
  rw [← coresFast_eq]
  exact fastCoverage0670

theorem coverageSize0670 : ∀ q : Pattern,
    (cores (witness0670 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0670 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0670
#print axioms coverageSize0670

noncomputable def pairing0671 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 7) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0671 : List (Fin 4935) := templateData0671

noncomputable def witness0671 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1680 else 786) else if t 2 = 1 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1660 else 741) else (if t 3 = 0 then 896 else if t 3 = 1 then 357 else 2159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1678 else 1080) else if t 2 = 1 then (if t 3 = 0 then 1669 else if t 3 = 1 then 1644 else 1647) else (if t 3 = 0 then 157 else if t 3 = 1 then 1646 else 1648)) else (if t 2 = 0 then (if t 3 = 0 then 2577 else if t 3 = 1 then 2860 else 3242) else if t 2 = 1 then (if t 3 = 0 then 2545 else if t 3 = 1 then 3232 else 3234) else (if t 3 = 0 then 4058 else if t 3 = 1 then 3963 else 4530))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1679 else 785) else if t 2 = 1 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1656 else 734) else (if t 3 = 0 then 894 else if t 3 = 1 then 350 else 2157)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1677 else 1079) else if t 2 = 1 then (if t 3 = 0 then 1665 else if t 3 = 1 then 1628 else 1632) else (if t 3 = 0 then 150 else if t 3 = 1 then 1630 else 1634)) else (if t 2 = 0 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1685 else 1082) else if t 2 = 1 then (if t 3 = 0 then 1666 else if t 3 = 1 then 1629 else 1633) else (if t 3 = 0 then 151 else if t 3 = 1 then 1631 else 1635))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1854 else 4061) else if t 2 = 1 then (if t 3 = 0 then 1673 else if t 3 = 1 then 1658 else 738) else (if t 3 = 0 then 3240 else if t 3 = 1 then 354 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2172 else if t 3 = 1 then 1851 else 1092) else if t 2 = 1 then (if t 3 = 0 then 1667 else if t 3 = 1 then 1636 else 1640) else (if t 3 = 0 then 154 else if t 3 = 1 then 1638 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 2173 else if t 3 = 1 then 1852 else 1093) else if t 2 = 1 then (if t 3 = 0 then 1668 else if t 3 = 1 then 1637 else 1641) else (if t 3 = 0 then 155 else if t 3 = 1 then 1639 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4836 else (if jt.2.val < 2 then 4843 else 4841)) else (if jt.2.val < 4 then 4842 else (if jt.2.val < 5 then 4844 else 4838))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3188 else (if jt.2.val < 2 then 3238 else 3190)) else (if jt.2.val < 4 then 3237 else (if jt.2.val < 5 then 3239 else 3185)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2391 else (if jt.2.val < 2 then 2408 else 2393)) else (if jt.2.val < 4 then 2406 else (if jt.2.val < 5 then 2407 else 2388))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1530 else (if jt.2.val < 2 then 1663 else 1534)) else (if jt.2.val < 4 then 1662 else (if jt.2.val < 5 then 1664 else 1527)))))

checked_coverage fastCoverage0671 pairing0671 template0671 witness0671

theorem coverage0671 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0671) (maskBits m))
    cores template0671 witness0671 := by
  rw [← coresFast_eq]
  exact fastCoverage0671

theorem coverageSize0671 : ∀ q : Pattern,
    (cores (witness0671 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0671 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0671
#print axioms coverageSize0671

noncomputable def pairing0672 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0672 : List (Fin 4935) := templateData0672

noncomputable def witness0672 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 3951) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2778) else (if t 3 = 0 then 3532 else if t 3 = 1 then 3530 else 3182)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 681) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 680) else (if t 3 = 0 then 2200 else if t 3 = 1 then 2196 else 688)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1173 else 695) else if t 2 = 1 then (if t 3 = 0 then 1174 else if t 3 = 1 then 1172 else 694) else (if t 3 = 0 then 1190 else if t 3 = 1 then 1189 else 698))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 189) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 188) else (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 196)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2570) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4179) else (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4180)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2578) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4181) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4164 else 4182))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 35 else 902) else if t 2 = 1 then (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 901) else (if t 3 = 0 then 54 else if t 3 = 1 then 53 else 905)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2462 else 2885) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4183) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4171 else 4184)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2487 else 3507) else if t 2 = 1 then (if t 3 = 0 then 3849 else if t 3 = 1 then 4177 else 4185) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4178 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4827 else (if jt.2.val < 2 then 4831 else 4832)) else (if jt.2.val < 4 then 4828 else (if jt.2.val < 5 then 4830 else 4829))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4133 else (if jt.2.val < 2 then 4161 else 4162)) else (if jt.2.val < 4 then 4158 else (if jt.2.val < 5 then 4160 else 4159)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4728 else (if jt.2.val < 2 then 4732 else 4733)) else (if jt.2.val < 4 then 4729 else (if jt.2.val < 5 then 4731 else 4730))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4131 else (if jt.2.val < 2 then 4173 else 4176)) else (if jt.2.val < 4 then 4172 else (if jt.2.val < 5 then 4175 else 4174)))))

checked_coverage fastCoverage0672 pairing0672 template0672 witness0672

theorem coverage0672 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0672) (maskBits m))
    cores template0672 witness0672 := by
  rw [← coresFast_eq]
  exact fastCoverage0672

theorem coverageSize0672 : ∀ q : Pattern,
    (cores (witness0672 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0672 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0672
#print axioms coverageSize0672

noncomputable def pairing0673 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0673 : List (Fin 4935) := templateData0673

noncomputable def witness0673 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4190) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2775) else (if t 3 = 0 then 3228 else if t 3 = 1 then 3225 else 3524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 667) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 654) else (if t 3 = 0 then 1612 else if t 3 = 1 then 1593 else 656)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 475 else 1138) else if t 2 = 1 then (if t 3 = 0 then 490 else if t 3 = 1 then 462 else 1132) else (if t 3 = 0 then 497 else if t 3 = 1 then 464 else 1134))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 175) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 161) else (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 163)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2549) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3877) else (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3878)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2879) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3882) else (if t 3 = 0 then 3918 else if t 3 = 1 then 3881 else 3883))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 994 else 177) else if t 2 = 1 then (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 167) else (if t 3 = 0 then 1013 else if t 3 = 1 then 990 else 169)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2555) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3886) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3885 else 3887)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2700 else 3197) else if t 2 = 1 then (if t 3 = 0 then 4191 else if t 3 = 1 then 3888 else 3890) else (if t 3 = 0 then 4192 else if t 3 = 1 then 3889 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4815 else (if jt.2.val < 2 then 4817 else 4820)) else (if jt.2.val < 4 then 4816 else (if jt.2.val < 5 then 4819 else 4818))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4107 else (if jt.2.val < 2 then 4109 else 4116)) else (if jt.2.val < 4 then 4108 else (if jt.2.val < 5 then 4115 else 4114)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4455 else (if jt.2.val < 2 then 4457 else 4460)) else (if jt.2.val < 4 then 4456 else (if jt.2.val < 5 then 4459 else 4458))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4174 else (if jt.2.val < 2 then 4189 else 4176)) else (if jt.2.val < 4 then 4187 else (if jt.2.val < 5 then 4188 else 4131)))))

checked_coverage fastCoverage0673 pairing0673 template0673 witness0673

theorem coverage0673 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0673) (maskBits m))
    cores template0673 witness0673 := by
  rw [← coresFast_eq]
  exact fastCoverage0673

theorem coverageSize0673 : ∀ q : Pattern,
    (cores (witness0673 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0673 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0673
#print axioms coverageSize0673

noncomputable def pairing0674 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0674 : List (Fin 4935) := templateData0674

noncomputable def witness0674 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3215) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2759) else (if t 3 = 0 then 4213 else if t 3 = 1 then 4211 else 3927)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 291) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 290) else (if t 3 = 0 then 2199 else if t 3 = 1 then 2195 else 298)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 964 else 305) else if t 2 = 1 then (if t 3 = 0 then 965 else if t 3 = 1 then 963 else 304) else (if t 3 = 0 then 980 else if t 3 = 1 then 979 else 308))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 585) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 584) else (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 592)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2572) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3488) else (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3489)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2838 else 2579) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3472 else 3490) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3473 else 3491))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 441 else 1118) else if t 2 = 1 then (if t 3 = 0 then 442 else if t 3 = 1 then 440 else 1117) else (if t 3 = 0 then 456 else if t 3 = 1 then 455 else 1121)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2471 else 2886) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3479 else 3492) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3480 else 3493)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2489 else 4197) else if t 2 = 1 then (if t 3 = 0 then 3095 else if t 3 = 1 then 3486 else 3494) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3487 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4791 else (if jt.2.val < 2 then 4795 else 4796)) else (if jt.2.val < 4 then 4792 else (if jt.2.val < 5 then 4794 else 4793))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3440 else (if jt.2.val < 2 then 3470 else 3471)) else (if jt.2.val < 4 then 3467 else (if jt.2.val < 5 then 3469 else 3468)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4730 else (if jt.2.val < 2 then 4736 else 4733)) else (if jt.2.val < 4 then 4734 else (if jt.2.val < 5 then 4735 else 4728))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3438 else (if jt.2.val < 2 then 3482 else 3485)) else (if jt.2.val < 4 then 3481 else (if jt.2.val < 5 then 3484 else 3483)))))

checked_coverage fastCoverage0674 pairing0674 template0674 witness0674

theorem coverage0674 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0674) (maskBits m))
    cores template0674 witness0674 := by
  rw [← coresFast_eq]
  exact fastCoverage0674

theorem coverageSize0674 : ∀ q : Pattern,
    (cores (witness0674 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0674 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0674
#print axioms coverageSize0674

noncomputable def pairing0675 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0675 : List (Fin 4935) := templateData0675

noncomputable def witness0675 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3499) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 2756) else (if t 3 = 0 then 3959 else if t 3 = 1 then 3953 else 4207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 277) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 264) else (if t 3 = 0 then 1611 else if t 3 = 1 then 1589 else 266)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 73 else 922) else if t 2 = 1 then (if t 3 = 0 then 88 else if t 3 = 1 then 60 else 916) else (if t 3 = 0 then 95 else if t 3 = 1 then 62 else 918))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 571) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 557) else (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 559)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2550) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3123) else (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3124)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2697 else 2880) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3126 else 3128) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3127 else 3129))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1204 else 573) else if t 2 = 1 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1198 else 563) else (if t 3 = 0 then 1223 else if t 3 = 1 then 1200 else 565)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2949 else 2556) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3130 else 3132) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3131 else 3133)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2701 else 3934) else if t 2 = 1 then (if t 3 = 0 then 3500 else if t 3 = 1 then 3134 else 3136) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3135 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4761 else (if jt.2.val < 2 then 4763 else 4766)) else (if jt.2.val < 4 then 4762 else (if jt.2.val < 5 then 4765 else 4764))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3396 else (if jt.2.val < 2 then 3398 else 3405)) else (if jt.2.val < 4 then 3397 else (if jt.2.val < 5 then 3404 else 3403)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4458 else (if jt.2.val < 2 then 4465 else 4460)) else (if jt.2.val < 4 then 4464 else (if jt.2.val < 5 then 4466 else 4455))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3483 else (if jt.2.val < 2 then 3498 else 3485)) else (if jt.2.val < 4 then 3496 else (if jt.2.val < 5 then 3497 else 3438)))))

checked_coverage fastCoverage0675 pairing0675 template0675 witness0675

theorem coverage0675 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0675) (maskBits m))
    cores template0675 witness0675 := by
  rw [← coresFast_eq]
  exact fastCoverage0675

theorem coverageSize0675 : ∀ q : Pattern,
    (cores (witness0675 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0675 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0675
#print axioms coverageSize0675

noncomputable def pairing0676 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0676 : List (Fin 4935) := templateData0676

noncomputable def witness0676 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 807 else 201) else if t 2 = 1 then (if t 3 = 0 then 809 else if t 3 = 1 then 805 else 199) else (if t 3 = 0 then 837 else if t 3 = 1 then 835 else 205)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 803 else if t 3 = 1 then 799 else 864) else if t 2 = 1 then (if t 3 = 0 then 801 else if t 3 = 1 then 797 else 862) else (if t 3 = 0 then 833 else if t 3 = 1 then 830 else 868)) else (if t 2 = 0 then (if t 3 = 0 then 4203 else if t 3 = 1 then 4054 else 3967) else if t 2 = 1 then (if t 3 = 0 then 2995 else if t 3 = 1 then 2993 else 3003) else (if t 3 = 0 then 3514 else if t 3 = 1 then 3329 else 3106))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 806 else 200) else if t 2 = 1 then (if t 3 = 0 then 808 else if t 3 = 1 then 804 else 198) else (if t 3 = 0 then 836 else if t 3 = 1 then 834 else 204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 802 else if t 3 = 1 then 798 else 863) else if t 2 = 1 then (if t 3 = 0 then 800 else if t 3 = 1 then 796 else 861) else (if t 3 = 0 then 832 else if t 3 = 1 then 829 else 867)) else (if t 2 = 0 then (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 866) else if t 2 = 1 then (if t 3 = 0 then 819 else if t 3 = 1 then 816 else 865) else (if t 3 = 0 then 839 else if t 3 = 1 then 838 else 869))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 66 else 3525) else if t 2 = 1 then (if t 3 = 0 then 1470 else if t 3 = 1 then 64 else 2127) else (if t 3 = 0 then 3942 else if t 3 = 1 then 74 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 270 else if t 3 = 1 then 854 else 876) else if t 2 = 1 then (if t 3 = 0 then 268 else if t 3 = 1 then 852 else 870) else (if t 3 = 0 then 278 else if t 3 = 1 then 858 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 275 else if t 3 = 1 then 857 else 877) else if t 2 = 1 then (if t 3 = 0 then 274 else if t 3 = 1 then 856 else 871) else (if t 3 = 0 then 281 else if t 3 = 1 then 860 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4761 else (if jt.2.val < 2 then 4787 else 4766)) else (if jt.2.val < 4 then 4785 else (if jt.2.val < 5 then 4786 else 4764))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4159 else (if jt.2.val < 2 then 4202 else 4162)) else (if jt.2.val < 4 then 4200 else (if jt.2.val < 5 then 4201 else 4133)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 794 else (if jt.2.val < 2 then 828 else 831)) else (if jt.2.val < 4 then 825 else (if jt.2.val < 5 then 827 else 826))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1224 else (if jt.2.val < 2 then 1230 else 1233)) else (if jt.2.val < 4 then 1229 else (if jt.2.val < 5 then 1232 else 1231)))))

checked_coverage fastCoverage0676 pairing0676 template0676 witness0676

theorem coverage0676 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0676) (maskBits m))
    cores template0676 witness0676 := by
  rw [← coresFast_eq]
  exact fastCoverage0676

theorem coverageSize0676 : ∀ q : Pattern,
    (cores (witness0676 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0676 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0676
#print axioms coverageSize0676

noncomputable def pairing0677 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0677 : List (Fin 4935) := templateData0677

noncomputable def witness0677 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 379 else 896) else if t 2 = 1 then (if t 3 = 0 then 386 else if t 3 = 1 then 371 else 892) else (if t 3 = 0 then 396 else if t 3 = 1 then 372 else 893)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 384 else if t 3 = 1 then 356 else 357) else if t 2 = 1 then (if t 3 = 0 then 382 else if t 3 = 1 then 336 else 340) else (if t 3 = 0 then 394 else if t 3 = 1 then 339 else 341)) else (if t 2 = 0 then (if t 3 = 0 then 3935 else if t 3 = 1 then 3929 else 4205) else if t 2 = 1 then (if t 3 = 0 then 2740 else if t 3 = 1 then 2728 else 2730) else (if t 3 = 0 then 3207 else if t 3 = 1 then 3203 else 3505))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 375 else 894) else if t 2 = 1 then (if t 3 = 0 then 385 else if t 3 = 1 then 363 else 888) else (if t 3 = 0 then 395 else if t 3 = 1 then 365 else 890)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 383 else if t 3 = 1 then 346 else 350) else if t 2 = 1 then (if t 3 = 0 then 381 else if t 3 = 1 then 318 else 324) else (if t 3 = 0 then 393 else if t 3 = 1 then 322 else 326)) else (if t 2 = 0 then (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 351) else if t 2 = 1 then (if t 3 = 0 then 389 else if t 3 = 1 then 320 else 325) else (if t 3 = 0 then 397 else if t 3 = 1 then 323 else 327))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 377 else 3240) else if t 2 = 1 then (if t 3 = 0 then 2139 else if t 3 = 1 then 367 else 1494) else (if t 3 = 0 then 4206 else if t 3 = 1 then 369 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 930 else if t 3 = 1 then 352 else 354) else if t 2 = 1 then (if t 3 = 0 then 924 else if t 3 = 1 then 328 else 332) else (if t 3 = 0 then 926 else if t 3 = 1 then 330 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 931 else if t 3 = 1 then 353 else 355) else if t 2 = 1 then (if t 3 = 0 then 925 else if t 3 = 1 then 329 else 333) else (if t 3 = 0 then 927 else if t 3 = 1 then 331 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4791 else (if jt.2.val < 2 then 4807 else 4796)) else (if jt.2.val < 4 then 4806 else (if jt.2.val < 5 then 4808 else 4793))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4114 else (if jt.2.val < 2 then 4129 else 4116)) else (if jt.2.val < 4 then 4128 else (if jt.2.val < 5 then 4130 else 4107)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 312 else (if jt.2.val < 2 then 314 else 349)) else (if jt.2.val < 4 then 313 else (if jt.2.val < 5 then 348 else 321))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1231 else (if jt.2.val < 2 then 1251 else 1233)) else (if jt.2.val < 4 then 1245 else (if jt.2.val < 5 then 1246 else 1224)))))

checked_coverage fastCoverage0677 pairing0677 template0677 witness0677

theorem coverage0677 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0677) (maskBits m))
    cores template0677 witness0677 := by
  rw [← coresFast_eq]
  exact fastCoverage0677

theorem coverageSize0677 : ∀ q : Pattern,
    (cores (witness0677 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0677 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0677
#print axioms coverageSize0677

noncomputable def pairing0678 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0678 : List (Fin 4935) := templateData0678

noncomputable def witness0678 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1029 else 597) else if t 2 = 1 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1027 else 595) else (if t 3 = 0 then 1053 else if t 3 = 1 then 1051 else 601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1025 else if t 3 = 1 then 1021 else 1080) else if t 2 = 1 then (if t 3 = 0 then 1023 else if t 3 = 1 then 1019 else 1078) else (if t 3 = 0 then 1049 else if t 3 = 1 then 1046 else 1084)) else (if t 2 = 0 then (if t 3 = 0 then 3520 else if t 3 = 1 then 3338 else 3242) else if t 2 = 1 then (if t 3 = 0 then 2972 else if t 3 = 1 then 2970 else 2980) else (if t 3 = 0 then 4198 else if t 3 = 1 then 4046 else 3860))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1028 else 596) else if t 2 = 1 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1026 else 594) else (if t 3 = 0 then 1052 else if t 3 = 1 then 1050 else 600)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1024 else if t 3 = 1 then 1020 else 1079) else if t 2 = 1 then (if t 3 = 0 then 1022 else if t 3 = 1 then 1018 else 1077) else (if t 3 = 0 then 1048 else if t 3 = 1 then 1045 else 1083)) else (if t 2 = 0 then (if t 3 = 0 then 1040 else if t 3 = 1 then 1038 else 1082) else if t 2 = 1 then (if t 3 = 0 then 1039 else if t 3 = 1 then 1037 else 1081) else (if t 3 = 0 then 1055 else if t 3 = 1 then 1054 else 1085))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 468 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1518 else if t 3 = 1 then 466 else 2148) else (if t 3 = 0 then 3206 else if t 3 = 1 then 476 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 660 else if t 3 = 1 then 1070 else 1092) else if t 2 = 1 then (if t 3 = 0 then 658 else if t 3 = 1 then 1068 else 1086) else (if t 3 = 0 then 668 else if t 3 = 1 then 1074 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 665 else if t 3 = 1 then 1073 else 1093) else if t 2 = 1 then (if t 3 = 0 then 664 else if t 3 = 1 then 1072 else 1087) else (if t 3 = 0 then 671 else if t 3 = 1 then 1076 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4815 else (if jt.2.val < 2 then 4823 else 4820)) else (if jt.2.val < 4 then 4821 else (if jt.2.val < 5 then 4822 else 4818))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3468 else (if jt.2.val < 2 then 3519 else 3471)) else (if jt.2.val < 4 then 3517 else (if jt.2.val < 5 then 3518 else 3440)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 826 else (if jt.2.val < 2 then 1047 else 831)) else (if jt.2.val < 4 then 1014 else (if jt.2.val < 5 then 1015 else 794))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1260 else (if jt.2.val < 2 then 1263 else 1269)) else (if jt.2.val < 4 then 1262 else (if jt.2.val < 5 then 1268 else 1267)))))

checked_coverage fastCoverage0678 pairing0678 template0678 witness0678

theorem coverage0678 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0678) (maskBits m))
    cores template0678 witness0678 := by
  rw [← coresFast_eq]
  exact fastCoverage0678

theorem coverageSize0678 : ∀ q : Pattern,
    (cores (witness0678 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0678 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0678
#print axioms coverageSize0678

noncomputable def pairing0679 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 6 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0679 : List (Fin 4935) := templateData0679

noncomputable def witness0679 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 763 else 1112) else if t 2 = 1 then (if t 3 = 0 then 770 else if t 3 = 1 then 755 else 1108) else (if t 3 = 0 then 780 else if t 3 = 1 then 756 else 1109)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 768 else if t 3 = 1 then 740 else 741) else if t 2 = 1 then (if t 3 = 0 then 766 else if t 3 = 1 then 720 else 723) else (if t 3 = 0 then 778 else if t 3 = 1 then 722 else 724)) else (if t 2 = 0 then (if t 3 = 0 then 3198 else if t 3 = 1 then 3191 else 3522) else if t 2 = 1 then (if t 3 = 0 then 2797 else if t 3 = 1 then 2785 else 2787) else (if t 3 = 0 then 3943 else if t 3 = 1 then 3939 else 4196))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 759 else 1110) else if t 2 = 1 then (if t 3 = 0 then 769 else if t 3 = 1 then 747 else 1104) else (if t 3 = 0 then 779 else if t 3 = 1 then 749 else 1106)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 767 else if t 3 = 1 then 732 else 734) else if t 2 = 1 then (if t 3 = 0 then 765 else if t 3 = 1 then 704 else 708) else (if t 3 = 0 then 777 else if t 3 = 1 then 706 else 710)) else (if t 2 = 0 then (if t 3 = 0 then 774 else if t 3 = 1 then 733 else 735) else if t 2 = 1 then (if t 3 = 0 then 773 else if t 3 = 1 then 705 else 709) else (if t 3 = 0 then 781 else if t 3 = 1 then 707 else 711))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 761 else 3966) else if t 2 = 1 then (if t 3 = 0 then 2160 else if t 3 = 1 then 751 else 1542) else (if t 3 = 0 then 3523 else if t 3 = 1 then 753 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1146 else if t 3 = 1 then 736 else 738) else if t 2 = 1 then (if t 3 = 0 then 1140 else if t 3 = 1 then 712 else 716) else (if t 3 = 0 then 1142 else if t 3 = 1 then 714 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 1147 else if t 3 = 1 then 737 else 739) else if t 2 = 1 then (if t 3 = 0 then 1141 else if t 3 = 1 then 713 else 717) else (if t 3 = 0 then 1143 else if t 3 = 1 then 715 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4827 else (if jt.2.val < 2 then 4834 else 4832)) else (if jt.2.val < 4 then 4833 else (if jt.2.val < 5 then 4835 else 4829))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3403 else (if jt.2.val < 2 then 3430 else 3405)) else (if jt.2.val < 4 then 3429 else (if jt.2.val < 5 then 3431 else 3396)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 321 else (if jt.2.val < 2 then 730 else 349)) else (if jt.2.val < 4 then 729 else (if jt.2.val < 5 then 731 else 312))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1267 else (if jt.2.val < 2 then 1287 else 1269)) else (if jt.2.val < 4 then 1284 else (if jt.2.val < 5 then 1285 else 1260)))))

checked_coverage fastCoverage0679 pairing0679 template0679 witness0679

theorem coverage0679 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0679) (maskBits m))
    cores template0679 witness0679 := by
  rw [← coresFast_eq]
  exact fastCoverage0679

theorem coverageSize0679 : ∀ q : Pattern,
    (cores (witness0679 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0679 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0679
#print axioms coverageSize0679

end Crown.CertificateData
