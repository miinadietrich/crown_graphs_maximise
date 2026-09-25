import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0019

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0760 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0760 : List (Fin 4935) := templateData0760

noncomputable def witness0760 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 4056) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2996) else (if t 3 = 0 then 2789 else if t 3 = 1 then 2788 else 2795)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 1173) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 1172) else (if t 3 = 0 then 727 else if t 3 = 1 then 725 else 757)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2197 else 1802) else if t 2 = 1 then (if t 3 = 0 then 2200 else if t 3 = 1 then 2196 else 1189) else (if t 3 = 0 then 743 else if t 3 = 1 then 742 else 764))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 822) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 821) else (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 70)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2829) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4163) else (if t 3 = 0 then 3836 else if t 3 = 1 then 4170 else 4177)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3464 else 2842) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4164) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4171 else 4178))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 189 else 203) else if t 2 = 1 then (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 202) else (if t 3 = 0 then 1808 else if t 3 = 1 then 901 else 2128)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2578) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4181) else (if t 3 = 0 then 4039 else if t 3 = 1 then 4183 else 4185)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2574 else 2580) else if t 2 = 1 then (if t 3 = 0 then 3916 else if t 3 = 1 then 4180 else 4182) else (if t 3 = 0 then 4040 else if t 3 = 1 then 4184 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4917 else (if jt.2.val < 2 then 4919 else 4922)) else (if jt.2.val < 4 then 4918 else (if jt.2.val < 5 then 4921 else 4920))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4693 else (if jt.2.val < 2 then 4697 else 4698)) else (if jt.2.val < 4 then 4694 else (if jt.2.val < 5 then 4696 else 4695)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4132 else (if jt.2.val < 2 then 4168 else 4169)) else (if jt.2.val < 4 then 4165 else (if jt.2.val < 5 then 4167 else 4166))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4278 else (if jt.2.val < 2 then 4282 else 4283)) else (if jt.2.val < 4 then 4279 else (if jt.2.val < 5 then 4281 else 4280)))))

checked_coverage fastCoverage0760 pairing0760 template0760 witness0760

theorem coverage0760 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0760) (maskBits m))
    cores template0760 witness0760 := by
  rw [← coresFast_eq]
  exact fastCoverage0760

theorem coverageSize0760 : ∀ q : Pattern,
    (cores (witness0760 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0760 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0760
#print axioms coverageSize0760

noncomputable def pairing0761 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0761 : List (Fin 4935) := templateData0761

noncomputable def witness0761 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 4203) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2995) else (if t 3 = 0 then 2751 else if t 3 = 1 then 2750 else 2757)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 1171) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 1170) else (if t 3 = 0 then 539 else if t 3 = 1 then 537 else 568)) else (if t 2 = 0 then (if t 3 = 0 then 1883 else if t 3 = 1 then 1879 else 2138) else if t 2 = 1 then (if t 3 = 0 then 1882 else if t 3 = 1 then 1878 else 1188) else (if t 3 = 0 then 555 else if t 3 = 1 then 554 else 575))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 820) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 819) else (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 274)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2828) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4000) else (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4017)) else (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2841) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4003) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4016 else 4018))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 390 else 404) else if t 2 = 1 then (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 403) else (if t 3 = 0 then 2141 else if t 3 = 1 then 925 else 1789)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2723) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4021) else (if t 3 = 0 then 4191 else if t 3 = 1 then 4023 else 4025)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2719 else 2725) else if t 2 = 1 then (if t 3 = 0 then 3918 else if t 3 = 1 then 4020 else 4022) else (if t 3 = 0 then 4192 else if t 3 = 1 then 4024 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4899 else (if jt.2.val < 2 then 4901 else 4904)) else (if jt.2.val < 4 then 4900 else (if jt.2.val < 5 then 4903 else 4902))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4432 else (if jt.2.val < 2 then 4436 else 4437)) else (if jt.2.val < 4 then 4433 else (if jt.2.val < 5 then 4435 else 4434)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3970 else (if jt.2.val < 2 then 4013 else 4014)) else (if jt.2.val < 4 then 4010 else (if jt.2.val < 5 then 4012 else 4011))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4280 else (if jt.2.val < 2 then 4286 else 4283)) else (if jt.2.val < 4 then 4284 else (if jt.2.val < 5 then 4285 else 4278)))))

checked_coverage fastCoverage0761 pairing0761 template0761 witness0761

theorem coverage0761 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0761) (maskBits m))
    cores template0761 witness0761 := by
  rw [← coresFast_eq]
  exact fastCoverage0761

theorem coverageSize0761 : ∀ q : Pattern,
    (cores (witness0761 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0761 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0761
#print axioms coverageSize0761

noncomputable def pairing0762 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0762 : List (Fin 4935) := templateData0762

noncomputable def witness0762 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2450 else 2485) else if t 2 = 1 then (if t 3 = 0 then 2446 else if t 3 = 1 then 2442 else 2482) else (if t 3 = 0 then 4196 else if t 3 = 1 then 3939 else 4060)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2448 else 1416) else if t 2 = 1 then (if t 3 = 0 then 2444 else if t 3 = 1 then 2440 else 1412) else (if t 3 = 0 then 724 else if t 3 = 1 then 722 else 756)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 343 else 374) else if t 2 = 1 then (if t 3 = 0 then 341 else if t 3 = 1 then 339 else 372) else (if t 3 = 0 then 2159 else if t 3 = 1 then 1489 else 1775))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2449 else 1586) else if t 2 = 1 then (if t 3 = 0 then 2445 else if t 3 = 1 then 2441 else 1582) else (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 69)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2447 else 2484) else if t 2 = 1 then (if t 3 = 0 then 2443 else if t 3 = 1 then 2439 else 2481) else (if t 3 = 0 then 2461 else if t 3 = 1 then 2459 else 2486)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2471 else 2489) else if t 2 = 1 then (if t 3 = 0 then 2470 else if t 3 = 1 then 2468 else 2488) else (if t 3 = 0 then 2474 else if t 3 = 1 then 2473 else 2490))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1915 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1906 else 1618) else (if t 3 = 0 then 103 else if t 3 = 1 then 91 else 93)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2883 else 3506) else if t 2 = 1 then (if t 3 = 0 then 2502 else if t 3 = 1 then 2492 else 2496) else (if t 3 = 0 then 2503 else if t 3 = 1 then 2493 else 2497)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2886 else 4197) else if t 2 = 1 then (if t 3 = 0 then 2504 else if t 3 = 1 then 2494 else 2498) else (if t 3 = 0 then 2505 else if t 3 = 1 then 2495 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4863 else (if jt.2.val < 2 then 4865 else 4868)) else (if jt.2.val < 4 then 4864 else (if jt.2.val < 5 then 4867 else 4866))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2437 else (if jt.2.val < 2 then 2467 else 2469)) else (if jt.2.val < 4 then 2464 else (if jt.2.val < 5 then 2466 else 2465)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4166 else (if jt.2.val < 2 then 4195 else 4169)) else (if jt.2.val < 4 then 4193 else (if jt.2.val < 5 then 4194 else 4132))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2436 else (if jt.2.val < 2 then 2480 else 2483)) else (if jt.2.val < 4 then 2477 else (if jt.2.val < 5 then 2479 else 2478)))))

checked_coverage fastCoverage0762 pairing0762 template0762 witness0762

theorem coverage0762 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0762) (maskBits m))
    cores template0762 witness0762 := by
  rw [← coresFast_eq]
  exact fastCoverage0762

theorem coverageSize0762 : ∀ q : Pattern,
    (cores (witness0762 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0762 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0762
#print axioms coverageSize0762

noncomputable def pairing0763 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0763 : List (Fin 4935) := templateData0763

noncomputable def witness0763 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2602 else 2633) else if t 2 = 1 then (if t 3 = 0 then 2598 else if t 3 = 1 then 2594 else 2630) else (if t 3 = 0 then 4044 else if t 3 = 1 then 3923 else 4207)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2600 else 1415) else if t 2 = 1 then (if t 3 = 0 then 2596 else if t 3 = 1 then 2592 else 1411) else (if t 3 = 0 then 536 else if t 3 = 1 then 534 else 567)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 143 else 173) else if t 2 = 1 then (if t 3 = 0 then 141 else if t 3 = 1 then 139 else 171) else (if t 3 = 0 then 1835 else if t 3 = 1 then 1537 else 2117))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2601 else 1585) else if t 2 = 1 then (if t 3 = 0 then 2597 else if t 3 = 1 then 2593 else 1581) else (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 273)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2599 else 2632) else if t 2 = 1 then (if t 3 = 0 then 2595 else if t 3 = 1 then 2591 else 2629) else (if t 3 = 0 then 2613 else if t 3 = 1 then 2611 else 2634)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2623 else 2637) else if t 2 = 1 then (if t 3 = 0 then 2622 else if t 3 = 1 then 2620 else 2636) else (if t 3 = 0 then 2626 else if t 3 = 1 then 2625 else 2638))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2227 else 1855) else if t 2 = 1 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2221 else 1615) else (if t 3 = 0 then 307 else if t 3 = 1 then 295 else 297)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2902 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2650 else if t 3 = 1 then 2640 else 2644) else (if t 3 = 0 then 2651 else if t 3 = 1 then 2641 else 2645)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2904 else 4045) else if t 2 = 1 then (if t 3 = 0 then 2652 else if t 3 = 1 then 2642 else 2646) else (if t 3 = 0 then 2653 else if t 3 = 1 then 2643 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4887 else (if jt.2.val < 2 then 4889 else 4892)) else (if jt.2.val < 4 then 4888 else (if jt.2.val < 5 then 4891 else 4890))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2589 else (if jt.2.val < 2 then 2619 else 2621)) else (if jt.2.val < 4 then 2616 else (if jt.2.val < 5 then 2618 else 2617)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4011 else (if jt.2.val < 2 then 4043 else 4014)) else (if jt.2.val < 4 then 4041 else (if jt.2.val < 5 then 4042 else 3970))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2478 else (if jt.2.val < 2 then 2631 else 2483)) else (if jt.2.val < 4 then 2587 else (if jt.2.val < 5 then 2588 else 2436)))))

checked_coverage fastCoverage0763 pairing0763 template0763 witness0763

theorem coverage0763 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0763) (maskBits m))
    cores template0763 witness0763 := by
  rw [← coresFast_eq]
  exact fastCoverage0763

theorem coverageSize0763 : ∀ q : Pattern,
    (cores (witness0763 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0763 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0763
#print axioms coverageSize0763

noncomputable def pairing0764 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0764 : List (Fin 4935) := templateData0764

noncomputable def witness0764 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1816) else if t 2 = 1 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 835) else (if t 3 = 0 then 50 else if t 3 = 1 then 48 else 75)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 1051) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2082) else (if t 3 = 0 then 1342 else if t 3 = 1 then 2090 else 2098)) else (if t 2 = 0 then (if t 3 = 0 then 4213 else if t 3 = 1 then 4211 else 4047) else if t 2 = 1 then (if t 3 = 0 then 3531 else if t 3 = 1 then 3528 else 2939) else (if t 3 = 0 then 2691 else if t 3 = 1 then 2690 else 2706))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1815) else if t 2 = 1 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 834) else (if t 3 = 0 then 49 else if t 3 = 1 then 47 else 74)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 1050) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2081) else (if t 3 = 0 then 1341 else if t 3 = 1 then 2089 else 2097)) else (if t 2 = 0 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 1056) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2083) else (if t 3 = 0 then 1344 else if t 3 = 1 then 2091 else 2099))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 1545 else 2763) else if t 2 = 1 then (if t 3 = 0 then 194 else if t 3 = 1 then 192 else 204) else (if t 3 = 0 then 4059 else if t 3 = 1 then 903 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 590 else if t 3 = 1 then 588 else 600) else if t 2 = 1 then (if t 3 = 0 then 1446 else if t 3 = 1 then 2100 else 2103) else (if t 3 = 0 then 1779 else if t 3 = 1 then 2106 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 593 else if t 3 = 1 then 592 else 602) else if t 2 = 1 then (if t 3 = 0 then 1448 else if t 3 = 1 then 2102 else 2105) else (if t 3 = 0 then 1781 else if t 3 = 1 then 2108 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4887 else (if jt.2.val < 2 then 4894 else 4892)) else (if jt.2.val < 4 then 4893 else (if jt.2.val < 5 then 4895 else 4890))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4695 else (if jt.2.val < 2 then 4706 else 4698)) else (if jt.2.val < 4 then 4704 else (if jt.2.val < 5 then 4705 else 4693)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2322 else (if jt.2.val < 2 then 2332 else 2333)) else (if jt.2.val < 4 then 2329 else (if jt.2.val < 5 then 2331 else 2330))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2358 else (if jt.2.val < 2 then 2362 else 2363)) else (if jt.2.val < 4 then 2359 else (if jt.2.val < 5 then 2361 else 2360)))))

checked_coverage fastCoverage0764 pairing0764 template0764 witness0764

theorem coverage0764 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0764) (maskBits m))
    cores template0764 witness0764 := by
  rw [← coresFast_eq]
  exact fastCoverage0764

theorem coverageSize0764 : ∀ q : Pattern,
    (cores (witness0764 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0764 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0764
#print axioms coverageSize0764

noncomputable def pairing0765 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0765 : List (Fin 4935) := templateData0765

noncomputable def witness0765 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 2146) else if t 2 = 1 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 833) else (if t 3 = 0 then 258 else if t 3 = 1 then 256 else 279)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 1049) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1730) else (if t 3 = 0 then 1353 else if t 3 = 1 then 1747 else 1750)) else (if t 2 = 0 then (if t 3 = 0 then 4066 else if t 3 = 1 then 4064 else 4198) else if t 2 = 1 then (if t 3 = 0 then 3351 else if t 3 = 1 then 3348 else 2938) else (if t 3 = 0 then 2547 else if t 3 = 1 then 2546 else 2561))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 2145) else if t 2 = 1 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 832) else (if t 3 = 0 then 257 else if t 3 = 1 then 255 else 278)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 1048) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1729) else (if t 3 = 0 then 1352 else if t 3 = 1 then 1746 else 1749)) else (if t 2 = 0 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 1055) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1734) else (if t 3 = 0 then 1355 else if t 3 = 1 then 1748 else 1751))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1497 else 2801) else if t 2 = 1 then (if t 3 = 0 then 395 else if t 3 = 1 then 393 else 405) else (if t 3 = 0 then 4206 else if t 3 = 1 then 926 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 779 else if t 3 = 1 then 777 else 789) else if t 2 = 1 then (if t 3 = 0 then 1449 else if t 3 = 1 then 1752 else 1755) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1758 else 1760)) else (if t 2 = 0 then (if t 3 = 0 then 782 else if t 3 = 1 then 781 else 791) else if t 2 = 1 then (if t 3 = 0 then 1451 else if t 3 = 1 then 1754 else 1757) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1759 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4863 else (if jt.2.val < 2 then 4870 else 4868)) else (if jt.2.val < 4 then 4869 else (if jt.2.val < 5 then 4871 else 4866))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4434 else (if jt.2.val < 2 then 4445 else 4437)) else (if jt.2.val < 4 then 4443 else (if jt.2.val < 5 then 4444 else 4432)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2268 else (if jt.2.val < 2 then 2278 else 2279)) else (if jt.2.val < 4 then 2275 else (if jt.2.val < 5 then 2277 else 2276))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2360 else (if jt.2.val < 2 then 2366 else 2363)) else (if jt.2.val < 4 then 2364 else (if jt.2.val < 5 then 2365 else 2358)))))

checked_coverage fastCoverage0765 pairing0765 template0765 witness0765

theorem coverage0765 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0765) (maskBits m))
    cores template0765 witness0765 := by
  rw [← coresFast_eq]
  exact fastCoverage0765

theorem coverageSize0765 : ∀ q : Pattern,
    (cores (witness0765 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0765 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0765
#print axioms coverageSize0765

noncomputable def pairing0766 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0766 : List (Fin 4935) := templateData0766

noncomputable def witness0766 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 428 else 469) else if t 2 = 1 then (if t 3 = 0 then 424 else if t 3 = 1 then 420 else 464) else (if t 3 = 0 then 2125 else if t 3 = 1 then 1507 else 1849)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 430 else if t 3 = 1 then 426 else 467) else if t 2 = 1 then (if t 3 = 0 then 422 else if t 3 = 1 then 418 else 462) else (if t 3 = 0 then 448 else if t 3 = 1 then 445 else 475)) else (if t 2 = 0 then (if t 3 = 0 then 2732 else if t 3 = 1 then 2731 else 2738) else if t 2 = 1 then (if t 3 = 0 then 2730 else if t 3 = 1 then 2728 else 2737) else (if t 3 = 0 then 4205 else if t 3 = 1 then 3929 else 4036))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 427 else 468) else if t 2 = 1 then (if t 3 = 0 then 423 else if t 3 = 1 then 419 else 463) else (if t 3 = 0 then 2124 else if t 3 = 1 then 1506 else 1848)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 429 else if t 3 = 1 then 425 else 466) else if t 2 = 1 then (if t 3 = 0 then 421 else if t 3 = 1 then 417 else 461) else (if t 3 = 0 then 447 else if t 3 = 1 then 444 else 474)) else (if t 2 = 0 then (if t 3 = 0 then 442 else if t 3 = 1 then 440 else 472) else if t 2 = 1 then (if t 3 = 0 then 438 else if t 3 = 1 then 436 else 470) else (if t 3 = 0 then 454 else if t 3 = 1 then 453 else 478))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 1115 else 4208) else if t 2 = 1 then (if t 3 = 0 then 504 else if t 3 = 1 then 492 else 494) else (if t 3 = 0 then 2744 else if t 3 = 1 then 1521 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1836 else if t 3 = 1 then 1113 else 2148) else if t 2 = 1 then (if t 3 = 0 then 498 else if t 3 = 1 then 480 else 484) else (if t 3 = 0 then 500 else if t 3 = 1 then 482 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 1838 else if t 3 = 1 then 1117 else 2149) else if t 2 = 1 then (if t 3 = 0 then 499 else if t 3 = 1 then 481 else 485) else (if t 3 = 0 then 501 else if t 3 = 1 then 483 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4899 else (if jt.2.val < 2 then 4915 else 4904)) else (if jt.2.val < 4 then 4914 else (if jt.2.val < 5 then 4916 else 4902))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2465 else (if jt.2.val < 2 then 2729 else 2469)) else (if jt.2.val < 4 then 2726 else (if jt.2.val < 5 then 2727 else 2437)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2330 else (if jt.2.val < 2 then 2345 else 2333)) else (if jt.2.val < 4 then 2343 else (if jt.2.val < 5 then 2344 else 2322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 416 else (if jt.2.val < 2 then 460 else 465)) else (if jt.2.val < 4 then 457 else (if jt.2.val < 5 then 459 else 458)))))

checked_coverage fastCoverage0766 pairing0766 template0766 witness0766

theorem coverage0766 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0766) (maskBits m))
    cores template0766 witness0766 := by
  rw [← coresFast_eq]
  exact fastCoverage0766

theorem coverageSize0766 : ∀ q : Pattern,
    (cores (witness0766 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0766 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0766
#print axioms coverageSize0766

noncomputable def pairing0767 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0767 : List (Fin 4935) := templateData0767

noncomputable def witness0767 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 624 else 661) else if t 2 = 1 then (if t 3 = 0 then 620 else if t 3 = 1 then 616 else 656) else (if t 3 = 0 then 1786 else if t 3 = 1 then 1459 else 2170)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 626 else if t 3 = 1 then 622 else 659) else if t 2 = 1 then (if t 3 = 0 then 618 else if t 3 = 1 then 614 else 654) else (if t 3 = 0 then 644 else if t 3 = 1 then 641 else 667)) else (if t 2 = 0 then (if t 3 = 0 then 2770 else if t 3 = 1 then 2769 else 2776) else if t 2 = 1 then (if t 3 = 0 then 2768 else if t 3 = 1 then 2766 else 2775) else (if t 3 = 0 then 4058 else if t 3 = 1 then 3945 else 4190))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 623 else 660) else if t 2 = 1 then (if t 3 = 0 then 619 else if t 3 = 1 then 615 else 655) else (if t 3 = 0 then 1785 else if t 3 = 1 then 1458 else 2169)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 625 else if t 3 = 1 then 621 else 658) else if t 2 = 1 then (if t 3 = 0 then 617 else if t 3 = 1 then 613 else 653) else (if t 3 = 0 then 643 else if t 3 = 1 then 640 else 666)) else (if t 2 = 0 then (if t 3 = 0 then 638 else if t 3 = 1 then 636 else 664) else if t 2 = 1 then (if t 3 = 0 then 634 else if t 3 = 1 then 632 else 662) else (if t 3 = 0 then 650 else if t 3 = 1 then 649 else 670))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 1146 else 4061) else if t 2 = 1 then (if t 3 = 0 then 696 else if t 3 = 1 then 684 else 686) else (if t 3 = 0 then 2782 else if t 3 = 1 then 1473 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2160 else if t 3 = 1 then 1140 else 1824) else if t 2 = 1 then (if t 3 = 0 then 690 else if t 3 = 1 then 672 else 676) else (if t 3 = 0 then 692 else if t 3 = 1 then 674 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 2162 else if t 3 = 1 then 1141 else 1825) else if t 2 = 1 then (if t 3 = 0 then 691 else if t 3 = 1 then 673 else 677) else (if t 3 = 0 then 693 else if t 3 = 1 then 675 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4917 else (if jt.2.val < 2 then 4924 else 4922)) else (if jt.2.val < 4 then 4923 else (if jt.2.val < 5 then 4925 else 4920))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2617 else (if jt.2.val < 2 then 2767 else 2621)) else (if jt.2.val < 4 then 2764 else (if jt.2.val < 5 then 2765 else 2589)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2276 else (if jt.2.val < 2 then 2303 else 2279)) else (if jt.2.val < 4 then 2301 else (if jt.2.val < 5 then 2302 else 2268))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 458 else (if jt.2.val < 2 then 657 else 465)) else (if jt.2.val < 4 then 609 else (if jt.2.val < 5 then 610 else 416)))))

checked_coverage fastCoverage0767 pairing0767 template0767 witness0767

theorem coverage0767 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0767) (maskBits m))
    cores template0767 witness0767 := by
  rw [← coresFast_eq]
  exact fastCoverage0767

theorem coverageSize0767 : ∀ q : Pattern,
    (cores (witness0767 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0767 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0767
#print axioms coverageSize0767

noncomputable def pairing0768 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0768 : List (Fin 4935) := templateData0768

noncomputable def witness0768 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 3925) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2750) else (if t 3 = 0 then 3352 else if t 3 = 1 then 3350 else 3210)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 538) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 537) else (if t 3 = 0 then 1882 else if t 3 = 1 then 1878 else 554)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1171 else 569) else if t 2 = 1 then (if t 3 = 0 then 1174 else if t 3 = 1 then 1170 else 568) else (if t 3 = 0 then 1190 else if t 3 = 1 then 1188 else 575))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 243) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 242) else (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 261)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2614) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4015) else (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4016)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2635) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4017) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4003 else 4018))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 390 else 931) else if t 2 = 1 then (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 925) else (if t 3 = 0 then 398 else if t 3 = 1 then 397 else 927)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2903) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4023) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4020 else 4024)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2723 else 3322) else if t 2 = 1 then (if t 3 = 0 then 3919 else if t 3 = 1 then 4021 else 4025) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4022 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4899 else (if jt.2.val < 2 then 4901 else 4904)) else (if jt.2.val < 4 then 4900 else (if jt.2.val < 5 then 4903 else 4902))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3971 else (if jt.2.val < 2 then 3999 else 4001)) else (if jt.2.val < 4 then 3996 else (if jt.2.val < 5 then 3998 else 3997)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4566 else (if jt.2.val < 2 then 4570 else 4571)) else (if jt.2.val < 4 then 4567 else (if jt.2.val < 5 then 4569 else 4568))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4069 else (if jt.2.val < 2 then 4075 else 4076)) else (if jt.2.val < 4 then 4070 else (if jt.2.val < 5 then 4072 else 4071)))))

checked_coverage fastCoverage0768 pairing0768 template0768 witness0768

theorem coverage0768 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0768) (maskBits m))
    cores template0768 witness0768 := by
  rw [← coresFast_eq]
  exact fastCoverage0768

theorem coverageSize0768 : ∀ q : Pattern,
    (cores (witness0768 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0768 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0768
#print axioms coverageSize0768

noncomputable def pairing0769 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0769 : List (Fin 4935) := templateData0769

noncomputable def witness0769 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4044) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2749) else (if t 3 = 0 then 3236 else if t 3 = 1 then 3234 else 3342)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 536) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 535) else (if t 3 = 0 then 1651 else if t 3 = 1 then 1647 else 553)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 724 else 1109) else if t 2 = 1 then (if t 3 = 0 then 727 else if t 3 = 1 then 723 else 1108) else (if t 3 = 0 then 743 else if t 3 = 1 then 741 else 1112))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 241) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 240) else (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 260)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2613) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3843) else (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3846)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2899) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3848) else (if t 3 = 0 then 3838 else if t 3 = 1 then 3837 else 3850))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 1003 else 307) else if t 2 = 1 then (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 301) else (if t 3 = 0 then 1013 else if t 3 = 1 then 999 else 303)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2651) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3856) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3853 else 3857)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2503 else 3184) else if t 2 = 1 then (if t 3 = 0 then 4039 else if t 3 = 1 then 3854 else 3858) else (if t 3 = 0 then 4040 else if t 3 = 1 then 3855 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4905 else (if jt.2.val < 2 then 4907 else 4910)) else (if jt.2.val < 4 then 4906 else (if jt.2.val < 5 then 4909 else 4908))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3805 else (if jt.2.val < 2 then 3833 else 3835)) else (if jt.2.val < 4 then 3830 else (if jt.2.val < 5 then 3832 else 3831)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4449 else (if jt.2.val < 2 then 4453 else 4454)) else (if jt.2.val < 4 then 4450 else (if jt.2.val < 5 then 4452 else 4451))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4071 else (if jt.2.val < 2 then 4085 else 4076)) else (if jt.2.val < 4 then 4080 else (if jt.2.val < 5 then 4081 else 4069)))))

checked_coverage fastCoverage0769 pairing0769 template0769 witness0769

theorem coverage0769 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0769) (maskBits m))
    cores template0769 witness0769 := by
  rw [← coresFast_eq]
  exact fastCoverage0769

theorem coverageSize0769 : ∀ q : Pattern,
    (cores (witness0769 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0769 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0769
#print axioms coverageSize0769

noncomputable def pairing0770 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0770 : List (Fin 4935) := templateData0770

noncomputable def witness0770 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3174) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2769) else (if t 3 = 0 then 4066 else if t 3 = 1 then 4064 else 3946)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 143) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 142) else (if t 3 = 0 then 1881 else if t 3 = 1 then 1877 else 158)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 962 else 173) else if t 2 = 1 then (if t 3 = 0 then 965 else if t 3 = 1 then 961 else 172) else (if t 3 = 0 then 980 else if t 3 = 1 then 978 else 179))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 637) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 636) else (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 651)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2623) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3291) else (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3292)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2637) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3276 else 3293) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3279 else 3294))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 774 else 1147) else if t 2 = 1 then (if t 3 = 0 then 775 else if t 3 = 1 then 773 else 1141) else (if t 3 = 0 then 782 else if t 3 = 1 then 781 else 1143)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2717 else 2904) else if t 2 = 1 then (if t 3 = 0 then 3165 else if t 3 = 1 then 3295 else 3299) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3296 else 3300)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2724 else 4045) else if t 2 = 1 then (if t 3 = 0 then 3167 else if t 3 = 1 then 3297 else 3301) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3298 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4845 else (if jt.2.val < 2 then 4847 else 4850)) else (if jt.2.val < 4 then 4846 else (if jt.2.val < 5 then 4849 else 4848))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3245 else (if jt.2.val < 2 then 3275 else 3277)) else (if jt.2.val < 4 then 3272 else (if jt.2.val < 5 then 3274 else 3273)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4568 else (if jt.2.val < 2 then 4574 else 4571)) else (if jt.2.val < 4 then 4572 else (if jt.2.val < 5 then 4573 else 4566))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3358 else (if jt.2.val < 2 then 3364 else 3365)) else (if jt.2.val < 4 then 3359 else (if jt.2.val < 5 then 3361 else 3360)))))

checked_coverage fastCoverage0770 pairing0770 template0770 witness0770

theorem coverage0770 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0770) (maskBits m))
    cores template0770 witness0770 := by
  rw [← coresFast_eq]
  exact fastCoverage0770

theorem coverageSize0770 : ∀ q : Pattern,
    (cores (witness0770 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0770 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0770
#print axioms coverageSize0770

noncomputable def pairing0771 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0771 : List (Fin 4935) := templateData0771

noncomputable def witness0771 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3320) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 2768) else (if t 3 = 0 then 3965 else if t 3 = 1 then 3963 else 4058)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 141) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 140) else (if t 3 = 0 then 1650 else if t 3 = 1 then 1646 else 157)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 341 else 893) else if t 2 = 1 then (if t 3 = 0 then 344 else if t 3 = 1 then 340 else 892) else (if t 3 = 0 then 359 else if t 3 = 1 then 357 else 896))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 635) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 634) else (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 650)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2622) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3089) else (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3092)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2900) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3080 else 3094) else (if t 3 = 0 then 3084 else if t 3 = 1 then 3083 else 3096))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1213 else 697) else if t 2 = 1 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1207 else 691) else (if t 3 = 0 then 1223 else if t 3 = 1 then 1209 else 693)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2956 else 2652) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3098 else 3102) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3099 else 3103)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2504 else 3928) else if t 2 = 1 then (if t 3 = 0 then 3315 else if t 3 = 1 then 3100 else 3104) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3101 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4851 else (if jt.2.val < 2 then 4853 else 4856)) else (if jt.2.val < 4 then 4852 else (if jt.2.val < 5 then 4855 else 4854))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3049 else (if jt.2.val < 2 then 3079 else 3081)) else (if jt.2.val < 4 then 3076 else (if jt.2.val < 5 then 3078 else 3077)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4451 else (if jt.2.val < 2 then 4463 else 4454)) else (if jt.2.val < 4 then 4461 else (if jt.2.val < 5 then 4462 else 4449))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3360 else (if jt.2.val < 2 then 3374 else 3365)) else (if jt.2.val < 4 then 3369 else (if jt.2.val < 5 then 3370 else 3358)))))

checked_coverage fastCoverage0771 pairing0771 template0771 witness0771

theorem coverage0771 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0771) (maskBits m))
    cores template0771 witness0771 := by
  rw [← coresFast_eq]
  exact fastCoverage0771

theorem coverageSize0771 : ∀ q : Pattern,
    (cores (witness0771 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0771 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0771
#print axioms coverageSize0771

noncomputable def pairing0772 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0772 : List (Fin 4935) := templateData0772

noncomputable def witness0772 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 803 else 271) else if t 2 = 1 then (if t 3 = 0 then 809 else if t 3 = 1 then 801 else 269) else (if t 3 = 0 then 837 else if t 3 = 1 then 833 else 279)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 807 else if t 3 = 1 then 799 else 855) else if t 2 = 1 then (if t 3 = 0 then 805 else if t 3 = 1 then 797 else 853) else (if t 3 = 0 then 835 else if t 3 = 1 then 830 else 859)) else (if t 2 = 0 then (if t 3 = 0 then 4056 else if t 3 = 1 then 4054 else 3954) else if t 2 = 1 then (if t 3 = 0 then 2996 else if t 3 = 1 then 2993 else 3002) else (if t 3 = 0 then 3330 else if t 3 = 1 then 3329 else 3152))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 802 else 270) else if t 2 = 1 then (if t 3 = 0 then 808 else if t 3 = 1 then 800 else 268) else (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 278)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 806 else if t 3 = 1 then 798 else 854) else if t 2 = 1 then (if t 3 = 0 then 804 else if t 3 = 1 then 796 else 852) else (if t 3 = 0 then 834 else if t 3 = 1 then 829 else 858)) else (if t 2 = 0 then (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 857) else if t 2 = 1 then (if t 3 = 0 then 821 else if t 3 = 1 then 816 else 856) else (if t 3 = 0 then 840 else if t 3 = 1 then 838 else 860))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 401 else 3345) else if t 2 = 1 then (if t 3 = 0 then 1500 else if t 3 = 1 then 399 else 1788) else (if t 3 = 0 then 3952 else if t 3 = 1 then 405 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 200 else if t 3 = 1 then 863 else 876) else if t 2 = 1 then (if t 3 = 0 then 198 else if t 3 = 1 then 861 else 870) else (if t 3 = 0 then 204 else if t 3 = 1 then 867 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 203 else if t 3 = 1 then 866 else 877) else if t 2 = 1 then (if t 3 = 0 then 202 else if t 3 = 1 then 865 else 871) else (if t 3 = 0 then 206 else if t 3 = 1 then 869 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4851 else (if jt.2.val < 2 then 4876 else 4856)) else (if jt.2.val < 4 then 4875 else (if jt.2.val < 5 then 4877 else 4854))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3997 else (if jt.2.val < 2 then 4055 else 4001)) else (if jt.2.val < 4 then 4052 else (if jt.2.val < 5 then 4053 else 3971)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 794 else (if jt.2.val < 2 then 828 else 831)) else (if jt.2.val < 4 then 825 else (if jt.2.val < 5 then 827 else 826))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1225 else (if jt.2.val < 2 then 1234 else 1235)) else (if jt.2.val < 4 then 1226 else (if jt.2.val < 5 then 1228 else 1227)))))

checked_coverage fastCoverage0772 pairing0772 template0772 witness0772

theorem coverage0772 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0772) (maskBits m))
    cores template0772 witness0772 := by
  rw [← coresFast_eq]
  exact fastCoverage0772

theorem coverageSize0772 : ∀ q : Pattern,
    (cores (witness0772 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0772 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0772
#print axioms coverageSize0772

noncomputable def pairing0773 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0773 : List (Fin 4935) := templateData0773

noncomputable def witness0773 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 16 else 918) else if t 2 = 1 then (if t 3 = 0 then 22 else if t 3 = 1 then 14 else 916) else (if t 3 = 0 then 50 else if t 3 = 1 then 46 else 922)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 20 else if t 3 = 1 then 12 else 62) else if t 2 = 1 then (if t 3 = 0 then 18 else if t 3 = 1 then 10 else 60) else (if t 3 = 0 then 48 else if t 3 = 1 then 43 else 73)) else (if t 2 = 0 then (if t 3 = 0 then 3941 else if t 3 = 1 then 3939 else 4060) else if t 2 = 1 then (if t 3 = 0 then 2788 else if t 3 = 1 then 2785 else 2794) else (if t 3 = 0 then 3192 else if t 3 = 1 then 3191 else 3312))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 15 else 917) else if t 2 = 1 then (if t 3 = 0 then 21 else if t 3 = 1 then 13 else 915) else (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 921)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 19 else if t 3 = 1 then 11 else 61) else if t 2 = 1 then (if t 3 = 0 then 17 else if t 3 = 1 then 9 else 59) else (if t 3 = 0 then 47 else if t 3 = 1 then 42 else 72)) else (if t 2 = 0 then (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 69) else if t 2 = 1 then (if t 3 = 0 then 34 else if t 3 = 1 then 29 else 68) else (if t 3 = 0 then 53 else if t 3 = 1 then 51 else 76))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 102 else 3229) else if t 2 = 1 then (if t 3 = 0 then 1806 else if t 3 = 1 then 96 else 1476) else (if t 3 = 0 then 4059 else if t 3 = 1 then 98 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 899 else if t 3 = 1 then 90 else 92) else if t 2 = 1 then (if t 3 = 0 then 897 else if t 3 = 1 then 78 else 82) else (if t 3 = 0 then 903 else if t 3 = 1 then 80 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 902 else if t 3 = 1 then 91 else 93) else if t 2 = 1 then (if t 3 = 0 then 901 else if t 3 = 1 then 79 else 83) else (if t 3 = 0 then 905 else if t 3 = 1 then 81 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4845 else (if jt.2.val < 2 then 4879 else 4850)) else (if jt.2.val < 4 then 4878 else (if jt.2.val < 5 then 4880 else 4848))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3831 else (if jt.2.val < 2 then 3940 else 3835)) else (if jt.2.val < 4 then 3937 else (if jt.2.val < 5 then 3938 else 3805)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 7 else (if jt.2.val < 2 then 41 else 44)) else (if jt.2.val < 4 then 38 else (if jt.2.val < 5 then 40 else 39))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1227 else (if jt.2.val < 2 then 1244 else 1235)) else (if jt.2.val < 4 then 1236 else (if jt.2.val < 5 then 1237 else 1225)))))

checked_coverage fastCoverage0773 pairing0773 template0773 witness0773

theorem coverage0773 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0773) (maskBits m))
    cores template0773 witness0773 := by
  rw [← coresFast_eq]
  exact fastCoverage0773

theorem coverageSize0773 : ∀ q : Pattern,
    (cores (witness0773 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0773 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0773
#print axioms coverageSize0773

noncomputable def pairing0774 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0774 : List (Fin 4935) := templateData0774

noncomputable def witness0774 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1025 else 661) else if t 2 = 1 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1023 else 659) else (if t 3 = 0 then 1053 else if t 3 = 1 then 1049 else 669)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1021 else 1071) else if t 2 = 1 then (if t 3 = 0 then 1027 else if t 3 = 1 then 1019 else 1069) else (if t 3 = 0 then 1051 else if t 3 = 1 then 1046 else 1075)) else (if t 2 = 0 then (if t 3 = 0 then 3340 else if t 3 = 1 then 3338 else 3226) else if t 2 = 1 then (if t 3 = 0 then 2973 else if t 3 = 1 then 2970 else 2979) else (if t 3 = 0 then 4047 else if t 3 = 1 then 4046 else 3905))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1024 else 660) else if t 2 = 1 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1022 else 658) else (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 668)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1020 else 1070) else if t 2 = 1 then (if t 3 = 0 then 1026 else if t 3 = 1 then 1018 else 1068) else (if t 3 = 0 then 1050 else if t 3 = 1 then 1045 else 1074)) else (if t 2 = 0 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1073) else if t 2 = 1 then (if t 3 = 0 then 1041 else if t 3 = 1 then 1037 else 1072) else (if t 3 = 0 then 1056 else if t 3 = 1 then 1054 else 1076))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 785 else 4061) else if t 2 = 1 then (if t 3 = 0 then 1548 else if t 3 = 1 then 783 else 1824) else (if t 3 = 0 then 3216 else if t 3 = 1 then 789 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 596 else if t 3 = 1 then 1079 else 1092) else if t 2 = 1 then (if t 3 = 0 then 594 else if t 3 = 1 then 1077 else 1086) else (if t 3 = 0 then 600 else if t 3 = 1 then 1083 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 599 else if t 3 = 1 then 1082 else 1093) else if t 2 = 1 then (if t 3 = 0 then 598 else if t 3 = 1 then 1081 else 1087) else (if t 3 = 0 then 602 else if t 3 = 1 then 1085 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4905 else (if jt.2.val < 2 then 4912 else 4910)) else (if jt.2.val < 4 then 4911 else (if jt.2.val < 5 then 4913 else 4908))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3273 else (if jt.2.val < 2 then 3339 else 3277)) else (if jt.2.val < 4 then 3336 else (if jt.2.val < 5 then 3337 else 3245)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 826 else (if jt.2.val < 2 then 1047 else 831)) else (if jt.2.val < 4 then 1014 else (if jt.2.val < 5 then 1015 else 794))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1261 else (if jt.2.val < 2 then 1270 else 1271)) else (if jt.2.val < 4 then 1264 else (if jt.2.val < 5 then 1266 else 1265)))))

checked_coverage fastCoverage0774 pairing0774 template0774 witness0774

theorem coverage0774 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0774) (maskBits m))
    cores template0774 witness0774 := by
  rw [← coresFast_eq]
  exact fastCoverage0774

theorem coverageSize0774 : ∀ q : Pattern,
    (cores (witness0774 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0774 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0774
#print axioms coverageSize0774

noncomputable def pairing0775 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0775 : List (Fin 4935) := templateData0775

noncomputable def witness0775 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 424 else 1134) else if t 2 = 1 then (if t 3 = 0 then 430 else if t 3 = 1 then 422 else 1132) else (if t 3 = 0 then 452 else if t 3 = 1 then 448 else 1138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 428 else if t 3 = 1 then 420 else 464) else if t 2 = 1 then (if t 3 = 0 then 426 else if t 3 = 1 then 418 else 462) else (if t 3 = 0 then 450 else if t 3 = 1 then 445 else 475)) else (if t 2 = 0 then (if t 3 = 0 then 3205 else if t 3 = 1 then 3203 else 3344) else if t 2 = 1 then (if t 3 = 0 then 2731 else if t 3 = 1 then 2728 else 2737) else (if t 3 = 0 then 3930 else if t 3 = 1 then 3929 else 4036))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 423 else 1133) else if t 2 = 1 then (if t 3 = 0 then 429 else if t 3 = 1 then 421 else 1131) else (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 1137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 427 else if t 3 = 1 then 419 else 463) else if t 2 = 1 then (if t 3 = 0 then 425 else if t 3 = 1 then 417 else 461) else (if t 3 = 0 then 449 else if t 3 = 1 then 444 else 474)) else (if t 2 = 0 then (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 471) else if t 2 = 1 then (if t 3 = 0 then 440 else if t 3 = 1 then 436 else 470) else (if t 3 = 0 then 455 else if t 3 = 1 then 453 else 478))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 504 else 3960) else if t 2 = 1 then (if t 3 = 0 then 1836 else if t 3 = 1 then 498 else 1524) else (if t 3 = 0 then 3343 else if t 3 = 1 then 500 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1115 else if t 3 = 1 then 492 else 494) else if t 2 = 1 then (if t 3 = 0 then 1113 else if t 3 = 1 then 480 else 484) else (if t 3 = 0 then 1119 else if t 3 = 1 then 482 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 1118 else if t 3 = 1 then 493 else 495) else if t 2 = 1 then (if t 3 = 0 then 1117 else if t 3 = 1 then 481 else 485) else (if t 3 = 0 then 1121 else if t 3 = 1 then 483 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4899 else (if jt.2.val < 2 then 4915 else 4904)) else (if jt.2.val < 4 then 4914 else (if jt.2.val < 5 then 4916 else 4902))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3077 else (if jt.2.val < 2 then 3204 else 3081)) else (if jt.2.val < 4 then 3201 else (if jt.2.val < 5 then 3202 else 3049)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 39 else (if jt.2.val < 2 then 446 else 44)) else (if jt.2.val < 4 then 414 else (if jt.2.val < 5 then 415 else 7))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1265 else (if jt.2.val < 2 then 1280 else 1271)) else (if jt.2.val < 4 then 1275 else (if jt.2.val < 5 then 1276 else 1261)))))

checked_coverage fastCoverage0775 pairing0775 template0775 witness0775

theorem coverage0775 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0775) (maskBits m))
    cores template0775 witness0775 := by
  rw [← coresFast_eq]
  exact fastCoverage0775

theorem coverageSize0775 : ∀ q : Pattern,
    (cores (witness0775 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0775 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0775
#print axioms coverageSize0775

noncomputable def pairing0776 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0776 : List (Fin 4935) := templateData0776

noncomputable def witness0776 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 3965) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3235) else (if t 3 = 0 then 3352 else if t 3 = 1 then 3351 else 2547)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1650) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1649) else (if t 3 = 0 then 1882 else if t 3 = 1 then 1880 else 1670)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2199 else 359) else if t 2 = 1 then (if t 3 = 0 then 2200 else if t 3 = 1 then 2198 else 1661) else (if t 3 = 0 then 1190 else if t 3 = 1 then 1892 else 1676))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1331) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1330) else (if t 3 = 0 then 1723 else if t 3 = 1 then 1721 else 1355)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3074) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4505) else (if t 3 = 0 then 3995 else if t 3 = 1 then 4498 else 4507)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3465 else 3084) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4506) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4499 else 4513))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1443 else 1223) else if t 2 = 1 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1442 else 1778) else (if t 3 = 0 then 398 else if t 3 = 1 then 1451 else 2120)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3161 else 3314) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4518) else (if t 3 = 0 then 3918 else if t 3 = 1 then 4516 else 4520)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 3164 else 3316) else if t 2 = 1 then (if t 3 = 0 then 3916 else if t 3 = 1 then 4515 else 4519) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4517 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4926 else (if jt.2.val < 2 then 4928 else 4931)) else (if jt.2.val < 4 then 4927 else (if jt.2.val < 5 then 4930 else 4929))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4711 else (if jt.2.val < 2 then 4715 else 4716)) else (if jt.2.val < 4 then 4712 else (if jt.2.val < 5 then 4714 else 4713)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4576 else (if jt.2.val < 2 then 4580 else 4581)) else (if jt.2.val < 4 then 4577 else (if jt.2.val < 5 then 4579 else 4578))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4549 else (if jt.2.val < 2 then 4553 else 4554)) else (if jt.2.val < 4 then 4550 else (if jt.2.val < 5 then 4552 else 4551)))))

checked_coverage fastCoverage0776 pairing0776 template0776 witness0776

theorem coverage0776 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0776) (maskBits m))
    cores template0776 witness0776 := by
  rw [← coresFast_eq]
  exact fastCoverage0776

theorem coverageSize0776 : ∀ q : Pattern,
    (cores (witness0776 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0776 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0776
#print axioms coverageSize0776

noncomputable def pairing0777 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0777 : List (Fin 4935) := templateData0777

noncomputable def witness0777 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4530) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 3234) else (if t 3 = 0 then 2751 else if t 3 = 1 then 2749 else 3342)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 1648) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 1647) else (if t 3 = 0 then 539 else if t 3 = 1 then 535 else 553)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 724 else 2159) else if t 2 = 1 then (if t 3 = 0 then 727 else if t 3 = 1 then 723 else 741) else (if t 3 = 0 then 1544 else if t 3 = 1 then 1108 else 1112))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 1329) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 1328) else (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 260)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 3073) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3827) else (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3846)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2474) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3837) else (if t 3 = 0 then 3849 else if t 3 = 1 then 3848 else 3850))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 1003 else 1375) else if t 2 = 1 then (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 999) else (if t 3 = 0 then 2141 else if t 3 = 1 then 301 else 303)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2957) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3853) else (if t 3 = 0 then 4191 else if t 3 = 1 then 3856 else 3857)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2503 else 2505) else if t 2 = 1 then (if t 3 = 0 then 4039 else if t 3 = 1 then 3854 else 3855) else (if t 3 = 0 then 4526 else if t 3 = 1 then 3858 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4905 else (if jt.2.val < 2 then 4907 else 4910)) else (if jt.2.val < 4 then 4906 else (if jt.2.val < 5 then 4909 else 4908))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3805 else (if jt.2.val < 2 then 3833 else 3835)) else (if jt.2.val < 4 then 3830 else (if jt.2.val < 5 then 3832 else 3831)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3804 else (if jt.2.val < 2 then 3842 else 3844)) else (if jt.2.val < 4 then 3839 else (if jt.2.val < 5 then 3841 else 3840))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4551 else (if jt.2.val < 2 then 4562 else 4554)) else (if jt.2.val < 4 then 4560 else (if jt.2.val < 5 then 4561 else 4549)))))

checked_coverage fastCoverage0777 pairing0777 template0777 witness0777

theorem coverage0777 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0777) (maskBits m))
    cores template0777 witness0777 := by
  rw [← coresFast_eq]
  exact fastCoverage0777

theorem coverageSize0777 : ∀ q : Pattern,
    (cores (witness0777 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0777 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0777
#print axioms coverageSize0777

noncomputable def pairing0778 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0778 : List (Fin 4935) := templateData0778

noncomputable def witness0778 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3258 else 2770) else if t 2 = 1 then (if t 3 = 0 then 3254 else if t 3 = 1 then 3250 else 2769) else (if t 3 = 0 then 4537 else if t 3 = 1 then 4064 else 3946)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3256 else 144) else if t 2 = 1 then (if t 3 = 0 then 3252 else if t 3 = 1 then 3248 else 142) else (if t 3 = 0 then 1879 else if t 3 = 1 then 1877 else 158)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 965 else 1496) else if t 2 = 1 then (if t 3 = 0 then 962 else if t 3 = 1 then 961 else 172) else (if t 3 = 0 then 2138 else if t 3 = 1 then 978 else 179))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3257 else 638) else if t 2 = 1 then (if t 3 = 0 then 3253 else if t 3 = 1 then 3249 else 636) else (if t 3 = 0 then 1720 else if t 3 = 1 then 1718 else 651)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3255 else 3091) else if t 2 = 1 then (if t 3 = 0 then 3251 else if t 3 = 1 then 3247 else 3291) else (if t 3 = 0 then 3269 else if t 3 = 1 then 3267 else 3292)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 3278 else 3095) else if t 2 = 1 then (if t 3 = 0 then 2837 else if t 3 = 1 then 3276 else 3293) else (if t 3 = 0 then 2841 else if t 3 = 1 then 3279 else 3294))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 775 else 2162) else if t 2 = 1 then (if t 3 = 0 then 774 else if t 3 = 1 then 773 else 1141) else (if t 3 = 0 then 1499 else if t 3 = 1 then 781 else 1143)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 3165 else 3500) else if t 2 = 1 then (if t 3 = 0 then 2717 else if t 3 = 1 then 3295 else 3299) else (if t 3 = 0 then 2719 else if t 3 = 1 then 3296 else 3300)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 3167 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2724 else if t 3 = 1 then 3297 else 3301) else (if t 3 = 0 then 2725 else if t 3 = 1 then 3298 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4845 else (if jt.2.val < 2 then 4847 else 4850)) else (if jt.2.val < 4 then 4846 else (if jt.2.val < 5 then 4849 else 4848))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3245 else (if jt.2.val < 2 then 3275 else 3277)) else (if jt.2.val < 4 then 3272 else (if jt.2.val < 5 then 3274 else 3273)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4578 else (if jt.2.val < 2 then 4589 else 4581)) else (if jt.2.val < 4 then 4587 else (if jt.2.val < 5 then 4588 else 4576))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3244 else (if jt.2.val < 2 then 3289 else 3290)) else (if jt.2.val < 4 then 3286 else (if jt.2.val < 5 then 3288 else 3287)))))

checked_coverage fastCoverage0778 pairing0778 template0778 witness0778

theorem coverage0778 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0778) (maskBits m))
    cores template0778 witness0778 := by
  rw [← coresFast_eq]
  exact fastCoverage0778

theorem coverageSize0778 : ∀ q : Pattern,
    (cores (witness0778 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0778 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0778
#print axioms coverageSize0778

noncomputable def pairing0779 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0779 : List (Fin 4935) := templateData0779

noncomputable def witness0779 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2598 else 3320) else if t 2 = 1 then (if t 3 = 0 then 2602 else if t 3 = 1 then 2594 else 3172) else (if t 3 = 0 then 3925 else if t 3 = 1 then 3923 else 4541)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2596 else 141) else if t 2 = 1 then (if t 3 = 0 then 2600 else if t 3 = 1 then 2592 else 139) else (if t 3 = 0 then 538 else if t 3 = 1 then 534 else 1537)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1413 else 893) else if t 2 = 1 then (if t 3 = 0 then 1415 else if t 3 = 1 then 1411 else 171) else (if t 3 = 0 then 569 else if t 3 = 1 then 567 else 2117))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2597 else 635) else if t 2 = 1 then (if t 3 = 0 then 2601 else if t 3 = 1 then 2593 else 633) else (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 1463)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2595 else 2622) else if t 2 = 1 then (if t 3 = 0 then 2599 else if t 3 = 1 then 2591 else 2620) else (if t 3 = 0 then 2614 else if t 3 = 1 then 2611 else 2625)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2897 else 2900) else if t 2 = 1 then (if t 3 = 0 then 2632 else if t 3 = 1 then 2629 else 2636) else (if t 3 = 0 then 2635 else if t 3 = 1 then 2634 else 2638))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2224 else 697) else if t 2 = 1 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2221 else 685) else (if t 3 = 0 then 931 else if t 3 = 1 then 295 else 1474)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2650 else 2652) else if t 2 = 1 then (if t 3 = 0 then 2902 else if t 3 = 1 then 2640 else 2642) else (if t 3 = 0 then 2903 else if t 3 = 1 then 2641 else 2643)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3183 else 3928) else if t 2 = 1 then (if t 3 = 0 then 3321 else if t 3 = 1 then 2644 else 2646) else (if t 3 = 0 then 3322 else if t 3 = 1 then 2645 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4887 else (if jt.2.val < 2 then 4889 else 4892)) else (if jt.2.val < 4 then 4888 else (if jt.2.val < 5 then 4891 else 4890))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3171 else (if jt.2.val < 2 then 3178 else 3179)) else (if jt.2.val < 4 then 3175 else (if jt.2.val < 5 then 3177 else 3176)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3840 else (if jt.2.val < 2 then 3924 else 3844)) else (if jt.2.val < 4 then 3921 else (if jt.2.val < 5 then 3922 else 3804))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3287 else (if jt.2.val < 2 then 3319 else 3290)) else (if jt.2.val < 4 then 3317 else (if jt.2.val < 5 then 3318 else 3244)))))

checked_coverage fastCoverage0779 pairing0779 template0779 witness0779

theorem coverage0779 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0779) (maskBits m))
    cores template0779 witness0779 := by
  rw [← coresFast_eq]
  exact fastCoverage0779

theorem coverageSize0779 : ∀ q : Pattern,
    (cores (witness0779 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0779 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0779
#print axioms coverageSize0779

noncomputable def pairing0780 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0780 : List (Fin 4935) := templateData0780

noncomputable def witness0780 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2058 else 452) else if t 2 = 1 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2056 else 1342) else (if t 3 = 0 then 837 else if t 3 = 1 then 1733 else 1359)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2054 else if t 3 = 1 then 2050 else 450) else if t 2 = 1 then (if t 3 = 0 then 2052 else if t 3 = 1 then 2048 else 2090) else (if t 3 = 0 then 835 else if t 3 = 1 then 2082 else 2098)) else (if t 2 = 0 then (if t 3 = 0 then 4546 else if t 3 = 1 then 4211 else 3930) else if t 2 = 1 then (if t 3 = 0 then 3530 else if t 3 = 1 then 3528 else 2690) else (if t 3 = 0 then 3330 else if t 3 = 1 then 2939 else 2706))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2057 else 451) else if t 2 = 1 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2055 else 1341) else (if t 3 = 0 then 836 else if t 3 = 1 then 1732 else 1358)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2053 else if t 3 = 1 then 2049 else 449) else if t 2 = 1 then (if t 3 = 0 then 2051 else if t 3 = 1 then 2047 else 2089) else (if t 3 = 0 then 834 else if t 3 = 1 then 2081 else 2097)) else (if t 2 = 0 then (if t 3 = 0 then 2071 else if t 3 = 1 then 2069 else 455) else if t 2 = 1 then (if t 3 = 0 then 2070 else if t 3 = 1 then 2067 else 2091) else (if t 3 = 0 then 840 else if t 3 = 1 then 2083 else 2099))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 590 else 3343) else if t 2 = 1 then (if t 3 = 0 then 194 else if t 3 = 1 then 1446 else 1779) else (if t 3 = 0 then 3952 else if t 3 = 1 then 1452 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1545 else if t 3 = 1 then 588 else 1119) else if t 2 = 1 then (if t 3 = 0 then 192 else if t 3 = 1 then 2100 else 2106) else (if t 3 = 0 then 204 else if t 3 = 1 then 2103 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 1547 else if t 3 = 1 then 592 else 1121) else if t 2 = 1 then (if t 3 = 0 then 196 else if t 3 = 1 then 2102 else 2108) else (if t 3 = 0 then 206 else if t 3 = 1 then 2105 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4887 else (if jt.2.val < 2 then 4894 else 4892)) else (if jt.2.val < 4 then 4893 else (if jt.2.val < 5 then 4895 else 4890))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4713 else (if jt.2.val < 2 then 4724 else 4716)) else (if jt.2.val < 4 then 4722 else (if jt.2.val < 5 then 4723 else 4711)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2045 else (if jt.2.val < 2 then 2079 else 2080)) else (if jt.2.val < 4 then 2076 else (if jt.2.val < 5 then 2078 else 2077))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2044 else (if jt.2.val < 2 then 2087 else 2088)) else (if jt.2.val < 4 then 2084 else (if jt.2.val < 5 then 2086 else 2085)))))

checked_coverage fastCoverage0780 pairing0780 template0780 witness0780

theorem coverage0780 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0780) (maskBits m))
    cores template0780 witness0780 := by
  rw [← coresFast_eq]
  exact fastCoverage0780

theorem coverageSize0780 : ∀ q : Pattern,
    (cores (witness0780 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0780 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0780
#print axioms coverageSize0780

noncomputable def pairing0781 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0781 : List (Fin 4935) := templateData0781

noncomputable def witness0781 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 16 else 2125) else if t 2 = 1 then (if t 3 = 0 then 22 else if t 3 = 1 then 14 else 46) else (if t 3 = 0 then 1471 else if t 3 = 1 then 916 else 922)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 20 else if t 3 = 1 then 12 else 1507) else if t 2 = 1 then (if t 3 = 0 then 18 else if t 3 = 1 then 10 else 43) else (if t 3 = 0 then 65 else if t 3 = 1 then 60 else 73)) else (if t 2 = 0 then (if t 3 = 0 then 3941 else if t 3 = 1 then 3939 else 4539) else if t 2 = 1 then (if t 3 = 0 then 2788 else if t 3 = 1 then 2785 else 3191) else (if t 3 = 0 then 2795 else if t 3 = 1 then 2794 else 3312))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 15 else 2124) else if t 2 = 1 then (if t 3 = 0 then 21 else if t 3 = 1 then 13 else 45) else (if t 3 = 0 then 1470 else if t 3 = 1 then 915 else 921)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 19 else if t 3 = 1 then 11 else 1506) else if t 2 = 1 then (if t 3 = 0 then 17 else if t 3 = 1 then 9 else 42) else (if t 3 = 0 then 64 else if t 3 = 1 then 59 else 72)) else (if t 2 = 0 then (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 1511) else if t 2 = 1 then (if t 3 = 0 then 34 else if t 3 = 1 then 29 else 51) else (if t 3 = 0 then 70 else if t 3 = 1 then 68 else 76))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 102 else 2744) else if t 2 = 1 then (if t 3 = 0 then 1806 else if t 3 = 1 then 96 else 98) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1476 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 899 else if t 3 = 1 then 90 else 1521) else if t 2 = 1 then (if t 3 = 0 then 897 else if t 3 = 1 then 78 else 80) else (if t 3 = 0 then 2127 else if t 3 = 1 then 82 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 902 else if t 3 = 1 then 91 else 1522) else if t 2 = 1 then (if t 3 = 0 then 901 else if t 3 = 1 then 79 else 81) else (if t 3 = 0 then 2128 else if t 3 = 1 then 83 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4845 else (if jt.2.val < 2 then 4879 else 4850)) else (if jt.2.val < 4 then 4878 else (if jt.2.val < 5 then 4880 else 4848))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3831 else (if jt.2.val < 2 then 3940 else 3835)) else (if jt.2.val < 4 then 3937 else (if jt.2.val < 5 then 3938 else 3805)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1997 else (if jt.2.val < 2 then 2002 else 2003)) else (if jt.2.val < 4 then 1999 else (if jt.2.val < 5 then 2001 else 2000))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2085 else (if jt.2.val < 2 then 2123 else 2088)) else (if jt.2.val < 4 then 2121 else (if jt.2.val < 5 then 2122 else 2044)))))

checked_coverage fastCoverage0781 pairing0781 template0781 witness0781

theorem coverage0781 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0781) (maskBits m))
    cores template0781 witness0781 := by
  rw [← coresFast_eq]
  exact fastCoverage0781

theorem coverageSize0781 : ∀ q : Pattern,
    (cores (witness0781 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0781 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0781
#print axioms coverageSize0781

noncomputable def pairing0782 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 3)))) (by decide +kernel)

noncomputable def template0782 : List (Fin 4935) := templateData0782

noncomputable def witness0782 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1031 else 1519) else if t 2 = 1 then (if t 3 = 0 then 1025 else if t 3 = 1 then 1023 else 659) else (if t 3 = 0 then 2146 else if t 3 = 1 then 1049 else 669)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1027 else 467) else if t 2 = 1 then (if t 3 = 0 then 1021 else if t 3 = 1 then 1019 else 1069) else (if t 3 = 0 then 1813 else if t 3 = 1 then 1046 else 1075)) else (if t 2 = 0 then (if t 3 = 0 then 3340 else if t 3 = 1 then 2973 else 2738) else if t 2 = 1 then (if t 3 = 0 then 3338 else if t 3 = 1 then 2970 else 2979) else (if t 3 = 0 then 4532 else if t 3 = 1 then 4046 else 3905))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1030 else 1518) else if t 2 = 1 then (if t 3 = 0 then 1024 else if t 3 = 1 then 1022 else 658) else (if t 3 = 0 then 2145 else if t 3 = 1 then 1048 else 668)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1026 else 466) else if t 2 = 1 then (if t 3 = 0 then 1020 else if t 3 = 1 then 1018 else 1068) else (if t 3 = 0 then 1812 else if t 3 = 1 then 1045 else 1074)) else (if t 2 = 0 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1041 else 472) else if t 2 = 1 then (if t 3 = 0 then 1038 else if t 3 = 1 then 1037 else 1072) else (if t 3 = 0 then 1817 else if t 3 = 1 then 1054 else 1076))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 1548 else 4542) else if t 2 = 1 then (if t 3 = 0 then 785 else if t 3 = 1 then 783 else 1824) else (if t 3 = 0 then 2801 else if t 3 = 1 then 789 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 596 else if t 3 = 1 then 594 else 2148) else if t 2 = 1 then (if t 3 = 0 then 1079 else if t 3 = 1 then 1077 else 1086) else (if t 3 = 0 then 1689 else if t 3 = 1 then 1083 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 599 else if t 3 = 1 then 598 else 2149) else if t 2 = 1 then (if t 3 = 0 then 1082 else if t 3 = 1 then 1081 else 1087) else (if t 3 = 0 then 1691 else if t 3 = 1 then 1085 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4905 else (if jt.2.val < 2 then 4912 else 4910)) else (if jt.2.val < 4 then 4911 else (if jt.2.val < 5 then 4913 else 4908))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3273 else (if jt.2.val < 2 then 3339 else 3277)) else (if jt.2.val < 4 then 3336 else (if jt.2.val < 5 then 3337 else 3245)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2077 else (if jt.2.val < 2 then 2144 else 2080)) else (if jt.2.val < 4 then 2142 else (if jt.2.val < 5 then 2143 else 2045))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1811 else (if jt.2.val < 2 then 1822 else 1823)) else (if jt.2.val < 4 then 1819 else (if jt.2.val < 5 then 1821 else 1820)))))

checked_coverage fastCoverage0782 pairing0782 template0782 witness0782

theorem coverage0782 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0782) (maskBits m))
    cores template0782 witness0782 := by
  rw [← coresFast_eq]
  exact fastCoverage0782

theorem coverageSize0782 : ∀ q : Pattern,
    (cores (witness0782 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0782 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0782
#print axioms coverageSize0782

noncomputable def pairing0783 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 3 else 6)))) (by decide +kernel)

noncomputable def template0783 : List (Fin 4935) := templateData0783

noncomputable def witness0783 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1568 else 1134) else if t 2 = 1 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1564 else 656) else (if t 3 = 0 then 271 else if t 3 = 1 then 266 else 2170)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1566 else 464) else if t 2 = 1 then (if t 3 = 0 then 1570 else if t 3 = 1 then 1562 else 1593) else (if t 3 = 0 then 855 else if t 3 = 1 then 1589 else 1597)) else (if t 2 = 0 then (if t 3 = 0 then 2485 else if t 3 = 1 then 2482 else 3344) else if t 2 = 1 then (if t 3 = 0 then 2855 else if t 3 = 1 then 3219 else 3225) else (if t 3 = 0 then 3954 else if t 3 = 1 then 3953 else 4525))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1567 else 1133) else if t 2 = 1 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1563 else 655) else (if t 3 = 0 then 270 else if t 3 = 1 then 265 else 2169)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1565 else 463) else if t 2 = 1 then (if t 3 = 0 then 1569 else if t 3 = 1 then 1561 else 1592) else (if t 3 = 0 then 854 else if t 3 = 1 then 1588 else 1596)) else (if t 2 = 0 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1582 else 471) else if t 2 = 1 then (if t 3 = 0 then 1584 else if t 3 = 1 then 1580 else 1595) else (if t 3 = 0 then 857 else if t 3 = 1 then 1591 else 1600))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1620 else 3960) else if t 2 = 1 then (if t 3 = 0 then 1854 else if t 3 = 1 then 1614 else 686) else (if t 3 = 0 then 3345 else if t 3 = 1 then 296 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2172 else if t 3 = 1 then 1617 else 494) else if t 2 = 1 then (if t 3 = 0 then 1851 else if t 3 = 1 then 1602 else 1606) else (if t 3 = 0 then 876 else if t 3 = 1 then 1604 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 2173 else if t 3 = 1 then 1618 else 495) else if t 2 = 1 then (if t 3 = 0 then 1852 else if t 3 = 1 then 1603 else 1607) else (if t 3 = 0 then 877 else if t 3 = 1 then 1605 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4926 else (if jt.2.val < 2 then 4933 else 4931)) else (if jt.2.val < 4 then 4932 else (if jt.2.val < 5 then 4934 else 4929))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3176 else (if jt.2.val < 2 then 3220 else 3179)) else (if jt.2.val < 4 then 3217 else (if jt.2.val < 5 then 3218 else 3171)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2000 else (if jt.2.val < 2 then 2035 else 2003)) else (if jt.2.val < 4 then 2031 else (if jt.2.val < 5 then 2032 else 1997))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1820 else (if jt.2.val < 2 then 1847 else 1823)) else (if jt.2.val < 4 then 1842 else (if jt.2.val < 5 then 1843 else 1811)))))

checked_coverage fastCoverage0783 pairing0783 template0783 witness0783

theorem coverage0783 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0783) (maskBits m))
    cores template0783 witness0783 := by
  rw [← coresFast_eq]
  exact fastCoverage0783

theorem coverageSize0783 : ∀ q : Pattern,
    (cores (witness0783 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0783 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0783
#print axioms coverageSize0783

noncomputable def pairing0784 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0784 : List (Fin 4935) := templateData0784

noncomputable def witness0784 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4486 else if t 3 = 1 then 4478 else 4066) else if t 2 = 1 then (if t 3 = 0 then 4482 else if t 3 = 1 then 4474 else 3351) else (if t 3 = 0 then 3236 else if t 3 = 1 then 3235 else 2547)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4484 else if t 3 = 1 then 4476 else 1881) else if t 2 = 1 then (if t 3 = 0 then 4480 else if t 3 = 1 then 4472 else 1880) else (if t 3 = 0 then 1651 else if t 3 = 1 then 1649 else 1670)) else (if t 2 = 0 then (if t 3 = 0 then 2201 else if t 3 = 1 then 2199 else 980) else if t 2 = 1 then (if t 3 = 0 then 2200 else if t 3 = 1 then 2198 else 1892) else (if t 3 = 0 then 743 else if t 3 = 1 then 1661 else 1676))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4485 else if t 3 = 1 then 4477 else 1722) else if t 2 = 1 then (if t 3 = 0 then 4481 else if t 3 = 1 then 4473 else 1721) else (if t 3 = 0 then 1332 else if t 3 = 1 then 1330 else 1355)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4483 else if t 3 = 1 then 4475 else 3270) else if t 2 = 1 then (if t 3 = 0 then 4479 else if t 3 = 1 then 4471 else 4498) else (if t 3 = 0 then 3829 else if t 3 = 1 then 4505 else 4507)) else (if t 2 = 0 then (if t 3 = 0 then 3466 else if t 3 = 1 then 3465 else 3280) else if t 2 = 1 then (if t 3 = 0 then 4157 else if t 3 = 1 then 4492 else 4499) else (if t 3 = 0 then 3838 else if t 3 = 1 then 4506 else 4513))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1443 else 782) else if t 2 = 1 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1442 else 1451) else (if t 3 = 0 then 1013 else if t 3 = 1 then 1778 else 2120)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3161 else 3166) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 4514 else 4516) else (if t 3 = 0 then 4038 else if t 3 = 1 then 4518 else 4520)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 3164 else 3168) else if t 2 = 1 then (if t 3 = 0 then 3916 else if t 3 = 1 then 4515 else 4517) else (if t 3 = 0 then 4040 else if t 3 = 1 then 4519 else 4521))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4926 else (if jt.2.val < 2 then 4928 else 4931)) else (if jt.2.val < 4 then 4927 else (if jt.2.val < 5 then 4930 else 4929))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4711 else (if jt.2.val < 2 then 4715 else 4716)) else (if jt.2.val < 4 then 4712 else (if jt.2.val < 5 then 4714 else 4713)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4468 else (if jt.2.val < 2 then 4503 else 4504)) else (if jt.2.val < 4 then 4500 else (if jt.2.val < 5 then 4502 else 4501))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4593 else (if jt.2.val < 2 then 4597 else 4598)) else (if jt.2.val < 4 then 4594 else (if jt.2.val < 5 then 4596 else 4595)))))

checked_coverage fastCoverage0784 pairing0784 template0784 witness0784

theorem coverage0784 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0784) (maskBits m))
    cores template0784 witness0784 := by
  rw [← coresFast_eq]
  exact fastCoverage0784

theorem coverageSize0784 : ∀ q : Pattern,
    (cores (witness0784 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0784 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0784
#print axioms coverageSize0784

noncomputable def pairing0785 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0785 : List (Fin 4935) := templateData0785

noncomputable def witness0785 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 4537) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 3350) else (if t 3 = 0 then 2751 else if t 3 = 1 then 2750 else 3210)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 1879) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 1878) else (if t 3 = 0 then 539 else if t 3 = 1 then 537 else 554)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1171 else 2138) else if t 2 = 1 then (if t 3 = 0 then 1174 else if t 3 = 1 then 1170 else 1188) else (if t 3 = 0 then 1544 else if t 3 = 1 then 568 else 575))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 1720) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 1719) else (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 261)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 3269) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 3993) else (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4016)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2841) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4003) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4017 else 4018))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 390 else 1499) else if t 2 = 1 then (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 397) else (if t 3 = 0 then 2141 else if t 3 = 1 then 925 else 927)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2719) else if t 2 = 1 then (if t 3 = 0 then 3917 else if t 3 = 1 then 4019 else 4020) else (if t 3 = 0 then 4191 else if t 3 = 1 then 4023 else 4024)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2723 else 2725) else if t 2 = 1 then (if t 3 = 0 then 3919 else if t 3 = 1 then 4021 else 4022) else (if t 3 = 0 then 4526 else if t 3 = 1 then 4025 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4899 else (if jt.2.val < 2 then 4901 else 4904)) else (if jt.2.val < 4 then 4900 else (if jt.2.val < 5 then 4903 else 4902))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3971 else (if jt.2.val < 2 then 3999 else 4001)) else (if jt.2.val < 4 then 3996 else (if jt.2.val < 5 then 3998 else 3997)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3970 else (if jt.2.val < 2 then 4013 else 4014)) else (if jt.2.val < 4 then 4010 else (if jt.2.val < 5 then 4012 else 4011))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4595 else (if jt.2.val < 2 then 4601 else 4598)) else (if jt.2.val < 4 then 4599 else (if jt.2.val < 5 then 4600 else 4593)))))

checked_coverage fastCoverage0785 pairing0785 template0785 witness0785

theorem coverage0785 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0785) (maskBits m))
    cores template0785 witness0785 := by
  rw [← coresFast_eq]
  exact fastCoverage0785

theorem coverageSize0785 : ∀ q : Pattern,
    (cores (witness0785 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0785 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0785
#print axioms coverageSize0785

noncomputable def pairing0786 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0786 : List (Fin 4935) := templateData0786

noncomputable def witness0786 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3062 else 2770) else if t 2 = 1 then (if t 3 = 0 then 3058 else if t 3 = 1 then 3054 else 2768) else (if t 3 = 0 then 4530 else if t 3 = 1 then 3963 else 4058)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3060 else 144) else if t 2 = 1 then (if t 3 = 0 then 3056 else if t 3 = 1 then 3052 else 140) else (if t 3 = 0 then 1648 else if t 3 = 1 then 1646 else 157)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 344 else 1496) else if t 2 = 1 then (if t 3 = 0 then 341 else if t 3 = 1 then 340 else 892) else (if t 3 = 0 then 2159 else if t 3 = 1 then 357 else 896))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3061 else 638) else if t 2 = 1 then (if t 3 = 0 then 3057 else if t 3 = 1 then 3053 else 634) else (if t 3 = 0 then 1329 else if t 3 = 1 then 1327 else 650)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3059 else 3091) else if t 2 = 1 then (if t 3 = 0 then 3055 else if t 3 = 1 then 3051 else 3089) else (if t 3 = 0 then 3073 else if t 3 = 1 then 3071 else 3092)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 3082 else 3095) else if t 2 = 1 then (if t 3 = 0 then 2470 else if t 3 = 1 then 3080 else 3094) else (if t 3 = 0 then 2474 else if t 3 = 1 then 3083 else 3096))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1219 else 2162) else if t 2 = 1 then (if t 3 = 0 then 1213 else if t 3 = 1 then 1207 else 691) else (if t 3 = 0 then 1375 else if t 3 = 1 then 1209 else 693)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 3313 else 3500) else if t 2 = 1 then (if t 3 = 0 then 2956 else if t 3 = 1 then 3098 else 3102) else (if t 3 = 0 then 2957 else if t 3 = 1 then 3099 else 3103)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 3315 else 4531) else if t 2 = 1 then (if t 3 = 0 then 2504 else if t 3 = 1 then 3100 else 3104) else (if t 3 = 0 then 2505 else if t 3 = 1 then 3101 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4851 else (if jt.2.val < 2 then 4853 else 4856)) else (if jt.2.val < 4 then 4852 else (if jt.2.val < 5 then 4855 else 4854))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3049 else (if jt.2.val < 2 then 3079 else 3081)) else (if jt.2.val < 4 then 3076 else (if jt.2.val < 5 then 3078 else 3077)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4501 else (if jt.2.val < 2 then 4529 else 4504)) else (if jt.2.val < 4 then 4527 else (if jt.2.val < 5 then 4528 else 4468))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3048 else (if jt.2.val < 2 then 3088 else 3090)) else (if jt.2.val < 4 then 3085 else (if jt.2.val < 5 then 3087 else 3086)))))

checked_coverage fastCoverage0786 pairing0786 template0786 witness0786

theorem coverage0786 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0786) (maskBits m))
    cores template0786 witness0786 := by
  rw [← coresFast_eq]
  exact fastCoverage0786

theorem coverageSize0786 : ∀ q : Pattern,
    (cores (witness0786 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0786 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0786
#print axioms coverageSize0786

noncomputable def pairing0787 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0787 : List (Fin 4935) := templateData0787

noncomputable def witness0787 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2602 else 3174) else if t 2 = 1 then (if t 3 = 0 then 2598 else if t 3 = 1 then 2594 else 3172) else (if t 3 = 0 then 4044 else if t 3 = 1 then 3923 else 4541)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2600 else 143) else if t 2 = 1 then (if t 3 = 0 then 2596 else if t 3 = 1 then 2592 else 139) else (if t 3 = 0 then 536 else if t 3 = 1 then 534 else 1537)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1415 else 173) else if t 2 = 1 then (if t 3 = 0 then 1413 else if t 3 = 1 then 1411 else 171) else (if t 3 = 0 then 1109 else if t 3 = 1 then 567 else 2117))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2601 else 637) else if t 2 = 1 then (if t 3 = 0 then 2597 else if t 3 = 1 then 2593 else 633) else (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 1463)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2599 else 2623) else if t 2 = 1 then (if t 3 = 0 then 2595 else if t 3 = 1 then 2591 else 2620) else (if t 3 = 0 then 2613 else if t 3 = 1 then 2611 else 2625)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2632 else 2637) else if t 2 = 1 then (if t 3 = 0 then 2897 else if t 3 = 1 then 2629 else 2636) else (if t 3 = 0 then 2899 else if t 3 = 1 then 2634 else 2638))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2227 else 1147) else if t 2 = 1 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2221 else 685) else (if t 3 = 0 then 307 else if t 3 = 1 then 295 else 1474)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3515 else if t 3 = 1 then 2902 else 2904) else if t 2 = 1 then (if t 3 = 0 then 2650 else if t 3 = 1 then 2640 else 2642) else (if t 3 = 0 then 2651 else if t 3 = 1 then 2641 else 2643)) else (if t 2 = 0 then (if t 3 = 0 then 4533 else if t 3 = 1 then 3321 else 4045) else if t 2 = 1 then (if t 3 = 0 then 3183 else if t 3 = 1 then 2644 else 2646) else (if t 3 = 0 then 3184 else if t 3 = 1 then 2645 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4887 else (if jt.2.val < 2 then 4889 else 4892)) else (if jt.2.val < 4 then 4888 else (if jt.2.val < 5 then 4891 else 4890))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3171 else (if jt.2.val < 2 then 3178 else 3179)) else (if jt.2.val < 4 then 3175 else (if jt.2.val < 5 then 3177 else 3176)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4011 else (if jt.2.val < 2 then 4043 else 4014)) else (if jt.2.val < 4 then 4041 else (if jt.2.val < 5 then 4042 else 3970))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3086 else (if jt.2.val < 2 then 3173 else 3090)) else (if jt.2.val < 4 then 3169 else (if jt.2.val < 5 then 3170 else 3048)))))

checked_coverage fastCoverage0787 pairing0787 template0787 witness0787

theorem coverage0787 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0787) (maskBits m))
    cores template0787 witness0787 := by
  rw [← coresFast_eq]
  exact fastCoverage0787

theorem coverageSize0787 : ∀ q : Pattern,
    (cores (witness0787 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0787 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0787
#print axioms coverageSize0787

noncomputable def pairing0788 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0788 : List (Fin 4935) := templateData0788

noncomputable def witness0788 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2058 else 1053) else if t 2 = 1 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2056 else 1733) else (if t 3 = 0 then 50 else if t 3 = 1 then 1342 else 1359)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2054 else if t 3 = 1 then 2050 else 1051) else if t 2 = 1 then (if t 3 = 0 then 2052 else if t 3 = 1 then 2048 else 2082) else (if t 3 = 0 then 48 else if t 3 = 1 then 2090 else 2098)) else (if t 2 = 0 then (if t 3 = 0 then 4546 else if t 3 = 1 then 4211 else 4047) else if t 2 = 1 then (if t 3 = 0 then 3530 else if t 3 = 1 then 3528 else 2939) else (if t 3 = 0 then 3192 else if t 3 = 1 then 2690 else 2706))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2057 else 1052) else if t 2 = 1 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2055 else 1732) else (if t 3 = 0 then 49 else if t 3 = 1 then 1341 else 1358)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2053 else if t 3 = 1 then 2049 else 1050) else if t 2 = 1 then (if t 3 = 0 then 2051 else if t 3 = 1 then 2047 else 2081) else (if t 3 = 0 then 47 else if t 3 = 1 then 2089 else 2097)) else (if t 2 = 0 then (if t 3 = 0 then 2071 else if t 3 = 1 then 2069 else 1056) else if t 2 = 1 then (if t 3 = 0 then 2070 else if t 3 = 1 then 2067 else 2083) else (if t 3 = 0 then 53 else if t 3 = 1 then 2091 else 2099))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 590 else 3216) else if t 2 = 1 then (if t 3 = 0 then 194 else if t 3 = 1 then 1446 else 1452) else (if t 3 = 0 then 4059 else if t 3 = 1 then 1779 else 4538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1545 else if t 3 = 1 then 588 else 600) else if t 2 = 1 then (if t 3 = 0 then 192 else if t 3 = 1 then 2100 else 2103) else (if t 3 = 0 then 903 else if t 3 = 1 then 2106 else 2109)) else (if t 2 = 0 then (if t 3 = 0 then 1547 else if t 3 = 1 then 592 else 602) else if t 2 = 1 then (if t 3 = 0 then 196 else if t 3 = 1 then 2102 else 2105) else (if t 3 = 0 then 905 else if t 3 = 1 then 2108 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4887 else (if jt.2.val < 2 then 4894 else 4892)) else (if jt.2.val < 4 then 4893 else (if jt.2.val < 5 then 4895 else 4890))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4713 else (if jt.2.val < 2 then 4724 else 4716)) else (if jt.2.val < 4 then 4722 else (if jt.2.val < 5 then 4723 else 4711)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2322 else (if jt.2.val < 2 then 2332 else 2333)) else (if jt.2.val < 4 then 2329 else (if jt.2.val < 5 then 2331 else 2330))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2323 else (if jt.2.val < 2 then 2327 else 2328)) else (if jt.2.val < 4 then 2324 else (if jt.2.val < 5 then 2326 else 2325)))))

checked_coverage fastCoverage0788 pairing0788 template0788 witness0788

theorem coverage0788 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0788) (maskBits m))
    cores template0788 witness0788 := by
  rw [← coresFast_eq]
  exact fastCoverage0788

theorem coverageSize0788 : ∀ q : Pattern,
    (cores (witness0788 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0788 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0788
#print axioms coverageSize0788

noncomputable def pairing0789 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0789 : List (Fin 4935) := templateData0789

noncomputable def witness0789 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 803 else 2146) else if t 2 = 1 then (if t 3 = 0 then 809 else if t 3 = 1 then 801 else 833) else (if t 3 = 0 then 1471 else if t 3 = 1 then 269 else 279)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 807 else if t 3 = 1 then 799 else 1813) else if t 2 = 1 then (if t 3 = 0 then 805 else if t 3 = 1 then 797 else 830) else (if t 3 = 0 then 65 else if t 3 = 1 then 853 else 859)) else (if t 2 = 0 then (if t 3 = 0 then 4056 else if t 3 = 1 then 4054 else 4532) else if t 2 = 1 then (if t 3 = 0 then 2996 else if t 3 = 1 then 2993 else 3329) else (if t 3 = 0 then 2795 else if t 3 = 1 then 3002 else 3152))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 802 else 2145) else if t 2 = 1 then (if t 3 = 0 then 808 else if t 3 = 1 then 800 else 832) else (if t 3 = 0 then 1470 else if t 3 = 1 then 268 else 278)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 806 else if t 3 = 1 then 798 else 1812) else if t 2 = 1 then (if t 3 = 0 then 804 else if t 3 = 1 then 796 else 829) else (if t 3 = 0 then 64 else if t 3 = 1 then 852 else 858)) else (if t 2 = 0 then (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 1817) else if t 2 = 1 then (if t 3 = 0 then 821 else if t 3 = 1 then 816 else 838) else (if t 3 = 0 then 70 else if t 3 = 1 then 856 else 860))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 401 else 2801) else if t 2 = 1 then (if t 3 = 0 then 1500 else if t 3 = 1 then 399 else 405) else (if t 3 = 0 then 4540 else if t 3 = 1 then 1788 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 200 else if t 3 = 1 then 863 else 1689) else if t 2 = 1 then (if t 3 = 0 then 198 else if t 3 = 1 then 861 else 867) else (if t 3 = 0 then 2127 else if t 3 = 1 then 870 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 203 else if t 3 = 1 then 866 else 1691) else if t 2 = 1 then (if t 3 = 0 then 202 else if t 3 = 1 then 865 else 869) else (if t 3 = 0 then 2128 else if t 3 = 1 then 871 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4851 else (if jt.2.val < 2 then 4876 else 4856)) else (if jt.2.val < 4 then 4875 else (if jt.2.val < 5 then 4877 else 4854))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3997 else (if jt.2.val < 2 then 4055 else 4001)) else (if jt.2.val < 4 then 4052 else (if jt.2.val < 5 then 4053 else 3971)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2288 else (if jt.2.val < 2 then 2293 else 2294)) else (if jt.2.val < 4 then 2290 else (if jt.2.val < 5 then 2292 else 2291))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2325 else (if jt.2.val < 2 then 2336 else 2328)) else (if jt.2.val < 4 then 2334 else (if jt.2.val < 5 then 2335 else 2323)))))

checked_coverage fastCoverage0789 pairing0789 template0789 witness0789

theorem coverage0789 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0789) (maskBits m))
    cores template0789 witness0789 := by
  rw [← coresFast_eq]
  exact fastCoverage0789

theorem coverageSize0789 : ∀ q : Pattern,
    (cores (witness0789 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0789 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0789
#print axioms coverageSize0789

noncomputable def pairing0790 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 3)))) (by decide +kernel)

noncomputable def template0790 : List (Fin 4935) := templateData0790

noncomputable def witness0790 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 430 else 1519) else if t 2 = 1 then (if t 3 = 0 then 424 else if t 3 = 1 then 422 else 1132) else (if t 3 = 0 then 2125 else if t 3 = 1 then 448 else 1138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 428 else if t 3 = 1 then 426 else 467) else if t 2 = 1 then (if t 3 = 0 then 420 else if t 3 = 1 then 418 else 462) else (if t 3 = 0 then 1507 else if t 3 = 1 then 445 else 475)) else (if t 2 = 0 then (if t 3 = 0 then 3205 else if t 3 = 1 then 2731 else 2738) else if t 2 = 1 then (if t 3 = 0 then 3203 else if t 3 = 1 then 2728 else 2737) else (if t 3 = 0 then 4539 else if t 3 = 1 then 3929 else 4036))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 429 else 1518) else if t 2 = 1 then (if t 3 = 0 then 423 else if t 3 = 1 then 421 else 1131) else (if t 3 = 0 then 2124 else if t 3 = 1 then 447 else 1137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 427 else if t 3 = 1 then 425 else 466) else if t 2 = 1 then (if t 3 = 0 then 419 else if t 3 = 1 then 417 else 461) else (if t 3 = 0 then 1506 else if t 3 = 1 then 444 else 474)) else (if t 2 = 0 then (if t 3 = 0 then 441 else if t 3 = 1 then 440 else 472) else if t 2 = 1 then (if t 3 = 0 then 437 else if t 3 = 1 then 436 else 470) else (if t 3 = 0 then 1511 else if t 3 = 1 then 453 else 478))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 1836 else 4542) else if t 2 = 1 then (if t 3 = 0 then 504 else if t 3 = 1 then 498 else 1524) else (if t 3 = 0 then 2744 else if t 3 = 1 then 500 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1115 else if t 3 = 1 then 1113 else 2148) else if t 2 = 1 then (if t 3 = 0 then 492 else if t 3 = 1 then 480 else 484) else (if t 3 = 0 then 1521 else if t 3 = 1 then 482 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 1118 else if t 3 = 1 then 1117 else 2149) else if t 2 = 1 then (if t 3 = 0 then 493 else if t 3 = 1 then 481 else 485) else (if t 3 = 0 then 1522 else if t 3 = 1 then 483 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4899 else (if jt.2.val < 2 then 4915 else 4904)) else (if jt.2.val < 4 then 4914 else (if jt.2.val < 5 then 4916 else 4902))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3077 else (if jt.2.val < 2 then 3204 else 3081)) else (if jt.2.val < 4 then 3201 else (if jt.2.val < 5 then 3202 else 3049)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2330 else (if jt.2.val < 2 then 2345 else 2333)) else (if jt.2.val < 4 then 2343 else (if jt.2.val < 5 then 2344 else 2322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1505 else (if jt.2.val < 2 then 1516 else 1517)) else (if jt.2.val < 4 then 1513 else (if jt.2.val < 5 then 1515 else 1514)))))

checked_coverage fastCoverage0790 pairing0790 template0790 witness0790

theorem coverage0790 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0790) (maskBits m))
    cores template0790 witness0790 := by
  rw [← coresFast_eq]
  exact fastCoverage0790

theorem coverageSize0790 : ∀ q : Pattern,
    (cores (witness0790 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0790 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0790
#print axioms coverageSize0790

noncomputable def pairing0791 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 3 else 5)))) (by decide +kernel)

noncomputable def template0791 : List (Fin 4935) := templateData0791

noncomputable def witness0791 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1572 else 661) else if t 2 = 1 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1564 else 656) else (if t 3 = 0 then 918 else if t 3 = 1 then 266 else 2170)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1570 else 1071) else if t 2 = 1 then (if t 3 = 0 then 1566 else if t 3 = 1 then 1562 else 1593) else (if t 3 = 0 then 62 else if t 3 = 1 then 1589 else 1597)) else (if t 2 = 0 then (if t 3 = 0 then 2485 else if t 3 = 1 then 2855 else 3226) else if t 2 = 1 then (if t 3 = 0 then 2482 else if t 3 = 1 then 3219 else 3225) else (if t 3 = 0 then 4060 else if t 3 = 1 then 3953 else 4525))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1571 else 660) else if t 2 = 1 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1563 else 655) else (if t 3 = 0 then 917 else if t 3 = 1 then 265 else 2169)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1569 else 1070) else if t 2 = 1 then (if t 3 = 0 then 1565 else if t 3 = 1 then 1561 else 1592) else (if t 3 = 0 then 61 else if t 3 = 1 then 1588 else 1596)) else (if t 2 = 0 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1584 else 1073) else if t 2 = 1 then (if t 3 = 0 then 1582 else if t 3 = 1 then 1580 else 1595) else (if t 3 = 0 then 69 else if t 3 = 1 then 1591 else 1600))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4547 else if t 3 = 1 then 1854 else 4061) else if t 2 = 1 then (if t 3 = 0 then 1620 else if t 3 = 1 then 1614 else 686) else (if t 3 = 0 then 3229 else if t 3 = 1 then 296 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2172 else if t 3 = 1 then 1851 else 1092) else if t 2 = 1 then (if t 3 = 0 then 1617 else if t 3 = 1 then 1602 else 1606) else (if t 3 = 0 then 92 else if t 3 = 1 then 1604 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 2173 else if t 3 = 1 then 1852 else 1093) else if t 2 = 1 then (if t 3 = 0 then 1618 else if t 3 = 1 then 1603 else 1607) else (if t 3 = 0 then 93 else if t 3 = 1 then 1605 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4926 else (if jt.2.val < 2 then 4933 else 4931)) else (if jt.2.val < 4 then 4932 else (if jt.2.val < 5 then 4934 else 4929))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3176 else (if jt.2.val < 2 then 3220 else 3179)) else (if jt.2.val < 4 then 3217 else (if jt.2.val < 5 then 3218 else 3171)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2291 else (if jt.2.val < 2 then 2315 else 2294)) else (if jt.2.val < 4 then 2313 else (if jt.2.val < 5 then 2314 else 2288))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1514 else (if jt.2.val < 2 then 1594 else 1517)) else (if jt.2.val < 4 then 1557 else (if jt.2.val < 5 then 1558 else 1505)))))

checked_coverage fastCoverage0791 pairing0791 template0791 witness0791

theorem coverage0791 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0791) (maskBits m))
    cores template0791 witness0791 := by
  rw [← coresFast_eq]
  exact fastCoverage0791

theorem coverageSize0791 : ∀ q : Pattern,
    (cores (witness0791 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0791 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0791
#print axioms coverageSize0791

noncomputable def pairing0792 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0792 : List (Fin 4935) := templateData0792

noncomputable def witness0792 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4150 else if t 3 = 1 then 4142 else 3941) else if t 2 = 1 then (if t 3 = 0 then 4146 else if t 3 = 1 then 4138 else 2788) else (if t 3 = 0 then 3532 else if t 3 = 1 then 3530 else 3192)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4148 else if t 3 = 1 then 4140 else 726) else if t 2 = 1 then (if t 3 = 0 then 4144 else if t 3 = 1 then 4136 else 725) else (if t 3 = 0 then 2200 else if t 3 = 1 then 2196 else 742)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1173 else 758) else if t 2 = 1 then (if t 3 = 0 then 1174 else if t 3 = 1 then 1172 else 757) else (if t 3 = 0 then 1190 else if t 3 = 1 then 1189 else 764))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4149 else if t 3 = 1 then 4141 else 35) else if t 2 = 1 then (if t 3 = 0 then 4145 else if t 3 = 1 then 4137 else 34) else (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 53)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 4147 else if t 3 = 1 then 4139 else 2462) else if t 2 = 1 then (if t 3 = 0 then 4143 else if t 3 = 1 then 4135 else 4170) else (if t 3 = 0 then 4157 else if t 3 = 1 then 4155 else 4171)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2829 else 2487) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4163 else 4177) else (if t 3 = 0 then 4004 else if t 3 = 1 then 4164 else 4178))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 189 else 902) else if t 2 = 1 then (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 901) else (if t 3 = 0 then 197 else if t 3 = 1 then 196 else 905)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2570 else 2885) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 4179 else 4183) else (if t 3 = 0 then 3916 else if t 3 = 1 then 4180 else 4184)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2578 else 3507) else if t 2 = 1 then (if t 3 = 0 then 3919 else if t 3 = 1 then 4181 else 4185) else (if t 3 = 0 then 3920 else if t 3 = 1 then 4182 else 4186))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4917 else (if jt.2.val < 2 then 4919 else 4922)) else (if jt.2.val < 4 then 4918 else (if jt.2.val < 5 then 4921 else 4920))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4133 else (if jt.2.val < 2 then 4161 else 4162)) else (if jt.2.val < 4 then 4158 else (if jt.2.val < 5 then 4160 else 4159)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4728 else (if jt.2.val < 2 then 4732 else 4733)) else (if jt.2.val < 4 then 4729 else (if jt.2.val < 5 then 4731 else 4730))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4216 else (if jt.2.val < 2 then 4220 else 4221)) else (if jt.2.val < 4 then 4217 else (if jt.2.val < 5 then 4219 else 4218)))))

checked_coverage fastCoverage0792 pairing0792 template0792 witness0792

theorem coverage0792 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0792) (maskBits m))
    cores template0792 witness0792 := by
  rw [← coresFast_eq]
  exact fastCoverage0792

theorem coverageSize0792 : ∀ q : Pattern,
    (cores (witness0792 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0792 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0792
#print axioms coverageSize0792

noncomputable def pairing0793 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0793 : List (Fin 4935) := templateData0793

noncomputable def witness0793 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 4196) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2787) else (if t 3 = 0 then 3236 else if t 3 = 1 then 3234 else 3522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 724) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 723) else (if t 3 = 0 then 1651 else if t 3 = 1 then 1647 else 741)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 536 else 1109) else if t 2 = 1 then (if t 3 = 0 then 539 else if t 3 = 1 then 535 else 1108) else (if t 3 = 0 then 555 else if t 3 = 1 then 553 else 1112))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 33) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 32) else (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 52)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2461) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3834) else (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3837)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2899) else if t 2 = 1 then (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3848) else (if t 3 = 0 then 3847 else if t 3 = 1 then 3846 else 3850))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 1003 else 103) else if t 2 = 1 then (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 97) else (if t 3 = 0 then 1013 else if t 3 = 1 then 999 else 99)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2503) else if t 2 = 1 then (if t 3 = 0 then 4037 else if t 3 = 1 then 3852 else 3854) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3853 else 3855)) else (if t 2 = 0 then (if t 3 = 0 then 3516 else if t 3 = 1 then 2651 else 3184) else if t 2 = 1 then (if t 3 = 0 then 4191 else if t 3 = 1 then 3856 else 3858) else (if t 3 = 0 then 4192 else if t 3 = 1 then 3857 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4905 else (if jt.2.val < 2 then 4907 else 4910)) else (if jt.2.val < 4 then 4906 else (if jt.2.val < 5 then 4909 else 4908))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4095 else (if jt.2.val < 2 then 4105 else 4106)) else (if jt.2.val < 4 then 4102 else (if jt.2.val < 5 then 4104 else 4103)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4449 else (if jt.2.val < 2 then 4453 else 4454)) else (if jt.2.val < 4 then 4450 else (if jt.2.val < 5 then 4452 else 4451))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4218 else (if jt.2.val < 2 then 4229 else 4221)) else (if jt.2.val < 4 then 4227 else (if jt.2.val < 5 then 4228 else 4216)))))

checked_coverage fastCoverage0793 pairing0793 template0793 witness0793

theorem coverage0793 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0793) (maskBits m))
    cores template0793 witness0793 := by
  rw [← coresFast_eq]
  exact fastCoverage0793

theorem coverageSize0793 : ∀ q : Pattern,
    (cores (witness0793 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0793 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0793
#print axioms coverageSize0793

noncomputable def pairing0794 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0794 : List (Fin 4935) := templateData0794

noncomputable def witness0794 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3457 else if t 3 = 1 then 3449 else 3205) else if t 2 = 1 then (if t 3 = 0 then 3453 else if t 3 = 1 then 3445 else 2731) else (if t 3 = 0 then 4213 else if t 3 = 1 then 4211 else 3930)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3455 else if t 3 = 1 then 3447 else 343) else if t 2 = 1 then (if t 3 = 0 then 3451 else if t 3 = 1 then 3443 else 342) else (if t 3 = 0 then 2199 else if t 3 = 1 then 2195 else 358)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 964 else 374) else if t 2 = 1 then (if t 3 = 0 then 965 else if t 3 = 1 then 963 else 373) else (if t 3 = 0 then 980 else if t 3 = 1 then 979 else 380))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3456 else if t 3 = 1 then 3448 else 441) else if t 2 = 1 then (if t 3 = 0 then 3452 else if t 3 = 1 then 3444 else 440) else (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 455)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3454 else if t 3 = 1 then 3446 else 2471) else if t 2 = 1 then (if t 3 = 0 then 3450 else if t 3 = 1 then 3442 else 3479) else (if t 3 = 0 then 3465 else if t 3 = 1 then 3462 else 3480)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2838 else 2489) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3472 else 3486) else (if t 3 = 0 then 3280 else if t 3 = 1 then 3473 else 3487))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 585 else 1118) else if t 2 = 1 then (if t 3 = 0 then 586 else if t 3 = 1 then 584 else 1117) else (if t 3 = 0 then 593 else if t 3 = 1 then 592 else 1121)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2572 else 2886) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3488 else 3492) else (if t 3 = 0 then 3164 else if t 3 = 1 then 3489 else 3493)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2579 else 4197) else if t 2 = 1 then (if t 3 = 0 then 3167 else if t 3 = 1 then 3490 else 3494) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3491 else 3495))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4881 else (if jt.2.val < 2 then 4883 else 4886)) else (if jt.2.val < 4 then 4882 else (if jt.2.val < 5 then 4885 else 4884))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3440 else (if jt.2.val < 2 then 3470 else 3471)) else (if jt.2.val < 4 then 3467 else (if jt.2.val < 5 then 3469 else 3468)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4730 else (if jt.2.val < 2 then 4736 else 4733)) else (if jt.2.val < 4 then 4734 else (if jt.2.val < 5 then 4735 else 4728))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3538 else (if jt.2.val < 2 then 3542 else 3543)) else (if jt.2.val < 4 then 3539 else (if jt.2.val < 5 then 3541 else 3540)))))

checked_coverage fastCoverage0794 pairing0794 template0794 witness0794

theorem coverage0794 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0794) (maskBits m))
    cores template0794 witness0794 := by
  rw [← coresFast_eq]
  exact fastCoverage0794

theorem coverageSize0794 : ∀ q : Pattern,
    (cores (witness0794 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0794 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0794
#print axioms coverageSize0794

noncomputable def pairing0795 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 5 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0795 : List (Fin 4935) := templateData0795

noncomputable def witness0795 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3505) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 2730) else (if t 3 = 0 then 3965 else if t 3 = 1 then 3963 else 4205)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 341) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 340) else (if t 3 = 0 then 1650 else if t 3 = 1 then 1646 else 357)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 141 else 893) else if t 2 = 1 then (if t 3 = 0 then 144 else if t 3 = 1 then 140 else 892) else (if t 3 = 0 then 159 else if t 3 = 1 then 157 else 896))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 439) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 438) else (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 454)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2470) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3080) else (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3083)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2622 else 2900) else if t 2 = 1 then (if t 3 = 0 then 3091 else if t 3 = 1 then 3089 else 3094) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3092 else 3096))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1213 else 505) else if t 2 = 1 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1207 else 499) else (if t 3 = 0 then 1223 else if t 3 = 1 then 1209 else 501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2956 else 2504) else if t 2 = 1 then (if t 3 = 0 then 3313 else if t 3 = 1 then 3098 else 3100) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3099 else 3101)) else (if t 2 = 0 then (if t 3 = 0 then 4199 else if t 3 = 1 then 2652 else 3928) else if t 2 = 1 then (if t 3 = 0 then 3500 else if t 3 = 1 then 3102 else 3104) else (if t 3 = 0 then 3501 else if t 3 = 1 then 3103 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4851 else (if jt.2.val < 2 then 4853 else 4856)) else (if jt.2.val < 4 then 4852 else (if jt.2.val < 5 then 4855 else 4854))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3384 else (if jt.2.val < 2 then 3394 else 3395)) else (if jt.2.val < 4 then 3391 else (if jt.2.val < 5 then 3393 else 3392)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4451 else (if jt.2.val < 2 then 4463 else 4454)) else (if jt.2.val < 4 then 4461 else (if jt.2.val < 5 then 4462 else 4449))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3540 else (if jt.2.val < 2 then 3551 else 3543)) else (if jt.2.val < 4 then 3549 else (if jt.2.val < 5 then 3550 else 3538)))))

checked_coverage fastCoverage0795 pairing0795 template0795 witness0795

theorem coverage0795 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0795) (maskBits m))
    cores template0795 witness0795 := by
  rw [← coresFast_eq]
  exact fastCoverage0795

theorem coverageSize0795 : ∀ q : Pattern,
    (cores (witness0795 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0795 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0795
#print axioms coverageSize0795

noncomputable def pairing0796 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0796 : List (Fin 4935) := templateData0796

noncomputable def witness0796 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 807 else 67) else if t 2 = 1 then (if t 3 = 0 then 809 else if t 3 = 1 then 805 else 65) else (if t 3 = 0 then 837 else if t 3 = 1 then 835 else 75)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 803 else if t 3 = 1 then 799 else 855) else if t 2 = 1 then (if t 3 = 0 then 801 else if t 3 = 1 then 797 else 853) else (if t 3 = 0 then 833 else if t 3 = 1 then 830 else 859)) else (if t 2 = 0 then (if t 3 = 0 then 4203 else if t 3 = 1 then 4054 else 3954) else if t 2 = 1 then (if t 3 = 0 then 2995 else if t 3 = 1 then 2993 else 3002) else (if t 3 = 0 then 3514 else if t 3 = 1 then 3329 else 3152))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 806 else 66) else if t 2 = 1 then (if t 3 = 0 then 808 else if t 3 = 1 then 804 else 64) else (if t 3 = 0 then 836 else if t 3 = 1 then 834 else 74)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 802 else if t 3 = 1 then 798 else 854) else if t 2 = 1 then (if t 3 = 0 then 800 else if t 3 = 1 then 796 else 852) else (if t 3 = 0 then 832 else if t 3 = 1 then 829 else 858)) else (if t 2 = 0 then (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 857) else if t 2 = 1 then (if t 3 = 0 then 819 else if t 3 = 1 then 816 else 856) else (if t 3 = 0 then 839 else if t 3 = 1 then 838 else 860))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 200 else 3525) else if t 2 = 1 then (if t 3 = 0 then 1500 else if t 3 = 1 then 198 else 2127) else (if t 3 = 0 then 3952 else if t 3 = 1 then 204 else 4204)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 401 else if t 3 = 1 then 863 else 876) else if t 2 = 1 then (if t 3 = 0 then 399 else if t 3 = 1 then 861 else 870) else (if t 3 = 0 then 405 else if t 3 = 1 then 867 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 404 else if t 3 = 1 then 866 else 877) else if t 2 = 1 then (if t 3 = 0 then 403 else if t 3 = 1 then 865 else 871) else (if t 3 = 0 then 407 else if t 3 = 1 then 869 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4851 else (if jt.2.val < 2 then 4876 else 4856)) else (if jt.2.val < 4 then 4875 else (if jt.2.val < 5 then 4877 else 4854))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4159 else (if jt.2.val < 2 then 4202 else 4162)) else (if jt.2.val < 4 then 4200 else (if jt.2.val < 5 then 4201 else 4133)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 794 else (if jt.2.val < 2 then 828 else 831)) else (if jt.2.val < 4 then 825 else (if jt.2.val < 5 then 827 else 826))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 793 else (if jt.2.val < 2 then 850 else 851)) else (if jt.2.val < 4 then 847 else (if jt.2.val < 5 then 849 else 848)))))

checked_coverage fastCoverage0796 pairing0796 template0796 witness0796

theorem coverage0796 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0796) (maskBits m))
    cores template0796 witness0796 := by
  rw [← coresFast_eq]
  exact fastCoverage0796

theorem coverageSize0796 : ∀ q : Pattern,
    (cores (witness0796 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0796 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0796
#print axioms coverageSize0796

noncomputable def pairing0797 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 2) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0797 : List (Fin 4935) := templateData0797

noncomputable def witness0797 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 224 else 918) else if t 2 = 1 then (if t 3 = 0 then 230 else if t 3 = 1 then 222 else 916) else (if t 3 = 0 then 258 else if t 3 = 1 then 254 else 922)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 228 else if t 3 = 1 then 220 else 266) else if t 2 = 1 then (if t 3 = 0 then 226 else if t 3 = 1 then 218 else 264) else (if t 3 = 0 then 256 else if t 3 = 1 then 251 else 277)) else (if t 2 = 0 then (if t 3 = 0 then 3925 else if t 3 = 1 then 3923 else 4207) else if t 2 = 1 then (if t 3 = 0 then 2750 else if t 3 = 1 then 2747 else 2756) else (if t 3 = 0 then 3210 else if t 3 = 1 then 3209 else 3499))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 223 else 917) else if t 2 = 1 then (if t 3 = 0 then 229 else if t 3 = 1 then 221 else 915) else (if t 3 = 0 then 257 else if t 3 = 1 then 253 else 921)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 227 else if t 3 = 1 then 219 else 265) else if t 2 = 1 then (if t 3 = 0 then 225 else if t 3 = 1 then 217 else 263) else (if t 3 = 0 then 255 else if t 3 = 1 then 250 else 276)) else (if t 2 = 0 then (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 273) else if t 2 = 1 then (if t 3 = 0 then 242 else if t 3 = 1 then 237 else 272) else (if t 3 = 0 then 261 else if t 3 = 1 then 259 else 280))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3536 else if t 3 = 1 then 306 else 3229) else if t 2 = 1 then (if t 3 = 0 then 2139 else if t 3 = 1 then 300 else 1476) else (if t 3 = 0 then 4206 else if t 3 = 1 then 302 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 930 else if t 3 = 1 then 294 else 296) else if t 2 = 1 then (if t 3 = 0 then 924 else if t 3 = 1 then 282 else 286) else (if t 3 = 0 then 926 else if t 3 = 1 then 284 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 931 else if t 3 = 1 then 295 else 297) else if t 2 = 1 then (if t 3 = 0 then 925 else if t 3 = 1 then 283 else 287) else (if t 3 = 0 then 927 else if t 3 = 1 then 285 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4881 else (if jt.2.val < 2 then 4897 else 4886)) else (if jt.2.val < 4 then 4896 else (if jt.2.val < 5 then 4898 else 4884))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4103 else (if jt.2.val < 2 then 4127 else 4106)) else (if jt.2.val < 4 then 4125 else (if jt.2.val < 5 then 4126 else 4095)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 215 else (if jt.2.val < 2 then 249 else 252)) else (if jt.2.val < 4 then 246 else (if jt.2.val < 5 then 248 else 247))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 848 else (if jt.2.val < 2 then 914 else 851)) else (if jt.2.val < 4 then 906 else (if jt.2.val < 5 then 907 else 793)))))

checked_coverage fastCoverage0797 pairing0797 template0797 witness0797

theorem coverage0797 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0797) (maskBits m))
    cores template0797 witness0797 := by
  rw [← coresFast_eq]
  exact fastCoverage0797

theorem coverageSize0797 : ∀ q : Pattern,
    (cores (witness0797 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0797 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0797
#print axioms coverageSize0797

noncomputable def pairing0798 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0798 : List (Fin 4935) := templateData0798

noncomputable def witness0798 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1029 else 469) else if t 2 = 1 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1027 else 467) else (if t 3 = 0 then 1053 else if t 3 = 1 then 1051 else 477)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1025 else if t 3 = 1 then 1021 else 1071) else if t 2 = 1 then (if t 3 = 0 then 1023 else if t 3 = 1 then 1019 else 1069) else (if t 3 = 0 then 1049 else if t 3 = 1 then 1046 else 1075)) else (if t 2 = 0 then (if t 3 = 0 then 3520 else if t 3 = 1 then 3338 else 3226) else if t 2 = 1 then (if t 3 = 0 then 2972 else if t 3 = 1 then 2970 else 2979) else (if t 3 = 0 then 4198 else if t 3 = 1 then 4046 else 3905))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1028 else 468) else if t 2 = 1 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1026 else 466) else (if t 3 = 0 then 1052 else if t 3 = 1 then 1050 else 476)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1024 else if t 3 = 1 then 1020 else 1070) else if t 2 = 1 then (if t 3 = 0 then 1022 else if t 3 = 1 then 1018 else 1068) else (if t 3 = 0 then 1048 else if t 3 = 1 then 1045 else 1074)) else (if t 2 = 0 then (if t 3 = 0 then 1040 else if t 3 = 1 then 1038 else 1073) else if t 2 = 1 then (if t 3 = 0 then 1039 else if t 3 = 1 then 1037 else 1072) else (if t 3 = 0 then 1055 else if t 3 = 1 then 1054 else 1076))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 596 else 4208) else if t 2 = 1 then (if t 3 = 0 then 1548 else if t 3 = 1 then 594 else 2148) else (if t 3 = 0 then 3216 else if t 3 = 1 then 600 else 3521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 785 else if t 3 = 1 then 1079 else 1092) else if t 2 = 1 then (if t 3 = 0 then 783 else if t 3 = 1 then 1077 else 1086) else (if t 3 = 0 then 789 else if t 3 = 1 then 1083 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 788 else if t 3 = 1 then 1082 else 1093) else if t 2 = 1 then (if t 3 = 0 then 787 else if t 3 = 1 then 1081 else 1087) else (if t 3 = 0 then 791 else if t 3 = 1 then 1085 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4905 else (if jt.2.val < 2 then 4912 else 4910)) else (if jt.2.val < 4 then 4911 else (if jt.2.val < 5 then 4913 else 4908))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3468 else (if jt.2.val < 2 then 3519 else 3471)) else (if jt.2.val < 4 then 3517 else (if jt.2.val < 5 then 3518 else 3440)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 826 else (if jt.2.val < 2 then 1047 else 831)) else (if jt.2.val < 4 then 1014 else (if jt.2.val < 5 then 1015 else 794))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1017 else (if jt.2.val < 2 then 1066 else 1067)) else (if jt.2.val < 4 then 1063 else (if jt.2.val < 5 then 1065 else 1064)))))

checked_coverage fastCoverage0798 pairing0798 template0798 witness0798

theorem coverage0798 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0798) (maskBits m))
    cores template0798 witness0798 := by
  rw [← coresFast_eq]
  exact fastCoverage0798

theorem coverageSize0798 : ∀ q : Pattern,
    (cores (witness0798 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0798 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0798
#print axioms coverageSize0798

noncomputable def pairing0799 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 7 else 0) else (if x.2 then 1 else 5)) else (if x.1.val < 3 then (if x.2 then 2 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0799 : List (Fin 4935) := templateData0799

noncomputable def witness0799 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 620 else 1134) else if t 2 = 1 then (if t 3 = 0 then 626 else if t 3 = 1 then 618 else 1132) else (if t 3 = 0 then 648 else if t 3 = 1 then 644 else 1138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 624 else if t 3 = 1 then 616 else 656) else if t 2 = 1 then (if t 3 = 0 then 622 else if t 3 = 1 then 614 else 654) else (if t 3 = 0 then 646 else if t 3 = 1 then 641 else 667)) else (if t 2 = 0 then (if t 3 = 0 then 3174 else if t 3 = 1 then 3172 else 3524) else if t 2 = 1 then (if t 3 = 0 then 2769 else if t 3 = 1 then 2766 else 2775) else (if t 3 = 0 then 3946 else if t 3 = 1 then 3945 else 4190))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 619 else 1133) else if t 2 = 1 then (if t 3 = 0 then 625 else if t 3 = 1 then 617 else 1131) else (if t 3 = 0 then 647 else if t 3 = 1 then 643 else 1137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 623 else if t 3 = 1 then 615 else 655) else if t 2 = 1 then (if t 3 = 0 then 621 else if t 3 = 1 then 613 else 653) else (if t 3 = 0 then 645 else if t 3 = 1 then 640 else 666)) else (if t 2 = 0 then (if t 3 = 0 then 637 else if t 3 = 1 then 633 else 663) else if t 2 = 1 then (if t 3 = 0 then 636 else if t 3 = 1 then 632 else 662) else (if t 3 = 0 then 651 else if t 3 = 1 then 649 else 670))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4214 else if t 3 = 1 then 696 else 3960) else if t 2 = 1 then (if t 3 = 0 then 2160 else if t 3 = 1 then 690 else 1524) else (if t 3 = 0 then 3523 else if t 3 = 1 then 692 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1146 else if t 3 = 1 then 684 else 686) else if t 2 = 1 then (if t 3 = 0 then 1140 else if t 3 = 1 then 672 else 676) else (if t 3 = 0 then 1142 else if t 3 = 1 then 674 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 1147 else if t 3 = 1 then 685 else 687) else if t 2 = 1 then (if t 3 = 0 then 1141 else if t 3 = 1 then 673 else 677) else (if t 3 = 0 then 1143 else if t 3 = 1 then 675 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4917 else (if jt.2.val < 2 then 4924 else 4922)) else (if jt.2.val < 4 then 4923 else (if jt.2.val < 5 then 4925 else 4920))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3392 else (if jt.2.val < 2 then 3428 else 3395)) else (if jt.2.val < 4 then 3426 else (if jt.2.val < 5 then 3427 else 3384)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 247 else (if jt.2.val < 2 then 642 else 252)) else (if jt.2.val < 4 then 611 else (if jt.2.val < 5 then 612 else 215))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1064 else (if jt.2.val < 2 then 1130 else 1067)) else (if jt.2.val < 4 then 1125 else (if jt.2.val < 5 then 1126 else 1017)))))

checked_coverage fastCoverage0799 pairing0799 template0799 witness0799

theorem coverage0799 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0799) (maskBits m))
    cores template0799 witness0799 := by
  rw [← coresFast_eq]
  exact fastCoverage0799

theorem coverageSize0799 : ∀ q : Pattern,
    (cores (witness0799 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0799 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0799
#print axioms coverageSize0799

end Crown.CertificateData
