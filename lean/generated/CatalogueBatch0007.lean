import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0006

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0240 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0240 : List (Fin 4935) := templateData0240

noncomputable def witness0240 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2446 else 2506) else if t 2 = 1 then (if t 3 = 0 then 2450 else if t 3 = 1 then 2442 else 2500) else (if t 3 = 0 then 2485 else if t 3 = 1 then 2482 else 2501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2444 else 1756) else if t 2 = 1 then (if t 3 = 0 then 2448 else if t 3 = 1 then 2440 else 1753) else (if t 3 = 0 then 1416 else if t 3 = 1 then 1412 else 1450)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 724 else 790) else if t 2 = 1 then (if t 3 = 0 then 726 else if t 3 = 1 then 722 else 778) else (if t 3 = 0 then 758 else if t 3 = 1 then 756 else 780))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2445 else 1909) else if t 2 = 1 then (if t 3 = 0 then 2449 else if t 3 = 1 then 2441 else 1906) else (if t 3 = 0 then 1586 else if t 3 = 1 then 1582 else 1618)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2443 else 2502) else if t 2 = 1 then (if t 3 = 0 then 2447 else if t 3 = 1 then 2439 else 2492) else (if t 3 = 0 then 2484 else if t 3 = 1 then 2481 else 2496)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2503) else if t 2 = 1 then (if t 3 = 0 then 2462 else if t 3 = 1 then 2459 else 2493) else (if t 3 = 0 then 2487 else if t 3 = 1 then 2486 else 2497))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 439 else 505) else if t 2 = 1 then (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 493) else (if t 3 = 0 then 473 else if t 3 = 1 then 471 else 495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2504) else if t 2 = 1 then (if t 3 = 0 then 2471 else if t 3 = 1 then 2468 else 2494) else (if t 3 = 0 then 2489 else if t 3 = 1 then 2488 else 2498)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2474 else 2505) else if t 2 = 1 then (if t 3 = 0 then 2475 else if t 3 = 1 then 2473 else 2495) else (if t 3 = 0 then 2491 else if t 3 = 1 then 2490 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3690 else (if jt.2.val < 2 then 3700 else 3701)) else (if jt.2.val < 4 then 3697 else (if jt.2.val < 5 then 3699 else 3698))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3691 else (if jt.2.val < 2 then 3695 else 3696)) else (if jt.2.val < 4 then 3692 else (if jt.2.val < 5 then 3694 else 3693)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2436 else (if jt.2.val < 2 then 2480 else 2483)) else (if jt.2.val < 4 then 2477 else (if jt.2.val < 5 then 2479 else 2478))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2430 else (if jt.2.val < 2 then 2432 else 2435)) else (if jt.2.val < 4 then 2431 else (if jt.2.val < 5 then 2434 else 2433)))))

checked_coverage fastCoverage0240 pairing0240 template0240 witness0240

theorem coverage0240 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0240) (maskBits m))
    cores template0240 witness0240 := by
  rw [← coresFast_eq]
  exact fastCoverage0240

theorem coverageSize0240 : ∀ q : Pattern,
    (cores (witness0240 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0240 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0240
#print axioms coverageSize0240

noncomputable def pairing0241 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0241 : List (Fin 4935) := templateData0241

noncomputable def witness0241 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2560 else 2561) else if t 2 = 1 then (if t 3 = 0 then 2565 else if t 3 = 1 then 2544 else 2546) else (if t 3 = 0 then 2577 else if t 3 = 1 then 2545 else 2547)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2558 else 1750) else if t 2 = 1 then (if t 3 = 0 then 2563 else if t 3 = 1 then 2538 else 1747) else (if t 3 = 0 then 1372 else if t 3 = 1 then 1350 else 1353)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 667 else 669) else if t 2 = 1 then (if t 3 = 0 then 681 else if t 3 = 1 then 641 else 646) else (if t 3 = 0 then 695 else if t 3 = 1 then 644 else 648))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2559 else 1903) else if t 2 = 1 then (if t 3 = 0 then 2564 else if t 3 = 1 then 2541 else 1900) else (if t 3 = 0 then 1687 else if t 3 = 1 then 1666 else 1668)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2548 else 2554) else if t 2 = 1 then (if t 3 = 0 then 2562 else if t 3 = 1 then 2519 else 2530) else (if t 3 = 0 then 2576 else if t 3 = 1 then 2526 else 2534)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2555) else if t 2 = 1 then (if t 3 = 0 then 2570 else if t 3 = 1 then 2521 else 2531) else (if t 3 = 0 then 2578 else if t 3 = 1 then 2527 else 2535))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 571 else 573) else if t 2 = 1 then (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 549) else (if t 3 = 0 then 599 else if t 3 = 1 then 547 else 551)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2556) else if t 2 = 1 then (if t 3 = 0 then 2572 else if t 3 = 1 then 2523 else 2532) else (if t 3 = 0 then 2579 else if t 3 = 1 then 2528 else 2536)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2551 else 2557) else if t 2 = 1 then (if t 3 = 0 then 2574 else if t 3 = 1 then 2524 else 2533) else (if t 3 = 0 then 2580 else if t 3 = 1 then 2529 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3702 else (if jt.2.val < 2 then 3704 else 3711)) else (if jt.2.val < 4 then 3703 else (if jt.2.val < 5 then 3710 else 3709))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3705 else (if jt.2.val < 2 then 3707 else 3713)) else (if jt.2.val < 4 then 3706 else (if jt.2.val < 5 then 3712 else 3708)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2510 else (if jt.2.val < 2 then 2512 else 2553)) else (if jt.2.val < 4 then 2511 else (if jt.2.val < 5 then 2552 else 2525))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2433 else (if jt.2.val < 2 then 2509 else 2435)) else (if jt.2.val < 4 then 2507 else (if jt.2.val < 5 then 2508 else 2430)))))

checked_coverage fastCoverage0241 pairing0241 template0241 witness0241

theorem coverage0241 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0241) (maskBits m))
    cores template0241 witness0241 := by
  rw [← coresFast_eq]
  exact fastCoverage0241

theorem coverageSize0241 : ∀ q : Pattern,
    (cores (witness0241 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0241 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0241
#print axioms coverageSize0241

noncomputable def pairing0242 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0242 : List (Fin 4935) := templateData0242

noncomputable def witness0242 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2598 else 2654) else if t 2 = 1 then (if t 3 = 0 then 2602 else if t 3 = 1 then 2594 else 2648) else (if t 3 = 0 then 2633 else if t 3 = 1 then 2630 else 2649)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2596 else 2104) else if t 2 = 1 then (if t 3 = 0 then 2600 else if t 3 = 1 then 2592 else 2101) else (if t 3 = 0 then 1415 else if t 3 = 1 then 1411 else 1447)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 536 else 601) else if t 2 = 1 then (if t 3 = 0 then 538 else if t 3 = 1 then 534 else 589) else (if t 3 = 0 then 569 else if t 3 = 1 then 567 else 591))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2597 else 2224) else if t 2 = 1 then (if t 3 = 0 then 2601 else if t 3 = 1 then 2593 else 2221) else (if t 3 = 0 then 1585 else if t 3 = 1 then 1581 else 1615)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2595 else 2650) else if t 2 = 1 then (if t 3 = 0 then 2599 else if t 3 = 1 then 2591 else 2640) else (if t 3 = 0 then 2632 else if t 3 = 1 then 2629 else 2644)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2651) else if t 2 = 1 then (if t 3 = 0 then 2614 else if t 3 = 1 then 2611 else 2641) else (if t 3 = 0 then 2635 else if t 3 = 1 then 2634 else 2645))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 635 else 697) else if t 2 = 1 then (if t 3 = 0 then 637 else if t 3 = 1 then 633 else 685) else (if t 3 = 0 then 665 else if t 3 = 1 then 663 else 687)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2622 else 2652) else if t 2 = 1 then (if t 3 = 0 then 2623 else if t 3 = 1 then 2620 else 2642) else (if t 3 = 0 then 2637 else if t 3 = 1 then 2636 else 2646)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2626 else 2653) else if t 2 = 1 then (if t 3 = 0 then 2627 else if t 3 = 1 then 2625 else 2643) else (if t 3 = 0 then 2639 else if t 3 = 1 then 2638 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3714 else (if jt.2.val < 2 then 3724 else 3725)) else (if jt.2.val < 4 then 3721 else (if jt.2.val < 5 then 3723 else 3722))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3715 else (if jt.2.val < 2 then 3719 else 3720)) else (if jt.2.val < 4 then 3716 else (if jt.2.val < 5 then 3718 else 3717)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2478 else (if jt.2.val < 2 then 2631 else 2483)) else (if jt.2.val < 4 then 2587 else (if jt.2.val < 5 then 2588 else 2436))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2581 else (if jt.2.val < 2 then 2583 else 2586)) else (if jt.2.val < 4 then 2582 else (if jt.2.val < 5 then 2585 else 2584)))))

checked_coverage fastCoverage0242 pairing0242 template0242 witness0242

theorem coverage0242 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0242) (maskBits m))
    cores template0242 witness0242 := by
  rw [← coresFast_eq]
  exact fastCoverage0242

theorem coverageSize0242 : ∀ q : Pattern,
    (cores (witness0242 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0242 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0242
#print axioms coverageSize0242

noncomputable def pairing0243 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0243 : List (Fin 4935) := templateData0243

noncomputable def witness0243 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2705 else 2706) else if t 2 = 1 then (if t 3 = 0 then 2710 else if t 3 = 1 then 2688 else 2690) else (if t 3 = 0 then 2722 else if t 3 = 1 then 2689 else 2691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2703 else 2098) else if t 2 = 1 then (if t 3 = 0 then 2708 else if t 3 = 1 then 2682 else 2090) else (if t 3 = 0 then 1371 else if t 3 = 1 then 1339 else 1342)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 475 else 477) else if t 2 = 1 then (if t 3 = 0 then 489 else if t 3 = 1 then 445 else 450) else (if t 3 = 0 then 503 else if t 3 = 1 then 448 else 452))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2704 else 2218) else if t 2 = 1 then (if t 3 = 0 then 2709 else if t 3 = 1 then 2685 else 2212) else (if t 3 = 0 then 1686 else if t 3 = 1 then 1657 else 1659)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2695 else 2699) else if t 2 = 1 then (if t 3 = 0 then 2707 else if t 3 = 1 then 2664 else 2674) else (if t 3 = 0 then 2721 else if t 3 = 1 then 2670 else 2678)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2700) else if t 2 = 1 then (if t 3 = 0 then 2715 else if t 3 = 1 then 2666 else 2675) else (if t 3 = 0 then 2723 else if t 3 = 1 then 2671 else 2679))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 760 else 762) else if t 2 = 1 then (if t 3 = 0 then 774 else if t 3 = 1 then 733 else 737) else (if t 3 = 0 then 788 else if t 3 = 1 then 735 else 739)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2697 else 2701) else if t 2 = 1 then (if t 3 = 0 then 2717 else if t 3 = 1 then 2668 else 2676) else (if t 3 = 0 then 2724 else if t 3 = 1 then 2672 else 2680)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2698 else 2702) else if t 2 = 1 then (if t 3 = 0 then 2719 else if t 3 = 1 then 2669 else 2677) else (if t 3 = 0 then 2725 else if t 3 = 1 then 2673 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3726 else (if jt.2.val < 2 then 3728 else 3735)) else (if jt.2.val < 4 then 3727 else (if jt.2.val < 5 then 3734 else 3733))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3729 else (if jt.2.val < 2 then 3731 else 3737)) else (if jt.2.val < 4 then 3730 else (if jt.2.val < 5 then 3736 else 3732)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2525 else (if jt.2.val < 2 then 2693 else 2553)) else (if jt.2.val < 4 then 2692 else (if jt.2.val < 5 then 2694 else 2510))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2584 else (if jt.2.val < 2 then 2657 else 2586)) else (if jt.2.val < 4 then 2655 else (if jt.2.val < 5 then 2656 else 2581)))))

checked_coverage fastCoverage0243 pairing0243 template0243 witness0243

theorem coverage0243 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0243) (maskBits m))
    cores template0243 witness0243 := by
  rw [← coresFast_eq]
  exact fastCoverage0243

theorem coverageSize0243 : ∀ q : Pattern,
    (cores (witness0243 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0243 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0243
#print axioms coverageSize0243

noncomputable def pairing0244 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0244 : List (Fin 4935) := templateData0244

noncomputable def witness0244 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 16 else 104) else if t 2 = 1 then (if t 3 = 0 then 20 else if t 3 = 1 then 12 else 94) else (if t 3 = 0 then 67 else if t 3 = 1 then 62 else 95)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 22 else if t 3 = 1 then 14 else 100) else if t 2 = 1 then (if t 3 = 0 then 18 else if t 3 = 1 then 10 else 86) else (if t 3 = 0 then 65 else if t 3 = 1 then 60 else 88)) else (if t 2 = 0 then (if t 3 = 0 then 2789 else if t 3 = 1 then 2787 else 2800) else if t 2 = 1 then (if t 3 = 0 then 2788 else if t 3 = 1 then 2785 else 2797) else (if t 3 = 0 then 2795 else if t 3 = 1 then 2794 else 2798))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 15 else 102) else if t 2 = 1 then (if t 3 = 0 then 19 else if t 3 = 1 then 11 else 90) else (if t 3 = 0 then 66 else if t 3 = 1 then 61 else 92)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 21 else if t 3 = 1 then 13 else 96) else if t 2 = 1 then (if t 3 = 0 then 17 else if t 3 = 1 then 9 else 78) else (if t 3 = 0 then 64 else if t 3 = 1 then 59 else 82)) else (if t 2 = 0 then (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 97) else if t 2 = 1 then (if t 3 = 0 then 34 else if t 3 = 1 then 29 else 79) else (if t 3 = 0 then 70 else if t 3 = 1 then 68 else 83))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 2124 else 2744) else if t 2 = 1 then (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1521) else (if t 3 = 0 then 2739 else if t 3 = 1 then 1848 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 98) else if t 2 = 1 then (if t 3 = 0 then 47 else if t 3 = 1 then 42 else 80) else (if t 3 = 0 then 74 else if t 3 = 1 then 72 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 54 else if t 3 = 1 then 52 else 99) else if t 2 = 1 then (if t 3 = 0 then 53 else if t 3 = 1 then 51 else 81) else (if t 3 = 0 then 77 else if t 3 = 1 then 76 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3726 else (if jt.2.val < 2 then 3743 else 3735)) else (if jt.2.val < 4 then 3741 else (if jt.2.val < 5 then 3742 else 3733))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3693 else (if jt.2.val < 2 then 3740 else 3696)) else (if jt.2.val < 4 then 3738 else (if jt.2.val < 5 then 3739 else 3691)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 6 else (if jt.2.val < 2 then 58 else 63)) else (if jt.2.val < 4 then 55 else (if jt.2.val < 5 then 57 else 56))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 0 else (if jt.2.val < 2 then 2 else 5)) else (if jt.2.val < 4 then 1 else (if jt.2.val < 5 then 4 else 3)))))

checked_coverage fastCoverage0244 pairing0244 template0244 witness0244

theorem coverage0244 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0244) (maskBits m))
    cores template0244 witness0244 := by
  rw [← coresFast_eq]
  exact fastCoverage0244

theorem coverageSize0244 : ∀ q : Pattern,
    (cores (witness0244 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0244 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0244
#print axioms coverageSize0244

noncomputable def pairing0245 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0245 : List (Fin 4935) := templateData0245

noncomputable def witness0245 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 178 else 179) else if t 2 = 1 then (if t 3 = 0 then 183 else if t 3 = 1 then 156 else 158) else (if t 3 = 0 then 201 else if t 3 = 1 then 157 else 159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 185 else if t 3 = 1 then 170 else 172) else if t 2 = 1 then (if t 3 = 0 then 181 else if t 3 = 1 then 136 else 142) else (if t 3 = 0 then 199 else if t 3 = 1 then 140 else 144)) else (if t 2 = 0 then (if t 3 = 0 then 2779 else if t 3 = 1 then 2775 else 2776) else if t 2 = 1 then (if t 3 = 0 then 2778 else if t 3 = 1 then 2766 else 2769) else (if t 3 = 0 then 2781 else if t 3 = 1 then 2768 else 2770))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 174 else 176) else if t 2 = 1 then (if t 3 = 0 then 182 else if t 3 = 1 then 146 else 152) else (if t 3 = 0 then 200 else if t 3 = 1 then 150 else 154)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 184 else if t 3 = 1 then 160 else 166) else if t 2 = 1 then (if t 3 = 0 then 180 else if t 3 = 1 then 117 else 128) else (if t 3 = 0 then 198 else if t 3 = 1 then 124 else 132)) else (if t 2 = 0 then (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 167) else if t 2 = 1 then (if t 3 = 0 then 188 else if t 3 = 1 then 119 else 129) else (if t 3 = 0 then 202 else if t 3 = 1 then 125 else 133))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 2115 else 2758) else if t 2 = 1 then (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1535) else (if t 3 = 0 then 2763 else if t 3 = 1 then 1833 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 168) else if t 2 = 1 then (if t 3 = 0 then 192 else if t 3 = 1 then 121 else 130) else (if t 3 = 0 then 204 else if t 3 = 1 then 126 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 197 else if t 3 = 1 then 163 else 169) else if t 2 = 1 then (if t 3 = 0 then 196 else if t 3 = 1 then 122 else 131) else (if t 3 = 0 then 206 else if t 3 = 1 then 127 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3714 else (if jt.2.val < 2 then 3745 else 3725)) else (if jt.2.val < 4 then 3744 else (if jt.2.val < 5 then 3746 else 3722))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3708 else (if jt.2.val < 2 then 3748 else 3713)) else (if jt.2.val < 4 then 3747 else (if jt.2.val < 5 then 3749 else 3705)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 108 else (if jt.2.val < 2 then 110 else 165)) else (if jt.2.val < 4 then 109 else (if jt.2.val < 5 then 164 else 123))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3 else (if jt.2.val < 2 then 107 else 5)) else (if jt.2.val < 4 then 105 else (if jt.2.val < 5 then 106 else 0)))))

checked_coverage fastCoverage0245 pairing0245 template0245 witness0245

theorem coverage0245 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0245) (maskBits m))
    cores template0245 witness0245 := by
  rw [← coresFast_eq]
  exact fastCoverage0245

theorem coverageSize0245 : ∀ q : Pattern,
    (cores (witness0245 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0245 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0245
#print axioms coverageSize0245

noncomputable def pairing0246 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0246 : List (Fin 4935) := templateData0246

noncomputable def witness0246 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 224 else 308) else if t 2 = 1 then (if t 3 = 0 then 228 else if t 3 = 1 then 220 else 298) else (if t 3 = 0 then 271 else if t 3 = 1 then 266 else 299)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 230 else if t 3 = 1 then 222 else 304) else if t 2 = 1 then (if t 3 = 0 then 226 else if t 3 = 1 then 218 else 290) else (if t 3 = 0 then 269 else if t 3 = 1 then 264 else 292)) else (if t 2 = 0 then (if t 3 = 0 then 2751 else if t 3 = 1 then 2749 else 2762) else if t 2 = 1 then (if t 3 = 0 then 2750 else if t 3 = 1 then 2747 else 2759) else (if t 3 = 0 then 2757 else if t 3 = 1 then 2756 else 2760))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 223 else 306) else if t 2 = 1 then (if t 3 = 0 then 227 else if t 3 = 1 then 219 else 294) else (if t 3 = 0 then 270 else if t 3 = 1 then 265 else 296)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 229 else if t 3 = 1 then 221 else 300) else if t 2 = 1 then (if t 3 = 0 then 225 else if t 3 = 1 then 217 else 282) else (if t 3 = 0 then 268 else if t 3 = 1 then 263 else 286)) else (if t 2 = 0 then (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 301) else if t 2 = 1 then (if t 3 = 0 then 242 else if t 3 = 1 then 237 else 283) else (if t 3 = 0 then 274 else if t 3 = 1 then 272 else 287))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1785 else 2782) else if t 2 = 1 then (if t 3 = 0 then 1461 else if t 3 = 1 then 1458 else 1473) else (if t 3 = 0 then 2777 else if t 3 = 1 then 2169 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 257 else if t 3 = 1 then 253 else 302) else if t 2 = 1 then (if t 3 = 0 then 255 else if t 3 = 1 then 250 else 284) else (if t 3 = 0 then 278 else if t 3 = 1 then 276 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 262 else if t 3 = 1 then 260 else 303) else if t 2 = 1 then (if t 3 = 0 then 261 else if t 3 = 1 then 259 else 285) else (if t 3 = 0 then 281 else if t 3 = 1 then 280 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3702 else (if jt.2.val < 2 then 3755 else 3711)) else (if jt.2.val < 4 then 3753 else (if jt.2.val < 5 then 3754 else 3709))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3717 else (if jt.2.val < 2 then 3752 else 3720)) else (if jt.2.val < 4 then 3750 else (if jt.2.val < 5 then 3751 else 3715)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 56 else (if jt.2.val < 2 then 267 else 63)) else (if jt.2.val < 4 then 213 else (if jt.2.val < 5 then 214 else 6))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 207 else (if jt.2.val < 2 then 209 else 212)) else (if jt.2.val < 4 then 208 else (if jt.2.val < 5 then 211 else 210)))))

checked_coverage fastCoverage0246 pairing0246 template0246 witness0246

theorem coverage0246 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0246) (maskBits m))
    cores template0246 witness0246 := by
  rw [← coresFast_eq]
  exact fastCoverage0246

theorem coverageSize0246 : ∀ q : Pattern,
    (cores (witness0246 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0246 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0246
#print axioms coverageSize0246

noncomputable def pairing0247 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0247 : List (Fin 4935) := templateData0247

noncomputable def witness0247 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 379 else 380) else if t 2 = 1 then (if t 3 = 0 then 384 else if t 3 = 1 then 356 else 358) else (if t 3 = 0 then 402 else if t 3 = 1 then 357 else 359)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 386 else if t 3 = 1 then 371 else 373) else if t 2 = 1 then (if t 3 = 0 then 382 else if t 3 = 1 then 336 else 342) else (if t 3 = 0 then 400 else if t 3 = 1 then 340 else 344)) else (if t 2 = 0 then (if t 3 = 0 then 2741 else if t 3 = 1 then 2737 else 2738) else if t 2 = 1 then (if t 3 = 0 then 2740 else if t 3 = 1 then 2728 else 2731) else (if t 3 = 0 then 2743 else if t 3 = 1 then 2730 else 2732))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 375 else 377) else if t 2 = 1 then (if t 3 = 0 then 383 else if t 3 = 1 then 346 else 352) else (if t 3 = 0 then 401 else if t 3 = 1 then 350 else 354)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 385 else if t 3 = 1 then 363 else 367) else if t 2 = 1 then (if t 3 = 0 then 381 else if t 3 = 1 then 318 else 328) else (if t 3 = 0 then 399 else if t 3 = 1 then 324 else 332)) else (if t 2 = 0 then (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 368) else if t 2 = 1 then (if t 3 = 0 then 389 else if t 3 = 1 then 320 else 329) else (if t 3 = 0 then 403 else if t 3 = 1 then 325 else 333))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1773 else 2796) else if t 2 = 1 then (if t 3 = 0 then 1497 else if t 3 = 1 then 1483 else 1487) else (if t 3 = 0 then 2801 else if t 3 = 1 then 2157 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 395 else if t 3 = 1 then 365 else 369) else if t 2 = 1 then (if t 3 = 0 then 393 else if t 3 = 1 then 322 else 330) else (if t 3 = 0 then 405 else if t 3 = 1 then 326 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 398 else if t 3 = 1 then 366 else 370) else if t 2 = 1 then (if t 3 = 0 then 397 else if t 3 = 1 then 323 else 331) else (if t 3 = 0 then 407 else if t 3 = 1 then 327 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3690 else (if jt.2.val < 2 then 3757 else 3701)) else (if jt.2.val < 4 then 3756 else (if jt.2.val < 5 then 3758 else 3698))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3732 else (if jt.2.val < 2 then 3760 else 3737)) else (if jt.2.val < 4 then 3759 else (if jt.2.val < 5 then 3761 else 3729)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 123 else (if jt.2.val < 2 then 361 else 165)) else (if jt.2.val < 4 then 360 else (if jt.2.val < 5 then 362 else 108))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 210 else (if jt.2.val < 2 then 311 else 212)) else (if jt.2.val < 4 then 309 else (if jt.2.val < 5 then 310 else 207)))))

checked_coverage fastCoverage0247 pairing0247 template0247 witness0247

theorem coverage0247 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0247) (maskBits m))
    cores template0247 witness0247 := by
  rw [← coresFast_eq]
  exact fastCoverage0247

theorem coverageSize0247 : ∀ q : Pattern,
    (cores (witness0247 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0247 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0247
#print axioms coverageSize0247

noncomputable def pairing0248 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0248 : List (Fin 4935) := templateData0248

noncomputable def witness0248 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2813 else 2722) else if t 2 = 1 then (if t 3 = 0 then 2817 else if t 3 = 1 then 2809 else 2860) else (if t 3 = 0 then 2485 else if t 3 = 1 then 2855 else 2868)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2811 else 1371) else if t 2 = 1 then (if t 3 = 0 then 2815 else if t 3 = 1 then 2807 else 1370) else (if t 3 = 0 then 1416 else if t 3 = 1 then 1414 else 1777)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1171 else 503) else if t 2 = 1 then (if t 3 = 0 then 1173 else if t 3 = 1 then 1169 else 1211) else (if t 3 = 0 then 758 else if t 3 = 1 then 1202 else 1222))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2812 else 1686) else if t 2 = 1 then (if t 3 = 0 then 2816 else if t 3 = 1 then 2808 else 1685) else (if t 3 = 0 then 1586 else if t 3 = 1 then 1584 else 1852)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2810 else 2721) else if t 2 = 1 then (if t 3 = 0 then 2814 else if t 3 = 1 then 2806 else 2859) else (if t 3 = 0 then 2484 else if t 3 = 1 then 2854 else 2864)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2723) else if t 2 = 1 then (if t 3 = 0 then 2829 else if t 3 = 1 then 2826 else 2861) else (if t 3 = 0 then 2487 else if t 3 = 1 then 2856 else 2865))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1040 else 788) else if t 2 = 1 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1082) else (if t 3 = 0 then 473 else if t 3 = 1 then 1073 else 1093)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2724) else if t 2 = 1 then (if t 3 = 0 then 2838 else if t 3 = 1 then 2835 else 2862) else (if t 3 = 0 then 2489 else if t 3 = 1 then 2857 else 2866)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2841 else 2725) else if t 2 = 1 then (if t 3 = 0 then 2842 else if t 3 = 1 then 2840 else 2863) else (if t 3 = 0 then 2491 else if t 3 = 1 then 2858 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3762 else (if jt.2.val < 2 then 3772 else 3773)) else (if jt.2.val < 4 then 3769 else (if jt.2.val < 5 then 3771 else 3770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3763 else (if jt.2.val < 2 then 3767 else 3768)) else (if jt.2.val < 4 then 3764 else (if jt.2.val < 5 then 3766 else 3765)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2803 else (if jt.2.val < 2 then 2852 else 2853)) else (if jt.2.val < 4 then 2849 else (if jt.2.val < 5 then 2851 else 2850))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2802 else (if jt.2.val < 2 then 2845 else 2848)) else (if jt.2.val < 4 then 2844 else (if jt.2.val < 5 then 2847 else 2846)))))

checked_coverage fastCoverage0248 pairing0248 template0248 witness0248

theorem coverage0248 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0248) (maskBits m))
    cores template0248 witness0248 := by
  rw [← coresFast_eq]
  exact fastCoverage0248

theorem coverageSize0248 : ∀ q : Pattern,
    (cores (witness0248 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0248 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0248
#print axioms coverageSize0248

noncomputable def pairing0249 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0249 : List (Fin 4935) := templateData0249

noncomputable def witness0249 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2560 else 2882) else if t 2 = 1 then (if t 3 = 0 then 2565 else if t 3 = 1 then 2544 else 2545) else (if t 3 = 0 then 2884 else if t 3 = 1 then 2546 else 2547)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2558 else 1357) else if t 2 = 1 then (if t 3 = 0 then 2563 else if t 3 = 1 then 2538 else 1350) else (if t 3 = 0 then 1762 else if t 3 = 1 then 1747 else 1353)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 667 else 1138) else if t 2 = 1 then (if t 3 = 0 then 681 else if t 3 = 1 then 641 else 644) else (if t 3 = 0 then 1145 else if t 3 = 1 then 646 else 648))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2559 else 1672) else if t 2 = 1 then (if t 3 = 0 then 2564 else if t 3 = 1 then 2541 else 1666) else (if t 3 = 0 then 1915 else if t 3 = 1 then 1900 else 1668)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2548 else 2878) else if t 2 = 1 then (if t 3 = 0 then 2562 else if t 3 = 1 then 2519 else 2526) else (if t 3 = 0 then 2883 else if t 3 = 1 then 2530 else 2534)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2879) else if t 2 = 1 then (if t 3 = 0 then 2570 else if t 3 = 1 then 2521 else 2527) else (if t 3 = 0 then 2885 else if t 3 = 1 then 2531 else 2535))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 571 else 1111) else if t 2 = 1 then (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 547) else (if t 3 = 0 then 1118 else if t 3 = 1 then 549 else 551)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2880) else if t 2 = 1 then (if t 3 = 0 then 2572 else if t 3 = 1 then 2523 else 2528) else (if t 3 = 0 then 2886 else if t 3 = 1 then 2532 else 2536)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2551 else 2881) else if t 2 = 1 then (if t 3 = 0 then 2574 else if t 3 = 1 then 2524 else 2529) else (if t 3 = 0 then 2887 else if t 3 = 1 then 2533 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3702 else (if jt.2.val < 2 then 3704 else 3711)) else (if jt.2.val < 4 then 3703 else (if jt.2.val < 5 then 3710 else 3709))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3705 else (if jt.2.val < 2 then 3707 else 3713)) else (if jt.2.val < 4 then 3706 else (if jt.2.val < 5 then 3712 else 3708)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2871 else (if jt.2.val < 2 then 2873 else 2877)) else (if jt.2.val < 4 then 2872 else (if jt.2.val < 5 then 2876 else 2875))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2846 else (if jt.2.val < 2 then 2874 else 2848)) else (if jt.2.val < 4 then 2869 else (if jt.2.val < 5 then 2870 else 2802)))))

checked_coverage fastCoverage0249 pairing0249 template0249 witness0249

theorem coverage0249 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0249) (maskBits m))
    cores template0249 witness0249 := by
  rw [← coresFast_eq]
  exact fastCoverage0249

theorem coverageSize0249 : ∀ q : Pattern,
    (cores (witness0249 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0249 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0249
#print axioms coverageSize0249

noncomputable def pairing0250 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0250 : List (Fin 4935) := templateData0250

noncomputable def witness0250 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2602 else 2906) else if t 2 = 1 then (if t 3 = 0 then 2598 else if t 3 = 1 then 2594 else 2648) else (if t 3 = 0 then 2898 else if t 3 = 1 then 2630 else 2649)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2600 else 2107) else if t 2 = 1 then (if t 3 = 0 then 2596 else if t 3 = 1 then 2592 else 2101) else (if t 3 = 0 then 1413 else if t 3 = 1 then 1411 else 1447)) else (if t 2 = 0 then (if t 3 = 0 then 540 else if t 3 = 1 then 538 else 1120) else if t 2 = 1 then (if t 3 = 0 then 536 else if t 3 = 1 then 534 else 589) else (if t 3 = 0 then 1109 else if t 3 = 1 then 567 else 591))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2601 else 2227) else if t 2 = 1 then (if t 3 = 0 then 2597 else if t 3 = 1 then 2593 else 2221) else (if t 3 = 0 then 1583 else if t 3 = 1 then 1581 else 1615)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2599 else 2902) else if t 2 = 1 then (if t 3 = 0 then 2595 else if t 3 = 1 then 2591 else 2640) else (if t 3 = 0 then 2897 else if t 3 = 1 then 2629 else 2644)) else (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2903) else if t 2 = 1 then (if t 3 = 0 then 2613 else if t 3 = 1 then 2611 else 2641) else (if t 3 = 0 then 2899 else if t 3 = 1 then 2634 else 2645))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 637 else 1147) else if t 2 = 1 then (if t 3 = 0 then 635 else if t 3 = 1 then 633 else 685) else (if t 3 = 0 then 1136 else if t 3 = 1 then 663 else 687)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2623 else 2904) else if t 2 = 1 then (if t 3 = 0 then 2622 else if t 3 = 1 then 2620 else 2642) else (if t 3 = 0 then 2900 else if t 3 = 1 then 2636 else 2646)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2627 else 2905) else if t 2 = 1 then (if t 3 = 0 then 2626 else if t 3 = 1 then 2625 else 2643) else (if t 3 = 0 then 2901 else if t 3 = 1 then 2638 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3714 else (if jt.2.val < 2 then 3724 else 3725)) else (if jt.2.val < 4 then 3721 else (if jt.2.val < 5 then 3723 else 3722))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3715 else (if jt.2.val < 2 then 3719 else 3720)) else (if jt.2.val < 4 then 3716 else (if jt.2.val < 5 then 3718 else 3717)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2850 else (if jt.2.val < 2 then 2896 else 2853)) else (if jt.2.val < 4 then 2888 else (if jt.2.val < 5 then 2889 else 2803))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2890 else (if jt.2.val < 2 then 2892 else 2895)) else (if jt.2.val < 4 then 2891 else (if jt.2.val < 5 then 2894 else 2893)))))

checked_coverage fastCoverage0250 pairing0250 template0250 witness0250

theorem coverage0250 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0250) (maskBits m))
    cores template0250 witness0250 := by
  rw [← coresFast_eq]
  exact fastCoverage0250

theorem coverageSize0250 : ∀ q : Pattern,
    (cores (witness0250 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0250 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0250
#print axioms coverageSize0250

noncomputable def pairing0251 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0251 : List (Fin 4935) := templateData0251

noncomputable def witness0251 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2953 else 2706) else if t 2 = 1 then (if t 3 = 0 then 2960 else if t 3 = 1 then 2937 else 2939) else (if t 3 = 0 then 2506 else if t 3 = 1 then 2938 else 2940)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2951 else 2098) else if t 2 = 1 then (if t 3 = 0 then 2958 else if t 3 = 1 then 2931 else 2082) else (if t 3 = 0 then 1756 else if t 3 = 1 then 1730 else 1733)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1075 else 477) else if t 2 = 1 then (if t 3 = 0 then 1084 else if t 3 = 1 then 1046 else 1051) else (if t 3 = 0 then 790 else if t 3 = 1 then 1049 else 1053))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2952 else 2218) else if t 2 = 1 then (if t 3 = 0 then 2959 else if t 3 = 1 then 2934 else 2206) else (if t 3 = 0 then 1909 else if t 3 = 1 then 1888 else 1890)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2947 else 2699) else if t 2 = 1 then (if t 3 = 0 then 2954 else if t 3 = 1 then 2913 else 2923) else (if t 3 = 0 then 2502 else if t 3 = 1 then 2919 else 2927)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2700) else if t 2 = 1 then (if t 3 = 0 then 2955 else if t 3 = 1 then 2915 else 2924) else (if t 3 = 0 then 2503 else if t 3 = 1 then 2920 else 2928))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1204 else 762) else if t 2 = 1 then (if t 3 = 0 then 1213 else if t 3 = 1 then 1180 else 1184) else (if t 3 = 0 then 505 else if t 3 = 1 then 1182 else 1186)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2949 else 2701) else if t 2 = 1 then (if t 3 = 0 then 2956 else if t 3 = 1 then 2917 else 2925) else (if t 3 = 0 then 2504 else if t 3 = 1 then 2921 else 2929)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2950 else 2702) else if t 2 = 1 then (if t 3 = 0 then 2957 else if t 3 = 1 then 2918 else 2926) else (if t 3 = 0 then 2505 else if t 3 = 1 then 2922 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3774 else (if jt.2.val < 2 then 3776 else 3783)) else (if jt.2.val < 4 then 3775 else (if jt.2.val < 5 then 3782 else 3781))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3777 else (if jt.2.val < 2 then 3779 else 3785)) else (if jt.2.val < 4 then 3778 else (if jt.2.val < 5 then 3784 else 3780)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2875 else (if jt.2.val < 2 then 2945 else 2877)) else (if jt.2.val < 4 then 2944 else (if jt.2.val < 5 then 2946 else 2871))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2893 else (if jt.2.val < 2 then 2943 else 2895)) else (if jt.2.val < 4 then 2941 else (if jt.2.val < 5 then 2942 else 2890)))))

checked_coverage fastCoverage0251 pairing0251 template0251 witness0251

theorem coverage0251 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0251) (maskBits m))
    cores template0251 witness0251 := by
  rw [← coresFast_eq]
  exact fastCoverage0251

theorem coverageSize0251 : ∀ q : Pattern,
    (cores (witness0251 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0251 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0251
#print axioms coverageSize0251

noncomputable def pairing0252 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0252 : List (Fin 4935) := templateData0252

noncomputable def witness0252 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 803 else 402) else if t 2 = 1 then (if t 3 = 0 then 807 else if t 3 = 1 then 799 else 864) else (if t 3 = 0 then 67 else if t 3 = 1 then 855 else 878)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 809 else if t 3 = 1 then 801 else 400) else if t 2 = 1 then (if t 3 = 0 then 805 else if t 3 = 1 then 797 else 862) else (if t 3 = 0 then 65 else if t 3 = 1 then 853 else 874)) else (if t 2 = 0 then (if t 3 = 0 then 2997 else if t 3 = 1 then 2995 else 2743) else if t 2 = 1 then (if t 3 = 0 then 2996 else if t 3 = 1 then 2993 else 3003) else (if t 3 = 0 then 2795 else if t 3 = 1 then 3002 else 3004))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 802 else 401) else if t 2 = 1 then (if t 3 = 0 then 806 else if t 3 = 1 then 798 else 863) else (if t 3 = 0 then 66 else if t 3 = 1 then 854 else 876)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 808 else if t 3 = 1 then 800 else 399) else if t 2 = 1 then (if t 3 = 0 then 804 else if t 3 = 1 then 796 else 861) else (if t 3 = 0 then 64 else if t 3 = 1 then 852 else 870)) else (if t 2 = 0 then (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 403) else if t 2 = 1 then (if t 3 = 0 then 821 else if t 3 = 1 then 816 else 865) else (if t 3 = 0 then 70 else if t 3 = 1 then 856 else 871))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 2145 else 2801) else if t 2 = 1 then (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1689) else (if t 3 = 0 then 2739 else if t 3 = 1 then 1598 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 405) else if t 2 = 1 then (if t 3 = 0 then 834 else if t 3 = 1 then 829 else 867) else (if t 3 = 0 then 74 else if t 3 = 1 then 858 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 841 else if t 3 = 1 then 839 else 407) else if t 2 = 1 then (if t 3 = 0 then 840 else if t 3 = 1 then 838 else 869) else (if t 3 = 0 then 77 else if t 3 = 1 then 860 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3774 else (if jt.2.val < 2 then 3791 else 3783)) else (if jt.2.val < 4 then 3789 else (if jt.2.val < 5 then 3790 else 3781))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3765 else (if jt.2.val < 2 then 3788 else 3768)) else (if jt.2.val < 4 then 3786 else (if jt.2.val < 5 then 3787 else 3763)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 793 else (if jt.2.val < 2 then 850 else 851)) else (if jt.2.val < 4 then 847 else (if jt.2.val < 5 then 849 else 848))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 792 else (if jt.2.val < 2 then 843 else 846)) else (if jt.2.val < 4 then 842 else (if jt.2.val < 5 then 845 else 844)))))

checked_coverage fastCoverage0252 pairing0252 template0252 witness0252

theorem coverage0252 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0252) (maskBits m))
    cores template0252 witness0252 := by
  rw [← coresFast_eq]
  exact fastCoverage0252

theorem coverageSize0252 : ∀ q : Pattern,
    (cores (witness0252 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0252 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0252
#print axioms coverageSize0252

noncomputable def pairing0253 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0253 : List (Fin 4935) := templateData0253

noncomputable def witness0253 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 178 else 896) else if t 2 = 1 then (if t 3 = 0 then 183 else if t 3 = 1 then 156 else 157) else (if t 3 = 0 then 900 else if t 3 = 1 then 158 else 159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 185 else if t 3 = 1 then 170 else 892) else if t 2 = 1 then (if t 3 = 0 then 181 else if t 3 = 1 then 136 else 140) else (if t 3 = 0 then 898 else if t 3 = 1 then 142 else 144)) else (if t 2 = 0 then (if t 3 = 0 then 2779 else if t 3 = 1 then 2775 else 2987) else if t 2 = 1 then (if t 3 = 0 then 2778 else if t 3 = 1 then 2766 else 2768) else (if t 3 = 0 then 2989 else if t 3 = 1 then 2769 else 2770))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 174 else 894) else if t 2 = 1 then (if t 3 = 0 then 182 else if t 3 = 1 then 146 else 150) else (if t 3 = 0 then 899 else if t 3 = 1 then 152 else 154)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 184 else if t 3 = 1 then 160 else 888) else if t 2 = 1 then (if t 3 = 0 then 180 else if t 3 = 1 then 117 else 124) else (if t 3 = 0 then 897 else if t 3 = 1 then 128 else 132)) else (if t 2 = 0 then (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 889) else if t 2 = 1 then (if t 3 = 0 then 188 else if t 3 = 1 then 119 else 125) else (if t 3 = 0 then 901 else if t 3 = 1 then 129 else 133))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 2115 else 2984) else if t 2 = 1 then (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1833) else (if t 3 = 0 then 2986 else if t 3 = 1 then 1535 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 890) else if t 2 = 1 then (if t 3 = 0 then 192 else if t 3 = 1 then 121 else 126) else (if t 3 = 0 then 903 else if t 3 = 1 then 130 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 197 else if t 3 = 1 then 163 else 891) else if t 2 = 1 then (if t 3 = 0 then 196 else if t 3 = 1 then 122 else 127) else (if t 3 = 0 then 905 else if t 3 = 1 then 131 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3714 else (if jt.2.val < 2 then 3745 else 3725)) else (if jt.2.val < 4 then 3744 else (if jt.2.val < 5 then 3746 else 3722))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3708 else (if jt.2.val < 2 then 3748 else 3713)) else (if jt.2.val < 4 then 3747 else (if jt.2.val < 5 then 3749 else 3705)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 881 else (if jt.2.val < 2 then 883 else 887)) else (if jt.2.val < 4 then 882 else (if jt.2.val < 5 then 886 else 885))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 844 else (if jt.2.val < 2 then 884 else 846)) else (if jt.2.val < 4 then 879 else (if jt.2.val < 5 then 880 else 792)))))

checked_coverage fastCoverage0253 pairing0253 template0253 witness0253

theorem coverage0253 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0253) (maskBits m))
    cores template0253 witness0253 := by
  rw [← coresFast_eq]
  exact fastCoverage0253

theorem coverageSize0253 : ∀ q : Pattern,
    (cores (witness0253 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0253 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0253
#print axioms coverageSize0253

noncomputable def pairing0254 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0254 : List (Fin 4935) := templateData0254

noncomputable def witness0254 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 228 else 932) else if t 2 = 1 then (if t 3 = 0 then 224 else if t 3 = 1 then 220 else 298) else (if t 3 = 0 then 918 else if t 3 = 1 then 266 else 299)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 230 else if t 3 = 1 then 226 else 928) else if t 2 = 1 then (if t 3 = 0 then 222 else if t 3 = 1 then 218 else 290) else (if t 3 = 0 then 916 else if t 3 = 1 then 264 else 292)) else (if t 2 = 0 then (if t 3 = 0 then 2751 else if t 3 = 1 then 2750 else 2985) else if t 2 = 1 then (if t 3 = 0 then 2749 else if t 3 = 1 then 2747 else 2759) else (if t 3 = 0 then 2983 else if t 3 = 1 then 2756 else 2760))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 227 else 930) else if t 2 = 1 then (if t 3 = 0 then 223 else if t 3 = 1 then 219 else 294) else (if t 3 = 0 then 917 else if t 3 = 1 then 265 else 296)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 229 else if t 3 = 1 then 225 else 924) else if t 2 = 1 then (if t 3 = 0 then 221 else if t 3 = 1 then 217 else 282) else (if t 3 = 0 then 915 else if t 3 = 1 then 263 else 286)) else (if t 2 = 0 then (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 925) else if t 2 = 1 then (if t 3 = 0 then 240 else if t 3 = 1 then 237 else 283) else (if t 3 = 0 then 919 else if t 3 = 1 then 272 else 287))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1461 else 2990) else if t 2 = 1 then (if t 3 = 0 then 1785 else if t 3 = 1 then 1458 else 1473) else (if t 3 = 0 then 2988 else if t 3 = 1 then 2169 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 257 else if t 3 = 1 then 255 else 926) else if t 2 = 1 then (if t 3 = 0 then 253 else if t 3 = 1 then 250 else 284) else (if t 3 = 0 then 921 else if t 3 = 1 then 276 else 288)) else (if t 2 = 0 then (if t 3 = 0 then 262 else if t 3 = 1 then 261 else 927) else if t 2 = 1 then (if t 3 = 0 then 260 else if t 3 = 1 then 259 else 285) else (if t 3 = 0 then 923 else if t 3 = 1 then 280 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3702 else (if jt.2.val < 2 then 3755 else 3711)) else (if jt.2.val < 4 then 3753 else (if jt.2.val < 5 then 3754 else 3709))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3717 else (if jt.2.val < 2 then 3752 else 3720)) else (if jt.2.val < 4 then 3750 else (if jt.2.val < 5 then 3751 else 3715)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 848 else (if jt.2.val < 2 then 914 else 851)) else (if jt.2.val < 4 then 906 else (if jt.2.val < 5 then 907 else 793))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 908 else (if jt.2.val < 2 then 910 else 913)) else (if jt.2.val < 4 then 909 else (if jt.2.val < 5 then 912 else 911)))))

checked_coverage fastCoverage0254 pairing0254 template0254 witness0254

theorem coverage0254 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0254) (maskBits m))
    cores template0254 witness0254 := by
  rw [← coresFast_eq]
  exact fastCoverage0254

theorem coverageSize0254 : ∀ q : Pattern,
    (cores (witness0254 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0254 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0254
#print axioms coverageSize0254

noncomputable def pairing0255 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0255 : List (Fin 4935) := templateData0255

noncomputable def witness0255 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 995 else 380) else if t 2 = 1 then (if t 3 = 0 then 1004 else if t 3 = 1 then 977 else 979) else (if t 3 = 0 then 104 else if t 3 = 1 then 978 else 980)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1006 else if t 3 = 1 then 991 else 373) else if t 2 = 1 then (if t 3 = 0 then 1000 else if t 3 = 1 then 957 else 963) else (if t 3 = 0 then 100 else if t 3 = 1 then 961 else 965)) else (if t 2 = 0 then (if t 3 = 0 then 2981 else if t 3 = 1 then 2979 else 2738) else if t 2 = 1 then (if t 3 = 0 then 2980 else if t 3 = 1 then 2970 else 2973) else (if t 3 = 0 then 2800 else if t 3 = 1 then 2972 else 2974))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 993 else 377) else if t 2 = 1 then (if t 3 = 0 then 1002 else if t 3 = 1 then 967 else 973) else (if t 3 = 0 then 102 else if t 3 = 1 then 971 else 975)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1005 else if t 3 = 1 then 987 else 367) else if t 2 = 1 then (if t 3 = 0 then 996 else if t 3 = 1 then 939 else 949) else (if t 3 = 0 then 96 else if t 3 = 1 then 945 else 953)) else (if t 2 = 0 then (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 368) else if t 2 = 1 then (if t 3 = 0 then 997 else if t 3 = 1 then 941 else 950) else (if t 3 = 0 then 97 else if t 3 = 1 then 946 else 954))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1430 else 2796) else if t 2 = 1 then (if t 3 = 0 then 1374 else if t 3 = 1 then 1795 else 1799) else (if t 3 = 0 then 2744 else if t 3 = 1 then 2136 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1011 else if t 3 = 1 then 989 else 369) else if t 2 = 1 then (if t 3 = 0 then 998 else if t 3 = 1 then 943 else 951) else (if t 3 = 0 then 98 else if t 3 = 1 then 947 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 1013 else if t 3 = 1 then 990 else 370) else if t 2 = 1 then (if t 3 = 0 then 999 else if t 3 = 1 then 944 else 952) else (if t 3 = 0 then 99 else if t 3 = 1 then 948 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3762 else (if jt.2.val < 2 then 3793 else 3773)) else (if jt.2.val < 4 then 3792 else (if jt.2.val < 5 then 3794 else 3770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3780 else (if jt.2.val < 2 then 3796 else 3785)) else (if jt.2.val < 4 then 3795 else (if jt.2.val < 5 then 3797 else 3777)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 885 else (if jt.2.val < 2 then 985 else 887)) else (if jt.2.val < 4 then 984 else (if jt.2.val < 5 then 986 else 881))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 911 else (if jt.2.val < 2 then 983 else 913)) else (if jt.2.val < 4 then 981 else (if jt.2.val < 5 then 982 else 908)))))

checked_coverage fastCoverage0255 pairing0255 template0255 witness0255

theorem coverage0255 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0255) (maskBits m))
    cores template0255 witness0255 := by
  rw [← coresFast_eq]
  exact fastCoverage0255

theorem coverageSize0255 : ∀ q : Pattern,
    (cores (witness0255 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0255 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0255
#print axioms coverageSize0255

noncomputable def pairing0256 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0256 : List (Fin 4935) := templateData0256

noncomputable def witness0256 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2813 else 2633) else if t 2 = 1 then (if t 3 = 0 then 2817 else if t 3 = 1 then 2809 else 2855) else (if t 3 = 0 then 2577 else if t 3 = 1 then 2860 else 2868)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2811 else 1415) else if t 2 = 1 then (if t 3 = 0 then 2815 else if t 3 = 1 then 2807 else 1414) else (if t 3 = 0 then 1372 else if t 3 = 1 then 1370 else 1777)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1171 else 569) else if t 2 = 1 then (if t 3 = 0 then 1173 else if t 3 = 1 then 1169 else 1202) else (if t 3 = 0 then 695 else if t 3 = 1 then 1211 else 1222))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2812 else 1585) else if t 2 = 1 then (if t 3 = 0 then 2816 else if t 3 = 1 then 2808 else 1584) else (if t 3 = 0 then 1687 else if t 3 = 1 then 1685 else 1852)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2810 else 2632) else if t 2 = 1 then (if t 3 = 0 then 2814 else if t 3 = 1 then 2806 else 2854) else (if t 3 = 0 then 2576 else if t 3 = 1 then 2859 else 2864)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2635) else if t 2 = 1 then (if t 3 = 0 then 2829 else if t 3 = 1 then 2826 else 2856) else (if t 3 = 0 then 2578 else if t 3 = 1 then 2861 else 2865))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1040 else 665) else if t 2 = 1 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1073) else (if t 3 = 0 then 599 else if t 3 = 1 then 1082 else 1093)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2637) else if t 2 = 1 then (if t 3 = 0 then 2838 else if t 3 = 1 then 2835 else 2857) else (if t 3 = 0 then 2579 else if t 3 = 1 then 2862 else 2866)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2841 else 2639) else if t 2 = 1 then (if t 3 = 0 then 2842 else if t 3 = 1 then 2840 else 2858) else (if t 3 = 0 then 2580 else if t 3 = 1 then 2863 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3762 else (if jt.2.val < 2 then 3772 else 3773)) else (if jt.2.val < 4 then 3769 else (if jt.2.val < 5 then 3771 else 3770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3763 else (if jt.2.val < 2 then 3767 else 3768)) else (if jt.2.val < 4 then 3764 else (if jt.2.val < 5 then 3766 else 3765)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3006 else (if jt.2.val < 2 then 3012 else 3015)) else (if jt.2.val < 4 then 3011 else (if jt.2.val < 5 then 3014 else 3013))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3007 else (if jt.2.val < 2 then 3016 else 3017)) else (if jt.2.val < 4 then 3008 else (if jt.2.val < 5 then 3010 else 3009)))))

checked_coverage fastCoverage0256 pairing0256 template0256 witness0256

theorem coverage0256 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0256) (maskBits m))
    cores template0256 witness0256 := by
  rw [← coresFast_eq]
  exact fastCoverage0256

theorem coverageSize0256 : ∀ q : Pattern,
    (cores (witness0256 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0256 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0256
#print axioms coverageSize0256

noncomputable def pairing0257 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0257 : List (Fin 4935) := templateData0257

noncomputable def witness0257 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2446 else 2898) else if t 2 = 1 then (if t 3 = 0 then 2450 else if t 3 = 1 then 2442 else 2482) else (if t 3 = 0 then 2884 else if t 3 = 1 then 2500 else 2501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2444 else 1413) else if t 2 = 1 then (if t 3 = 0 then 2448 else if t 3 = 1 then 2440 else 1412) else (if t 3 = 0 then 1762 else if t 3 = 1 then 1753 else 1450)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 724 else 1109) else if t 2 = 1 then (if t 3 = 0 then 726 else if t 3 = 1 then 722 else 756) else (if t 3 = 0 then 1145 else if t 3 = 1 then 778 else 780))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2445 else 1583) else if t 2 = 1 then (if t 3 = 0 then 2449 else if t 3 = 1 then 2441 else 1582) else (if t 3 = 0 then 1915 else if t 3 = 1 then 1906 else 1618)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2443 else 2897) else if t 2 = 1 then (if t 3 = 0 then 2447 else if t 3 = 1 then 2439 else 2481) else (if t 3 = 0 then 2883 else if t 3 = 1 then 2492 else 2496)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2899) else if t 2 = 1 then (if t 3 = 0 then 2462 else if t 3 = 1 then 2459 else 2486) else (if t 3 = 0 then 2885 else if t 3 = 1 then 2493 else 2497))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 439 else 1136) else if t 2 = 1 then (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 471) else (if t 3 = 0 then 1118 else if t 3 = 1 then 493 else 495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2900) else if t 2 = 1 then (if t 3 = 0 then 2471 else if t 3 = 1 then 2468 else 2488) else (if t 3 = 0 then 2886 else if t 3 = 1 then 2494 else 2498)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2474 else 2901) else if t 2 = 1 then (if t 3 = 0 then 2475 else if t 3 = 1 then 2473 else 2490) else (if t 3 = 0 then 2887 else if t 3 = 1 then 2495 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3690 else (if jt.2.val < 2 then 3700 else 3701)) else (if jt.2.val < 4 then 3697 else (if jt.2.val < 5 then 3699 else 3698))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3691 else (if jt.2.val < 2 then 3695 else 3696)) else (if jt.2.val < 4 then 3692 else (if jt.2.val < 5 then 3694 else 3693)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3020 else (if jt.2.val < 2 then 3022 else 3025)) else (if jt.2.val < 4 then 3021 else (if jt.2.val < 5 then 3024 else 3023))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3009 else (if jt.2.val < 2 then 3026 else 3017)) else (if jt.2.val < 4 then 3018 else (if jt.2.val < 5 then 3019 else 3007)))))

checked_coverage fastCoverage0257 pairing0257 template0257 witness0257

theorem coverage0257 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0257) (maskBits m))
    cores template0257 witness0257 := by
  rw [← coresFast_eq]
  exact fastCoverage0257

theorem coverageSize0257 : ∀ q : Pattern,
    (cores (witness0257 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0257 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0257
#print axioms coverageSize0257

noncomputable def pairing0258 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0258 : List (Fin 4935) := templateData0258

noncomputable def witness0258 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2710 else 2906) else if t 2 = 1 then (if t 3 = 0 then 2705 else if t 3 = 1 then 2688 else 2690) else (if t 3 = 0 then 2882 else if t 3 = 1 then 2689 else 2691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2708 else 2107) else if t 2 = 1 then (if t 3 = 0 then 2703 else if t 3 = 1 then 2682 else 2090) else (if t 3 = 0 then 1357 else if t 3 = 1 then 1339 else 1342)) else (if t 2 = 0 then (if t 3 = 0 then 491 else if t 3 = 1 then 489 else 1120) else if t 2 = 1 then (if t 3 = 0 then 475 else if t 3 = 1 then 445 else 450) else (if t 3 = 0 then 1138 else if t 3 = 1 then 448 else 452))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2709 else 2227) else if t 2 = 1 then (if t 3 = 0 then 2704 else if t 3 = 1 then 2685 else 2212) else (if t 3 = 0 then 1672 else if t 3 = 1 then 1657 else 1659)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2707 else 2902) else if t 2 = 1 then (if t 3 = 0 then 2695 else if t 3 = 1 then 2664 else 2674) else (if t 3 = 0 then 2878 else if t 3 = 1 then 2670 else 2678)) else (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2903) else if t 2 = 1 then (if t 3 = 0 then 2696 else if t 3 = 1 then 2666 else 2675) else (if t 3 = 0 then 2879 else if t 3 = 1 then 2671 else 2679))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 774 else 1147) else if t 2 = 1 then (if t 3 = 0 then 760 else if t 3 = 1 then 733 else 737) else (if t 3 = 0 then 1111 else if t 3 = 1 then 735 else 739)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2717 else 2904) else if t 2 = 1 then (if t 3 = 0 then 2697 else if t 3 = 1 then 2668 else 2676) else (if t 3 = 0 then 2880 else if t 3 = 1 then 2672 else 2680)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2719 else 2905) else if t 2 = 1 then (if t 3 = 0 then 2698 else if t 3 = 1 then 2669 else 2677) else (if t 3 = 0 then 2881 else if t 3 = 1 then 2673 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3726 else (if jt.2.val < 2 then 3728 else 3735)) else (if jt.2.val < 4 then 3727 else (if jt.2.val < 5 then 3734 else 3733))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3729 else (if jt.2.val < 2 then 3731 else 3737)) else (if jt.2.val < 4 then 3730 else (if jt.2.val < 5 then 3736 else 3732)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3013 else (if jt.2.val < 2 then 3033 else 3015)) else (if jt.2.val < 4 then 3027 else (if jt.2.val < 5 then 3028 else 3006))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3029 else (if jt.2.val < 2 then 3031 else 3035)) else (if jt.2.val < 4 then 3030 else (if jt.2.val < 5 then 3034 else 3032)))))

checked_coverage fastCoverage0258 pairing0258 template0258 witness0258

theorem coverage0258 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0258) (maskBits m))
    cores template0258 witness0258 := by
  rw [← coresFast_eq]
  exact fastCoverage0258

theorem coverageSize0258 : ∀ q : Pattern,
    (cores (witness0258 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0258 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0258
#print axioms coverageSize0258

noncomputable def pairing0259 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 2 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0259 : List (Fin 4935) := templateData0259

noncomputable def witness0259 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2960 else 2654) else if t 2 = 1 then (if t 3 = 0 then 2953 else if t 3 = 1 then 2937 else 2939) else (if t 3 = 0 then 2561 else if t 3 = 1 then 2938 else 2940)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2958 else 2104) else if t 2 = 1 then (if t 3 = 0 then 2951 else if t 3 = 1 then 2931 else 2082) else (if t 3 = 0 then 1750 else if t 3 = 1 then 1730 else 1733)) else (if t 2 = 0 then (if t 3 = 0 then 1091 else if t 3 = 1 then 1084 else 601) else if t 2 = 1 then (if t 3 = 0 then 1075 else if t 3 = 1 then 1046 else 1051) else (if t 3 = 0 then 669 else if t 3 = 1 then 1049 else 1053))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2959 else 2224) else if t 2 = 1 then (if t 3 = 0 then 2952 else if t 3 = 1 then 2934 else 2206) else (if t 3 = 0 then 1903 else if t 3 = 1 then 1888 else 1890)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2954 else 2650) else if t 2 = 1 then (if t 3 = 0 then 2947 else if t 3 = 1 then 2913 else 2923) else (if t 3 = 0 then 2554 else if t 3 = 1 then 2919 else 2927)) else (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2651) else if t 2 = 1 then (if t 3 = 0 then 2948 else if t 3 = 1 then 2915 else 2924) else (if t 3 = 0 then 2555 else if t 3 = 1 then 2920 else 2928))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1213 else 697) else if t 2 = 1 then (if t 3 = 0 then 1204 else if t 3 = 1 then 1180 else 1184) else (if t 3 = 0 then 573 else if t 3 = 1 then 1182 else 1186)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2956 else 2652) else if t 2 = 1 then (if t 3 = 0 then 2949 else if t 3 = 1 then 2917 else 2925) else (if t 3 = 0 then 2556 else if t 3 = 1 then 2921 else 2929)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2957 else 2653) else if t 2 = 1 then (if t 3 = 0 then 2950 else if t 3 = 1 then 2918 else 2926) else (if t 3 = 0 then 2557 else if t 3 = 1 then 2922 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3774 else (if jt.2.val < 2 then 3776 else 3783)) else (if jt.2.val < 4 then 3775 else (if jt.2.val < 5 then 3782 else 3781))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3777 else (if jt.2.val < 2 then 3779 else 3785)) else (if jt.2.val < 4 then 3778 else (if jt.2.val < 5 then 3784 else 3780)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3023 else (if jt.2.val < 2 then 3040 else 3025)) else (if jt.2.val < 4 then 3036 else (if jt.2.val < 5 then 3037 else 3020))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3032 else (if jt.2.val < 2 then 3039 else 3035)) else (if jt.2.val < 4 then 3038 else (if jt.2.val < 5 then 3041 else 3029)))))

checked_coverage fastCoverage0259 pairing0259 template0259 witness0259

theorem coverage0259 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0259) (maskBits m))
    cores template0259 witness0259 := by
  rw [← coresFast_eq]
  exact fastCoverage0259

theorem coverageSize0259 : ∀ q : Pattern,
    (cores (witness0259 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0259 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0259
#print axioms coverageSize0259

noncomputable def pairing0260 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0260 : List (Fin 4935) := templateData0260

noncomputable def witness0260 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 803 else 271) else if t 2 = 1 then (if t 3 = 0 then 807 else if t 3 = 1 then 799 else 855) else (if t 3 = 0 then 201 else if t 3 = 1 then 864 else 878)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 809 else if t 3 = 1 then 801 else 269) else if t 2 = 1 then (if t 3 = 0 then 805 else if t 3 = 1 then 797 else 853) else (if t 3 = 0 then 199 else if t 3 = 1 then 862 else 874)) else (if t 2 = 0 then (if t 3 = 0 then 2997 else if t 3 = 1 then 2995 else 2757) else if t 2 = 1 then (if t 3 = 0 then 2996 else if t 3 = 1 then 2993 else 3002) else (if t 3 = 0 then 2781 else if t 3 = 1 then 3003 else 3004))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 802 else 270) else if t 2 = 1 then (if t 3 = 0 then 806 else if t 3 = 1 then 798 else 854) else (if t 3 = 0 then 200 else if t 3 = 1 then 863 else 876)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 808 else if t 3 = 1 then 800 else 268) else if t 2 = 1 then (if t 3 = 0 then 804 else if t 3 = 1 then 796 else 852) else (if t 3 = 0 then 198 else if t 3 = 1 then 861 else 870)) else (if t 2 = 0 then (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 274) else if t 2 = 1 then (if t 3 = 0 then 821 else if t 3 = 1 then 816 else 856) else (if t 3 = 0 then 202 else if t 3 = 1 then 865 else 871))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 2145 else 2777) else if t 2 = 1 then (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1598) else (if t 3 = 0 then 2763 else if t 3 = 1 then 1689 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 278) else if t 2 = 1 then (if t 3 = 0 then 834 else if t 3 = 1 then 829 else 858) else (if t 3 = 0 then 204 else if t 3 = 1 then 867 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 841 else if t 3 = 1 then 839 else 281) else if t 2 = 1 then (if t 3 = 0 then 840 else if t 3 = 1 then 838 else 860) else (if t 3 = 0 then 206 else if t 3 = 1 then 869 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3774 else (if jt.2.val < 2 then 3791 else 3783)) else (if jt.2.val < 4 then 3789 else (if jt.2.val < 5 then 3790 else 3781))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3765 else (if jt.2.val < 2 then 3788 else 3768)) else (if jt.2.val < 4 then 3786 else (if jt.2.val < 5 then 3787 else 3763)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1224 else (if jt.2.val < 2 then 1230 else 1233)) else (if jt.2.val < 4 then 1229 else (if jt.2.val < 5 then 1232 else 1231))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1225 else (if jt.2.val < 2 then 1234 else 1235)) else (if jt.2.val < 4 then 1226 else (if jt.2.val < 5 then 1228 else 1227)))))

checked_coverage fastCoverage0260 pairing0260 template0260 witness0260

theorem coverage0260 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0260) (maskBits m))
    cores template0260 witness0260 := by
  rw [← coresFast_eq]
  exact fastCoverage0260

theorem coverageSize0260 : ∀ q : Pattern,
    (cores (witness0260 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0260 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0260
#print axioms coverageSize0260

noncomputable def pairing0261 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0261 : List (Fin 4935) := templateData0261

noncomputable def witness0261 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 16 else 918) else if t 2 = 1 then (if t 3 = 0 then 20 else if t 3 = 1 then 12 else 62) else (if t 3 = 0 then 900 else if t 3 = 1 then 94 else 95)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 22 else if t 3 = 1 then 14 else 916) else if t 2 = 1 then (if t 3 = 0 then 18 else if t 3 = 1 then 10 else 60) else (if t 3 = 0 then 898 else if t 3 = 1 then 86 else 88)) else (if t 2 = 0 then (if t 3 = 0 then 2789 else if t 3 = 1 then 2787 else 2983) else if t 2 = 1 then (if t 3 = 0 then 2788 else if t 3 = 1 then 2785 else 2794) else (if t 3 = 0 then 2989 else if t 3 = 1 then 2797 else 2798))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 15 else 917) else if t 2 = 1 then (if t 3 = 0 then 19 else if t 3 = 1 then 11 else 61) else (if t 3 = 0 then 899 else if t 3 = 1 then 90 else 92)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 21 else if t 3 = 1 then 13 else 915) else if t 2 = 1 then (if t 3 = 0 then 17 else if t 3 = 1 then 9 else 59) else (if t 3 = 0 then 897 else if t 3 = 1 then 78 else 82)) else (if t 2 = 0 then (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 919) else if t 2 = 1 then (if t 3 = 0 then 34 else if t 3 = 1 then 29 else 68) else (if t 3 = 0 then 901 else if t 3 = 1 then 79 else 83))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 2124 else 2988) else if t 2 = 1 then (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1848) else (if t 3 = 0 then 2986 else if t 3 = 1 then 1521 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 921) else if t 2 = 1 then (if t 3 = 0 then 47 else if t 3 = 1 then 42 else 72) else (if t 3 = 0 then 903 else if t 3 = 1 then 80 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 54 else if t 3 = 1 then 52 else 923) else if t 2 = 1 then (if t 3 = 0 then 53 else if t 3 = 1 then 51 else 76) else (if t 3 = 0 then 905 else if t 3 = 1 then 81 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3726 else (if jt.2.val < 2 then 3743 else 3735)) else (if jt.2.val < 4 then 3741 else (if jt.2.val < 5 then 3742 else 3733))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3693 else (if jt.2.val < 2 then 3740 else 3696)) else (if jt.2.val < 4 then 3738 else (if jt.2.val < 5 then 3739 else 3691)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1238 else (if jt.2.val < 2 then 1240 else 1243)) else (if jt.2.val < 4 then 1239 else (if jt.2.val < 5 then 1242 else 1241))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1227 else (if jt.2.val < 2 then 1244 else 1235)) else (if jt.2.val < 4 then 1236 else (if jt.2.val < 5 then 1237 else 1225)))))

checked_coverage fastCoverage0261 pairing0261 template0261 witness0261

theorem coverage0261 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0261) (maskBits m))
    cores template0261 witness0261 := by
  rw [← coresFast_eq]
  exact fastCoverage0261

theorem coverageSize0261 : ∀ q : Pattern,
    (cores (witness0261 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0261 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0261
#print axioms coverageSize0261

noncomputable def pairing0262 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0262 : List (Fin 4935) := templateData0262

noncomputable def witness0262 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 384 else 932) else if t 2 = 1 then (if t 3 = 0 then 379 else if t 3 = 1 then 356 else 358) else (if t 3 = 0 then 896 else if t 3 = 1 then 357 else 359)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 386 else if t 3 = 1 then 382 else 928) else if t 2 = 1 then (if t 3 = 0 then 371 else if t 3 = 1 then 336 else 342) else (if t 3 = 0 then 892 else if t 3 = 1 then 340 else 344)) else (if t 2 = 0 then (if t 3 = 0 then 2741 else if t 3 = 1 then 2740 else 2985) else if t 2 = 1 then (if t 3 = 0 then 2737 else if t 3 = 1 then 2728 else 2731) else (if t 3 = 0 then 2987 else if t 3 = 1 then 2730 else 2732))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 383 else 930) else if t 2 = 1 then (if t 3 = 0 then 375 else if t 3 = 1 then 346 else 352) else (if t 3 = 0 then 894 else if t 3 = 1 then 350 else 354)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 385 else if t 3 = 1 then 381 else 924) else if t 2 = 1 then (if t 3 = 0 then 363 else if t 3 = 1 then 318 else 328) else (if t 3 = 0 then 888 else if t 3 = 1 then 324 else 332)) else (if t 2 = 0 then (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 925) else if t 2 = 1 then (if t 3 = 0 then 364 else if t 3 = 1 then 320 else 329) else (if t 3 = 0 then 889 else if t 3 = 1 then 325 else 333))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1497 else 2990) else if t 2 = 1 then (if t 3 = 0 then 1773 else if t 3 = 1 then 1483 else 1487) else (if t 3 = 0 then 2984 else if t 3 = 1 then 2157 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 395 else if t 3 = 1 then 393 else 926) else if t 2 = 1 then (if t 3 = 0 then 365 else if t 3 = 1 then 322 else 330) else (if t 3 = 0 then 890 else if t 3 = 1 then 326 else 334)) else (if t 2 = 0 then (if t 3 = 0 then 398 else if t 3 = 1 then 397 else 927) else if t 2 = 1 then (if t 3 = 0 then 366 else if t 3 = 1 then 323 else 331) else (if t 3 = 0 then 891 else if t 3 = 1 then 327 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3690 else (if jt.2.val < 2 then 3757 else 3701)) else (if jt.2.val < 4 then 3756 else (if jt.2.val < 5 then 3758 else 3698))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3732 else (if jt.2.val < 2 then 3760 else 3737)) else (if jt.2.val < 4 then 3759 else (if jt.2.val < 5 then 3761 else 3729)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1231 else (if jt.2.val < 2 then 1251 else 1233)) else (if jt.2.val < 4 then 1245 else (if jt.2.val < 5 then 1246 else 1224))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1247 else (if jt.2.val < 2 then 1249 else 1253)) else (if jt.2.val < 4 then 1248 else (if jt.2.val < 5 then 1252 else 1250)))))

checked_coverage fastCoverage0262 pairing0262 template0262 witness0262

theorem coverage0262 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0262) (maskBits m))
    cores template0262 witness0262 := by
  rw [← coresFast_eq]
  exact fastCoverage0262

theorem coverageSize0262 : ∀ q : Pattern,
    (cores (witness0262 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0262 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0262
#print axioms coverageSize0262

noncomputable def pairing0263 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0263 : List (Fin 4935) := templateData0263

noncomputable def witness0263 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 1004 else 308) else if t 2 = 1 then (if t 3 = 0 then 995 else if t 3 = 1 then 977 else 979) else (if t 3 = 0 then 179 else if t 3 = 1 then 978 else 980)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1006 else if t 3 = 1 then 1000 else 304) else if t 2 = 1 then (if t 3 = 0 then 991 else if t 3 = 1 then 957 else 963) else (if t 3 = 0 then 172 else if t 3 = 1 then 961 else 965)) else (if t 2 = 0 then (if t 3 = 0 then 2981 else if t 3 = 1 then 2980 else 2762) else if t 2 = 1 then (if t 3 = 0 then 2979 else if t 3 = 1 then 2970 else 2973) else (if t 3 = 0 then 2776 else if t 3 = 1 then 2972 else 2974))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 1002 else 306) else if t 2 = 1 then (if t 3 = 0 then 993 else if t 3 = 1 then 967 else 973) else (if t 3 = 0 then 176 else if t 3 = 1 then 971 else 975)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1005 else if t 3 = 1 then 996 else 300) else if t 2 = 1 then (if t 3 = 0 then 987 else if t 3 = 1 then 939 else 949) else (if t 3 = 0 then 166 else if t 3 = 1 then 945 else 953)) else (if t 2 = 0 then (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 301) else if t 2 = 1 then (if t 3 = 0 then 988 else if t 3 = 1 then 941 else 950) else (if t 3 = 0 then 167 else if t 3 = 1 then 946 else 954))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1374 else 2782) else if t 2 = 1 then (if t 3 = 0 then 1430 else if t 3 = 1 then 1795 else 1799) else (if t 3 = 0 then 2758 else if t 3 = 1 then 2136 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1011 else if t 3 = 1 then 998 else 302) else if t 2 = 1 then (if t 3 = 0 then 989 else if t 3 = 1 then 943 else 951) else (if t 3 = 0 then 168 else if t 3 = 1 then 947 else 955)) else (if t 2 = 0 then (if t 3 = 0 then 1013 else if t 3 = 1 then 999 else 303) else if t 2 = 1 then (if t 3 = 0 then 990 else if t 3 = 1 then 944 else 952) else (if t 3 = 0 then 169 else if t 3 = 1 then 948 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3762 else (if jt.2.val < 2 then 3793 else 3773)) else (if jt.2.val < 4 then 3792 else (if jt.2.val < 5 then 3794 else 3770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3780 else (if jt.2.val < 2 then 3796 else 3785)) else (if jt.2.val < 4 then 3795 else (if jt.2.val < 5 then 3797 else 3777)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1241 else (if jt.2.val < 2 then 1258 else 1243)) else (if jt.2.val < 4 then 1254 else (if jt.2.val < 5 then 1255 else 1238))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1250 else (if jt.2.val < 2 then 1257 else 1253)) else (if jt.2.val < 4 then 1256 else (if jt.2.val < 5 then 1259 else 1247)))))

checked_coverage fastCoverage0263 pairing0263 template0263 witness0263

theorem coverage0263 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0263) (maskBits m))
    cores template0263 witness0263 := by
  rw [← coresFast_eq]
  exact fastCoverage0263

theorem coverageSize0263 : ∀ q : Pattern,
    (cores (witness0263 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0263 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0263
#print axioms coverageSize0263

noncomputable def pairing0264 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0264 : List (Fin 4935) := templateData0264

noncomputable def witness0264 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3822 else if t 3 = 1 then 3814 else 3860) else if t 2 = 1 then (if t 3 = 0 then 3818 else if t 3 = 1 then 3810 else 2980) else (if t 3 = 0 then 2751 else if t 3 = 1 then 2749 else 2762)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3820 else if t 3 = 1 then 3812 else 1084) else if t 2 = 1 then (if t 3 = 0 then 3816 else if t 3 = 1 then 3808 else 1078) else (if t 3 = 0 then 539 else if t 3 = 1 then 535 else 595)) else (if t 2 = 0 then (if t 3 = 0 then 728 else if t 3 = 1 then 724 else 790) else if t 2 = 1 then (if t 3 = 0 then 727 else if t 3 = 1 then 723 else 784) else (if t 3 = 0 then 1544 else if t 3 = 1 then 1108 else 1549))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3821 else if t 3 = 1 then 3813 else 1003) else if t 2 = 1 then (if t 3 = 0 then 3817 else if t 3 = 1 then 3809 else 997) else (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 301)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3819 else if t 3 = 1 then 3811 else 2955) else if t 2 = 1 then (if t 3 = 0 then 3815 else if t 3 = 1 then 3807 else 3852) else (if t 3 = 0 then 3845 else if t 3 = 1 then 3843 else 3856)) else (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2503) else if t 2 = 1 then (if t 3 = 0 then 3836 else if t 3 = 1 then 3834 else 3854) else (if t 3 = 0 then 3849 else if t 3 = 1 then 3848 else 3858))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 1375) else if t 2 = 1 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 999) else (if t 3 = 0 then 262 else if t 3 = 1 then 260 else 303)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2957) else if t 2 = 1 then (if t 3 = 0 then 3829 else if t 3 = 1 then 3827 else 3853) else (if t 3 = 0 then 3847 else if t 3 = 1 then 3846 else 3857)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2474 else 2505) else if t 2 = 1 then (if t 3 = 0 then 3838 else if t 3 = 1 then 3837 else 3855) else (if t 3 = 0 then 3851 else if t 3 = 1 then 3850 else 3859))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3806 else (if jt.2.val < 2 then 3826 else 3828)) else (if jt.2.val < 4 then 3823 else (if jt.2.val < 5 then 3825 else 3824))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3805 else (if jt.2.val < 2 then 3833 else 3835)) else (if jt.2.val < 4 then 3830 else (if jt.2.val < 5 then 3832 else 3831)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3804 else (if jt.2.val < 2 then 3842 else 3844)) else (if jt.2.val < 4 then 3839 else (if jt.2.val < 5 then 3841 else 3840))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3798 else (if jt.2.val < 2 then 3800 else 3803)) else (if jt.2.val < 4 then 3799 else (if jt.2.val < 5 then 3802 else 3801)))))

checked_coverage fastCoverage0264 pairing0264 template0264 witness0264

theorem coverage0264 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0264) (maskBits m))
    cores template0264 witness0264 := by
  rw [← coresFast_eq]
  exact fastCoverage0264

theorem coverageSize0264 : ∀ q : Pattern,
    (cores (witness0264 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0264 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0264
#print axioms coverageSize0264

noncomputable def pairing0265 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0265 : List (Fin 4935) := templateData0265

noncomputable def witness0265 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 3905) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2979) else (if t 3 = 0 then 2741 else if t 3 = 1 then 2737 else 2738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 1075) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 1069) else (if t 3 = 0 then 490 else if t 3 = 1 then 462 else 467)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 667 else 669) else if t 2 = 1 then (if t 3 = 0 then 682 else if t 3 = 1 then 654 else 659) else (if t 3 = 0 then 1526 else if t 3 = 1 then 1132 else 1519))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 994) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 988) else (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 368)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2948) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3884) else (if t 3 = 0 then 3917 else if t 3 = 1 then 3880 else 3888)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2555) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3886) else (if t 3 = 0 then 3919 else if t 3 = 1 then 3882 else 3890))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 1431) else if t 2 = 1 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 990) else (if t 3 = 0 then 398 else if t 3 = 1 then 366 else 370)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2950) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3885) else (if t 3 = 0 then 3918 else if t 3 = 1 then 3881 else 3889)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2551 else 2557) else if t 2 = 1 then (if t 3 = 0 then 3916 else if t 3 = 1 then 3878 else 3887) else (if t 3 = 0 then 3920 else if t 3 = 1 then 3883 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3870 else (if jt.2.val < 2 then 3872 else 3894)) else (if jt.2.val < 4 then 3871 else (if jt.2.val < 5 then 3893 else 3874))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3867 else (if jt.2.val < 2 then 3869 else 3897)) else (if jt.2.val < 4 then 3868 else (if jt.2.val < 5 then 3896 else 3876)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3864 else (if jt.2.val < 2 then 3866 else 3901)) else (if jt.2.val < 4 then 3865 else (if jt.2.val < 5 then 3900 else 3879))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3801 else (if jt.2.val < 2 then 3863 else 3803)) else (if jt.2.val < 4 then 3861 else (if jt.2.val < 5 then 3862 else 3798)))))

checked_coverage fastCoverage0265 pairing0265 template0265 witness0265

theorem coverage0265 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0265) (maskBits m))
    cores template0265 witness0265 := by
  rw [← coresFast_eq]
  exact fastCoverage0265

theorem coverageSize0265 : ∀ q : Pattern,
    (cores (witness0265 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0265 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0265
#print axioms coverageSize0265

noncomputable def pairing0266 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0266 : List (Fin 4935) := templateData0266

noncomputable def witness0266 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2598 else 2654) else if t 2 = 1 then (if t 3 = 0 then 2602 else if t 3 = 1 then 2594 else 2648) else (if t 3 = 0 then 3925 else if t 3 = 1 then 3923 else 3927)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2596 else 2104) else if t 2 = 1 then (if t 3 = 0 then 2600 else if t 3 = 1 then 2592 else 2101) else (if t 3 = 0 then 538 else if t 3 = 1 then 534 else 589)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1413 else 1453) else if t 2 = 1 then (if t 3 = 0 then 1415 else if t 3 = 1 then 1411 else 1447) else (if t 3 = 0 then 569 else if t 3 = 1 then 567 else 591))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2597 else 2224) else if t 2 = 1 then (if t 3 = 0 then 2601 else if t 3 = 1 then 2593 else 2221) else (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 295)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2595 else 2650) else if t 2 = 1 then (if t 3 = 0 then 2599 else if t 3 = 1 then 2591 else 2640) else (if t 3 = 0 then 2614 else if t 3 = 1 then 2611 else 2641)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2897 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2632 else if t 3 = 1 then 2629 else 2644) else (if t 3 = 0 then 2635 else if t 3 = 1 then 2634 else 2645))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 635 else 697) else if t 2 = 1 then (if t 3 = 0 then 637 else if t 3 = 1 then 633 else 685) else (if t 3 = 0 then 1464 else if t 3 = 1 then 1463 else 1474)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2622 else 2652) else if t 2 = 1 then (if t 3 = 0 then 2623 else if t 3 = 1 then 2620 else 2642) else (if t 3 = 0 then 2627 else if t 3 = 1 then 2625 else 2643)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2900 else 3928) else if t 2 = 1 then (if t 3 = 0 then 2637 else if t 3 = 1 then 2636 else 2646) else (if t 3 = 0 then 2639 else if t 3 = 1 then 2638 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3714 else (if jt.2.val < 2 then 3724 else 3725)) else (if jt.2.val < 4 then 3721 else (if jt.2.val < 5 then 3723 else 3722))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3171 else (if jt.2.val < 2 then 3178 else 3179)) else (if jt.2.val < 4 then 3175 else (if jt.2.val < 5 then 3177 else 3176)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3840 else (if jt.2.val < 2 then 3924 else 3844)) else (if jt.2.val < 4 then 3921 else (if jt.2.val < 5 then 3922 else 3804))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2581 else (if jt.2.val < 2 then 2583 else 2586)) else (if jt.2.val < 4 then 2582 else (if jt.2.val < 5 then 2585 else 2584)))))

checked_coverage fastCoverage0266 pairing0266 template0266 witness0266

theorem coverage0266 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0266) (maskBits m))
    cores template0266 witness0266 := by
  rw [← coresFast_eq]
  exact fastCoverage0266

theorem coverageSize0266 : ∀ q : Pattern,
    (cores (witness0266 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0266 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0266
#print axioms coverageSize0266

noncomputable def pairing0267 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0267 : List (Fin 4935) := templateData0267

noncomputable def witness0267 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2705 else 2706) else if t 2 = 1 then (if t 3 = 0 then 2710 else if t 3 = 1 then 2688 else 2690) else (if t 3 = 0 then 3935 else if t 3 = 1 then 3929 else 3930)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2703 else 2098) else if t 2 = 1 then (if t 3 = 0 then 2708 else if t 3 = 1 then 2682 else 2090) else (if t 3 = 0 then 489 else if t 3 = 1 then 445 else 450)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1357 else 1359) else if t 2 = 1 then (if t 3 = 0 then 1371 else if t 3 = 1 then 1339 else 1342) else (if t 3 = 0 then 503 else if t 3 = 1 then 448 else 452))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2704 else 2218) else if t 2 = 1 then (if t 3 = 0 then 2709 else if t 3 = 1 then 2685 else 2212) else (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 353)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2695 else 2699) else if t 2 = 1 then (if t 3 = 0 then 2707 else if t 3 = 1 then 2664 else 2674) else (if t 3 = 0 then 2715 else if t 3 = 1 then 2666 else 2675)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2878 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2721 else if t 3 = 1 then 2670 else 2678) else (if t 3 = 0 then 2723 else if t 3 = 1 then 2671 else 2679))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 760 else 762) else if t 2 = 1 then (if t 3 = 0 then 774 else if t 3 = 1 then 733 else 737) else (if t 3 = 0 then 1499 else if t 3 = 1 then 1484 else 1488)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2697 else 2701) else if t 2 = 1 then (if t 3 = 0 then 2717 else if t 3 = 1 then 2668 else 2676) else (if t 3 = 0 then 2719 else if t 3 = 1 then 2669 else 2677)) else (if t 2 = 0 then (if t 3 = 0 then 3936 else if t 3 = 1 then 2880 else 3934) else if t 2 = 1 then (if t 3 = 0 then 2724 else if t 3 = 1 then 2672 else 2680) else (if t 3 = 0 then 2725 else if t 3 = 1 then 2673 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3726 else (if jt.2.val < 2 then 3728 else 3735)) else (if jt.2.val < 4 then 3727 else (if jt.2.val < 5 then 3734 else 3733))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3185 else (if jt.2.val < 2 then 3187 else 3190)) else (if jt.2.val < 4 then 3186 else (if jt.2.val < 5 then 3189 else 3188)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3879 else (if jt.2.val < 2 then 3932 else 3901)) else (if jt.2.val < 4 then 3931 else (if jt.2.val < 5 then 3933 else 3864))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2584 else (if jt.2.val < 2 then 2657 else 2586)) else (if jt.2.val < 4 then 2655 else (if jt.2.val < 5 then 2656 else 2581)))))

checked_coverage fastCoverage0267 pairing0267 template0267 witness0267

theorem coverage0267 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0267) (maskBits m))
    cores template0267 witness0267 := by
  rw [← coresFast_eq]
  exact fastCoverage0267

theorem coverageSize0267 : ∀ q : Pattern,
    (cores (witness0267 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0267 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0267
#print axioms coverageSize0267

noncomputable def pairing0268 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0268 : List (Fin 4935) := templateData0268

noncomputable def witness0268 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 16 else 104) else if t 2 = 1 then (if t 3 = 0 then 22 else if t 3 = 1 then 14 else 100) else (if t 3 = 0 then 1471 else if t 3 = 1 then 916 else 1478)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 20 else if t 3 = 1 then 12 else 94) else if t 2 = 1 then (if t 3 = 0 then 18 else if t 3 = 1 then 10 else 86) else (if t 3 = 0 then 65 else if t 3 = 1 then 60 else 88)) else (if t 2 = 0 then (if t 3 = 0 then 3941 else if t 3 = 1 then 3939 else 3943) else if t 2 = 1 then (if t 3 = 0 then 2788 else if t 3 = 1 then 2785 else 2797) else (if t 3 = 0 then 2795 else if t 3 = 1 then 2794 else 2798))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 15 else 102) else if t 2 = 1 then (if t 3 = 0 then 21 else if t 3 = 1 then 13 else 96) else (if t 3 = 0 then 1470 else if t 3 = 1 then 915 else 1476)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 19 else if t 3 = 1 then 11 else 90) else if t 2 = 1 then (if t 3 = 0 then 17 else if t 3 = 1 then 9 else 78) else (if t 3 = 0 then 64 else if t 3 = 1 then 59 else 82)) else (if t 2 = 0 then (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 91) else if t 2 = 1 then (if t 3 = 0 then 34 else if t 3 = 1 then 29 else 79) else (if t 3 = 0 then 70 else if t 3 = 1 then 68 else 83))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 2124 else 2744) else if t 2 = 1 then (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 98) else (if t 3 = 0 then 3942 else if t 3 = 1 then 921 else 3944)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1521) else if t 2 = 1 then (if t 3 = 0 then 47 else if t 3 = 1 then 42 else 80) else (if t 3 = 0 then 74 else if t 3 = 1 then 72 else 84)) else (if t 2 = 0 then (if t 3 = 0 then 1512 else if t 3 = 1 then 1511 else 1522) else if t 2 = 1 then (if t 3 = 0 then 53 else if t 3 = 1 then 51 else 81) else (if t 3 = 0 then 77 else if t 3 = 1 then 76 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3726 else (if jt.2.val < 2 then 3743 else 3735)) else (if jt.2.val < 4 then 3741 else (if jt.2.val < 5 then 3742 else 3733))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3831 else (if jt.2.val < 2 then 3940 else 3835)) else (if jt.2.val < 4 then 3937 else (if jt.2.val < 5 then 3938 else 3805)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1997 else (if jt.2.val < 2 then 2002 else 2003)) else (if jt.2.val < 4 then 1999 else (if jt.2.val < 5 then 2001 else 2000))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 0 else (if jt.2.val < 2 then 2 else 5)) else (if jt.2.val < 4 then 1 else (if jt.2.val < 5 then 4 else 3)))))

checked_coverage fastCoverage0268 pairing0268 template0268 witness0268

theorem coverage0268 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0268) (maskBits m))
    cores template0268 witness0268 := by
  rw [← coresFast_eq]
  exact fastCoverage0268

theorem coverageSize0268 : ∀ q : Pattern,
    (cores (witness0268 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0268 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0268
#print axioms coverageSize0268

noncomputable def pairing0269 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 2) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0269 : List (Fin 4935) := templateData0269

noncomputable def witness0269 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 178 else 179) else if t 2 = 1 then (if t 3 = 0 then 185 else if t 3 = 1 then 170 else 172) else (if t 3 = 0 then 1501 else if t 3 = 1 then 892 else 1496)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 183 else if t 3 = 1 then 156 else 158) else if t 2 = 1 then (if t 3 = 0 then 181 else if t 3 = 1 then 136 else 142) else (if t 3 = 0 then 199 else if t 3 = 1 then 140 else 144)) else (if t 2 = 0 then (if t 3 = 0 then 3951 else if t 3 = 1 then 3945 else 3946) else if t 2 = 1 then (if t 3 = 0 then 2778 else if t 3 = 1 then 2766 else 2769) else (if t 3 = 0 then 2781 else if t 3 = 1 then 2768 else 2770))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 174 else 176) else if t 2 = 1 then (if t 3 = 0 then 184 else if t 3 = 1 then 160 else 166) else (if t 3 = 0 then 1500 else if t 3 = 1 then 888 else 1494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 182 else if t 3 = 1 then 146 else 152) else if t 2 = 1 then (if t 3 = 0 then 180 else if t 3 = 1 then 117 else 128) else (if t 3 = 0 then 198 else if t 3 = 1 then 124 else 132)) else (if t 2 = 0 then (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 153) else if t 2 = 1 then (if t 3 = 0 then 188 else if t 3 = 1 then 119 else 129) else (if t 3 = 0 then 202 else if t 3 = 1 then 125 else 133))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 2115 else 2758) else if t 2 = 1 then (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 168) else (if t 3 = 0 then 3952 else if t 3 = 1 then 890 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1535) else if t 2 = 1 then (if t 3 = 0 then 192 else if t 3 = 1 then 121 else 130) else (if t 3 = 0 then 204 else if t 3 = 1 then 126 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 1547 else if t 3 = 1 then 1532 else 1536) else if t 2 = 1 then (if t 3 = 0 then 196 else if t 3 = 1 then 122 else 131) else (if t 3 = 0 then 206 else if t 3 = 1 then 127 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3714 else (if jt.2.val < 2 then 3745 else 3725)) else (if jt.2.val < 4 then 3744 else (if jt.2.val < 5 then 3746 else 3722))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3876 else (if jt.2.val < 2 then 3948 else 3897)) else (if jt.2.val < 4 then 3947 else (if jt.2.val < 5 then 3949 else 3867)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2004 else (if jt.2.val < 2 then 2006 else 2009)) else (if jt.2.val < 4 then 2005 else (if jt.2.val < 5 then 2008 else 2007))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3 else (if jt.2.val < 2 then 107 else 5)) else (if jt.2.val < 4 then 105 else (if jt.2.val < 5 then 106 else 0)))))

checked_coverage fastCoverage0269 pairing0269 template0269 witness0269

theorem coverage0269 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0269) (maskBits m))
    cores template0269 witness0269 := by
  rw [← coresFast_eq]
  exact fastCoverage0269

theorem coverageSize0269 : ∀ q : Pattern,
    (cores (witness0269 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0269 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0269
#print axioms coverageSize0269

noncomputable def pairing0270 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0270 : List (Fin 4935) := templateData0270

noncomputable def witness0270 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1568 else 1622) else if t 2 = 1 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1564 else 1616) else (if t 3 = 0 then 271 else if t 3 = 1 then 266 else 299)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1566 else 1619) else if t 2 = 1 then (if t 3 = 0 then 1570 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 855 else if t 3 = 1 then 1589 else 1611)) else (if t 2 = 0 then (if t 3 = 0 then 2485 else if t 3 = 1 then 2482 else 2501) else if t 2 = 1 then (if t 3 = 0 then 2855 else if t 3 = 1 then 3219 else 3227) else (if t 3 = 0 then 3954 else if t 3 = 1 then 3953 else 3959))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1567 else 1620) else if t 2 = 1 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1563 else 1614) else (if t 3 = 0 then 270 else if t 3 = 1 then 265 else 296)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1565 else 1617) else if t 2 = 1 then (if t 3 = 0 then 1569 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 854 else if t 3 = 1 then 1588 else 1604)) else (if t 2 = 0 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1582 else 1618) else if t 2 = 1 then (if t 3 = 0 then 1584 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 857 else if t 3 = 1 then 1591 else 1605))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 1133 else 3960) else if t 2 = 1 then (if t 3 = 0 then 660 else if t 3 = 1 then 655 else 686) else (if t 3 = 0 then 2777 else if t 3 = 1 then 2169 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 468 else if t 3 = 1 then 463 else 494) else if t 2 = 1 then (if t 3 = 0 then 1070 else if t 3 = 1 then 1592 else 1606) else (if t 3 = 0 then 1598 else if t 3 = 1 then 1596 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 473 else if t 3 = 1 then 471 else 495) else if t 2 = 1 then (if t 3 = 0 then 1073 else if t 3 = 1 then 1595 else 1607) else (if t 3 = 0 then 1601 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3870 else (if jt.2.val < 2 then 3957 else 3894)) else (if jt.2.val < 4 then 3955 else (if jt.2.val < 5 then 3956 else 3874))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3176 else (if jt.2.val < 2 then 3220 else 3179)) else (if jt.2.val < 4 then 3217 else (if jt.2.val < 5 then 3218 else 3171)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2000 else (if jt.2.val < 2 then 2035 else 2003)) else (if jt.2.val < 4 then 2031 else (if jt.2.val < 5 then 2032 else 1997))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1551 else (if jt.2.val < 2 then 1553 else 1556)) else (if jt.2.val < 4 then 1552 else (if jt.2.val < 5 then 1555 else 1554)))))

checked_coverage fastCoverage0270 pairing0270 template0270 witness0270

theorem coverage0270 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0270) (maskBits m))
    cores template0270 witness0270 := by
  rw [← coresFast_eq]
  exact fastCoverage0270

theorem coverageSize0270 : ∀ q : Pattern,
    (cores (witness0270 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0270 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0270
#print axioms coverageSize0270

noncomputable def pairing0271 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0271 : List (Fin 4935) := templateData0271

noncomputable def witness0271 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1675 else 1676) else if t 2 = 1 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1660 else 1661) else (if t 3 = 0 then 402 else if t 3 = 1 then 357 else 359)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1669 else 1670) else if t 2 = 1 then (if t 3 = 0 then 1678 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 864 else if t 3 = 1 then 1646 else 1650)) else (if t 2 = 0 then (if t 3 = 0 then 2577 else if t 3 = 1 then 2545 else 2547) else if t 2 = 1 then (if t 3 = 0 then 2860 else if t 3 = 1 then 3232 else 3235) else (if t 3 = 0 then 3967 else if t 3 = 1 then 3963 else 3965))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1671 else 1673) else if t 2 = 1 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1656 else 1658) else (if t 3 = 0 then 401 else if t 3 = 1 then 350 else 354)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1665 else 1667) else if t 2 = 1 then (if t 3 = 0 then 1677 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 863 else if t 3 = 1 then 1630 else 1638)) else (if t 2 = 0 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1666 else 1668) else if t 2 = 1 then (if t 3 = 0 then 1685 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 866 else if t 3 = 1 then 1631 else 1639))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3968 else if t 3 = 1 then 1110 else 3966) else if t 2 = 1 then (if t 3 = 0 then 785 else if t 3 = 1 then 734 else 738) else (if t 3 = 0 then 2801 else if t 3 = 1 then 2157 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 596 else if t 3 = 1 then 546 else 550) else if t 2 = 1 then (if t 3 = 0 then 1079 else if t 3 = 1 then 1632 else 1640) else (if t 3 = 0 then 1689 else if t 3 = 1 then 1634 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 599 else if t 3 = 1 then 547 else 551) else if t 2 = 1 then (if t 3 = 0 then 1082 else if t 3 = 1 then 1633 else 1641) else (if t 3 = 0 then 1691 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3806 else (if jt.2.val < 2 then 3962 else 3828)) else (if jt.2.val < 4 then 3961 else (if jt.2.val < 5 then 3964 else 3824))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3188 else (if jt.2.val < 2 then 3238 else 3190)) else (if jt.2.val < 4 then 3237 else (if jt.2.val < 5 then 3239 else 3185)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2007 else (if jt.2.val < 2 then 2041 else 2009)) else (if jt.2.val < 4 then 2040 else (if jt.2.val < 5 then 2042 else 2004))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1554 else (if jt.2.val < 2 then 1625 else 1556)) else (if jt.2.val < 4 then 1623 else (if jt.2.val < 5 then 1624 else 1551)))))

checked_coverage fastCoverage0271 pairing0271 template0271 witness0271

theorem coverage0271 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0271) (maskBits m))
    cores template0271 witness0271 := by
  rw [← coresFast_eq]
  exact fastCoverage0271

theorem coverageSize0271 : ∀ q : Pattern,
    (cores (witness0271 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0271 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0271
#print axioms coverageSize0271

noncomputable def pairing0272 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0272 : List (Fin 4935) := templateData0272

noncomputable def witness0272 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3988 else if t 3 = 1 then 3980 else 3935) else if t 2 = 1 then (if t 3 = 0 then 3984 else if t 3 = 1 then 3976 else 2740) else (if t 3 = 0 then 2751 else if t 3 = 1 then 2750 else 2985)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3986 else if t 3 = 1 then 3978 else 489) else if t 2 = 1 then (if t 3 = 0 then 3982 else if t 3 = 1 then 3974 else 488) else (if t 3 = 0 then 539 else if t 3 = 1 then 537 else 1114)) else (if t 2 = 0 then (if t 3 = 0 then 1175 else if t 3 = 1 then 1171 else 503) else if t 2 = 1 then (if t 3 = 0 then 1174 else if t 3 = 1 then 1170 else 502) else (if t 3 = 0 then 1544 else if t 3 = 1 then 568 else 1837))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3987 else if t 3 = 1 then 3979 else 390) else if t 2 = 1 then (if t 3 = 0 then 3983 else if t 3 = 1 then 3975 else 389) else (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 925)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3985 else if t 3 = 1 then 3977 else 2715) else if t 2 = 1 then (if t 3 = 0 then 3981 else if t 3 = 1 then 3973 else 4019) else (if t 3 = 0 then 3845 else if t 3 = 1 then 4015 else 4023)) else (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2723) else if t 2 = 1 then (if t 3 = 0 then 4002 else if t 3 = 1 then 4000 else 4021) else (if t 3 = 0 then 3849 else if t 3 = 1 then 4017 else 4025))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 1499) else if t 2 = 1 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 397) else (if t 3 = 0 then 262 else if t 3 = 1 then 261 else 927)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2719) else if t 2 = 1 then (if t 3 = 0 then 3995 else if t 3 = 1 then 3993 else 4020) else (if t 3 = 0 then 3847 else if t 3 = 1 then 4016 else 4024)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2841 else 2725) else if t 2 = 1 then (if t 3 = 0 then 4004 else if t 3 = 1 then 4003 else 4022) else (if t 3 = 0 then 3851 else if t 3 = 1 then 4018 else 4026))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3972 else (if jt.2.val < 2 then 3992 else 3994)) else (if jt.2.val < 4 then 3989 else (if jt.2.val < 5 then 3991 else 3990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3971 else (if jt.2.val < 2 then 3999 else 4001)) else (if jt.2.val < 4 then 3996 else (if jt.2.val < 5 then 3998 else 3997)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3970 else (if jt.2.val < 2 then 4013 else 4014)) else (if jt.2.val < 4 then 4010 else (if jt.2.val < 5 then 4012 else 4011))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3969 else (if jt.2.val < 2 then 4006 else 4009)) else (if jt.2.val < 4 then 4005 else (if jt.2.val < 5 then 4008 else 4007)))))

checked_coverage fastCoverage0272 pairing0272 template0272 witness0272

theorem coverage0272 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0272) (maskBits m))
    cores template0272 witness0272 := by
  rw [← coresFast_eq]
  exact fastCoverage0272

theorem coverageSize0272 : ∀ q : Pattern,
    (cores (witness0272 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0272 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0272
#print axioms coverageSize0272

noncomputable def pairing0273 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0273 : List (Fin 4935) := templateData0273

noncomputable def witness0273 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3913 else if t 3 = 1 then 3904 else 4036) else if t 2 = 1 then (if t 3 = 0 then 3909 else if t 3 = 1 then 3898 else 2737) else (if t 3 = 0 then 2981 else if t 3 = 1 then 2979 else 2738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3911 else if t 3 = 1 then 3902 else 475) else if t 2 = 1 then (if t 3 = 0 then 3907 else if t 3 = 1 then 3892 else 462) else (if t 3 = 0 then 1090 else if t 3 = 1 then 1069 else 467)) else (if t 2 = 0 then (if t 3 = 0 then 683 else if t 3 = 1 then 667 else 1138) else if t 2 = 1 then (if t 3 = 0 then 682 else if t 3 = 1 then 654 else 1132) else (if t 3 = 0 then 1826 else if t 3 = 1 then 659 else 1519))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3912 else if t 3 = 1 then 3903 else 376) else if t 2 = 1 then (if t 3 = 0 then 3908 else if t 3 = 1 then 3895 else 364) else (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 368)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3910 else if t 3 = 1 then 3899 else 2696) else if t 2 = 1 then (if t 3 = 0 then 3906 else if t 3 = 1 then 3873 else 3880) else (if t 3 = 0 then 4037 else if t 3 = 1 then 3884 else 3888)) else (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2879) else if t 2 = 1 then (if t 3 = 0 then 3915 else if t 3 = 1 then 3877 else 3882) else (if t 3 = 0 then 4039 else if t 3 = 1 then 3886 else 3890))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 1774) else if t 2 = 1 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 366) else (if t 3 = 0 then 1013 else if t 3 = 1 then 990 else 370)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2698) else if t 2 = 1 then (if t 3 = 0 then 3914 else if t 3 = 1 then 3875 else 3881) else (if t 3 = 0 then 4038 else if t 3 = 1 then 3885 else 3889)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2551 else 2881) else if t 2 = 1 then (if t 3 = 0 then 3916 else if t 3 = 1 then 3878 else 3883) else (if t 3 = 0 then 4040 else if t 3 = 1 then 3887 else 3891))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3870 else (if jt.2.val < 2 then 3872 else 3894)) else (if jt.2.val < 4 then 3871 else (if jt.2.val < 5 then 3893 else 3874))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3867 else (if jt.2.val < 2 then 3869 else 3897)) else (if jt.2.val < 4 then 3868 else (if jt.2.val < 5 then 3896 else 3876)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4029 else (if jt.2.val < 2 then 4031 else 4035)) else (if jt.2.val < 4 then 4030 else (if jt.2.val < 5 then 4034 else 4033))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 4007 else (if jt.2.val < 2 then 4032 else 4009)) else (if jt.2.val < 4 then 4027 else (if jt.2.val < 5 then 4028 else 3969)))))

checked_coverage fastCoverage0273 pairing0273 template0273 witness0273

theorem coverage0273 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0273) (maskBits m))
    cores template0273 witness0273 := by
  rw [← coresFast_eq]
  exact fastCoverage0273

theorem coverageSize0273 : ∀ q : Pattern,
    (cores (witness0273 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0273 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0273
#print axioms coverageSize0273

noncomputable def pairing0274 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0274 : List (Fin 4935) := templateData0274

noncomputable def witness0274 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2602 else 2906) else if t 2 = 1 then (if t 3 = 0 then 2598 else if t 3 = 1 then 2594 else 2648) else (if t 3 = 0 then 4044 else if t 3 = 1 then 3923 else 3927)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2600 else 2107) else if t 2 = 1 then (if t 3 = 0 then 2596 else if t 3 = 1 then 2592 else 2101) else (if t 3 = 0 then 536 else if t 3 = 1 then 534 else 589)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1415 else 1780) else if t 2 = 1 then (if t 3 = 0 then 1413 else if t 3 = 1 then 1411 else 1447) else (if t 3 = 0 then 1109 else if t 3 = 1 then 567 else 591))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2601 else 2227) else if t 2 = 1 then (if t 3 = 0 then 2597 else if t 3 = 1 then 2593 else 2221) else (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 295)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2599 else 2902) else if t 2 = 1 then (if t 3 = 0 then 2595 else if t 3 = 1 then 2591 else 2640) else (if t 3 = 0 then 2613 else if t 3 = 1 then 2611 else 2641)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2632 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2897 else if t 3 = 1 then 2629 else 2644) else (if t 3 = 0 then 2899 else if t 3 = 1 then 2634 else 2645))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 637 else 1147) else if t 2 = 1 then (if t 3 = 0 then 635 else if t 3 = 1 then 633 else 685) else (if t 3 = 0 then 1787 else if t 3 = 1 then 1463 else 1474)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2623 else 2904) else if t 2 = 1 then (if t 3 = 0 then 2622 else if t 3 = 1 then 2620 else 2642) else (if t 3 = 0 then 2626 else if t 3 = 1 then 2625 else 2643)) else (if t 2 = 0 then (if t 3 = 0 then 3926 else if t 3 = 1 then 2637 else 4045) else if t 2 = 1 then (if t 3 = 0 then 2900 else if t 3 = 1 then 2636 else 2646) else (if t 3 = 0 then 2901 else if t 3 = 1 then 2638 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3714 else (if jt.2.val < 2 then 3724 else 3725)) else (if jt.2.val < 4 then 3721 else (if jt.2.val < 5 then 3723 else 3722))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3171 else (if jt.2.val < 2 then 3178 else 3179)) else (if jt.2.val < 4 then 3175 else (if jt.2.val < 5 then 3177 else 3176)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4011 else (if jt.2.val < 2 then 4043 else 4014)) else (if jt.2.val < 4 then 4041 else (if jt.2.val < 5 then 4042 else 3970))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2890 else (if jt.2.val < 2 then 2892 else 2895)) else (if jt.2.val < 4 then 2891 else (if jt.2.val < 5 then 2894 else 2893)))))

checked_coverage fastCoverage0274 pairing0274 template0274 witness0274

theorem coverage0274 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0274) (maskBits m))
    cores template0274 witness0274 := by
  rw [← coresFast_eq]
  exact fastCoverage0274

theorem coverageSize0274 : ∀ q : Pattern,
    (cores (witness0274 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0274 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0274
#print axioms coverageSize0274

noncomputable def pairing0275 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0275 : List (Fin 4935) := templateData0275

noncomputable def witness0275 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2953 else 2706) else if t 2 = 1 then (if t 3 = 0 then 2960 else if t 3 = 1 then 2937 else 2939) else (if t 3 = 0 then 3860 else if t 3 = 1 then 4046 else 4047)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2951 else 2098) else if t 2 = 1 then (if t 3 = 0 then 2958 else if t 3 = 1 then 2931 else 2082) else (if t 3 = 0 then 1084 else if t 3 = 1 then 1046 else 1051)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1750 else 1359) else if t 2 = 1 then (if t 3 = 0 then 1756 else if t 3 = 1 then 1730 else 1733) else (if t 3 = 0 then 790 else if t 3 = 1 then 1049 else 1053))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2952 else 2218) else if t 2 = 1 then (if t 3 = 0 then 2959 else if t 3 = 1 then 2934 else 2206) else (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 974)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2947 else 2699) else if t 2 = 1 then (if t 3 = 0 then 2954 else if t 3 = 1 then 2913 else 2923) else (if t 3 = 0 then 2955 else if t 3 = 1 then 2915 else 2924)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2554 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2502 else if t 3 = 1 then 2919 else 2927) else (if t 3 = 0 then 2503 else if t 3 = 1 then 2920 else 2928))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1204 else 762) else if t 2 = 1 then (if t 3 = 0 then 1213 else if t 3 = 1 then 1180 else 1184) else (if t 3 = 0 then 1375 else if t 3 = 1 then 1796 else 1800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2949 else 2701) else if t 2 = 1 then (if t 3 = 0 then 2956 else if t 3 = 1 then 2917 else 2925) else (if t 3 = 0 then 2957 else if t 3 = 1 then 2918 else 2926)) else (if t 2 = 0 then (if t 3 = 0 then 4051 else if t 3 = 1 then 2556 else 3934) else if t 2 = 1 then (if t 3 = 0 then 2504 else if t 3 = 1 then 2921 else 2929) else (if t 3 = 0 then 2505 else if t 3 = 1 then 2922 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3774 else (if jt.2.val < 2 then 3776 else 3783)) else (if jt.2.val < 4 then 3775 else (if jt.2.val < 5 then 3782 else 3781))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3323 else (if jt.2.val < 2 then 3325 else 3328)) else (if jt.2.val < 4 then 3324 else (if jt.2.val < 5 then 3327 else 3326)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 4033 else (if jt.2.val < 2 then 4049 else 4035)) else (if jt.2.val < 4 then 4048 else (if jt.2.val < 5 then 4050 else 4029))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2893 else (if jt.2.val < 2 then 2943 else 2895)) else (if jt.2.val < 4 then 2941 else (if jt.2.val < 5 then 2942 else 2890)))))

checked_coverage fastCoverage0275 pairing0275 template0275 witness0275

theorem coverage0275 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0275) (maskBits m))
    cores template0275 witness0275 := by
  rw [← coresFast_eq]
  exact fastCoverage0275

theorem coverageSize0275 : ∀ q : Pattern,
    (cores (witness0275 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0275 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0275
#print axioms coverageSize0275

noncomputable def pairing0276 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0276 : List (Fin 4935) := templateData0276

noncomputable def witness0276 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 803 else 402) else if t 2 = 1 then (if t 3 = 0 then 809 else if t 3 = 1 then 801 else 400) else (if t 3 = 0 then 1471 else if t 3 = 1 then 269 else 1790)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 807 else if t 3 = 1 then 799 else 864) else if t 2 = 1 then (if t 3 = 0 then 805 else if t 3 = 1 then 797 else 862) else (if t 3 = 0 then 65 else if t 3 = 1 then 853 else 874)) else (if t 2 = 0 then (if t 3 = 0 then 4056 else if t 3 = 1 then 4054 else 3967) else if t 2 = 1 then (if t 3 = 0 then 2996 else if t 3 = 1 then 2993 else 3003) else (if t 3 = 0 then 2795 else if t 3 = 1 then 3002 else 3004))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 802 else 401) else if t 2 = 1 then (if t 3 = 0 then 808 else if t 3 = 1 then 800 else 399) else (if t 3 = 0 then 1470 else if t 3 = 1 then 268 else 1788)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 806 else if t 3 = 1 then 798 else 863) else if t 2 = 1 then (if t 3 = 0 then 804 else if t 3 = 1 then 796 else 861) else (if t 3 = 0 then 64 else if t 3 = 1 then 852 else 870)) else (if t 2 = 0 then (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 866) else if t 2 = 1 then (if t 3 = 0 then 821 else if t 3 = 1 then 816 else 865) else (if t 3 = 0 then 70 else if t 3 = 1 then 856 else 871))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 2145 else 2801) else if t 2 = 1 then (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 405) else (if t 3 = 0 then 3942 else if t 3 = 1 then 278 else 4057)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1689) else if t 2 = 1 then (if t 3 = 0 then 834 else if t 3 = 1 then 829 else 867) else (if t 3 = 0 then 74 else if t 3 = 1 then 858 else 872)) else (if t 2 = 0 then (if t 3 = 0 then 1818 else if t 3 = 1 then 1817 else 1691) else if t 2 = 1 then (if t 3 = 0 then 840 else if t 3 = 1 then 838 else 869) else (if t 3 = 0 then 77 else if t 3 = 1 then 860 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3774 else (if jt.2.val < 2 then 3791 else 3783)) else (if jt.2.val < 4 then 3789 else (if jt.2.val < 5 then 3790 else 3781))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3997 else (if jt.2.val < 2 then 4055 else 4001)) else (if jt.2.val < 4 then 4052 else (if jt.2.val < 5 then 4053 else 3971)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2288 else (if jt.2.val < 2 then 2293 else 2294)) else (if jt.2.val < 4 then 2290 else (if jt.2.val < 5 then 2292 else 2291))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 792 else (if jt.2.val < 2 then 843 else 846)) else (if jt.2.val < 4 then 842 else (if jt.2.val < 5 then 845 else 844)))))

checked_coverage fastCoverage0276 pairing0276 template0276 witness0276

theorem coverage0276 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0276) (maskBits m))
    cores template0276 witness0276 := by
  rw [← coresFast_eq]
  exact fastCoverage0276

theorem coverageSize0276 : ∀ q : Pattern,
    (cores (witness0276 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0276 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0276
#print axioms coverageSize0276

noncomputable def pairing0277 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 2) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0277 : List (Fin 4935) := templateData0277

noncomputable def witness0277 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 178 else 896) else if t 2 = 1 then (if t 3 = 0 then 185 else if t 3 = 1 then 170 else 892) else (if t 3 = 0 then 1807 else if t 3 = 1 then 172 else 1496)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 183 else if t 3 = 1 then 156 else 157) else if t 2 = 1 then (if t 3 = 0 then 181 else if t 3 = 1 then 136 else 140) else (if t 3 = 0 then 898 else if t 3 = 1 then 142 else 144)) else (if t 2 = 0 then (if t 3 = 0 then 3951 else if t 3 = 1 then 3945 else 4058) else if t 2 = 1 then (if t 3 = 0 then 2778 else if t 3 = 1 then 2766 else 2768) else (if t 3 = 0 then 2989 else if t 3 = 1 then 2769 else 2770))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 174 else 894) else if t 2 = 1 then (if t 3 = 0 then 184 else if t 3 = 1 then 160 else 888) else (if t 3 = 0 then 1806 else if t 3 = 1 then 166 else 1494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 182 else if t 3 = 1 then 146 else 150) else if t 2 = 1 then (if t 3 = 0 then 180 else if t 3 = 1 then 117 else 124) else (if t 3 = 0 then 897 else if t 3 = 1 then 128 else 132)) else (if t 2 = 0 then (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 151) else if t 2 = 1 then (if t 3 = 0 then 188 else if t 3 = 1 then 119 else 125) else (if t 3 = 0 then 901 else if t 3 = 1 then 129 else 133))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 2115 else 2984) else if t 2 = 1 then (if t 3 = 0 then 194 else if t 3 = 1 then 162 else 890) else (if t 3 = 0 then 4059 else if t 3 = 1 then 168 else 3950)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1833) else if t 2 = 1 then (if t 3 = 0 then 192 else if t 3 = 1 then 121 else 126) else (if t 3 = 0 then 903 else if t 3 = 1 then 130 else 134)) else (if t 2 = 0 then (if t 3 = 0 then 1547 else if t 3 = 1 then 1532 else 1834) else if t 2 = 1 then (if t 3 = 0 then 196 else if t 3 = 1 then 122 else 127) else (if t 3 = 0 then 905 else if t 3 = 1 then 131 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3714 else (if jt.2.val < 2 then 3745 else 3725)) else (if jt.2.val < 4 then 3744 else (if jt.2.val < 5 then 3746 else 3722))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3876 else (if jt.2.val < 2 then 3948 else 3897)) else (if jt.2.val < 4 then 3947 else (if jt.2.val < 5 then 3949 else 3867)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2295 else (if jt.2.val < 2 then 2297 else 2300)) else (if jt.2.val < 4 then 2296 else (if jt.2.val < 5 then 2299 else 2298))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 844 else (if jt.2.val < 2 then 884 else 846)) else (if jt.2.val < 4 then 879 else (if jt.2.val < 5 then 880 else 792)))))

checked_coverage fastCoverage0277 pairing0277 template0277 witness0277

theorem coverage0277 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0277) (maskBits m))
    cores template0277 witness0277 := by
  rw [← coresFast_eq]
  exact fastCoverage0277

theorem coverageSize0277 : ∀ q : Pattern,
    (cores (witness0277 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0277 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0277
#print axioms coverageSize0277

noncomputable def pairing0278 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0278 : List (Fin 4935) := templateData0278

noncomputable def witness0278 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1572 else 1856) else if t 2 = 1 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1564 else 1616) else (if t 3 = 0 then 918 else if t 3 = 1 then 266 else 299)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1570 else 1853) else if t 2 = 1 then (if t 3 = 0 then 1566 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 62 else if t 3 = 1 then 1589 else 1611)) else (if t 2 = 0 then (if t 3 = 0 then 2485 else if t 3 = 1 then 2855 else 2868) else if t 2 = 1 then (if t 3 = 0 then 2482 else if t 3 = 1 then 3219 else 3227) else (if t 3 = 0 then 4060 else if t 3 = 1 then 3953 else 3959))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1571 else 1854) else if t 2 = 1 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1563 else 1614) else (if t 3 = 0 then 917 else if t 3 = 1 then 265 else 296)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1569 else 1851) else if t 2 = 1 then (if t 3 = 0 then 1565 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 61 else if t 3 = 1 then 1588 else 1604)) else (if t 2 = 0 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1584 else 1852) else if t 2 = 1 then (if t 3 = 0 then 1582 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 69 else if t 3 = 1 then 1591 else 1605))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3958 else if t 3 = 1 then 660 else 4061) else if t 2 = 1 then (if t 3 = 0 then 1133 else if t 3 = 1 then 655 else 686) else (if t 3 = 0 then 2988 else if t 3 = 1 then 2169 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 468 else if t 3 = 1 then 1070 else 1092) else if t 2 = 1 then (if t 3 = 0 then 463 else if t 3 = 1 then 1592 else 1606) else (if t 3 = 0 then 1848 else if t 3 = 1 then 1596 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 473 else if t 3 = 1 then 1073 else 1093) else if t 2 = 1 then (if t 3 = 0 then 471 else if t 3 = 1 then 1595 else 1607) else (if t 3 = 0 then 1850 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3870 else (if jt.2.val < 2 then 3957 else 3894)) else (if jt.2.val < 4 then 3955 else (if jt.2.val < 5 then 3956 else 3874))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3176 else (if jt.2.val < 2 then 3220 else 3179)) else (if jt.2.val < 4 then 3217 else (if jt.2.val < 5 then 3218 else 3171)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2291 else (if jt.2.val < 2 then 2315 else 2294)) else (if jt.2.val < 4 then 2313 else (if jt.2.val < 5 then 2314 else 2288))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1839 else (if jt.2.val < 2 then 1841 else 1846)) else (if jt.2.val < 4 then 1840 else (if jt.2.val < 5 then 1845 else 1844)))))

checked_coverage fastCoverage0278 pairing0278 template0278 witness0278

theorem coverage0278 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0278) (maskBits m))
    cores template0278 witness0278 := by
  rw [← coresFast_eq]
  exact fastCoverage0278

theorem coverageSize0278 : ∀ q : Pattern,
    (cores (witness0278 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0278 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0278
#print axioms coverageSize0278

noncomputable def pairing0279 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 2 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0279 : List (Fin 4935) := templateData0279

noncomputable def witness0279 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1904 else 1676) else if t 2 = 1 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1891 else 1892) else (if t 3 = 0 then 104 else if t 3 = 1 then 978 else 980)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1901 else 1670) else if t 2 = 1 then (if t 3 = 0 then 1907 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 94 else if t 3 = 1 then 1877 else 1881)) else (if t 2 = 0 then (if t 3 = 0 then 2884 else if t 3 = 1 then 2546 else 2547) else if t 2 = 1 then (if t 3 = 0 then 2500 else if t 3 = 1 then 3348 else 3351) else (if t 3 = 0 then 3943 else if t 3 = 1 then 4064 else 4066))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1902 else 1673) else if t 2 = 1 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1887 else 1889) else (if t 3 = 0 then 102 else if t 3 = 1 then 971 else 975)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1899 else 1667) else if t 2 = 1 then (if t 3 = 0 then 1905 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 90 else if t 3 = 1 then 1861 else 1869)) else (if t 2 = 0 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1900 else 1668) else if t 2 = 1 then (if t 3 = 0 then 1906 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 91 else if t 3 = 1 then 1862 else 1870))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 4067 else if t 3 = 1 then 572 else 3966) else if t 2 = 1 then (if t 3 = 0 then 504 else if t 3 = 1 then 1181 else 1185) else (if t 3 = 0 then 2744 else if t 3 = 1 then 2136 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1115 else if t 3 = 1 then 548 else 550) else if t 2 = 1 then (if t 3 = 0 then 492 else if t 3 = 1 then 1863 else 1871) else (if t 3 = 0 then 1521 else if t 3 = 1 then 1865 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 1118 else if t 3 = 1 then 549 else 551) else if t 2 = 1 then (if t 3 = 0 then 493 else if t 3 = 1 then 1864 else 1872) else (if t 3 = 0 then 1522 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3972 else (if jt.2.val < 2 then 4063 else 3994)) else (if jt.2.val < 4 then 4062 else (if jt.2.val < 5 then 4065 else 3990))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3326 else (if jt.2.val < 2 then 3354 else 3328)) else (if jt.2.val < 4 then 3353 else (if jt.2.val < 5 then 3355 else 3323)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2298 else (if jt.2.val < 2 then 2320 else 2300)) else (if jt.2.val < 4 then 2319 else (if jt.2.val < 5 then 2321 else 2295))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1844 else (if jt.2.val < 2 then 1895 else 1846)) else (if jt.2.val < 4 then 1893 else (if jt.2.val < 5 then 1894 else 1839)))))

checked_coverage fastCoverage0279 pairing0279 template0279 witness0279

theorem coverage0279 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0279) (maskBits m))
    cores template0279 witness0279 := by
  rw [← coresFast_eq]
  exact fastCoverage0279

theorem coverageSize0279 : ∀ q : Pattern,
    (cores (witness0279 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0279 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0279
#print axioms coverageSize0279

end Crown.CertificateData
