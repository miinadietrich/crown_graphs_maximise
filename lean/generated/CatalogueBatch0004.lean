import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0003

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0120 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0120 : List (Fin 4935) := templateData0120

noncomputable def witness0120 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2446 else 2506) else if t 2 = 1 then (if t 3 = 0 then 2450 else if t 3 = 1 then 2442 else 2500) else (if t 3 = 0 then 2485 else if t 3 = 1 then 2482 else 2501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2444 else 1756) else if t 2 = 1 then (if t 3 = 0 then 2448 else if t 3 = 1 then 2440 else 1753) else (if t 3 = 0 then 1416 else if t 3 = 1 then 1412 else 1450)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 341 else 406) else if t 2 = 1 then (if t 3 = 0 then 343 else if t 3 = 1 then 339 else 394) else (if t 3 = 0 then 374 else if t 3 = 1 then 372 else 396))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2445 else 1909) else if t 2 = 1 then (if t 3 = 0 then 2449 else if t 3 = 1 then 2441 else 1906) else (if t 3 = 0 then 1586 else if t 3 = 1 then 1582 else 1618)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2443 else 2502) else if t 2 = 1 then (if t 3 = 0 then 2447 else if t 3 = 1 then 2439 else 2492) else (if t 3 = 0 then 2484 else if t 3 = 1 then 2481 else 2496)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2504) else if t 2 = 1 then (if t 3 = 0 then 2471 else if t 3 = 1 then 2468 else 2494) else (if t 3 = 0 then 2489 else if t 3 = 1 then 2488 else 2498))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 33 else 103) else if t 2 = 1 then (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 91) else (if t 3 = 0 then 71 else if t 3 = 1 then 69 else 93)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2503) else if t 2 = 1 then (if t 3 = 0 then 2462 else if t 3 = 1 then 2459 else 2493) else (if t 3 = 0 then 2487 else if t 3 = 1 then 2486 else 2497)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2474 else 2505) else if t 2 = 1 then (if t 3 = 0 then 2475 else if t 3 = 1 then 2473 else 2495) else (if t 3 = 0 then 2491 else if t 3 = 1 then 2490 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2438 else (if jt.2.val < 2 then 2458 else 2460)) else (if jt.2.val < 4 then 2455 else (if jt.2.val < 5 then 2457 else 2456))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2437 else (if jt.2.val < 2 then 2467 else 2469)) else (if jt.2.val < 4 then 2464 else (if jt.2.val < 5 then 2466 else 2465)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2436 else (if jt.2.val < 2 then 2480 else 2483)) else (if jt.2.val < 4 then 2477 else (if jt.2.val < 5 then 2479 else 2478))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2430 else (if jt.2.val < 2 then 2432 else 2435)) else (if jt.2.val < 4 then 2431 else (if jt.2.val < 5 then 2434 else 2433)))))

checked_coverage fastCoverage0120 pairing0120 template0120 witness0120

theorem coverage0120 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0120) (maskBits m))
    cores template0120 witness0120 := by
  rw [← coresFast_eq]
  exact fastCoverage0120

theorem coverageSize0120 : ∀ q : Pattern,
    (cores (witness0120 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0120 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0120
#print axioms coverageSize0120

noncomputable def pairing0121 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0121 : List (Fin 4935) := templateData0121

noncomputable def witness0121 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2560 else 2561) else if t 2 = 1 then (if t 3 = 0 then 2565 else if t 3 = 1 then 2544 else 2546) else (if t 3 = 0 then 2577 else if t 3 = 1 then 2545 else 2547)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2558 else 1750) else if t 2 = 1 then (if t 3 = 0 then 2563 else if t 3 = 1 then 2538 else 1747) else (if t 3 = 0 then 1372 else if t 3 = 1 then 1350 else 1353)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 277 else 279) else if t 2 = 1 then (if t 3 = 0 then 291 else if t 3 = 1 then 251 else 256) else (if t 3 = 0 then 305 else if t 3 = 1 then 254 else 258))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2559 else 1903) else if t 2 = 1 then (if t 3 = 0 then 2564 else if t 3 = 1 then 2541 else 1900) else (if t 3 = 0 then 1687 else if t 3 = 1 then 1666 else 1668)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2548 else 2554) else if t 2 = 1 then (if t 3 = 0 then 2562 else if t 3 = 1 then 2519 else 2530) else (if t 3 = 0 then 2576 else if t 3 = 1 then 2526 else 2534)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2556) else if t 2 = 1 then (if t 3 = 0 then 2572 else if t 3 = 1 then 2523 else 2532) else (if t 3 = 0 then 2579 else if t 3 = 1 then 2528 else 2536))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 175 else 177) else if t 2 = 1 then (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 153) else (if t 3 = 0 then 203 else if t 3 = 1 then 151 else 155)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2555) else if t 2 = 1 then (if t 3 = 0 then 2570 else if t 3 = 1 then 2521 else 2531) else (if t 3 = 0 then 2578 else if t 3 = 1 then 2527 else 2535)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2551 else 2557) else if t 2 = 1 then (if t 3 = 0 then 2574 else if t 3 = 1 then 2524 else 2533) else (if t 3 = 0 then 2580 else if t 3 = 1 then 2529 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2516 else (if jt.2.val < 2 then 2518 else 2540)) else (if jt.2.val < 4 then 2517 else (if jt.2.val < 5 then 2539 else 2520))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2513 else (if jt.2.val < 2 then 2515 else 2543)) else (if jt.2.val < 4 then 2514 else (if jt.2.val < 5 then 2542 else 2522)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2510 else (if jt.2.val < 2 then 2512 else 2553)) else (if jt.2.val < 4 then 2511 else (if jt.2.val < 5 then 2552 else 2525))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2433 else (if jt.2.val < 2 then 2509 else 2435)) else (if jt.2.val < 4 then 2507 else (if jt.2.val < 5 then 2508 else 2430)))))

checked_coverage fastCoverage0121 pairing0121 template0121 witness0121

theorem coverage0121 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0121) (maskBits m))
    cores template0121 witness0121 := by
  rw [← coresFast_eq]
  exact fastCoverage0121

theorem coverageSize0121 : ∀ q : Pattern,
    (cores (witness0121 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0121 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0121
#print axioms coverageSize0121

noncomputable def pairing0122 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0122 : List (Fin 4935) := templateData0122

noncomputable def witness0122 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2598 else 2654) else if t 2 = 1 then (if t 3 = 0 then 2602 else if t 3 = 1 then 2594 else 2648) else (if t 3 = 0 then 2633 else if t 3 = 1 then 2630 else 2649)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2596 else 2104) else if t 2 = 1 then (if t 3 = 0 then 2600 else if t 3 = 1 then 2592 else 2101) else (if t 3 = 0 then 1415 else if t 3 = 1 then 1411 else 1447)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 141 else 205) else if t 2 = 1 then (if t 3 = 0 then 143 else if t 3 = 1 then 139 else 193) else (if t 3 = 0 then 173 else if t 3 = 1 then 171 else 195))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2597 else 2224) else if t 2 = 1 then (if t 3 = 0 then 2601 else if t 3 = 1 then 2593 else 2221) else (if t 3 = 0 then 1585 else if t 3 = 1 then 1581 else 1615)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2595 else 2650) else if t 2 = 1 then (if t 3 = 0 then 2599 else if t 3 = 1 then 2591 else 2640) else (if t 3 = 0 then 2632 else if t 3 = 1 then 2629 else 2644)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2622 else 2652) else if t 2 = 1 then (if t 3 = 0 then 2623 else if t 3 = 1 then 2620 else 2642) else (if t 3 = 0 then 2637 else if t 3 = 1 then 2636 else 2646))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 241 else 307) else if t 2 = 1 then (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 295) else (if t 3 = 0 then 275 else if t 3 = 1 then 273 else 297)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2651) else if t 2 = 1 then (if t 3 = 0 then 2614 else if t 3 = 1 then 2611 else 2641) else (if t 3 = 0 then 2635 else if t 3 = 1 then 2634 else 2645)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2626 else 2653) else if t 2 = 1 then (if t 3 = 0 then 2627 else if t 3 = 1 then 2625 else 2643) else (if t 3 = 0 then 2639 else if t 3 = 1 then 2638 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2590 else (if jt.2.val < 2 then 2610 else 2612)) else (if jt.2.val < 4 then 2607 else (if jt.2.val < 5 then 2609 else 2608))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2589 else (if jt.2.val < 2 then 2619 else 2621)) else (if jt.2.val < 4 then 2616 else (if jt.2.val < 5 then 2618 else 2617)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2478 else (if jt.2.val < 2 then 2631 else 2483)) else (if jt.2.val < 4 then 2587 else (if jt.2.val < 5 then 2588 else 2436))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2581 else (if jt.2.val < 2 then 2583 else 2586)) else (if jt.2.val < 4 then 2582 else (if jt.2.val < 5 then 2585 else 2584)))))

checked_coverage fastCoverage0122 pairing0122 template0122 witness0122

theorem coverage0122 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0122) (maskBits m))
    cores template0122 witness0122 := by
  rw [← coresFast_eq]
  exact fastCoverage0122

theorem coverageSize0122 : ∀ q : Pattern,
    (cores (witness0122 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0122 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0122
#print axioms coverageSize0122

noncomputable def pairing0123 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0123 : List (Fin 4935) := templateData0123

noncomputable def witness0123 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2705 else 2706) else if t 2 = 1 then (if t 3 = 0 then 2710 else if t 3 = 1 then 2688 else 2690) else (if t 3 = 0 then 2722 else if t 3 = 1 then 2689 else 2691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2703 else 2098) else if t 2 = 1 then (if t 3 = 0 then 2708 else if t 3 = 1 then 2682 else 2090) else (if t 3 = 0 then 1371 else if t 3 = 1 then 1339 else 1342)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 73 else 75) else if t 2 = 1 then (if t 3 = 0 then 87 else if t 3 = 1 then 43 else 48) else (if t 3 = 0 then 101 else if t 3 = 1 then 46 else 50))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2704 else 2218) else if t 2 = 1 then (if t 3 = 0 then 2709 else if t 3 = 1 then 2685 else 2212) else (if t 3 = 0 then 1686 else if t 3 = 1 then 1657 else 1659)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2695 else 2699) else if t 2 = 1 then (if t 3 = 0 then 2707 else if t 3 = 1 then 2664 else 2674) else (if t 3 = 0 then 2721 else if t 3 = 1 then 2670 else 2678)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2697 else 2701) else if t 2 = 1 then (if t 3 = 0 then 2717 else if t 3 = 1 then 2668 else 2676) else (if t 3 = 0 then 2724 else if t 3 = 1 then 2672 else 2680))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 376 else 378) else if t 2 = 1 then (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 353) else (if t 3 = 0 then 404 else if t 3 = 1 then 351 else 355)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2700) else if t 2 = 1 then (if t 3 = 0 then 2715 else if t 3 = 1 then 2666 else 2675) else (if t 3 = 0 then 2723 else if t 3 = 1 then 2671 else 2679)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2698 else 2702) else if t 2 = 1 then (if t 3 = 0 then 2719 else if t 3 = 1 then 2669 else 2677) else (if t 3 = 0 then 2725 else if t 3 = 1 then 2673 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2661 else (if jt.2.val < 2 then 2663 else 2684)) else (if jt.2.val < 4 then 2662 else (if jt.2.val < 5 then 2683 else 2665))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2658 else (if jt.2.val < 2 then 2660 else 2687)) else (if jt.2.val < 4 then 2659 else (if jt.2.val < 5 then 2686 else 2667)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2525 else (if jt.2.val < 2 then 2693 else 2553)) else (if jt.2.val < 4 then 2692 else (if jt.2.val < 5 then 2694 else 2510))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2584 else (if jt.2.val < 2 then 2657 else 2586)) else (if jt.2.val < 4 then 2655 else (if jt.2.val < 5 then 2656 else 2581)))))

checked_coverage fastCoverage0123 pairing0123 template0123 witness0123

theorem coverage0123 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0123) (maskBits m))
    cores template0123 witness0123 := by
  rw [← coresFast_eq]
  exact fastCoverage0123

theorem coverageSize0123 : ∀ q : Pattern,
    (cores (witness0123 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0123 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0123
#print axioms coverageSize0123

noncomputable def pairing0124 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0124 : List (Fin 4935) := templateData0124

noncomputable def witness0124 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 424 else 506) else if t 2 = 1 then (if t 3 = 0 then 428 else if t 3 = 1 then 420 else 496) else (if t 3 = 0 then 469 else if t 3 = 1 then 464 else 497)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 430 else if t 3 = 1 then 422 else 502) else if t 2 = 1 then (if t 3 = 0 then 426 else if t 3 = 1 then 418 else 488) else (if t 3 = 0 then 467 else if t 3 = 1 then 462 else 490)) else (if t 2 = 0 then (if t 3 = 0 then 2732 else if t 3 = 1 then 2730 else 2743) else if t 2 = 1 then (if t 3 = 0 then 2731 else if t 3 = 1 then 2728 else 2740) else (if t 3 = 0 then 2738 else if t 3 = 1 then 2737 else 2741))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 423 else 504) else if t 2 = 1 then (if t 3 = 0 then 427 else if t 3 = 1 then 419 else 492) else (if t 3 = 0 then 468 else if t 3 = 1 then 463 else 494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 429 else if t 3 = 1 then 421 else 498) else if t 2 = 1 then (if t 3 = 0 then 425 else if t 3 = 1 then 417 else 480) else (if t 3 = 0 then 466 else if t 3 = 1 then 461 else 484)) else (if t 2 = 0 then (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 499) else if t 2 = 1 then (if t 3 = 0 then 440 else if t 3 = 1 then 436 else 481) else (if t 3 = 0 then 472 else if t 3 = 1 then 470 else 485))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 2124 else 2744) else if t 2 = 1 then (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1521) else (if t 3 = 0 then 2739 else if t 3 = 1 then 1848 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 500) else if t 2 = 1 then (if t 3 = 0 then 449 else if t 3 = 1 then 444 else 482) else (if t 3 = 0 then 476 else if t 3 = 1 then 474 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 456 else if t 3 = 1 then 454 else 501) else if t 2 = 1 then (if t 3 = 0 then 455 else if t 3 = 1 then 453 else 483) else (if t 3 = 0 then 479 else if t 3 = 1 then 478 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2661 else (if jt.2.val < 2 then 2735 else 2684)) else (if jt.2.val < 4 then 2733 else (if jt.2.val < 5 then 2734 else 2665))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2465 else (if jt.2.val < 2 then 2729 else 2469)) else (if jt.2.val < 4 then 2726 else (if jt.2.val < 5 then 2727 else 2437)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 416 else (if jt.2.val < 2 then 460 else 465)) else (if jt.2.val < 4 then 457 else (if jt.2.val < 5 then 459 else 458))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 408 else (if jt.2.val < 2 then 410 else 413)) else (if jt.2.val < 4 then 409 else (if jt.2.val < 5 then 412 else 411)))))

checked_coverage fastCoverage0124 pairing0124 template0124 witness0124

theorem coverage0124 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0124) (maskBits m))
    cores template0124 witness0124 := by
  rw [← coresFast_eq]
  exact fastCoverage0124

theorem coverageSize0124 : ∀ q : Pattern,
    (cores (witness0124 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0124 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0124
#print axioms coverageSize0124

noncomputable def pairing0125 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 5 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0125 : List (Fin 4935) := templateData0125

noncomputable def witness0125 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 574 else 575) else if t 2 = 1 then (if t 3 = 0 then 579 else if t 3 = 1 then 552 else 554) else (if t 3 = 0 then 597 else if t 3 = 1 then 553 else 555)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 581 else if t 3 = 1 then 566 else 568) else if t 2 = 1 then (if t 3 = 0 then 577 else if t 3 = 1 then 532 else 537) else (if t 3 = 0 then 595 else if t 3 = 1 then 535 else 539)) else (if t 2 = 0 then (if t 3 = 0 then 2760 else if t 3 = 1 then 2756 else 2757) else if t 2 = 1 then (if t 3 = 0 then 2759 else if t 3 = 1 then 2747 else 2750) else (if t 3 = 0 then 2762 else if t 3 = 1 then 2749 else 2751))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 570 else 572) else if t 2 = 1 then (if t 3 = 0 then 578 else if t 3 = 1 then 544 else 548) else (if t 3 = 0 then 596 else if t 3 = 1 then 546 else 550)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 580 else if t 3 = 1 then 556 else 562) else if t 2 = 1 then (if t 3 = 0 then 576 else if t 3 = 1 then 515 else 524) else (if t 3 = 0 then 594 else if t 3 = 1 then 520 else 528)) else (if t 2 = 0 then (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 563) else if t 2 = 1 then (if t 3 = 0 then 584 else if t 3 = 1 then 516 else 525) else (if t 3 = 0 then 598 else if t 3 = 1 then 521 else 529))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 2115 else 2758) else if t 2 = 1 then (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1535) else (if t 3 = 0 then 2763 else if t 3 = 1 then 1833 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 564) else if t 2 = 1 then (if t 3 = 0 then 588 else if t 3 = 1 then 517 else 526) else (if t 3 = 0 then 600 else if t 3 = 1 then 522 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 593 else if t 3 = 1 then 559 else 565) else if t 2 = 1 then (if t 3 = 0 then 592 else if t 3 = 1 then 518 else 527) else (if t 3 = 0 then 602 else if t 3 = 1 then 523 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2590 else (if jt.2.val < 2 then 2746 else 2612)) else (if jt.2.val < 4 then 2745 else (if jt.2.val < 5 then 2748 else 2608))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2522 else (if jt.2.val < 2 then 2753 else 2543)) else (if jt.2.val < 4 then 2752 else (if jt.2.val < 5 then 2754 else 2513)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 510 else (if jt.2.val < 2 then 512 else 561)) else (if jt.2.val < 4 then 511 else (if jt.2.val < 5 then 560 else 519))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 411 else (if jt.2.val < 2 then 509 else 413)) else (if jt.2.val < 4 then 507 else (if jt.2.val < 5 then 508 else 408)))))

checked_coverage fastCoverage0125 pairing0125 template0125 witness0125

theorem coverage0125 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0125) (maskBits m))
    cores template0125 witness0125 := by
  rw [← coresFast_eq]
  exact fastCoverage0125

theorem coverageSize0125 : ∀ q : Pattern,
    (cores (witness0125 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0125 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0125
#print axioms coverageSize0125

noncomputable def pairing0126 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0126 : List (Fin 4935) := templateData0126

noncomputable def witness0126 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 620 else 698) else if t 2 = 1 then (if t 3 = 0 then 624 else if t 3 = 1 then 616 else 688) else (if t 3 = 0 then 661 else if t 3 = 1 then 656 else 689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 626 else if t 3 = 1 then 618 else 694) else if t 2 = 1 then (if t 3 = 0 then 622 else if t 3 = 1 then 614 else 680) else (if t 3 = 0 then 659 else if t 3 = 1 then 654 else 682)) else (if t 2 = 0 then (if t 3 = 0 then 2770 else if t 3 = 1 then 2768 else 2781) else if t 2 = 1 then (if t 3 = 0 then 2769 else if t 3 = 1 then 2766 else 2778) else (if t 3 = 0 then 2776 else if t 3 = 1 then 2775 else 2779))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 619 else 696) else if t 2 = 1 then (if t 3 = 0 then 623 else if t 3 = 1 then 615 else 684) else (if t 3 = 0 then 660 else if t 3 = 1 then 655 else 686)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 625 else if t 3 = 1 then 617 else 690) else if t 2 = 1 then (if t 3 = 0 then 621 else if t 3 = 1 then 613 else 672) else (if t 3 = 0 then 658 else if t 3 = 1 then 653 else 676)) else (if t 2 = 0 then (if t 3 = 0 then 638 else if t 3 = 1 then 634 else 691) else if t 2 = 1 then (if t 3 = 0 then 636 else if t 3 = 1 then 632 else 673) else (if t 3 = 0 then 664 else if t 3 = 1 then 662 else 677))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1785 else 2782) else if t 2 = 1 then (if t 3 = 0 then 1461 else if t 3 = 1 then 1458 else 1473) else (if t 3 = 0 then 2777 else if t 3 = 1 then 2169 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 647 else if t 3 = 1 then 643 else 692) else if t 2 = 1 then (if t 3 = 0 then 645 else if t 3 = 1 then 640 else 674) else (if t 3 = 0 then 668 else if t 3 = 1 then 666 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 652 else if t 3 = 1 then 650 else 693) else if t 2 = 1 then (if t 3 = 0 then 651 else if t 3 = 1 then 649 else 675) else (if t 3 = 0 then 671 else if t 3 = 1 then 670 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2516 else (if jt.2.val < 2 then 2773 else 2540)) else (if jt.2.val < 4 then 2771 else (if jt.2.val < 5 then 2772 else 2520))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2617 else (if jt.2.val < 2 then 2767 else 2621)) else (if jt.2.val < 4 then 2764 else (if jt.2.val < 5 then 2765 else 2589)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 458 else (if jt.2.val < 2 then 657 else 465)) else (if jt.2.val < 4 then 609 else (if jt.2.val < 5 then 610 else 416))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 603 else (if jt.2.val < 2 then 605 else 608)) else (if jt.2.val < 4 then 604 else (if jt.2.val < 5 then 607 else 606)))))

checked_coverage fastCoverage0126 pairing0126 template0126 witness0126

theorem coverage0126 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0126) (maskBits m))
    cores template0126 witness0126 := by
  rw [← coresFast_eq]
  exact fastCoverage0126

theorem coverageSize0126 : ∀ q : Pattern,
    (cores (witness0126 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0126 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0126
#print axioms coverageSize0126

noncomputable def pairing0127 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0127 : List (Fin 4935) := templateData0127

noncomputable def witness0127 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 763 else 764) else if t 2 = 1 then (if t 3 = 0 then 768 else if t 3 = 1 then 740 else 742) else (if t 3 = 0 then 786 else if t 3 = 1 then 741 else 743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 770 else if t 3 = 1 then 755 else 757) else if t 2 = 1 then (if t 3 = 0 then 766 else if t 3 = 1 then 720 else 725) else (if t 3 = 0 then 784 else if t 3 = 1 then 723 else 727)) else (if t 2 = 0 then (if t 3 = 0 then 2798 else if t 3 = 1 then 2794 else 2795) else if t 2 = 1 then (if t 3 = 0 then 2797 else if t 3 = 1 then 2785 else 2788) else (if t 3 = 0 then 2800 else if t 3 = 1 then 2787 else 2789))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 759 else 761) else if t 2 = 1 then (if t 3 = 0 then 767 else if t 3 = 1 then 732 else 736) else (if t 3 = 0 then 785 else if t 3 = 1 then 734 else 738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 769 else if t 3 = 1 then 747 else 751) else if t 2 = 1 then (if t 3 = 0 then 765 else if t 3 = 1 then 704 else 712) else (if t 3 = 0 then 783 else if t 3 = 1 then 708 else 716)) else (if t 2 = 0 then (if t 3 = 0 then 775 else if t 3 = 1 then 748 else 752) else if t 2 = 1 then (if t 3 = 0 then 773 else if t 3 = 1 then 705 else 713) else (if t 3 = 0 then 787 else if t 3 = 1 then 709 else 717))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1773 else 2796) else if t 2 = 1 then (if t 3 = 0 then 1497 else if t 3 = 1 then 1483 else 1487) else (if t 3 = 0 then 2801 else if t 3 = 1 then 2157 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 779 else if t 3 = 1 then 749 else 753) else if t 2 = 1 then (if t 3 = 0 then 777 else if t 3 = 1 then 706 else 714) else (if t 3 = 0 then 789 else if t 3 = 1 then 710 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 782 else if t 3 = 1 then 750 else 754) else if t 2 = 1 then (if t 3 = 0 then 781 else if t 3 = 1 then 707 else 715) else (if t 3 = 0 then 791 else if t 3 = 1 then 711 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2438 else (if jt.2.val < 2 then 2784 else 2460)) else (if jt.2.val < 4 then 2783 else (if jt.2.val < 5 then 2786 else 2456))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2667 else (if jt.2.val < 2 then 2791 else 2687)) else (if jt.2.val < 4 then 2790 else (if jt.2.val < 5 then 2792 else 2658)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 519 else (if jt.2.val < 2 then 745 else 561)) else (if jt.2.val < 4 then 744 else (if jt.2.val < 5 then 746 else 510))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 606 else (if jt.2.val < 2 then 701 else 608)) else (if jt.2.val < 4 then 699 else (if jt.2.val < 5 then 700 else 603)))))

checked_coverage fastCoverage0127 pairing0127 template0127 witness0127

theorem coverage0127 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0127) (maskBits m))
    cores template0127 witness0127 := by
  rw [← coresFast_eq]
  exact fastCoverage0127

theorem coverageSize0127 : ∀ q : Pattern,
    (cores (witness0127 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0127 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0127
#print axioms coverageSize0127

noncomputable def pairing0128 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0128 : List (Fin 4935) := templateData0128

noncomputable def witness0128 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2813 else 2722) else if t 2 = 1 then (if t 3 = 0 then 2817 else if t 3 = 1 then 2809 else 2860) else (if t 3 = 0 then 2485 else if t 3 = 1 then 2855 else 2868)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2811 else 1371) else if t 2 = 1 then (if t 3 = 0 then 2815 else if t 3 = 1 then 2807 else 1370) else (if t 3 = 0 then 1416 else if t 3 = 1 then 1414 else 1777)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 962 else 101) else if t 2 = 1 then (if t 3 = 0 then 964 else if t 3 = 1 then 960 else 1001) else (if t 3 = 0 then 374 else if t 3 = 1 then 992 else 1012))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2812 else 1686) else if t 2 = 1 then (if t 3 = 0 then 2816 else if t 3 = 1 then 2808 else 1685) else (if t 3 = 0 then 1586 else if t 3 = 1 then 1584 else 1852)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2810 else 2721) else if t 2 = 1 then (if t 3 = 0 then 2814 else if t 3 = 1 then 2806 else 2859) else (if t 3 = 0 then 2484 else if t 3 = 1 then 2854 else 2864)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2724) else if t 2 = 1 then (if t 3 = 0 then 2838 else if t 3 = 1 then 2835 else 2862) else (if t 3 = 0 then 2489 else if t 3 = 1 then 2857 else 2866))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 820 else 404) else if t 2 = 1 then (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 866) else (if t 3 = 0 then 71 else if t 3 = 1 then 857 else 877)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2723) else if t 2 = 1 then (if t 3 = 0 then 2829 else if t 3 = 1 then 2826 else 2861) else (if t 3 = 0 then 2487 else if t 3 = 1 then 2856 else 2865)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2841 else 2725) else if t 2 = 1 then (if t 3 = 0 then 2842 else if t 3 = 1 then 2840 else 2863) else (if t 3 = 0 then 2491 else if t 3 = 1 then 2858 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2805 else (if jt.2.val < 2 then 2825 else 2827)) else (if jt.2.val < 4 then 2822 else (if jt.2.val < 5 then 2824 else 2823))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2804 else (if jt.2.val < 2 then 2834 else 2836)) else (if jt.2.val < 4 then 2831 else (if jt.2.val < 5 then 2833 else 2832)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2803 else (if jt.2.val < 2 then 2852 else 2853)) else (if jt.2.val < 4 then 2849 else (if jt.2.val < 5 then 2851 else 2850))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2802 else (if jt.2.val < 2 then 2845 else 2848)) else (if jt.2.val < 4 then 2844 else (if jt.2.val < 5 then 2847 else 2846)))))

checked_coverage fastCoverage0128 pairing0128 template0128 witness0128

theorem coverage0128 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0128) (maskBits m))
    cores template0128 witness0128 := by
  rw [← coresFast_eq]
  exact fastCoverage0128

theorem coverageSize0128 : ∀ q : Pattern,
    (cores (witness0128 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0128 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0128
#print axioms coverageSize0128

noncomputable def pairing0129 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0129 : List (Fin 4935) := templateData0129

noncomputable def witness0129 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2569 else if t 3 = 1 then 2560 else 2882) else if t 2 = 1 then (if t 3 = 0 then 2565 else if t 3 = 1 then 2544 else 2545) else (if t 3 = 0 then 2884 else if t 3 = 1 then 2546 else 2547)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2567 else if t 3 = 1 then 2558 else 1357) else if t 2 = 1 then (if t 3 = 0 then 2563 else if t 3 = 1 then 2538 else 1350) else (if t 3 = 0 then 1762 else if t 3 = 1 then 1747 else 1353)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 277 else 922) else if t 2 = 1 then (if t 3 = 0 then 291 else if t 3 = 1 then 251 else 254) else (if t 3 = 0 then 929 else if t 3 = 1 then 256 else 258))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2568 else if t 3 = 1 then 2559 else 1672) else if t 2 = 1 then (if t 3 = 0 then 2564 else if t 3 = 1 then 2541 else 1666) else (if t 3 = 0 then 1915 else if t 3 = 1 then 1900 else 1668)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2566 else if t 3 = 1 then 2548 else 2878) else if t 2 = 1 then (if t 3 = 0 then 2562 else if t 3 = 1 then 2519 else 2526) else (if t 3 = 0 then 2883 else if t 3 = 1 then 2530 else 2534)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2880) else if t 2 = 1 then (if t 3 = 0 then 2572 else if t 3 = 1 then 2523 else 2528) else (if t 3 = 0 then 2886 else if t 3 = 1 then 2532 else 2536))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 175 else 895) else if t 2 = 1 then (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 151) else (if t 3 = 0 then 902 else if t 3 = 1 then 153 else 155)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2571 else if t 3 = 1 then 2549 else 2879) else if t 2 = 1 then (if t 3 = 0 then 2570 else if t 3 = 1 then 2521 else 2527) else (if t 3 = 0 then 2885 else if t 3 = 1 then 2531 else 2535)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2551 else 2881) else if t 2 = 1 then (if t 3 = 0 then 2574 else if t 3 = 1 then 2524 else 2529) else (if t 3 = 0 then 2887 else if t 3 = 1 then 2533 else 2537))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2516 else (if jt.2.val < 2 then 2518 else 2540)) else (if jt.2.val < 4 then 2517 else (if jt.2.val < 5 then 2539 else 2520))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2513 else (if jt.2.val < 2 then 2515 else 2543)) else (if jt.2.val < 4 then 2514 else (if jt.2.val < 5 then 2542 else 2522)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2871 else (if jt.2.val < 2 then 2873 else 2877)) else (if jt.2.val < 4 then 2872 else (if jt.2.val < 5 then 2876 else 2875))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2846 else (if jt.2.val < 2 then 2874 else 2848)) else (if jt.2.val < 4 then 2869 else (if jt.2.val < 5 then 2870 else 2802)))))

checked_coverage fastCoverage0129 pairing0129 template0129 witness0129

theorem coverage0129 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0129) (maskBits m))
    cores template0129 witness0129 := by
  rw [← coresFast_eq]
  exact fastCoverage0129

theorem coverageSize0129 : ∀ q : Pattern,
    (cores (witness0129 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0129 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0129
#print axioms coverageSize0129

noncomputable def pairing0130 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0130 : List (Fin 4935) := templateData0130

noncomputable def witness0130 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2602 else 2906) else if t 2 = 1 then (if t 3 = 0 then 2598 else if t 3 = 1 then 2594 else 2648) else (if t 3 = 0 then 2898 else if t 3 = 1 then 2630 else 2649)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2600 else 2107) else if t 2 = 1 then (if t 3 = 0 then 2596 else if t 3 = 1 then 2592 else 2101) else (if t 3 = 0 then 1413 else if t 3 = 1 then 1411 else 1447)) else (if t 2 = 0 then (if t 3 = 0 then 145 else if t 3 = 1 then 143 else 904) else if t 2 = 1 then (if t 3 = 0 then 141 else if t 3 = 1 then 139 else 193) else (if t 3 = 0 then 893 else if t 3 = 1 then 171 else 195))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2601 else 2227) else if t 2 = 1 then (if t 3 = 0 then 2597 else if t 3 = 1 then 2593 else 2221) else (if t 3 = 0 then 1583 else if t 3 = 1 then 1581 else 1615)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2599 else 2902) else if t 2 = 1 then (if t 3 = 0 then 2595 else if t 3 = 1 then 2591 else 2640) else (if t 3 = 0 then 2897 else if t 3 = 1 then 2629 else 2644)) else (if t 2 = 0 then (if t 3 = 0 then 2624 else if t 3 = 1 then 2623 else 2904) else if t 2 = 1 then (if t 3 = 0 then 2622 else if t 3 = 1 then 2620 else 2642) else (if t 3 = 0 then 2900 else if t 3 = 1 then 2636 else 2646))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 243 else 931) else if t 2 = 1 then (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 295) else (if t 3 = 0 then 920 else if t 3 = 1 then 273 else 297)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2903) else if t 2 = 1 then (if t 3 = 0 then 2613 else if t 3 = 1 then 2611 else 2641) else (if t 3 = 0 then 2899 else if t 3 = 1 then 2634 else 2645)) else (if t 2 = 0 then (if t 3 = 0 then 2628 else if t 3 = 1 then 2627 else 2905) else if t 2 = 1 then (if t 3 = 0 then 2626 else if t 3 = 1 then 2625 else 2643) else (if t 3 = 0 then 2901 else if t 3 = 1 then 2638 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2590 else (if jt.2.val < 2 then 2610 else 2612)) else (if jt.2.val < 4 then 2607 else (if jt.2.val < 5 then 2609 else 2608))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2589 else (if jt.2.val < 2 then 2619 else 2621)) else (if jt.2.val < 4 then 2616 else (if jt.2.val < 5 then 2618 else 2617)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2850 else (if jt.2.val < 2 then 2896 else 2853)) else (if jt.2.val < 4 then 2888 else (if jt.2.val < 5 then 2889 else 2803))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2890 else (if jt.2.val < 2 then 2892 else 2895)) else (if jt.2.val < 4 then 2891 else (if jt.2.val < 5 then 2894 else 2893)))))

checked_coverage fastCoverage0130 pairing0130 template0130 witness0130

theorem coverage0130 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0130) (maskBits m))
    cores template0130 witness0130 := by
  rw [← coresFast_eq]
  exact fastCoverage0130

theorem coverageSize0130 : ∀ q : Pattern,
    (cores (witness0130 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0130 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0130
#print axioms coverageSize0130

noncomputable def pairing0131 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0131 : List (Fin 4935) := templateData0131

noncomputable def witness0131 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2953 else 2706) else if t 2 = 1 then (if t 3 = 0 then 2960 else if t 3 = 1 then 2937 else 2939) else (if t 3 = 0 then 2506 else if t 3 = 1 then 2938 else 2940)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2951 else 2098) else if t 2 = 1 then (if t 3 = 0 then 2958 else if t 3 = 1 then 2931 else 2082) else (if t 3 = 0 then 1756 else if t 3 = 1 then 1730 else 1733)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 859 else 75) else if t 2 = 1 then (if t 3 = 0 then 868 else if t 3 = 1 then 830 else 835) else (if t 3 = 0 then 406 else if t 3 = 1 then 833 else 837))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2952 else 2218) else if t 2 = 1 then (if t 3 = 0 then 2959 else if t 3 = 1 then 2934 else 2206) else (if t 3 = 0 then 1909 else if t 3 = 1 then 1888 else 1890)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2947 else 2699) else if t 2 = 1 then (if t 3 = 0 then 2954 else if t 3 = 1 then 2913 else 2923) else (if t 3 = 0 then 2502 else if t 3 = 1 then 2919 else 2927)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2949 else 2701) else if t 2 = 1 then (if t 3 = 0 then 2956 else if t 3 = 1 then 2917 else 2925) else (if t 3 = 0 then 2504 else if t 3 = 1 then 2921 else 2929))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 994 else 378) else if t 2 = 1 then (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 974) else (if t 3 = 0 then 103 else if t 3 = 1 then 972 else 976)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2700) else if t 2 = 1 then (if t 3 = 0 then 2955 else if t 3 = 1 then 2915 else 2924) else (if t 3 = 0 then 2503 else if t 3 = 1 then 2920 else 2928)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2950 else 2702) else if t 2 = 1 then (if t 3 = 0 then 2957 else if t 3 = 1 then 2918 else 2926) else (if t 3 = 0 then 2505 else if t 3 = 1 then 2922 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2910 else (if jt.2.val < 2 then 2912 else 2933)) else (if jt.2.val < 4 then 2911 else (if jt.2.val < 5 then 2932 else 2914))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2907 else (if jt.2.val < 2 then 2909 else 2936)) else (if jt.2.val < 4 then 2908 else (if jt.2.val < 5 then 2935 else 2916)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2875 else (if jt.2.val < 2 then 2945 else 2877)) else (if jt.2.val < 4 then 2944 else (if jt.2.val < 5 then 2946 else 2871))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2893 else (if jt.2.val < 2 then 2943 else 2895)) else (if jt.2.val < 4 then 2941 else (if jt.2.val < 5 then 2942 else 2890)))))

checked_coverage fastCoverage0131 pairing0131 template0131 witness0131

theorem coverage0131 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0131) (maskBits m))
    cores template0131 witness0131 := by
  rw [← coresFast_eq]
  exact fastCoverage0131

theorem coverageSize0131 : ∀ q : Pattern,
    (cores (witness0131 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0131 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0131
#print axioms coverageSize0131

noncomputable def pairing0132 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0132 : List (Fin 4935) := templateData0132

noncomputable def witness0132 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1025 else 786) else if t 2 = 1 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1021 else 1080) else (if t 3 = 0 then 469 else if t 3 = 1 then 1071 else 1094)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1023 else 784) else if t 2 = 1 then (if t 3 = 0 then 1027 else if t 3 = 1 then 1019 else 1078) else (if t 3 = 0 then 467 else if t 3 = 1 then 1069 else 1090)) else (if t 2 = 0 then (if t 3 = 0 then 2974 else if t 3 = 1 then 2972 else 2800) else if t 2 = 1 then (if t 3 = 0 then 2973 else if t 3 = 1 then 2970 else 2980) else (if t 3 = 0 then 2738 else if t 3 = 1 then 2979 else 2981))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1024 else 785) else if t 2 = 1 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1020 else 1079) else (if t 3 = 0 then 468 else if t 3 = 1 then 1070 else 1092)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1022 else 783) else if t 2 = 1 then (if t 3 = 0 then 1026 else if t 3 = 1 then 1018 else 1077) else (if t 3 = 0 then 466 else if t 3 = 1 then 1068 else 1086)) else (if t 2 = 0 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 787) else if t 2 = 1 then (if t 3 = 0 then 1041 else if t 3 = 1 then 1037 else 1081) else (if t 3 = 0 then 472 else if t 3 = 1 then 1072 else 1087))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 2145 else 2801) else if t 2 = 1 then (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1689) else (if t 3 = 0 then 2739 else if t 3 = 1 then 1598 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 789) else if t 2 = 1 then (if t 3 = 0 then 1050 else if t 3 = 1 then 1045 else 1083) else (if t 3 = 0 then 476 else if t 3 = 1 then 1074 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 1057 else if t 3 = 1 then 1055 else 791) else if t 2 = 1 then (if t 3 = 0 then 1056 else if t 3 = 1 then 1054 else 1085) else (if t 3 = 0 then 479 else if t 3 = 1 then 1076 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2910 else (if jt.2.val < 2 then 2977 else 2933)) else (if jt.2.val < 4 then 2975 else (if jt.2.val < 5 then 2976 else 2914))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2832 else (if jt.2.val < 2 then 2971 else 2836)) else (if jt.2.val < 4 then 2968 else (if jt.2.val < 5 then 2969 else 2804)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1017 else (if jt.2.val < 2 then 1066 else 1067)) else (if jt.2.val < 4 then 1063 else (if jt.2.val < 5 then 1065 else 1064))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1016 else (if jt.2.val < 2 then 1059 else 1062)) else (if jt.2.val < 4 then 1058 else (if jt.2.val < 5 then 1061 else 1060)))))

checked_coverage fastCoverage0132 pairing0132 template0132 witness0132

theorem coverage0132 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0132) (maskBits m))
    cores template0132 witness0132 := by
  rw [← coresFast_eq]
  exact fastCoverage0132

theorem coverageSize0132 : ∀ q : Pattern,
    (cores (witness0132 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0132 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0132
#print axioms coverageSize0132

noncomputable def pairing0133 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 6 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0133 : List (Fin 4935) := templateData0133

noncomputable def witness0133 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 574 else 1112) else if t 2 = 1 then (if t 3 = 0 then 579 else if t 3 = 1 then 552 else 553) else (if t 3 = 0 then 1116 else if t 3 = 1 then 554 else 555)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 581 else if t 3 = 1 then 566 else 1108) else if t 2 = 1 then (if t 3 = 0 then 577 else if t 3 = 1 then 532 else 535) else (if t 3 = 0 then 1114 else if t 3 = 1 then 537 else 539)) else (if t 2 = 0 then (if t 3 = 0 then 2760 else if t 3 = 1 then 2756 else 2983) else if t 2 = 1 then (if t 3 = 0 then 2759 else if t 3 = 1 then 2747 else 2749) else (if t 3 = 0 then 2985 else if t 3 = 1 then 2750 else 2751))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 570 else 1110) else if t 2 = 1 then (if t 3 = 0 then 578 else if t 3 = 1 then 544 else 546) else (if t 3 = 0 then 1115 else if t 3 = 1 then 548 else 550)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 580 else if t 3 = 1 then 556 else 1104) else if t 2 = 1 then (if t 3 = 0 then 576 else if t 3 = 1 then 515 else 520) else (if t 3 = 0 then 1113 else if t 3 = 1 then 524 else 528)) else (if t 2 = 0 then (if t 3 = 0 then 586 else if t 3 = 1 then 557 else 1105) else if t 2 = 1 then (if t 3 = 0 then 584 else if t 3 = 1 then 516 else 521) else (if t 3 = 0 then 1117 else if t 3 = 1 then 525 else 529))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 2115 else 2984) else if t 2 = 1 then (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1833) else (if t 3 = 0 then 2986 else if t 3 = 1 then 1535 else 2755)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 1106) else if t 2 = 1 then (if t 3 = 0 then 588 else if t 3 = 1 then 517 else 522) else (if t 3 = 0 then 1119 else if t 3 = 1 then 526 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 593 else if t 3 = 1 then 559 else 1107) else if t 2 = 1 then (if t 3 = 0 then 592 else if t 3 = 1 then 518 else 523) else (if t 3 = 0 then 1121 else if t 3 = 1 then 527 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2590 else (if jt.2.val < 2 then 2746 else 2612)) else (if jt.2.val < 4 then 2745 else (if jt.2.val < 5 then 2748 else 2608))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2522 else (if jt.2.val < 2 then 2753 else 2543)) else (if jt.2.val < 4 then 2752 else (if jt.2.val < 5 then 2754 else 2513)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1095 else (if jt.2.val < 2 then 1097 else 1103)) else (if jt.2.val < 4 then 1096 else (if jt.2.val < 5 then 1102 else 1101))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1060 else (if jt.2.val < 2 then 1100 else 1062)) else (if jt.2.val < 4 then 1098 else (if jt.2.val < 5 then 1099 else 1016)))))

checked_coverage fastCoverage0133 pairing0133 template0133 witness0133

theorem coverage0133 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0133) (maskBits m))
    cores template0133 witness0133 := by
  rw [← coresFast_eq]
  exact fastCoverage0133

theorem coverageSize0133 : ∀ q : Pattern,
    (cores (witness0133 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0133 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0133
#print axioms coverageSize0133

noncomputable def pairing0134 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0134 : List (Fin 4935) := templateData0134

noncomputable def witness0134 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 624 else 1148) else if t 2 = 1 then (if t 3 = 0 then 620 else if t 3 = 1 then 616 else 688) else (if t 3 = 0 then 1134 else if t 3 = 1 then 656 else 689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 626 else if t 3 = 1 then 622 else 1144) else if t 2 = 1 then (if t 3 = 0 then 618 else if t 3 = 1 then 614 else 680) else (if t 3 = 0 then 1132 else if t 3 = 1 then 654 else 682)) else (if t 2 = 0 then (if t 3 = 0 then 2770 else if t 3 = 1 then 2769 else 2989) else if t 2 = 1 then (if t 3 = 0 then 2768 else if t 3 = 1 then 2766 else 2778) else (if t 3 = 0 then 2987 else if t 3 = 1 then 2775 else 2779))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 623 else 1146) else if t 2 = 1 then (if t 3 = 0 then 619 else if t 3 = 1 then 615 else 684) else (if t 3 = 0 then 1133 else if t 3 = 1 then 655 else 686)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 625 else if t 3 = 1 then 621 else 1140) else if t 2 = 1 then (if t 3 = 0 then 617 else if t 3 = 1 then 613 else 672) else (if t 3 = 0 then 1131 else if t 3 = 1 then 653 else 676)) else (if t 2 = 0 then (if t 3 = 0 then 638 else if t 3 = 1 then 636 else 1141) else if t 2 = 1 then (if t 3 = 0 then 634 else if t 3 = 1 then 632 else 673) else (if t 3 = 0 then 1135 else if t 3 = 1 then 662 else 677))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2774 else if t 3 = 1 then 1461 else 2990) else if t 2 = 1 then (if t 3 = 0 then 1785 else if t 3 = 1 then 1458 else 1473) else (if t 3 = 0 then 2988 else if t 3 = 1 then 2169 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 647 else if t 3 = 1 then 645 else 1142) else if t 2 = 1 then (if t 3 = 0 then 643 else if t 3 = 1 then 640 else 674) else (if t 3 = 0 then 1137 else if t 3 = 1 then 666 else 678)) else (if t 2 = 0 then (if t 3 = 0 then 652 else if t 3 = 1 then 651 else 1143) else if t 2 = 1 then (if t 3 = 0 then 650 else if t 3 = 1 then 649 else 675) else (if t 3 = 0 then 1139 else if t 3 = 1 then 670 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2516 else (if jt.2.val < 2 then 2773 else 2540)) else (if jt.2.val < 4 then 2771 else (if jt.2.val < 5 then 2772 else 2520))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2617 else (if jt.2.val < 2 then 2767 else 2621)) else (if jt.2.val < 4 then 2764 else (if jt.2.val < 5 then 2765 else 2589)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1064 else (if jt.2.val < 2 then 1130 else 1067)) else (if jt.2.val < 4 then 1125 else (if jt.2.val < 5 then 1126 else 1017))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1122 else (if jt.2.val < 2 then 1124 else 1129)) else (if jt.2.val < 4 then 1123 else (if jt.2.val < 5 then 1128 else 1127)))))

checked_coverage fastCoverage0134 pairing0134 template0134 witness0134

theorem coverage0134 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0134) (maskBits m))
    cores template0134 witness0134 := by
  rw [← coresFast_eq]
  exact fastCoverage0134

theorem coverageSize0134 : ∀ q : Pattern,
    (cores (witness0134 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0134 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0134
#print axioms coverageSize0134

noncomputable def pairing0135 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0135 : List (Fin 4935) := templateData0135

noncomputable def witness0135 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1205 else 764) else if t 2 = 1 then (if t 3 = 0 then 1214 else if t 3 = 1 then 1187 else 1189) else (if t 3 = 0 then 506 else if t 3 = 1 then 1188 else 1190)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1201 else 757) else if t 2 = 1 then (if t 3 = 0 then 1210 else if t 3 = 1 then 1167 else 1172) else (if t 3 = 0 then 502 else if t 3 = 1 then 1170 else 1174)) else (if t 2 = 0 then (if t 3 = 0 then 3004 else if t 3 = 1 then 3002 else 2795) else if t 2 = 1 then (if t 3 = 0 then 3003 else if t 3 = 1 then 2993 else 2996) else (if t 3 = 0 then 2743 else if t 3 = 1 then 2995 else 2997))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1203 else 761) else if t 2 = 1 then (if t 3 = 0 then 1212 else if t 3 = 1 then 1179 else 1183) else (if t 3 = 0 then 504 else if t 3 = 1 then 1181 else 1185)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1197 else 751) else if t 2 = 1 then (if t 3 = 0 then 1206 else if t 3 = 1 then 1151 else 1159) else (if t 3 = 0 then 498 else if t 3 = 1 then 1155 else 1163)) else (if t 2 = 0 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1198 else 752) else if t 2 = 1 then (if t 3 = 0 then 1207 else if t 3 = 1 then 1152 else 1160) else (if t 3 = 0 then 499 else if t 3 = 1 then 1156 else 1164))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1430 else 2796) else if t 2 = 1 then (if t 3 = 0 then 1374 else if t 3 = 1 then 1795 else 1799) else (if t 3 = 0 then 2744 else if t 3 = 1 then 2136 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1199 else 753) else if t 2 = 1 then (if t 3 = 0 then 1208 else if t 3 = 1 then 1153 else 1161) else (if t 3 = 0 then 500 else if t 3 = 1 then 1157 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 1223 else if t 3 = 1 then 1200 else 754) else if t 2 = 1 then (if t 3 = 0 then 1209 else if t 3 = 1 then 1154 else 1162) else (if t 3 = 0 then 501 else if t 3 = 1 then 1158 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2805 else (if jt.2.val < 2 then 2992 else 2827)) else (if jt.2.val < 4 then 2991 else (if jt.2.val < 5 then 2994 else 2823))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2916 else (if jt.2.val < 2 then 2999 else 2936)) else (if jt.2.val < 4 then 2998 else (if jt.2.val < 5 then 3000 else 2907)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1101 else (if jt.2.val < 2 then 1195 else 1103)) else (if jt.2.val < 4 then 1194 else (if jt.2.val < 5 then 1196 else 1095))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1127 else (if jt.2.val < 2 then 1193 else 1129)) else (if jt.2.val < 4 then 1191 else (if jt.2.val < 5 then 1192 else 1122)))))

checked_coverage fastCoverage0135 pairing0135 template0135 witness0135

theorem coverage0135 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0135) (maskBits m))
    cores template0135 witness0135 := by
  rw [← coresFast_eq]
  exact fastCoverage0135

theorem coverageSize0135 : ∀ q : Pattern,
    (cores (witness0135 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0135 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0135
#print axioms coverageSize0135

noncomputable def pairing0136 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0136 : List (Fin 4935) := templateData0136

noncomputable def witness0136 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2821 else if t 3 = 1 then 2813 else 2633) else if t 2 = 1 then (if t 3 = 0 then 2817 else if t 3 = 1 then 2809 else 2855) else (if t 3 = 0 then 2577 else if t 3 = 1 then 2860 else 2868)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2819 else if t 3 = 1 then 2811 else 1415) else if t 2 = 1 then (if t 3 = 0 then 2815 else if t 3 = 1 then 2807 else 1414) else (if t 3 = 0 then 1372 else if t 3 = 1 then 1370 else 1777)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 962 else 173) else if t 2 = 1 then (if t 3 = 0 then 964 else if t 3 = 1 then 960 else 992) else (if t 3 = 0 then 305 else if t 3 = 1 then 1001 else 1012))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2820 else if t 3 = 1 then 2812 else 1585) else if t 2 = 1 then (if t 3 = 0 then 2816 else if t 3 = 1 then 2808 else 1584) else (if t 3 = 0 then 1687 else if t 3 = 1 then 1685 else 1852)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2818 else if t 3 = 1 then 2810 else 2632) else if t 2 = 1 then (if t 3 = 0 then 2814 else if t 3 = 1 then 2806 else 2854) else (if t 3 = 0 then 2576 else if t 3 = 1 then 2859 else 2864)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2637) else if t 2 = 1 then (if t 3 = 0 then 2838 else if t 3 = 1 then 2835 else 2857) else (if t 3 = 0 then 2579 else if t 3 = 1 then 2862 else 2866))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 820 else 275) else if t 2 = 1 then (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 857) else (if t 3 = 0 then 203 else if t 3 = 1 then 866 else 877)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2830 else if t 3 = 1 then 2828 else 2635) else if t 2 = 1 then (if t 3 = 0 then 2829 else if t 3 = 1 then 2826 else 2856) else (if t 3 = 0 then 2578 else if t 3 = 1 then 2861 else 2865)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2841 else 2639) else if t 2 = 1 then (if t 3 = 0 then 2842 else if t 3 = 1 then 2840 else 2858) else (if t 3 = 0 then 2580 else if t 3 = 1 then 2863 else 2867))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2805 else (if jt.2.val < 2 then 2825 else 2827)) else (if jt.2.val < 4 then 2822 else (if jt.2.val < 5 then 2824 else 2823))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2804 else (if jt.2.val < 2 then 2834 else 2836)) else (if jt.2.val < 4 then 2831 else (if jt.2.val < 5 then 2833 else 2832)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3006 else (if jt.2.val < 2 then 3012 else 3015)) else (if jt.2.val < 4 then 3011 else (if jt.2.val < 5 then 3014 else 3013))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3007 else (if jt.2.val < 2 then 3016 else 3017)) else (if jt.2.val < 4 then 3008 else (if jt.2.val < 5 then 3010 else 3009)))))

checked_coverage fastCoverage0136 pairing0136 template0136 witness0136

theorem coverage0136 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0136) (maskBits m))
    cores template0136 witness0136 := by
  rw [← coresFast_eq]
  exact fastCoverage0136

theorem coverageSize0136 : ∀ q : Pattern,
    (cores (witness0136 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0136 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0136
#print axioms coverageSize0136

noncomputable def pairing0137 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0137 : List (Fin 4935) := templateData0137

noncomputable def witness0137 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2454 else if t 3 = 1 then 2446 else 2898) else if t 2 = 1 then (if t 3 = 0 then 2450 else if t 3 = 1 then 2442 else 2482) else (if t 3 = 0 then 2884 else if t 3 = 1 then 2500 else 2501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2452 else if t 3 = 1 then 2444 else 1413) else if t 2 = 1 then (if t 3 = 0 then 2448 else if t 3 = 1 then 2440 else 1412) else (if t 3 = 0 then 1762 else if t 3 = 1 then 1753 else 1450)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 341 else 893) else if t 2 = 1 then (if t 3 = 0 then 343 else if t 3 = 1 then 339 else 372) else (if t 3 = 0 then 929 else if t 3 = 1 then 394 else 396))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2453 else if t 3 = 1 then 2445 else 1583) else if t 2 = 1 then (if t 3 = 0 then 2449 else if t 3 = 1 then 2441 else 1582) else (if t 3 = 0 then 1915 else if t 3 = 1 then 1906 else 1618)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2451 else if t 3 = 1 then 2443 else 2897) else if t 2 = 1 then (if t 3 = 0 then 2447 else if t 3 = 1 then 2439 else 2481) else (if t 3 = 0 then 2883 else if t 3 = 1 then 2492 else 2496)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2900) else if t 2 = 1 then (if t 3 = 0 then 2471 else if t 3 = 1 then 2468 else 2488) else (if t 3 = 0 then 2886 else if t 3 = 1 then 2494 else 2498))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 33 else 920) else if t 2 = 1 then (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 69) else (if t 3 = 0 then 902 else if t 3 = 1 then 91 else 93)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2463 else if t 3 = 1 then 2461 else 2899) else if t 2 = 1 then (if t 3 = 0 then 2462 else if t 3 = 1 then 2459 else 2486) else (if t 3 = 0 then 2885 else if t 3 = 1 then 2493 else 2497)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2474 else 2901) else if t 2 = 1 then (if t 3 = 0 then 2475 else if t 3 = 1 then 2473 else 2490) else (if t 3 = 0 then 2887 else if t 3 = 1 then 2495 else 2499))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2438 else (if jt.2.val < 2 then 2458 else 2460)) else (if jt.2.val < 4 then 2455 else (if jt.2.val < 5 then 2457 else 2456))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2437 else (if jt.2.val < 2 then 2467 else 2469)) else (if jt.2.val < 4 then 2464 else (if jt.2.val < 5 then 2466 else 2465)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3020 else (if jt.2.val < 2 then 3022 else 3025)) else (if jt.2.val < 4 then 3021 else (if jt.2.val < 5 then 3024 else 3023))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3009 else (if jt.2.val < 2 then 3026 else 3017)) else (if jt.2.val < 4 then 3018 else (if jt.2.val < 5 then 3019 else 3007)))))

checked_coverage fastCoverage0137 pairing0137 template0137 witness0137

theorem coverage0137 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0137) (maskBits m))
    cores template0137 witness0137 := by
  rw [← coresFast_eq]
  exact fastCoverage0137

theorem coverageSize0137 : ∀ q : Pattern,
    (cores (witness0137 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0137 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0137
#print axioms coverageSize0137

noncomputable def pairing0138 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0138 : List (Fin 4935) := templateData0138

noncomputable def witness0138 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2710 else 2906) else if t 2 = 1 then (if t 3 = 0 then 2705 else if t 3 = 1 then 2688 else 2690) else (if t 3 = 0 then 2882 else if t 3 = 1 then 2689 else 2691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2708 else 2107) else if t 2 = 1 then (if t 3 = 0 then 2703 else if t 3 = 1 then 2682 else 2090) else (if t 3 = 0 then 1357 else if t 3 = 1 then 1339 else 1342)) else (if t 2 = 0 then (if t 3 = 0 then 89 else if t 3 = 1 then 87 else 904) else if t 2 = 1 then (if t 3 = 0 then 73 else if t 3 = 1 then 43 else 48) else (if t 3 = 0 then 922 else if t 3 = 1 then 46 else 50))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2709 else 2227) else if t 2 = 1 then (if t 3 = 0 then 2704 else if t 3 = 1 then 2685 else 2212) else (if t 3 = 0 then 1672 else if t 3 = 1 then 1657 else 1659)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2707 else 2902) else if t 2 = 1 then (if t 3 = 0 then 2695 else if t 3 = 1 then 2664 else 2674) else (if t 3 = 0 then 2878 else if t 3 = 1 then 2670 else 2678)) else (if t 2 = 0 then (if t 3 = 0 then 2718 else if t 3 = 1 then 2717 else 2904) else if t 2 = 1 then (if t 3 = 0 then 2697 else if t 3 = 1 then 2668 else 2676) else (if t 3 = 0 then 2880 else if t 3 = 1 then 2672 else 2680))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 390 else 931) else if t 2 = 1 then (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 353) else (if t 3 = 0 then 895 else if t 3 = 1 then 351 else 355)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2715 else 2903) else if t 2 = 1 then (if t 3 = 0 then 2696 else if t 3 = 1 then 2666 else 2675) else (if t 3 = 0 then 2879 else if t 3 = 1 then 2671 else 2679)) else (if t 2 = 0 then (if t 3 = 0 then 2720 else if t 3 = 1 then 2719 else 2905) else if t 2 = 1 then (if t 3 = 0 then 2698 else if t 3 = 1 then 2669 else 2677) else (if t 3 = 0 then 2881 else if t 3 = 1 then 2673 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2661 else (if jt.2.val < 2 then 2663 else 2684)) else (if jt.2.val < 4 then 2662 else (if jt.2.val < 5 then 2683 else 2665))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2658 else (if jt.2.val < 2 then 2660 else 2687)) else (if jt.2.val < 4 then 2659 else (if jt.2.val < 5 then 2686 else 2667)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3013 else (if jt.2.val < 2 then 3033 else 3015)) else (if jt.2.val < 4 then 3027 else (if jt.2.val < 5 then 3028 else 3006))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3029 else (if jt.2.val < 2 then 3031 else 3035)) else (if jt.2.val < 4 then 3030 else (if jt.2.val < 5 then 3034 else 3032)))))

checked_coverage fastCoverage0138 pairing0138 template0138 witness0138

theorem coverage0138 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0138) (maskBits m))
    cores template0138 witness0138 := by
  rw [← coresFast_eq]
  exact fastCoverage0138

theorem coverageSize0138 : ∀ q : Pattern,
    (cores (witness0138 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0138 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0138
#print axioms coverageSize0138

noncomputable def pairing0139 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 3 else 1)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0139 : List (Fin 4935) := templateData0139

noncomputable def witness0139 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2960 else 2654) else if t 2 = 1 then (if t 3 = 0 then 2953 else if t 3 = 1 then 2937 else 2939) else (if t 3 = 0 then 2561 else if t 3 = 1 then 2938 else 2940)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2958 else 2104) else if t 2 = 1 then (if t 3 = 0 then 2951 else if t 3 = 1 then 2931 else 2082) else (if t 3 = 0 then 1750 else if t 3 = 1 then 1730 else 1733)) else (if t 2 = 0 then (if t 3 = 0 then 875 else if t 3 = 1 then 868 else 205) else if t 2 = 1 then (if t 3 = 0 then 859 else if t 3 = 1 then 830 else 835) else (if t 3 = 0 then 279 else if t 3 = 1 then 833 else 837))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2959 else 2224) else if t 2 = 1 then (if t 3 = 0 then 2952 else if t 3 = 1 then 2934 else 2206) else (if t 3 = 0 then 1903 else if t 3 = 1 then 1888 else 1890)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2954 else 2650) else if t 2 = 1 then (if t 3 = 0 then 2947 else if t 3 = 1 then 2913 else 2923) else (if t 3 = 0 then 2554 else if t 3 = 1 then 2919 else 2927)) else (if t 2 = 0 then (if t 3 = 0 then 2966 else if t 3 = 1 then 2956 else 2652) else if t 2 = 1 then (if t 3 = 0 then 2949 else if t 3 = 1 then 2917 else 2925) else (if t 3 = 0 then 2556 else if t 3 = 1 then 2921 else 2929))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 1003 else 307) else if t 2 = 1 then (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 974) else (if t 3 = 0 then 177 else if t 3 = 1 then 972 else 976)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2955 else 2651) else if t 2 = 1 then (if t 3 = 0 then 2948 else if t 3 = 1 then 2915 else 2924) else (if t 3 = 0 then 2555 else if t 3 = 1 then 2920 else 2928)) else (if t 2 = 0 then (if t 3 = 0 then 2967 else if t 3 = 1 then 2957 else 2653) else if t 2 = 1 then (if t 3 = 0 then 2950 else if t 3 = 1 then 2918 else 2926) else (if t 3 = 0 then 2557 else if t 3 = 1 then 2922 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2910 else (if jt.2.val < 2 then 2912 else 2933)) else (if jt.2.val < 4 then 2911 else (if jt.2.val < 5 then 2932 else 2914))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2907 else (if jt.2.val < 2 then 2909 else 2936)) else (if jt.2.val < 4 then 2908 else (if jt.2.val < 5 then 2935 else 2916)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3023 else (if jt.2.val < 2 then 3040 else 3025)) else (if jt.2.val < 4 then 3036 else (if jt.2.val < 5 then 3037 else 3020))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3032 else (if jt.2.val < 2 then 3039 else 3035)) else (if jt.2.val < 4 then 3038 else (if jt.2.val < 5 then 3041 else 3029)))))

checked_coverage fastCoverage0139 pairing0139 template0139 witness0139

theorem coverage0139 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0139) (maskBits m))
    cores template0139 witness0139 := by
  rw [← coresFast_eq]
  exact fastCoverage0139

theorem coverageSize0139 : ∀ q : Pattern,
    (cores (witness0139 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0139 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0139
#print axioms coverageSize0139

noncomputable def pairing0140 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0140 : List (Fin 4935) := templateData0140

noncomputable def witness0140 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1025 else 661) else if t 2 = 1 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1021 else 1071) else (if t 3 = 0 then 597 else if t 3 = 1 then 1080 else 1094)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1023 else 659) else if t 2 = 1 then (if t 3 = 0 then 1027 else if t 3 = 1 then 1019 else 1069) else (if t 3 = 0 then 595 else if t 3 = 1 then 1078 else 1090)) else (if t 2 = 0 then (if t 3 = 0 then 2974 else if t 3 = 1 then 2972 else 2776) else if t 2 = 1 then (if t 3 = 0 then 2973 else if t 3 = 1 then 2970 else 2979) else (if t 3 = 0 then 2762 else if t 3 = 1 then 2980 else 2981))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1024 else 660) else if t 2 = 1 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1020 else 1070) else (if t 3 = 0 then 596 else if t 3 = 1 then 1079 else 1092)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1022 else 658) else if t 2 = 1 then (if t 3 = 0 then 1026 else if t 3 = 1 then 1018 else 1068) else (if t 3 = 0 then 594 else if t 3 = 1 then 1077 else 1086)) else (if t 2 = 0 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 664) else if t 2 = 1 then (if t 3 = 0 then 1041 else if t 3 = 1 then 1037 else 1072) else (if t 3 = 0 then 598 else if t 3 = 1 then 1081 else 1087))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 2145 else 2777) else if t 2 = 1 then (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1598) else (if t 3 = 0 then 2763 else if t 3 = 1 then 1689 else 2982)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 668) else if t 2 = 1 then (if t 3 = 0 then 1050 else if t 3 = 1 then 1045 else 1074) else (if t 3 = 0 then 600 else if t 3 = 1 then 1083 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 1057 else if t 3 = 1 then 1055 else 671) else if t 2 = 1 then (if t 3 = 0 then 1056 else if t 3 = 1 then 1054 else 1076) else (if t 3 = 0 then 602 else if t 3 = 1 then 1085 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2910 else (if jt.2.val < 2 then 2977 else 2933)) else (if jt.2.val < 4 then 2975 else (if jt.2.val < 5 then 2976 else 2914))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2832 else (if jt.2.val < 2 then 2971 else 2836)) else (if jt.2.val < 4 then 2968 else (if jt.2.val < 5 then 2969 else 2804)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1260 else (if jt.2.val < 2 then 1263 else 1269)) else (if jt.2.val < 4 then 1262 else (if jt.2.val < 5 then 1268 else 1267))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1261 else (if jt.2.val < 2 then 1270 else 1271)) else (if jt.2.val < 4 then 1264 else (if jt.2.val < 5 then 1266 else 1265)))))

checked_coverage fastCoverage0140 pairing0140 template0140 witness0140

theorem coverage0140 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0140) (maskBits m))
    cores template0140 witness0140 := by
  rw [← coresFast_eq]
  exact fastCoverage0140

theorem coverageSize0140 : ∀ q : Pattern,
    (cores (witness0140 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0140 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0140
#print axioms coverageSize0140

noncomputable def pairing0141 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 7 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0141 : List (Fin 4935) := templateData0141

noncomputable def witness0141 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 424 else 1134) else if t 2 = 1 then (if t 3 = 0 then 428 else if t 3 = 1 then 420 else 464) else (if t 3 = 0 then 1116 else if t 3 = 1 then 496 else 497)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 430 else if t 3 = 1 then 422 else 1132) else if t 2 = 1 then (if t 3 = 0 then 426 else if t 3 = 1 then 418 else 462) else (if t 3 = 0 then 1114 else if t 3 = 1 then 488 else 490)) else (if t 2 = 0 then (if t 3 = 0 then 2732 else if t 3 = 1 then 2730 else 2987) else if t 2 = 1 then (if t 3 = 0 then 2731 else if t 3 = 1 then 2728 else 2737) else (if t 3 = 0 then 2985 else if t 3 = 1 then 2740 else 2741))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 423 else 1133) else if t 2 = 1 then (if t 3 = 0 then 427 else if t 3 = 1 then 419 else 463) else (if t 3 = 0 then 1115 else if t 3 = 1 then 492 else 494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 429 else if t 3 = 1 then 421 else 1131) else if t 2 = 1 then (if t 3 = 0 then 425 else if t 3 = 1 then 417 else 461) else (if t 3 = 0 then 1113 else if t 3 = 1 then 480 else 484)) else (if t 2 = 0 then (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 1135) else if t 2 = 1 then (if t 3 = 0 then 440 else if t 3 = 1 then 436 else 470) else (if t 3 = 0 then 1117 else if t 3 = 1 then 481 else 485))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 2124 else 2988) else if t 2 = 1 then (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1848) else (if t 3 = 0 then 2986 else if t 3 = 1 then 1521 else 2742)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 1137) else if t 2 = 1 then (if t 3 = 0 then 449 else if t 3 = 1 then 444 else 474) else (if t 3 = 0 then 1119 else if t 3 = 1 then 482 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 456 else if t 3 = 1 then 454 else 1139) else if t 2 = 1 then (if t 3 = 0 then 455 else if t 3 = 1 then 453 else 478) else (if t 3 = 0 then 1121 else if t 3 = 1 then 483 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2661 else (if jt.2.val < 2 then 2735 else 2684)) else (if jt.2.val < 4 then 2733 else (if jt.2.val < 5 then 2734 else 2665))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2465 else (if jt.2.val < 2 then 2729 else 2469)) else (if jt.2.val < 4 then 2726 else (if jt.2.val < 5 then 2727 else 2437)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1272 else (if jt.2.val < 2 then 1274 else 1279)) else (if jt.2.val < 4 then 1273 else (if jt.2.val < 5 then 1278 else 1277))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1265 else (if jt.2.val < 2 then 1280 else 1271)) else (if jt.2.val < 4 then 1275 else (if jt.2.val < 5 then 1276 else 1261)))))

checked_coverage fastCoverage0141 pairing0141 template0141 witness0141

theorem coverage0141 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0141) (maskBits m))
    cores template0141 witness0141 := by
  rw [← coresFast_eq]
  exact fastCoverage0141

theorem coverageSize0141 : ∀ q : Pattern,
    (cores (witness0141 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0141 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0141
#print axioms coverageSize0141

noncomputable def pairing0142 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0142 : List (Fin 4935) := templateData0142

noncomputable def witness0142 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 768 else 1148) else if t 2 = 1 then (if t 3 = 0 then 763 else if t 3 = 1 then 740 else 742) else (if t 3 = 0 then 1112 else if t 3 = 1 then 741 else 743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 770 else if t 3 = 1 then 766 else 1144) else if t 2 = 1 then (if t 3 = 0 then 755 else if t 3 = 1 then 720 else 725) else (if t 3 = 0 then 1108 else if t 3 = 1 then 723 else 727)) else (if t 2 = 0 then (if t 3 = 0 then 2798 else if t 3 = 1 then 2797 else 2989) else if t 2 = 1 then (if t 3 = 0 then 2794 else if t 3 = 1 then 2785 else 2788) else (if t 3 = 0 then 2983 else if t 3 = 1 then 2787 else 2789))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 767 else 1146) else if t 2 = 1 then (if t 3 = 0 then 759 else if t 3 = 1 then 732 else 736) else (if t 3 = 0 then 1110 else if t 3 = 1 then 734 else 738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 769 else if t 3 = 1 then 765 else 1140) else if t 2 = 1 then (if t 3 = 0 then 747 else if t 3 = 1 then 704 else 712) else (if t 3 = 0 then 1104 else if t 3 = 1 then 708 else 716)) else (if t 2 = 0 then (if t 3 = 0 then 775 else if t 3 = 1 then 773 else 1141) else if t 2 = 1 then (if t 3 = 0 then 748 else if t 3 = 1 then 705 else 713) else (if t 3 = 0 then 1105 else if t 3 = 1 then 709 else 717))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2799 else if t 3 = 1 then 1497 else 2990) else if t 2 = 1 then (if t 3 = 0 then 1773 else if t 3 = 1 then 1483 else 1487) else (if t 3 = 0 then 2984 else if t 3 = 1 then 2157 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 779 else if t 3 = 1 then 777 else 1142) else if t 2 = 1 then (if t 3 = 0 then 749 else if t 3 = 1 then 706 else 714) else (if t 3 = 0 then 1106 else if t 3 = 1 then 710 else 718)) else (if t 2 = 0 then (if t 3 = 0 then 782 else if t 3 = 1 then 781 else 1143) else if t 2 = 1 then (if t 3 = 0 then 750 else if t 3 = 1 then 707 else 715) else (if t 3 = 0 then 1107 else if t 3 = 1 then 711 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2438 else (if jt.2.val < 2 then 2784 else 2460)) else (if jt.2.val < 4 then 2783 else (if jt.2.val < 5 then 2786 else 2456))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2667 else (if jt.2.val < 2 then 2791 else 2687)) else (if jt.2.val < 4 then 2790 else (if jt.2.val < 5 then 2792 else 2658)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1267 else (if jt.2.val < 2 then 1287 else 1269)) else (if jt.2.val < 4 then 1284 else (if jt.2.val < 5 then 1285 else 1260))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1281 else (if jt.2.val < 2 then 1283 else 1289)) else (if jt.2.val < 4 then 1282 else (if jt.2.val < 5 then 1288 else 1286)))))

checked_coverage fastCoverage0142 pairing0142 template0142 witness0142

theorem coverage0142 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0142) (maskBits m))
    cores template0142 witness0142 := by
  rw [← coresFast_eq]
  exact fastCoverage0142

theorem coverageSize0142 : ∀ q : Pattern,
    (cores (witness0142 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0142 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0142
#print axioms coverageSize0142

noncomputable def pairing0143 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 3)) else (if x.1.val < 3 then (if x.2 then 4 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0143 : List (Fin 4935) := templateData0143

noncomputable def witness0143 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1214 else 698) else if t 2 = 1 then (if t 3 = 0 then 1205 else if t 3 = 1 then 1187 else 1189) else (if t 3 = 0 then 575 else if t 3 = 1 then 1188 else 1190)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1210 else 694) else if t 2 = 1 then (if t 3 = 0 then 1201 else if t 3 = 1 then 1167 else 1172) else (if t 3 = 0 then 568 else if t 3 = 1 then 1170 else 1174)) else (if t 2 = 0 then (if t 3 = 0 then 3004 else if t 3 = 1 then 3003 else 2781) else if t 2 = 1 then (if t 3 = 0 then 3002 else if t 3 = 1 then 2993 else 2996) else (if t 3 = 0 then 2757 else if t 3 = 1 then 2995 else 2997))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1212 else 696) else if t 2 = 1 then (if t 3 = 0 then 1203 else if t 3 = 1 then 1179 else 1183) else (if t 3 = 0 then 572 else if t 3 = 1 then 1181 else 1185)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1206 else 690) else if t 2 = 1 then (if t 3 = 0 then 1197 else if t 3 = 1 then 1151 else 1159) else (if t 3 = 0 then 562 else if t 3 = 1 then 1155 else 1163)) else (if t 2 = 0 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1207 else 691) else if t 2 = 1 then (if t 3 = 0 then 1198 else if t 3 = 1 then 1152 else 1160) else (if t 3 = 0 then 563 else if t 3 = 1 then 1156 else 1164))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3005 else if t 3 = 1 then 1374 else 2782) else if t 2 = 1 then (if t 3 = 0 then 1430 else if t 3 = 1 then 1795 else 1799) else (if t 3 = 0 then 2758 else if t 3 = 1 then 2136 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1221 else if t 3 = 1 then 1208 else 692) else if t 2 = 1 then (if t 3 = 0 then 1199 else if t 3 = 1 then 1153 else 1161) else (if t 3 = 0 then 564 else if t 3 = 1 then 1157 else 1165)) else (if t 2 = 0 then (if t 3 = 0 then 1223 else if t 3 = 1 then 1209 else 693) else if t 2 = 1 then (if t 3 = 0 then 1200 else if t 3 = 1 then 1154 else 1162) else (if t 3 = 0 then 565 else if t 3 = 1 then 1158 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2805 else (if jt.2.val < 2 then 2992 else 2827)) else (if jt.2.val < 4 then 2991 else (if jt.2.val < 5 then 2994 else 2823))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2916 else (if jt.2.val < 2 then 2999 else 2936)) else (if jt.2.val < 4 then 2998 else (if jt.2.val < 5 then 3000 else 2907)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1277 else (if jt.2.val < 2 then 1294 else 1279)) else (if jt.2.val < 4 then 1292 else (if jt.2.val < 5 then 1293 else 1272))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1286 else (if jt.2.val < 2 then 1291 else 1289)) else (if jt.2.val < 4 then 1290 else (if jt.2.val < 5 then 1295 else 1281)))))

checked_coverage fastCoverage0143 pairing0143 template0143 witness0143

theorem coverage0143 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0143) (maskBits m))
    cores template0143 witness0143 := by
  rw [← coresFast_eq]
  exact fastCoverage0143

theorem coverageSize0143 : ∀ q : Pattern,
    (cores (witness0143 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0143 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0143
#print axioms coverageSize0143

noncomputable def pairing0144 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0144 : List (Fin 4935) := templateData0144

noncomputable def witness0144 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3066 else if t 3 = 1 then 3058 else 3106) else if t 2 = 1 then (if t 3 = 0 then 3062 else if t 3 = 1 then 3054 else 3003) else (if t 3 = 0 then 2770 else if t 3 = 1 then 2768 else 2781)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3064 else if t 3 = 1 then 3056 else 868) else if t 2 = 1 then (if t 3 = 0 then 3060 else if t 3 = 1 then 3052 else 862) else (if t 3 = 0 then 144 else if t 3 = 1 then 140 else 199)) else (if t 2 = 0 then (if t 3 = 0 then 345 else if t 3 = 1 then 341 else 406) else if t 2 = 1 then (if t 3 = 0 then 344 else if t 3 = 1 then 340 else 400) else (if t 3 = 0 then 1496 else if t 3 = 1 then 892 else 1501))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3065 else if t 3 = 1 then 3057 else 1213) else if t 2 = 1 then (if t 3 = 0 then 3061 else if t 3 = 1 then 3053 else 1207) else (if t 3 = 0 then 638 else if t 3 = 1 then 634 else 691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3063 else if t 3 = 1 then 3055 else 2956) else if t 2 = 1 then (if t 3 = 0 then 3059 else if t 3 = 1 then 3051 else 3098) else (if t 3 = 0 then 3091 else if t 3 = 1 then 3089 else 3102)) else (if t 2 = 0 then (if t 3 = 0 then 2472 else if t 3 = 1 then 2470 else 2504) else if t 2 = 1 then (if t 3 = 0 then 3082 else if t 3 = 1 then 3080 else 3100) else (if t 3 = 0 then 3095 else if t 3 = 1 then 3094 else 3104))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 1375) else if t 2 = 1 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 1209) else (if t 3 = 0 then 652 else if t 3 = 1 then 650 else 693)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3075 else if t 3 = 1 then 3073 else 2957) else if t 2 = 1 then (if t 3 = 0 then 3074 else if t 3 = 1 then 3071 else 3099) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3092 else 3103)) else (if t 2 = 0 then (if t 3 = 0 then 2476 else if t 3 = 1 then 2474 else 2505) else if t 2 = 1 then (if t 3 = 0 then 3084 else if t 3 = 1 then 3083 else 3101) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3096 else 3105))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3050 else (if jt.2.val < 2 then 3070 else 3072)) else (if jt.2.val < 4 then 3067 else (if jt.2.val < 5 then 3069 else 3068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3049 else (if jt.2.val < 2 then 3079 else 3081)) else (if jt.2.val < 4 then 3076 else (if jt.2.val < 5 then 3078 else 3077)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3048 else (if jt.2.val < 2 then 3088 else 3090)) else (if jt.2.val < 4 then 3085 else (if jt.2.val < 5 then 3087 else 3086))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3042 else (if jt.2.val < 2 then 3044 else 3047)) else (if jt.2.val < 4 then 3043 else (if jt.2.val < 5 then 3046 else 3045)))))

checked_coverage fastCoverage0144 pairing0144 template0144 witness0144

theorem coverage0144 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0144) (maskBits m))
    cores template0144 witness0144 := by
  rw [← coresFast_eq]
  exact fastCoverage0144

theorem coverageSize0144 : ∀ q : Pattern,
    (cores (witness0144 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0144 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0144
#print axioms coverageSize0144

noncomputable def pairing0145 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0145 : List (Fin 4935) := templateData0145

noncomputable def witness0145 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3152) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 3002) else (if t 3 = 0 then 2798 else if t 3 = 1 then 2794 else 2795)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 859) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 853) else (if t 3 = 0 then 88 else if t 3 = 1 then 60 else 65)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 277 else 279) else if t 2 = 1 then (if t 3 = 0 then 292 else if t 3 = 1 then 264 else 269) else (if t 3 = 0 then 1478 else if t 3 = 1 then 916 else 1471))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 1204) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 1198) else (if t 3 = 0 then 775 else if t 3 = 1 then 748 else 752)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2949) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3130) else (if t 3 = 0 then 3165 else if t 3 = 1 then 3126 else 3134)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2556) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3123 else 3132) else (if t 3 = 0 then 3167 else if t 3 = 1 then 3128 else 3136))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 1431) else if t 2 = 1 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 1200) else (if t 3 = 0 then 782 else if t 3 = 1 then 750 else 754)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2950) else if t 2 = 1 then (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3131) else (if t 3 = 0 then 3166 else if t 3 = 1 then 3127 else 3135)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2551 else 2557) else if t 2 = 1 then (if t 3 = 0 then 3164 else if t 3 = 1 then 3124 else 3133) else (if t 3 = 0 then 3168 else if t 3 = 1 then 3129 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3116 else (if jt.2.val < 2 then 3118 else 3140)) else (if jt.2.val < 4 then 3117 else (if jt.2.val < 5 then 3139 else 3120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3113 else (if jt.2.val < 2 then 3115 else 3143)) else (if jt.2.val < 4 then 3114 else (if jt.2.val < 5 then 3142 else 3122)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3110 else (if jt.2.val < 2 then 3112 else 3148)) else (if jt.2.val < 4 then 3111 else (if jt.2.val < 5 then 3147 else 3125))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3045 else (if jt.2.val < 2 then 3109 else 3047)) else (if jt.2.val < 4 then 3107 else (if jt.2.val < 5 then 3108 else 3042)))))

checked_coverage fastCoverage0145 pairing0145 template0145 witness0145

theorem coverage0145 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0145) (maskBits m))
    cores template0145 witness0145 := by
  rw [← coresFast_eq]
  exact fastCoverage0145

theorem coverageSize0145 : ∀ q : Pattern,
    (cores (witness0145 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0145 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0145
#print axioms coverageSize0145

noncomputable def pairing0146 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0146 : List (Fin 4935) := templateData0146

noncomputable def witness0146 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2598 else 2654) else if t 2 = 1 then (if t 3 = 0 then 2602 else if t 3 = 1 then 2594 else 2648) else (if t 3 = 0 then 3174 else if t 3 = 1 then 3172 else 3182)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2596 else 2104) else if t 2 = 1 then (if t 3 = 0 then 2600 else if t 3 = 1 then 2592 else 2101) else (if t 3 = 0 then 143 else if t 3 = 1 then 139 else 193)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1413 else 1453) else if t 2 = 1 then (if t 3 = 0 then 1415 else if t 3 = 1 then 1411 else 1447) else (if t 3 = 0 then 173 else if t 3 = 1 then 171 else 195))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2597 else 2224) else if t 2 = 1 then (if t 3 = 0 then 2601 else if t 3 = 1 then 2593 else 2221) else (if t 3 = 0 then 637 else if t 3 = 1 then 633 else 685)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2595 else 2650) else if t 2 = 1 then (if t 3 = 0 then 2599 else if t 3 = 1 then 2591 else 2640) else (if t 3 = 0 then 2623 else if t 3 = 1 then 2620 else 2642)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2897 else 3183) else if t 2 = 1 then (if t 3 = 0 then 2632 else if t 3 = 1 then 2629 else 2644) else (if t 3 = 0 then 2637 else if t 3 = 1 then 2636 else 2646))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 241 else 307) else if t 2 = 1 then (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 295) else (if t 3 = 0 then 1464 else if t 3 = 1 then 1463 else 1474)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2613 else 2651) else if t 2 = 1 then (if t 3 = 0 then 2614 else if t 3 = 1 then 2611 else 2641) else (if t 3 = 0 then 2627 else if t 3 = 1 then 2625 else 2643)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2899 else 3184) else if t 2 = 1 then (if t 3 = 0 then 2635 else if t 3 = 1 then 2634 else 2645) else (if t 3 = 0 then 2639 else if t 3 = 1 then 2638 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2590 else (if jt.2.val < 2 then 2610 else 2612)) else (if jt.2.val < 4 then 2607 else (if jt.2.val < 5 then 2609 else 2608))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3171 else (if jt.2.val < 2 then 3178 else 3179)) else (if jt.2.val < 4 then 3175 else (if jt.2.val < 5 then 3177 else 3176)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3086 else (if jt.2.val < 2 then 3173 else 3090)) else (if jt.2.val < 4 then 3169 else (if jt.2.val < 5 then 3170 else 3048))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2581 else (if jt.2.val < 2 then 2583 else 2586)) else (if jt.2.val < 4 then 2582 else (if jt.2.val < 5 then 2585 else 2584)))))

checked_coverage fastCoverage0146 pairing0146 template0146 witness0146

theorem coverage0146 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0146) (maskBits m))
    cores template0146 witness0146 := by
  rw [← coresFast_eq]
  exact fastCoverage0146

theorem coverageSize0146 : ∀ q : Pattern,
    (cores (witness0146 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0146 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0146
#print axioms coverageSize0146

noncomputable def pairing0147 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0147 : List (Fin 4935) := templateData0147

noncomputable def witness0147 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2714 else if t 3 = 1 then 2705 else 2706) else if t 2 = 1 then (if t 3 = 0 then 2710 else if t 3 = 1 then 2688 else 2690) else (if t 3 = 0 then 3198 else if t 3 = 1 then 3191 else 3192)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2712 else if t 3 = 1 then 2703 else 2098) else if t 2 = 1 then (if t 3 = 0 then 2708 else if t 3 = 1 then 2682 else 2090) else (if t 3 = 0 then 87 else if t 3 = 1 then 43 else 48)) else (if t 2 = 0 then (if t 3 = 0 then 1373 else if t 3 = 1 then 1357 else 1359) else if t 2 = 1 then (if t 3 = 0 then 1371 else if t 3 = 1 then 1339 else 1342) else (if t 3 = 0 then 101 else if t 3 = 1 then 46 else 50))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2713 else if t 3 = 1 then 2704 else 2218) else if t 2 = 1 then (if t 3 = 0 then 2709 else if t 3 = 1 then 2685 else 2212) else (if t 3 = 0 then 774 else if t 3 = 1 then 733 else 737)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2711 else if t 3 = 1 then 2695 else 2699) else if t 2 = 1 then (if t 3 = 0 then 2707 else if t 3 = 1 then 2664 else 2674) else (if t 3 = 0 then 2717 else if t 3 = 1 then 2668 else 2676)) else (if t 2 = 0 then (if t 3 = 0 then 3199 else if t 3 = 1 then 2878 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2721 else if t 3 = 1 then 2670 else 2678) else (if t 3 = 0 then 2724 else if t 3 = 1 then 2672 else 2680))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 376 else 378) else if t 2 = 1 then (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 353) else (if t 3 = 0 then 1499 else if t 3 = 1 then 1484 else 1488)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2716 else if t 3 = 1 then 2696 else 2700) else if t 2 = 1 then (if t 3 = 0 then 2715 else if t 3 = 1 then 2666 else 2675) else (if t 3 = 0 then 2719 else if t 3 = 1 then 2669 else 2677)) else (if t 2 = 0 then (if t 3 = 0 then 3200 else if t 3 = 1 then 2879 else 3197) else if t 2 = 1 then (if t 3 = 0 then 2723 else if t 3 = 1 then 2671 else 2679) else (if t 3 = 0 then 2725 else if t 3 = 1 then 2673 else 2681))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2661 else (if jt.2.val < 2 then 2663 else 2684)) else (if jt.2.val < 4 then 2662 else (if jt.2.val < 5 then 2683 else 2665))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3185 else (if jt.2.val < 2 then 3187 else 3190)) else (if jt.2.val < 4 then 3186 else (if jt.2.val < 5 then 3189 else 3188)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3125 else (if jt.2.val < 2 then 3194 else 3148)) else (if jt.2.val < 4 then 3193 else (if jt.2.val < 5 then 3195 else 3110))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2584 else (if jt.2.val < 2 then 2657 else 2586)) else (if jt.2.val < 4 then 2655 else (if jt.2.val < 5 then 2656 else 2581)))))

checked_coverage fastCoverage0147 pairing0147 template0147 witness0147

theorem coverage0147 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0147) (maskBits m))
    cores template0147 witness0147 := by
  rw [← coresFast_eq]
  exact fastCoverage0147

theorem coverageSize0147 : ∀ q : Pattern,
    (cores (witness0147 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0147 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0147
#print axioms coverageSize0147

noncomputable def pairing0148 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0148 : List (Fin 4935) := templateData0148

noncomputable def witness0148 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 424 else 506) else if t 2 = 1 then (if t 3 = 0 then 430 else if t 3 = 1 then 422 else 502) else (if t 3 = 0 then 1519 else if t 3 = 1 then 1132 else 1526)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 428 else if t 3 = 1 then 420 else 496) else if t 2 = 1 then (if t 3 = 0 then 426 else if t 3 = 1 then 418 else 488) else (if t 3 = 0 then 467 else if t 3 = 1 then 462 else 490)) else (if t 2 = 0 then (if t 3 = 0 then 3205 else if t 3 = 1 then 3203 else 3207) else if t 2 = 1 then (if t 3 = 0 then 2731 else if t 3 = 1 then 2728 else 2740) else (if t 3 = 0 then 2738 else if t 3 = 1 then 2737 else 2741))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 423 else 504) else if t 2 = 1 then (if t 3 = 0 then 429 else if t 3 = 1 then 421 else 498) else (if t 3 = 0 then 1518 else if t 3 = 1 then 1131 else 1524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 427 else if t 3 = 1 then 419 else 492) else if t 2 = 1 then (if t 3 = 0 then 425 else if t 3 = 1 then 417 else 480) else (if t 3 = 0 then 466 else if t 3 = 1 then 461 else 484)) else (if t 2 = 0 then (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 493) else if t 2 = 1 then (if t 3 = 0 then 440 else if t 3 = 1 then 436 else 481) else (if t 3 = 0 then 472 else if t 3 = 1 then 470 else 485))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2736 else if t 3 = 1 then 2124 else 2744) else if t 2 = 1 then (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 500) else (if t 3 = 0 then 3206 else if t 3 = 1 then 1137 else 3208)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1521) else if t 2 = 1 then (if t 3 = 0 then 449 else if t 3 = 1 then 444 else 482) else (if t 3 = 0 then 476 else if t 3 = 1 then 474 else 486)) else (if t 2 = 0 then (if t 3 = 0 then 1512 else if t 3 = 1 then 1511 else 1522) else if t 2 = 1 then (if t 3 = 0 then 455 else if t 3 = 1 then 453 else 483) else (if t 3 = 0 then 479 else if t 3 = 1 then 478 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2661 else (if jt.2.val < 2 then 2735 else 2684)) else (if jt.2.val < 4 then 2733 else (if jt.2.val < 5 then 2734 else 2665))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3077 else (if jt.2.val < 2 then 3204 else 3081)) else (if jt.2.val < 4 then 3201 else (if jt.2.val < 5 then 3202 else 3049)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1505 else (if jt.2.val < 2 then 1516 else 1517)) else (if jt.2.val < 4 then 1513 else (if jt.2.val < 5 then 1515 else 1514))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 408 else (if jt.2.val < 2 then 410 else 413)) else (if jt.2.val < 4 then 409 else (if jt.2.val < 5 then 412 else 411)))))

checked_coverage fastCoverage0148 pairing0148 template0148 witness0148

theorem coverage0148 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0148) (maskBits m))
    cores template0148 witness0148 := by
  rw [← coresFast_eq]
  exact fastCoverage0148

theorem coverageSize0148 : ∀ q : Pattern,
    (cores (witness0148 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0148 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0148
#print axioms coverageSize0148

noncomputable def pairing0149 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0149 : List (Fin 4935) := templateData0149

noncomputable def witness0149 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 574 else 575) else if t 2 = 1 then (if t 3 = 0 then 581 else if t 3 = 1 then 566 else 568) else (if t 3 = 0 then 1549 else if t 3 = 1 then 1108 else 1544)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 579 else if t 3 = 1 then 552 else 554) else if t 2 = 1 then (if t 3 = 0 then 577 else if t 3 = 1 then 532 else 537) else (if t 3 = 0 then 595 else if t 3 = 1 then 535 else 539)) else (if t 2 = 0 then (if t 3 = 0 then 3215 else if t 3 = 1 then 3209 else 3210) else if t 2 = 1 then (if t 3 = 0 then 2759 else if t 3 = 1 then 2747 else 2750) else (if t 3 = 0 then 2762 else if t 3 = 1 then 2749 else 2751))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 570 else 572) else if t 2 = 1 then (if t 3 = 0 then 580 else if t 3 = 1 then 556 else 562) else (if t 3 = 0 then 1548 else if t 3 = 1 then 1104 else 1542)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 578 else if t 3 = 1 then 544 else 548) else if t 2 = 1 then (if t 3 = 0 then 576 else if t 3 = 1 then 515 else 524) else (if t 3 = 0 then 594 else if t 3 = 1 then 520 else 528)) else (if t 2 = 0 then (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 549) else if t 2 = 1 then (if t 3 = 0 then 584 else if t 3 = 1 then 516 else 525) else (if t 3 = 0 then 598 else if t 3 = 1 then 521 else 529))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 2115 else 2758) else if t 2 = 1 then (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 564) else (if t 3 = 0 then 3216 else if t 3 = 1 then 1106 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1535) else if t 2 = 1 then (if t 3 = 0 then 588 else if t 3 = 1 then 517 else 526) else (if t 3 = 0 then 600 else if t 3 = 1 then 522 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 1547 else if t 3 = 1 then 1532 else 1536) else if t 2 = 1 then (if t 3 = 0 then 592 else if t 3 = 1 then 518 else 527) else (if t 3 = 0 then 602 else if t 3 = 1 then 523 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2590 else (if jt.2.val < 2 then 2746 else 2612)) else (if jt.2.val < 4 then 2745 else (if jt.2.val < 5 then 2748 else 2608))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3122 else (if jt.2.val < 2 then 3212 else 3143)) else (if jt.2.val < 4 then 3211 else (if jt.2.val < 5 then 3213 else 3113)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1527 else (if jt.2.val < 2 then 1529 else 1534)) else (if jt.2.val < 4 then 1528 else (if jt.2.val < 5 then 1533 else 1530))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 411 else (if jt.2.val < 2 then 509 else 413)) else (if jt.2.val < 4 then 507 else (if jt.2.val < 5 then 508 else 408)))))

checked_coverage fastCoverage0149 pairing0149 template0149 witness0149

theorem coverage0149 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0149) (maskBits m))
    cores template0149 witness0149 := by
  rw [← coresFast_eq]
  exact fastCoverage0149

theorem coverageSize0149 : ∀ q : Pattern,
    (cores (witness0149 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0149 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0149
#print axioms coverageSize0149

noncomputable def pairing0150 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0150 : List (Fin 4935) := templateData0150

noncomputable def witness0150 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1568 else 1622) else if t 2 = 1 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1564 else 1616) else (if t 3 = 0 then 661 else if t 3 = 1 then 656 else 689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1566 else 1619) else if t 2 = 1 then (if t 3 = 0 then 1570 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 1071 else if t 3 = 1 then 1593 else 1612)) else (if t 2 = 0 then (if t 3 = 0 then 2485 else if t 3 = 1 then 2482 else 2501) else if t 2 = 1 then (if t 3 = 0 then 2855 else if t 3 = 1 then 3219 else 3227) else (if t 3 = 0 then 3226 else if t 3 = 1 then 3225 else 3228))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1567 else 1620) else if t 2 = 1 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1563 else 1614) else (if t 3 = 0 then 660 else if t 3 = 1 then 655 else 686)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1565 else 1617) else if t 2 = 1 then (if t 3 = 0 then 1569 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 1070 else if t 3 = 1 then 1592 else 1606)) else (if t 2 = 0 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1582 else 1618) else if t 2 = 1 then (if t 3 = 0 then 1584 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 1073 else if t 3 = 1 then 1595 else 1607))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 917 else 3229) else if t 2 = 1 then (if t 3 = 0 then 270 else if t 3 = 1 then 265 else 296) else (if t 3 = 0 then 2777 else if t 3 = 1 then 2169 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 66 else if t 3 = 1 then 61 else 92) else if t 2 = 1 then (if t 3 = 0 then 854 else if t 3 = 1 then 1588 else 1604) else (if t 3 = 0 then 1598 else if t 3 = 1 then 1596 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 71 else if t 3 = 1 then 69 else 93) else if t 2 = 1 then (if t 3 = 0 then 857 else if t 3 = 1 then 1591 else 1605) else (if t 3 = 0 then 1601 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3116 else (if jt.2.val < 2 then 3223 else 3140)) else (if jt.2.val < 4 then 3221 else (if jt.2.val < 5 then 3222 else 3120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3176 else (if jt.2.val < 2 then 3220 else 3179)) else (if jt.2.val < 4 then 3217 else (if jt.2.val < 5 then 3218 else 3171)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1514 else (if jt.2.val < 2 then 1594 else 1517)) else (if jt.2.val < 4 then 1557 else (if jt.2.val < 5 then 1558 else 1505))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1551 else (if jt.2.val < 2 then 1553 else 1556)) else (if jt.2.val < 4 then 1552 else (if jt.2.val < 5 then 1555 else 1554)))))

checked_coverage fastCoverage0150 pairing0150 template0150 witness0150

theorem coverage0150 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0150) (maskBits m))
    cores template0150 witness0150 := by
  rw [← coresFast_eq]
  exact fastCoverage0150

theorem coverageSize0150 : ∀ q : Pattern,
    (cores (witness0150 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0150 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0150
#print axioms coverageSize0150

noncomputable def pairing0151 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0151 : List (Fin 4935) := templateData0151

noncomputable def witness0151 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1675 else 1676) else if t 2 = 1 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1660 else 1661) else (if t 3 = 0 then 786 else if t 3 = 1 then 741 else 743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1669 else 1670) else if t 2 = 1 then (if t 3 = 0 then 1678 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 1080 else if t 3 = 1 then 1647 else 1651)) else (if t 2 = 0 then (if t 3 = 0 then 2577 else if t 3 = 1 then 2545 else 2547) else if t 2 = 1 then (if t 3 = 0 then 2860 else if t 3 = 1 then 3232 else 3235) else (if t 3 = 0 then 3242 else if t 3 = 1 then 3234 else 3236))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1671 else 1673) else if t 2 = 1 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1656 else 1658) else (if t 3 = 0 then 785 else if t 3 = 1 then 734 else 738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1665 else 1667) else if t 2 = 1 then (if t 3 = 0 then 1677 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 1079 else if t 3 = 1 then 1632 else 1640)) else (if t 2 = 0 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1666 else 1668) else if t 2 = 1 then (if t 3 = 0 then 1685 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 1082 else if t 3 = 1 then 1633 else 1641))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3241 else if t 3 = 1 then 894 else 3240) else if t 2 = 1 then (if t 3 = 0 then 401 else if t 3 = 1 then 350 else 354) else (if t 3 = 0 then 2801 else if t 3 = 1 then 2157 else 2793)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 200 else if t 3 = 1 then 150 else 154) else if t 2 = 1 then (if t 3 = 0 then 863 else if t 3 = 1 then 1630 else 1638) else (if t 3 = 0 then 1689 else if t 3 = 1 then 1634 else 1642)) else (if t 2 = 0 then (if t 3 = 0 then 203 else if t 3 = 1 then 151 else 155) else if t 2 = 1 then (if t 3 = 0 then 866 else if t 3 = 1 then 1631 else 1639) else (if t 3 = 0 then 1691 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3050 else (if jt.2.val < 2 then 3231 else 3072)) else (if jt.2.val < 4 then 3230 else (if jt.2.val < 5 then 3233 else 3068))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3188 else (if jt.2.val < 2 then 3238 else 3190)) else (if jt.2.val < 4 then 3237 else (if jt.2.val < 5 then 3239 else 3185)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1530 else (if jt.2.val < 2 then 1663 else 1534)) else (if jt.2.val < 4 then 1662 else (if jt.2.val < 5 then 1664 else 1527))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1554 else (if jt.2.val < 2 then 1625 else 1556)) else (if jt.2.val < 4 then 1623 else (if jt.2.val < 5 then 1624 else 1551)))))

checked_coverage fastCoverage0151 pairing0151 template0151 witness0151

theorem coverage0151 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0151) (maskBits m))
    cores template0151 witness0151 := by
  rw [← coresFast_eq]
  exact fastCoverage0151

theorem coverageSize0151 : ∀ q : Pattern,
    (cores (witness0151 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0151 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0151
#print axioms coverageSize0151

noncomputable def pairing0152 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0152 : List (Fin 4935) := templateData0152

noncomputable def witness0152 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3262 else if t 3 = 1 then 3254 else 3198) else if t 2 = 1 then (if t 3 = 0 then 3258 else if t 3 = 1 then 3250 else 2797) else (if t 3 = 0 then 2770 else if t 3 = 1 then 2769 else 2989)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3260 else if t 3 = 1 then 3252 else 87) else if t 2 = 1 then (if t 3 = 0 then 3256 else if t 3 = 1 then 3248 else 86) else (if t 3 = 0 then 144 else if t 3 = 1 then 142 else 898)) else (if t 2 = 0 then (if t 3 = 0 then 966 else if t 3 = 1 then 962 else 101) else if t 2 = 1 then (if t 3 = 0 then 965 else if t 3 = 1 then 961 else 100) else (if t 3 = 0 then 1496 else if t 3 = 1 then 172 else 1807))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3261 else if t 3 = 1 then 3253 else 774) else if t 2 = 1 then (if t 3 = 0 then 3257 else if t 3 = 1 then 3249 else 773) else (if t 3 = 0 then 638 else if t 3 = 1 then 636 else 1141)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3259 else if t 3 = 1 then 3251 else 2717) else if t 2 = 1 then (if t 3 = 0 then 3255 else if t 3 = 1 then 3247 else 3295) else (if t 3 = 0 then 3091 else if t 3 = 1 then 3291 else 3299)) else (if t 2 = 0 then (if t 3 = 0 then 2839 else if t 3 = 1 then 2837 else 2724) else if t 2 = 1 then (if t 3 = 0 then 3278 else if t 3 = 1 then 3276 else 3297) else (if t 3 = 0 then 3095 else if t 3 = 1 then 3293 else 3301))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 1499) else if t 2 = 1 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 781) else (if t 3 = 0 then 652 else if t 3 = 1 then 651 else 1143)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3271 else if t 3 = 1 then 3269 else 2719) else if t 2 = 1 then (if t 3 = 0 then 3270 else if t 3 = 1 then 3267 else 3296) else (if t 3 = 0 then 3093 else if t 3 = 1 then 3292 else 3300)) else (if t 2 = 0 then (if t 3 = 0 then 2843 else if t 3 = 1 then 2841 else 2725) else if t 2 = 1 then (if t 3 = 0 then 3280 else if t 3 = 1 then 3279 else 3298) else (if t 3 = 0 then 3097 else if t 3 = 1 then 3294 else 3302))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3246 else (if jt.2.val < 2 then 3266 else 3268)) else (if jt.2.val < 4 then 3263 else (if jt.2.val < 5 then 3265 else 3264))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3245 else (if jt.2.val < 2 then 3275 else 3277)) else (if jt.2.val < 4 then 3272 else (if jt.2.val < 5 then 3274 else 3273)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3244 else (if jt.2.val < 2 then 3289 else 3290)) else (if jt.2.val < 4 then 3286 else (if jt.2.val < 5 then 3288 else 3287))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3243 else (if jt.2.val < 2 then 3282 else 3285)) else (if jt.2.val < 4 then 3281 else (if jt.2.val < 5 then 3284 else 3283)))))

checked_coverage fastCoverage0152 pairing0152 template0152 witness0152

theorem coverage0152 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0152) (maskBits m))
    cores template0152 witness0152 := by
  rw [← coresFast_eq]
  exact fastCoverage0152

theorem coverageSize0152 : ∀ q : Pattern,
    (cores (witness0152 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0152 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0152
#print axioms coverageSize0152

noncomputable def pairing0153 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0153 : List (Fin 4935) := templateData0153

noncomputable def witness0153 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3160 else if t 3 = 1 then 3151 else 3312) else if t 2 = 1 then (if t 3 = 0 then 3156 else if t 3 = 1 then 3144 else 2794) else (if t 3 = 0 then 3004 else if t 3 = 1 then 3002 else 2795)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3158 else if t 3 = 1 then 3149 else 73) else if t 2 = 1 then (if t 3 = 0 then 3154 else if t 3 = 1 then 3138 else 60) else (if t 3 = 0 then 874 else if t 3 = 1 then 853 else 65)) else (if t 2 = 0 then (if t 3 = 0 then 293 else if t 3 = 1 then 277 else 922) else if t 2 = 1 then (if t 3 = 0 then 292 else if t 3 = 1 then 264 else 916) else (if t 3 = 0 then 1790 else if t 3 = 1 then 269 else 1471))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3159 else if t 3 = 1 then 3150 else 760) else if t 2 = 1 then (if t 3 = 0 then 3155 else if t 3 = 1 then 3141 else 748) else (if t 3 = 0 then 1219 else if t 3 = 1 then 1198 else 752)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3157 else if t 3 = 1 then 3145 else 2697) else if t 2 = 1 then (if t 3 = 0 then 3153 else if t 3 = 1 then 3119 else 3126) else (if t 3 = 0 then 3313 else if t 3 = 1 then 3130 else 3134)) else (if t 2 = 0 then (if t 3 = 0 then 2573 else if t 3 = 1 then 2550 else 2880) else if t 2 = 1 then (if t 3 = 0 then 3163 else if t 3 = 1 then 3123 else 3128) else (if t 3 = 0 then 3315 else if t 3 = 1 then 3132 else 3136))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 1774) else if t 2 = 1 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 750) else (if t 3 = 0 then 1223 else if t 3 = 1 then 1200 else 754)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 3162 else if t 3 = 1 then 3146 else 2698) else if t 2 = 1 then (if t 3 = 0 then 3161 else if t 3 = 1 then 3121 else 3127) else (if t 3 = 0 then 3314 else if t 3 = 1 then 3131 else 3135)) else (if t 2 = 0 then (if t 3 = 0 then 2575 else if t 3 = 1 then 2551 else 2881) else if t 2 = 1 then (if t 3 = 0 then 3164 else if t 3 = 1 then 3124 else 3129) else (if t 3 = 0 then 3316 else if t 3 = 1 then 3133 else 3137))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3116 else (if jt.2.val < 2 then 3118 else 3140)) else (if jt.2.val < 4 then 3117 else (if jt.2.val < 5 then 3139 else 3120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3113 else (if jt.2.val < 2 then 3115 else 3143)) else (if jt.2.val < 4 then 3114 else (if jt.2.val < 5 then 3142 else 3122)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3305 else (if jt.2.val < 2 then 3307 else 3311)) else (if jt.2.val < 4 then 3306 else (if jt.2.val < 5 then 3310 else 3309))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3283 else (if jt.2.val < 2 then 3308 else 3285)) else (if jt.2.val < 4 then 3303 else (if jt.2.val < 5 then 3304 else 3243)))))

checked_coverage fastCoverage0153 pairing0153 template0153 witness0153

theorem coverage0153 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0153) (maskBits m))
    cores template0153 witness0153 := by
  rw [← coresFast_eq]
  exact fastCoverage0153

theorem coverageSize0153 : ∀ q : Pattern,
    (cores (witness0153 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0153 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0153
#print axioms coverageSize0153

noncomputable def pairing0154 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0154 : List (Fin 4935) := templateData0154

noncomputable def witness0154 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2606 else if t 3 = 1 then 2602 else 2906) else if t 2 = 1 then (if t 3 = 0 then 2598 else if t 3 = 1 then 2594 else 2648) else (if t 3 = 0 then 3320 else if t 3 = 1 then 3172 else 3182)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2604 else if t 3 = 1 then 2600 else 2107) else if t 2 = 1 then (if t 3 = 0 then 2596 else if t 3 = 1 then 2592 else 2101) else (if t 3 = 0 then 141 else if t 3 = 1 then 139 else 193)) else (if t 2 = 0 then (if t 3 = 0 then 1417 else if t 3 = 1 then 1415 else 1780) else if t 2 = 1 then (if t 3 = 0 then 1413 else if t 3 = 1 then 1411 else 1447) else (if t 3 = 0 then 893 else if t 3 = 1 then 171 else 195))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2605 else if t 3 = 1 then 2601 else 2227) else if t 2 = 1 then (if t 3 = 0 then 2597 else if t 3 = 1 then 2593 else 2221) else (if t 3 = 0 then 635 else if t 3 = 1 then 633 else 685)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2603 else if t 3 = 1 then 2599 else 2902) else if t 2 = 1 then (if t 3 = 0 then 2595 else if t 3 = 1 then 2591 else 2640) else (if t 3 = 0 then 2622 else if t 3 = 1 then 2620 else 2642)) else (if t 2 = 0 then (if t 3 = 0 then 3180 else if t 3 = 1 then 2632 else 3321) else if t 2 = 1 then (if t 3 = 0 then 2897 else if t 3 = 1 then 2629 else 2644) else (if t 3 = 0 then 2900 else if t 3 = 1 then 2636 else 2646))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 243 else 931) else if t 2 = 1 then (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 295) else (if t 3 = 0 then 1787 else if t 3 = 1 then 1463 else 1474)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2615 else if t 3 = 1 then 2614 else 2903) else if t 2 = 1 then (if t 3 = 0 then 2613 else if t 3 = 1 then 2611 else 2641) else (if t 3 = 0 then 2626 else if t 3 = 1 then 2625 else 2643)) else (if t 2 = 0 then (if t 3 = 0 then 3181 else if t 3 = 1 then 2635 else 3322) else if t 2 = 1 then (if t 3 = 0 then 2899 else if t 3 = 1 then 2634 else 2645) else (if t 3 = 0 then 2901 else if t 3 = 1 then 2638 else 2647))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2590 else (if jt.2.val < 2 then 2610 else 2612)) else (if jt.2.val < 4 then 2607 else (if jt.2.val < 5 then 2609 else 2608))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3171 else (if jt.2.val < 2 then 3178 else 3179)) else (if jt.2.val < 4 then 3175 else (if jt.2.val < 5 then 3177 else 3176)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3287 else (if jt.2.val < 2 then 3319 else 3290)) else (if jt.2.val < 4 then 3317 else (if jt.2.val < 5 then 3318 else 3244))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2890 else (if jt.2.val < 2 then 2892 else 2895)) else (if jt.2.val < 4 then 2891 else (if jt.2.val < 5 then 2894 else 2893)))))

checked_coverage fastCoverage0154 pairing0154 template0154 witness0154

theorem coverage0154 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0154) (maskBits m))
    cores template0154 witness0154 := by
  rw [← coresFast_eq]
  exact fastCoverage0154

theorem coverageSize0154 : ∀ q : Pattern,
    (cores (witness0154 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0154 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0154
#print axioms coverageSize0154

noncomputable def pairing0155 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 4 else 1)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0155 : List (Fin 4935) := templateData0155

noncomputable def witness0155 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2964 else if t 3 = 1 then 2953 else 2706) else if t 2 = 1 then (if t 3 = 0 then 2960 else if t 3 = 1 then 2937 else 2939) else (if t 3 = 0 then 3106 else if t 3 = 1 then 3329 else 3330)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2962 else if t 3 = 1 then 2951 else 2098) else if t 2 = 1 then (if t 3 = 0 then 2958 else if t 3 = 1 then 2931 else 2082) else (if t 3 = 0 then 868 else if t 3 = 1 then 830 else 835)) else (if t 2 = 0 then (if t 3 = 0 then 1763 else if t 3 = 1 then 1750 else 1359) else if t 2 = 1 then (if t 3 = 0 then 1756 else if t 3 = 1 then 1730 else 1733) else (if t 3 = 0 then 406 else if t 3 = 1 then 833 else 837))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2963 else if t 3 = 1 then 2952 else 2218) else if t 2 = 1 then (if t 3 = 0 then 2959 else if t 3 = 1 then 2934 else 2206) else (if t 3 = 0 then 1213 else if t 3 = 1 then 1180 else 1184)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2961 else if t 3 = 1 then 2947 else 2699) else if t 2 = 1 then (if t 3 = 0 then 2954 else if t 3 = 1 then 2913 else 2923) else (if t 3 = 0 then 2956 else if t 3 = 1 then 2917 else 2925)) else (if t 2 = 0 then (if t 3 = 0 then 3334 else if t 3 = 1 then 2554 else 3196) else if t 2 = 1 then (if t 3 = 0 then 2502 else if t 3 = 1 then 2919 else 2927) else (if t 3 = 0 then 2504 else if t 3 = 1 then 2921 else 2929))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 994 else 378) else if t 2 = 1 then (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 974) else (if t 3 = 0 then 1375 else if t 3 = 1 then 1796 else 1800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2965 else if t 3 = 1 then 2948 else 2700) else if t 2 = 1 then (if t 3 = 0 then 2955 else if t 3 = 1 then 2915 else 2924) else (if t 3 = 0 then 2957 else if t 3 = 1 then 2918 else 2926)) else (if t 2 = 0 then (if t 3 = 0 then 3335 else if t 3 = 1 then 2555 else 3197) else if t 2 = 1 then (if t 3 = 0 then 2503 else if t 3 = 1 then 2920 else 2928) else (if t 3 = 0 then 2505 else if t 3 = 1 then 2922 else 2930))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2910 else (if jt.2.val < 2 then 2912 else 2933)) else (if jt.2.val < 4 then 2911 else (if jt.2.val < 5 then 2932 else 2914))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3323 else (if jt.2.val < 2 then 3325 else 3328)) else (if jt.2.val < 4 then 3324 else (if jt.2.val < 5 then 3327 else 3326)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3309 else (if jt.2.val < 2 then 3332 else 3311)) else (if jt.2.val < 4 then 3331 else (if jt.2.val < 5 then 3333 else 3305))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2893 else (if jt.2.val < 2 then 2943 else 2895)) else (if jt.2.val < 4 then 2941 else (if jt.2.val < 5 then 2942 else 2890)))))

checked_coverage fastCoverage0155 pairing0155 template0155 witness0155

theorem coverage0155 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0155) (maskBits m))
    cores template0155 witness0155 := by
  rw [← coresFast_eq]
  exact fastCoverage0155

theorem coverageSize0155 : ∀ q : Pattern,
    (cores (witness0155 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0155 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0155
#print axioms coverageSize0155

noncomputable def pairing0156 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0156 : List (Fin 4935) := templateData0156

noncomputable def witness0156 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1025 else 786) else if t 2 = 1 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1023 else 784) else (if t 3 = 0 then 1519 else if t 3 = 1 then 659 else 1826)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1021 else 1080) else if t 2 = 1 then (if t 3 = 0 then 1027 else if t 3 = 1 then 1019 else 1078) else (if t 3 = 0 then 467 else if t 3 = 1 then 1069 else 1090)) else (if t 2 = 0 then (if t 3 = 0 then 3340 else if t 3 = 1 then 3338 else 3242) else if t 2 = 1 then (if t 3 = 0 then 2973 else if t 3 = 1 then 2970 else 2980) else (if t 3 = 0 then 2738 else if t 3 = 1 then 2979 else 2981))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1024 else 785) else if t 2 = 1 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1022 else 783) else (if t 3 = 0 then 1518 else if t 3 = 1 then 658 else 1824)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1020 else 1079) else if t 2 = 1 then (if t 3 = 0 then 1026 else if t 3 = 1 then 1018 else 1077) else (if t 3 = 0 then 466 else if t 3 = 1 then 1068 else 1086)) else (if t 2 = 0 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1082) else if t 2 = 1 then (if t 3 = 0 then 1041 else if t 3 = 1 then 1037 else 1081) else (if t 3 = 0 then 472 else if t 3 = 1 then 1072 else 1087))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2978 else if t 3 = 1 then 2145 else 2801) else if t 2 = 1 then (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 789) else (if t 3 = 0 then 3206 else if t 3 = 1 then 668 else 3341)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1689) else if t 2 = 1 then (if t 3 = 0 then 1050 else if t 3 = 1 then 1045 else 1083) else (if t 3 = 0 then 476 else if t 3 = 1 then 1074 else 1088)) else (if t 2 = 0 then (if t 3 = 0 then 1818 else if t 3 = 1 then 1817 else 1691) else if t 2 = 1 then (if t 3 = 0 then 1056 else if t 3 = 1 then 1054 else 1085) else (if t 3 = 0 then 479 else if t 3 = 1 then 1076 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2910 else (if jt.2.val < 2 then 2977 else 2933)) else (if jt.2.val < 4 then 2975 else (if jt.2.val < 5 then 2976 else 2914))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3273 else (if jt.2.val < 2 then 3339 else 3277)) else (if jt.2.val < 4 then 3336 else (if jt.2.val < 5 then 3337 else 3245)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1811 else (if jt.2.val < 2 then 1822 else 1823)) else (if jt.2.val < 4 then 1819 else (if jt.2.val < 5 then 1821 else 1820))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1016 else (if jt.2.val < 2 then 1059 else 1062)) else (if jt.2.val < 4 then 1058 else (if jt.2.val < 5 then 1061 else 1060)))))

checked_coverage fastCoverage0156 pairing0156 template0156 witness0156

theorem coverage0156 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0156) (maskBits m))
    cores template0156 witness0156 := by
  rw [← coresFast_eq]
  exact fastCoverage0156

theorem coverageSize0156 : ∀ q : Pattern,
    (cores (witness0156 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0156 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0156
#print axioms coverageSize0156

noncomputable def pairing0157 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0157 : List (Fin 4935) := templateData0157

noncomputable def witness0157 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 574 else 1112) else if t 2 = 1 then (if t 3 = 0 then 581 else if t 3 = 1 then 566 else 1108) else (if t 3 = 0 then 1837 else if t 3 = 1 then 568 else 1544)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 579 else if t 3 = 1 then 552 else 553) else if t 2 = 1 then (if t 3 = 0 then 577 else if t 3 = 1 then 532 else 535) else (if t 3 = 0 then 1114 else if t 3 = 1 then 537 else 539)) else (if t 2 = 0 then (if t 3 = 0 then 3215 else if t 3 = 1 then 3209 else 3342) else if t 2 = 1 then (if t 3 = 0 then 2759 else if t 3 = 1 then 2747 else 2749) else (if t 3 = 0 then 2985 else if t 3 = 1 then 2750 else 2751))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 570 else 1110) else if t 2 = 1 then (if t 3 = 0 then 580 else if t 3 = 1 then 556 else 1104) else (if t 3 = 0 then 1836 else if t 3 = 1 then 562 else 1542)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 578 else if t 3 = 1 then 544 else 546) else if t 2 = 1 then (if t 3 = 0 then 576 else if t 3 = 1 then 515 else 520) else (if t 3 = 0 then 1113 else if t 3 = 1 then 524 else 528)) else (if t 2 = 0 then (if t 3 = 0 then 585 else if t 3 = 1 then 545 else 547) else if t 2 = 1 then (if t 3 = 0 then 584 else if t 3 = 1 then 516 else 521) else (if t 3 = 0 then 1117 else if t 3 = 1 then 525 else 529))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2761 else if t 3 = 1 then 2115 else 2984) else if t 2 = 1 then (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 1106) else (if t 3 = 0 then 3343 else if t 3 = 1 then 564 else 3214)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1833) else if t 2 = 1 then (if t 3 = 0 then 588 else if t 3 = 1 then 517 else 522) else (if t 3 = 0 then 1119 else if t 3 = 1 then 526 else 530)) else (if t 2 = 0 then (if t 3 = 0 then 1547 else if t 3 = 1 then 1532 else 1834) else if t 2 = 1 then (if t 3 = 0 then 592 else if t 3 = 1 then 518 else 523) else (if t 3 = 0 then 1121 else if t 3 = 1 then 527 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2590 else (if jt.2.val < 2 then 2746 else 2612)) else (if jt.2.val < 4 then 2745 else (if jt.2.val < 5 then 2748 else 2608))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3122 else (if jt.2.val < 2 then 3212 else 3143)) else (if jt.2.val < 4 then 3211 else (if jt.2.val < 5 then 3213 else 3113)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1827 else (if jt.2.val < 2 then 1829 else 1832)) else (if jt.2.val < 4 then 1828 else (if jt.2.val < 5 then 1831 else 1830))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1060 else (if jt.2.val < 2 then 1100 else 1062)) else (if jt.2.val < 4 then 1098 else (if jt.2.val < 5 then 1099 else 1016)))))

checked_coverage fastCoverage0157 pairing0157 template0157 witness0157

theorem coverage0157 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0157) (maskBits m))
    cores template0157 witness0157 := by
  rw [← coresFast_eq]
  exact fastCoverage0157

theorem coverageSize0157 : ∀ q : Pattern,
    (cores (witness0157 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0157 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0157
#print axioms coverageSize0157

noncomputable def pairing0158 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0158 : List (Fin 4935) := templateData0158

noncomputable def witness0158 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1572 else 1856) else if t 2 = 1 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1564 else 1616) else (if t 3 = 0 then 1134 else if t 3 = 1 then 656 else 689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1570 else 1853) else if t 2 = 1 then (if t 3 = 0 then 1566 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 464 else if t 3 = 1 then 1593 else 1612)) else (if t 2 = 0 then (if t 3 = 0 then 2485 else if t 3 = 1 then 2855 else 2868) else if t 2 = 1 then (if t 3 = 0 then 2482 else if t 3 = 1 then 3219 else 3227) else (if t 3 = 0 then 3344 else if t 3 = 1 then 3225 else 3228))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1571 else 1854) else if t 2 = 1 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1563 else 1614) else (if t 3 = 0 then 1133 else if t 3 = 1 then 655 else 686)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1569 else 1851) else if t 2 = 1 then (if t 3 = 0 then 1565 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 463 else if t 3 = 1 then 1592 else 1606)) else (if t 2 = 0 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1584 else 1852) else if t 2 = 1 then (if t 3 = 0 then 1582 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 471 else if t 3 = 1 then 1595 else 1607))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3224 else if t 3 = 1 then 270 else 3345) else if t 2 = 1 then (if t 3 = 0 then 917 else if t 3 = 1 then 265 else 296) else (if t 3 = 0 then 2988 else if t 3 = 1 then 2169 else 2780)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 66 else if t 3 = 1 then 854 else 876) else if t 2 = 1 then (if t 3 = 0 then 61 else if t 3 = 1 then 1588 else 1604) else (if t 3 = 0 then 1848 else if t 3 = 1 then 1596 else 1608)) else (if t 2 = 0 then (if t 3 = 0 then 71 else if t 3 = 1 then 857 else 877) else if t 2 = 1 then (if t 3 = 0 then 69 else if t 3 = 1 then 1591 else 1605) else (if t 3 = 0 then 1850 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3116 else (if jt.2.val < 2 then 3223 else 3140)) else (if jt.2.val < 4 then 3221 else (if jt.2.val < 5 then 3222 else 3120))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3176 else (if jt.2.val < 2 then 3220 else 3179)) else (if jt.2.val < 4 then 3217 else (if jt.2.val < 5 then 3218 else 3171)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1820 else (if jt.2.val < 2 then 1847 else 1823)) else (if jt.2.val < 4 then 1842 else (if jt.2.val < 5 then 1843 else 1811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1839 else (if jt.2.val < 2 then 1841 else 1846)) else (if jt.2.val < 4 then 1840 else (if jt.2.val < 5 then 1845 else 1844)))))

checked_coverage fastCoverage0158 pairing0158 template0158 witness0158

theorem coverage0158 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0158) (maskBits m))
    cores template0158 witness0158 := by
  rw [← coresFast_eq]
  exact fastCoverage0158

theorem coverageSize0158 : ∀ q : Pattern,
    (cores (witness0158 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0158 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0158
#print axioms coverageSize0158

noncomputable def pairing0159 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.2 then 1 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0159 : List (Fin 4935) := templateData0159

noncomputable def witness0159 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1904 else 1676) else if t 2 = 1 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1891 else 1892) else (if t 3 = 0 then 506 else if t 3 = 1 then 1188 else 1190)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1901 else 1670) else if t 2 = 1 then (if t 3 = 0 then 1907 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 496 else if t 3 = 1 then 1878 else 1882)) else (if t 2 = 0 then (if t 3 = 0 then 2884 else if t 3 = 1 then 2546 else 2547) else if t 2 = 1 then (if t 3 = 0 then 2500 else if t 3 = 1 then 3348 else 3351) else (if t 3 = 0 then 3207 else if t 3 = 1 then 3350 else 3352))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1902 else 1673) else if t 2 = 1 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1887 else 1889) else (if t 3 = 0 then 504 else if t 3 = 1 then 1181 else 1185)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1899 else 1667) else if t 2 = 1 then (if t 3 = 0 then 1905 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 492 else if t 3 = 1 then 1863 else 1871)) else (if t 2 = 0 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1900 else 1668) else if t 2 = 1 then (if t 3 = 0 then 1906 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 493 else if t 3 = 1 then 1864 else 1872))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 3356 else if t 3 = 1 then 176 else 3240) else if t 2 = 1 then (if t 3 = 0 then 102 else if t 3 = 1 then 971 else 975) else (if t 3 = 0 then 2744 else if t 3 = 1 then 2136 else 3001)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 899 else if t 3 = 1 then 152 else 154) else if t 2 = 1 then (if t 3 = 0 then 90 else if t 3 = 1 then 1861 else 1869) else (if t 3 = 0 then 1521 else if t 3 = 1 then 1865 else 1873)) else (if t 2 = 0 then (if t 3 = 0 then 902 else if t 3 = 1 then 153 else 155) else if t 2 = 1 then (if t 3 = 0 then 91 else if t 3 = 1 then 1862 else 1870) else (if t 3 = 0 then 1522 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 3246 else (if jt.2.val < 2 then 3347 else 3268)) else (if jt.2.val < 4 then 3346 else (if jt.2.val < 5 then 3349 else 3264))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3326 else (if jt.2.val < 2 then 3354 else 3328)) else (if jt.2.val < 4 then 3353 else (if jt.2.val < 5 then 3355 else 3323)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1830 else (if jt.2.val < 2 then 1897 else 1832)) else (if jt.2.val < 4 then 1896 else (if jt.2.val < 5 then 1898 else 1827))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1844 else (if jt.2.val < 2 then 1895 else 1846)) else (if jt.2.val < 4 then 1893 else (if jt.2.val < 5 then 1894 else 1839)))))

checked_coverage fastCoverage0159 pairing0159 template0159 witness0159

theorem coverage0159 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0159) (maskBits m))
    cores template0159 witness0159 := by
  rw [← coresFast_eq]
  exact fastCoverage0159

theorem coverageSize0159 : ∀ q : Pattern,
    (cores (witness0159 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0159 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0159
#print axioms coverageSize0159

end Crown.CertificateData
