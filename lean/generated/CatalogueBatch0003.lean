import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0002

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0080 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0080 : List (Fin 4935) := templateData0080

noncomputable def witness0080 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1546) else if t 2 = 1 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 589) else (if t 3 = 0 then 1053 else if t 3 = 1 then 1051 else 601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 193) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2101) else (if t 3 = 0 then 1733 else if t 3 = 1 then 2082 else 2104)) else (if t 2 = 0 then (if t 3 = 0 then 50 else if t 3 = 1 then 48 else 904) else if t 2 = 1 then (if t 3 = 0 then 1342 else if t 3 = 1 then 2090 else 2107) else (if t 3 = 0 then 1359 else if t 3 = 1 then 2098 else 2111))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1545) else if t 2 = 1 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 588) else (if t 3 = 0 then 1052 else if t 3 = 1 then 1050 else 600)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 192) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2100) else (if t 3 = 0 then 1732 else if t 3 = 1 then 2081 else 2103)) else (if t 2 = 0 then (if t 3 = 0 then 49 else if t 3 = 1 then 47 else 903) else if t 2 = 1 then (if t 3 = 0 then 1341 else if t 3 = 1 then 2089 else 2106) else (if t 3 = 0 then 1358 else if t 3 = 1 then 2097 else 2109))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1547) else if t 2 = 1 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 592) else (if t 3 = 0 then 1057 else if t 3 = 1 then 1056 else 602)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 196) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2102) else (if t 3 = 0 then 1735 else if t 3 = 1 then 2083 else 2105)) else (if t 2 = 0 then (if t 3 = 0 then 54 else if t 3 = 1 then 53 else 905) else if t 2 = 1 then (if t 3 = 0 then 1344 else if t 3 = 1 then 2091 else 2108) else (if t 3 = 0 then 1361 else if t 3 = 1 then 2099 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2046 else (if jt.2.val < 2 then 2066 else 2068)) else (if jt.2.val < 4 then 2063 else (if jt.2.val < 5 then 2065 else 2064))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2322 else (if jt.2.val < 2 then 2332 else 2333)) else (if jt.2.val < 4 then 2329 else (if jt.2.val < 5 then 2331 else 2330)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2323 else (if jt.2.val < 2 then 2327 else 2328)) else (if jt.2.val < 4 then 2324 else (if jt.2.val < 5 then 2326 else 2325))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2043 else (if jt.2.val < 2 then 2093 else 2096)) else (if jt.2.val < 4 then 2092 else (if jt.2.val < 5 then 2095 else 2094)))))

checked_coverage fastCoverage0080 pairing0080 template0080 witness0080

theorem coverage0080 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0080) (maskBits m))
    cores template0080 witness0080 := by
  rw [← coresFast_eq]
  exact fastCoverage0080

theorem coverageSize0080 : ∀ q : Pattern,
    (cores (witness0080 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0080 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0080
#print axioms coverageSize0080

noncomputable def pairing0081 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0081 : List (Fin 4935) := templateData0081

noncomputable def witness0081 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 2117) else if t 2 = 1 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 567) else (if t 3 = 0 then 780 else if t 3 = 1 then 756 else 1109)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 171) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1411) else (if t 3 = 0 then 1450 else if t 3 = 1 then 1412 else 1413)) else (if t 2 = 0 then (if t 3 = 0 then 1012 else if t 3 = 1 then 992 else 173) else if t 2 = 1 then (if t 3 = 0 then 1777 else if t 3 = 1 then 1414 else 1415) else (if t 3 = 0 then 2119 else if t 3 = 1 then 1416 else 1417))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 2115) else if t 2 = 1 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 558) else (if t 3 = 0 then 779 else if t 3 = 1 then 749 else 1106)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 162) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1393) else (if t 3 = 0 then 1449 else if t 3 = 1 then 1396 else 1398)) else (if t 2 = 0 then (if t 3 = 0 then 1011 else if t 3 = 1 then 989 else 168) else if t 2 = 1 then (if t 3 = 0 then 1776 else if t 3 = 1 then 1400 else 1402) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1404 else 1406))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 2116) else if t 2 = 1 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 559) else (if t 3 = 0 then 782 else if t 3 = 1 then 750 else 1107)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 163) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1394) else (if t 3 = 0 then 1451 else if t 3 = 1 then 1397 else 1399)) else (if t 2 = 0 then (if t 3 = 0 then 1013 else if t 3 = 1 then 990 else 169) else if t 2 = 1 then (if t 3 = 0 then 1778 else if t 3 = 1 then 1401 else 1403) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1405 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1386 else (if jt.2.val < 2 then 1388 else 1410)) else (if jt.2.val < 4 then 1387 else (if jt.2.val < 5 then 1409 else 1390))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2280 else (if jt.2.val < 2 then 2282 else 2285)) else (if jt.2.val < 4 then 2281 else (if jt.2.val < 5 then 2284 else 2283)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1380 else (if jt.2.val < 2 then 1382 else 1426)) else (if jt.2.val < 4 then 1381 else (if jt.2.val < 5 then 1425 else 1395))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2094 else (if jt.2.val < 2 then 2114 else 2096)) else (if jt.2.val < 4 then 2112 else (if jt.2.val < 5 then 2113 else 2043)))))

checked_coverage fastCoverage0081 pairing0081 template0081 witness0081

theorem coverage0081 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0081) (maskBits m))
    cores template0081 witness0081 := by
  rw [← coresFast_eq]
  exact fastCoverage0081

theorem coverageSize0081 : ∀ q : Pattern,
    (cores (witness0081 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0081 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0081
#print axioms coverageSize0081

noncomputable def pairing0082 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0082 : List (Fin 4935) := templateData0082

noncomputable def witness0082 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 807 else 201) else if t 2 = 1 then (if t 3 = 0 then 803 else if t 3 = 1 then 799 else 864) else (if t 3 = 0 then 2146 else if t 3 = 1 then 1813 else 1690)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 809 else if t 3 = 1 then 805 else 199) else if t 2 = 1 then (if t 3 = 0 then 801 else if t 3 = 1 then 797 else 862) else (if t 3 = 0 then 833 else if t 3 = 1 then 830 else 868)) else (if t 2 = 0 then (if t 3 = 0 then 1471 else if t 3 = 1 then 65 else 2129) else if t 2 = 1 then (if t 3 = 0 then 269 else if t 3 = 1 then 853 else 874) else (if t 3 = 0 then 279 else if t 3 = 1 then 859 else 875))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 806 else 200) else if t 2 = 1 then (if t 3 = 0 then 802 else if t 3 = 1 then 798 else 863) else (if t 3 = 0 then 2145 else if t 3 = 1 then 1812 else 1689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 808 else if t 3 = 1 then 804 else 198) else if t 2 = 1 then (if t 3 = 0 then 800 else if t 3 = 1 then 796 else 861) else (if t 3 = 0 then 832 else if t 3 = 1 then 829 else 867)) else (if t 2 = 0 then (if t 3 = 0 then 1470 else if t 3 = 1 then 64 else 2127) else if t 2 = 1 then (if t 3 = 0 then 268 else if t 3 = 1 then 852 else 870) else (if t 3 = 0 then 278 else if t 3 = 1 then 858 else 872))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 822 else 203) else if t 2 = 1 then (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 866) else (if t 3 = 0 then 2147 else if t 3 = 1 then 1817 else 1691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 202) else if t 2 = 1 then (if t 3 = 0 then 819 else if t 3 = 1 then 816 else 865) else (if t 3 = 0 then 839 else if t 3 = 1 then 838 else 869)) else (if t 2 = 0 then (if t 3 = 0 then 1472 else if t 3 = 1 then 70 else 2128) else if t 2 = 1 then (if t 3 = 0 then 274 else if t 3 = 1 then 856 else 871) else (if t 3 = 0 then 281 else if t 3 = 1 then 860 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 795 else (if jt.2.val < 2 then 815 else 817)) else (if jt.2.val < 4 then 812 else (if jt.2.val < 5 then 814 else 813))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2288 else (if jt.2.val < 2 then 2293 else 2294)) else (if jt.2.val < 4 then 2290 else (if jt.2.val < 5 then 2292 else 2291)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2325 else (if jt.2.val < 2 then 2336 else 2328)) else (if jt.2.val < 4 then 2334 else (if jt.2.val < 5 then 2335 else 2323))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1224 else (if jt.2.val < 2 then 1230 else 1233)) else (if jt.2.val < 4 then 1229 else (if jt.2.val < 5 then 1232 else 1231)))))

checked_coverage fastCoverage0082 pairing0082 template0082 witness0082

theorem coverage0082 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0082) (maskBits m))
    cores template0082 witness0082 := by
  rw [← coresFast_eq]
  exact fastCoverage0082

theorem coverageSize0082 : ∀ q : Pattern,
    (cores (witness0082 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0082 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0082
#print axioms coverageSize0082

noncomputable def pairing0083 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0083 : List (Fin 4935) := templateData0083

noncomputable def witness0083 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 379 else 896) else if t 2 = 1 then (if t 3 = 0 then 384 else if t 3 = 1 then 356 else 357) else (if t 3 = 0 then 1498 else if t 3 = 1 then 1489 else 2159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 386 else if t 3 = 1 then 371 else 892) else if t 2 = 1 then (if t 3 = 0 then 382 else if t 3 = 1 then 336 else 340) else (if t 3 = 0 then 394 else if t 3 = 1 then 339 else 341)) else (if t 2 = 0 then (if t 3 = 0 then 2140 else if t 3 = 1 then 373 else 1496) else if t 2 = 1 then (if t 3 = 0 then 928 else if t 3 = 1 then 342 else 344) else (if t 3 = 0 then 929 else if t 3 = 1 then 343 else 345))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 375 else 894) else if t 2 = 1 then (if t 3 = 0 then 383 else if t 3 = 1 then 346 else 350) else (if t 3 = 0 then 1497 else if t 3 = 1 then 1483 else 2157)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 385 else if t 3 = 1 then 363 else 888) else if t 2 = 1 then (if t 3 = 0 then 381 else if t 3 = 1 then 318 else 324) else (if t 3 = 0 then 393 else if t 3 = 1 then 322 else 326)) else (if t 2 = 0 then (if t 3 = 0 then 2139 else if t 3 = 1 then 367 else 1494) else if t 2 = 1 then (if t 3 = 0 then 924 else if t 3 = 1 then 328 else 332) else (if t 3 = 0 then 926 else if t 3 = 1 then 330 else 334))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 376 else 895) else if t 2 = 1 then (if t 3 = 0 then 390 else if t 3 = 1 then 347 else 351) else (if t 3 = 0 then 1499 else if t 3 = 1 then 1484 else 2158)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 391 else if t 3 = 1 then 364 else 889) else if t 2 = 1 then (if t 3 = 0 then 389 else if t 3 = 1 then 320 else 325) else (if t 3 = 0 then 397 else if t 3 = 1 then 323 else 327)) else (if t 2 = 0 then (if t 3 = 0 then 2141 else if t 3 = 1 then 368 else 1495) else if t 2 = 1 then (if t 3 = 0 then 925 else if t 3 = 1 then 329 else 333) else (if t 3 = 0 then 927 else if t 3 = 1 then 331 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 315 else (if jt.2.val < 2 then 317 else 338)) else (if jt.2.val < 4 then 316 else (if jt.2.val < 5 then 337 else 319))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2337 else (if jt.2.val < 2 then 2339 else 2342)) else (if jt.2.val < 4 then 2338 else (if jt.2.val < 5 then 2341 else 2340)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1395 else (if jt.2.val < 2 then 1492 else 1426)) else (if jt.2.val < 4 then 1491 else (if jt.2.val < 5 then 1493 else 1380))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1231 else (if jt.2.val < 2 then 1251 else 1233)) else (if jt.2.val < 4 then 1245 else (if jt.2.val < 5 then 1246 else 1224)))))

checked_coverage fastCoverage0083 pairing0083 template0083 witness0083

theorem coverage0083 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0083) (maskBits m))
    cores template0083 witness0083 := by
  rw [← coresFast_eq]
  exact fastCoverage0083

theorem coverageSize0083 : ∀ q : Pattern,
    (cores (witness0083 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0083 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0083
#print axioms coverageSize0083

noncomputable def pairing0084 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0084 : List (Fin 4935) := templateData0084

noncomputable def witness0084 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 428 else 1116) else if t 2 = 1 then (if t 3 = 0 then 430 else if t 3 = 1 then 426 else 1114) else (if t 3 = 0 then 1519 else if t 3 = 1 then 467 else 2150)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 424 else if t 3 = 1 then 420 else 496) else if t 2 = 1 then (if t 3 = 0 then 422 else if t 3 = 1 then 418 else 488) else (if t 3 = 0 then 1132 else if t 3 = 1 then 462 else 490)) else (if t 2 = 0 then (if t 3 = 0 then 2125 else if t 3 = 1 then 1507 else 1523) else if t 2 = 1 then (if t 3 = 0 then 448 else if t 3 = 1 then 445 else 489) else (if t 3 = 0 then 1138 else if t 3 = 1 then 475 else 491))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 427 else 1115) else if t 2 = 1 then (if t 3 = 0 then 429 else if t 3 = 1 then 425 else 1113) else (if t 3 = 0 then 1518 else if t 3 = 1 then 466 else 2148)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 423 else if t 3 = 1 then 419 else 492) else if t 2 = 1 then (if t 3 = 0 then 421 else if t 3 = 1 then 417 else 480) else (if t 3 = 0 then 1131 else if t 3 = 1 then 461 else 484)) else (if t 2 = 0 then (if t 3 = 0 then 2124 else if t 3 = 1 then 1506 else 1521) else if t 2 = 1 then (if t 3 = 0 then 447 else if t 3 = 1 then 444 else 482) else (if t 3 = 0 then 1137 else if t 3 = 1 then 474 else 486))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 441 else 1118) else if t 2 = 1 then (if t 3 = 0 then 442 else if t 3 = 1 then 440 else 1117) else (if t 3 = 0 then 1520 else if t 3 = 1 then 472 else 2149)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 439 else if t 3 = 1 then 437 else 493) else if t 2 = 1 then (if t 3 = 0 then 438 else if t 3 = 1 then 436 else 481) else (if t 3 = 0 then 1135 else if t 3 = 1 then 470 else 485)) else (if t 2 = 0 then (if t 3 = 0 then 2126 else if t 3 = 1 then 1511 else 1522) else if t 2 = 1 then (if t 3 = 0 then 454 else if t 3 = 1 then 453 else 483) else (if t 3 = 0 then 1139 else if t 3 = 1 then 478 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 315 else (if jt.2.val < 2 then 435 else 338)) else (if jt.2.val < 4 then 433 else (if jt.2.val < 5 then 434 else 319))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2330 else (if jt.2.val < 2 then 2345 else 2333)) else (if jt.2.val < 4 then 2343 else (if jt.2.val < 5 then 2344 else 2322)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1505 else (if jt.2.val < 2 then 1516 else 1517)) else (if jt.2.val < 4 then 1513 else (if jt.2.val < 5 then 1515 else 1514))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1272 else (if jt.2.val < 2 then 1274 else 1279)) else (if jt.2.val < 4 then 1273 else (if jt.2.val < 5 then 1278 else 1277)))))

checked_coverage fastCoverage0084 pairing0084 template0084 witness0084

theorem coverage0084 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0084) (maskBits m))
    cores template0084 witness0084 := by
  rw [← coresFast_eq]
  exact fastCoverage0084

theorem coverageSize0084 : ∀ q : Pattern,
    (cores (witness0084 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0084 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0084
#print axioms coverageSize0084

noncomputable def pairing0085 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0085 : List (Fin 4935) := templateData0085

noncomputable def witness0085 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1205 else 575) else if t 2 = 1 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1201 else 568) else (if t 3 = 0 then 2161 else if t 3 = 1 then 757 else 1544)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1214 else if t 3 = 1 then 1187 else 1188) else if t 2 = 1 then (if t 3 = 0 then 1210 else if t 3 = 1 then 1167 else 1170) else (if t 3 = 0 then 694 else if t 3 = 1 then 1172 else 1174)) else (if t 2 = 0 then (if t 3 = 0 then 1376 else if t 3 = 1 then 1801 else 2138) else if t 2 = 1 then (if t 3 = 0 then 1211 else if t 3 = 1 then 1169 else 1171) else (if t 3 = 0 then 695 else if t 3 = 1 then 1173 else 1175))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1203 else 572) else if t 2 = 1 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1197 else 562) else (if t 3 = 0 then 2160 else if t 3 = 1 then 751 else 1542)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1212 else if t 3 = 1 then 1179 else 1181) else if t 2 = 1 then (if t 3 = 0 then 1206 else if t 3 = 1 then 1151 else 1155) else (if t 3 = 0 then 690 else if t 3 = 1 then 1159 else 1163)) else (if t 2 = 0 then (if t 3 = 0 then 1374 else if t 3 = 1 then 1795 else 2136) else if t 2 = 1 then (if t 3 = 0 then 1208 else if t 3 = 1 then 1153 else 1157) else (if t 3 = 0 then 692 else if t 3 = 1 then 1161 else 1165))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1204 else 573) else if t 2 = 1 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1198 else 563) else (if t 3 = 0 then 2162 else if t 3 = 1 then 752 else 1543)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1213 else if t 3 = 1 then 1180 else 1182) else if t 2 = 1 then (if t 3 = 0 then 1207 else if t 3 = 1 then 1152 else 1156) else (if t 3 = 0 then 691 else if t 3 = 1 then 1160 else 1164)) else (if t 2 = 0 then (if t 3 = 0 then 1375 else if t 3 = 1 then 1796 else 2137) else if t 2 = 1 then (if t 3 = 0 then 1209 else if t 3 = 1 then 1154 else 1158) else (if t 3 = 0 then 693 else if t 3 = 1 then 1162 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 795 else (if jt.2.val < 2 then 1150 else 817)) else (if jt.2.val < 4 then 1149 else (if jt.2.val < 5 then 1168 else 813))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2283 else (if jt.2.val < 2 then 2311 else 2285)) else (if jt.2.val < 4 then 2310 else (if jt.2.val < 5 then 2312 else 2280)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2346 else (if jt.2.val < 2 then 2348 else 2351)) else (if jt.2.val < 4 then 2347 else (if jt.2.val < 5 then 2350 else 2349))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1277 else (if jt.2.val < 2 then 1294 else 1279)) else (if jt.2.val < 4 then 1292 else (if jt.2.val < 5 then 1293 else 1272)))))

checked_coverage fastCoverage0085 pairing0085 template0085 witness0085

theorem coverage0085 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0085) (maskBits m))
    cores template0085 witness0085 := by
  rw [← coresFast_eq]
  exact fastCoverage0085

theorem coverageSize0085 : ∀ q : Pattern,
    (cores (witness0085 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0085 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0085
#print axioms coverageSize0085

noncomputable def pairing0086 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0086 : List (Fin 4935) := templateData0086

noncomputable def witness0086 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1574 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1570 else 1853) else (if t 3 = 0 then 661 else if t 3 = 1 then 1071 else 1094)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1566 else 1619) else if t 2 = 1 then (if t 3 = 0 then 1564 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 656 else if t 3 = 1 then 1593 else 1612)) else (if t 2 = 0 then (if t 3 = 0 then 918 else if t 3 = 1 then 62 else 95) else if t 2 = 1 then (if t 3 = 0 then 266 else if t 3 = 1 then 1589 else 1611) else (if t 3 = 0 then 2170 else if t 3 = 1 then 1597 else 1613))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1573 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1569 else 1851) else (if t 3 = 0 then 660 else if t 3 = 1 then 1070 else 1092)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1565 else 1617) else if t 2 = 1 then (if t 3 = 0 then 1563 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 655 else if t 3 = 1 then 1592 else 1606)) else (if t 2 = 0 then (if t 3 = 0 then 917 else if t 3 = 1 then 61 else 92) else if t 2 = 1 then (if t 3 = 0 then 265 else if t 3 = 1 then 1588 else 1604) else (if t 3 = 0 then 2169 else if t 3 = 1 then 1596 else 1608))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1586 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1584 else 1852) else (if t 3 = 0 then 665 else if t 3 = 1 then 1073 else 1093)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1582 else 1618) else if t 2 = 1 then (if t 3 = 0 then 1581 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 663 else if t 3 = 1 then 1595 else 1607)) else (if t 2 = 0 then (if t 3 = 0 then 920 else if t 3 = 1 then 69 else 93) else if t 2 = 1 then (if t 3 = 0 then 273 else if t 3 = 1 then 1591 else 1605) else (if t 3 = 0 then 2171 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1386 else (if jt.2.val < 2 then 1579 else 1410)) else (if jt.2.val < 4 then 1577 else (if jt.2.val < 5 then 1578 else 1390))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2291 else (if jt.2.val < 2 then 2315 else 2294)) else (if jt.2.val < 4 then 2313 else (if jt.2.val < 5 then 2314 else 2288)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1514 else (if jt.2.val < 2 then 1594 else 1517)) else (if jt.2.val < 4 then 1557 else (if jt.2.val < 5 then 1558 else 1505))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2163 else (if jt.2.val < 2 then 2165 else 2168)) else (if jt.2.val < 4 then 2164 else (if jt.2.val < 5 then 2167 else 2166)))))

checked_coverage fastCoverage0086 pairing0086 template0086 witness0086

theorem coverage0086 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0086) (maskBits m))
    cores template0086 witness0086 := by
  rw [← coresFast_eq]
  exact fastCoverage0086

theorem coverageSize0086 : ∀ q : Pattern,
    (cores (witness0086 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0086 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0086
#print axioms coverageSize0086

noncomputable def pairing0087 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0087 : List (Fin 4935) := templateData0087

noncomputable def witness0087 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2219 else 1676) else if t 2 = 1 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2213 else 1661) else (if t 3 = 0 then 1148 else if t 3 = 1 then 742 else 743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2207 else 1892) else if t 2 = 1 then (if t 3 = 0 then 2222 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 688 else if t 3 = 1 then 2196 else 2200)) else (if t 2 = 0 then (if t 3 = 0 then 308 else if t 3 = 1 then 979 else 980) else if t 2 = 1 then (if t 3 = 0 then 298 else if t 3 = 1 then 2195 else 2199) else (if t 3 = 0 then 1475 else if t 3 = 1 then 2197 else 2201))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2217 else 1673) else if t 2 = 1 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2211 else 1658) else (if t 3 = 0 then 1146 else if t 3 = 1 then 736 else 738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2205 else 1889) else if t 2 = 1 then (if t 3 = 0 then 2220 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 684 else if t 3 = 1 then 2181 else 2189)) else (if t 2 = 0 then (if t 3 = 0 then 306 else if t 3 = 1 then 973 else 975) else if t 2 = 1 then (if t 3 = 0 then 294 else if t 3 = 1 then 2179 else 2187) else (if t 3 = 0 then 1473 else if t 3 = 1 then 2183 else 2191))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2218 else 1674) else if t 2 = 1 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2212 else 1659) else (if t 3 = 0 then 1147 else if t 3 = 1 then 737 else 739)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2206 else 1890) else if t 2 = 1 then (if t 3 = 0 then 2221 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 685 else if t 3 = 1 then 2182 else 2190)) else (if t 2 = 0 then (if t 3 = 0 then 307 else if t 3 = 1 then 974 else 976) else if t 2 = 1 then (if t 3 = 0 then 295 else if t 3 = 1 then 2180 else 2188) else (if t 3 = 0 then 1474 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2046 else (if jt.2.val < 2 then 2176 else 2068)) else (if jt.2.val < 4 then 2175 else (if jt.2.val < 5 then 2194 else 2064))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2340 else (if jt.2.val < 2 then 2356 else 2342)) else (if jt.2.val < 4 then 2355 else (if jt.2.val < 5 then 2357 else 2337)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2349 else (if jt.2.val < 2 then 2353 else 2351)) else (if jt.2.val < 4 then 2352 else (if jt.2.val < 5 then 2354 else 2346))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2166 else (if jt.2.val < 2 then 2216 else 2168)) else (if jt.2.val < 4 then 2214 else (if jt.2.val < 5 then 2215 else 2163)))))

checked_coverage fastCoverage0087 pairing0087 template0087 witness0087

theorem coverage0087 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0087) (maskBits m))
    cores template0087 witness0087 := by
  rw [← coresFast_eq]
  exact fastCoverage0087

theorem coverageSize0087 : ∀ q : Pattern,
    (cores (witness0087 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0087 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0087
#print axioms coverageSize0087

noncomputable def pairing0088 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0088 : List (Fin 4935) := templateData0088

noncomputable def witness0088 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1816) else if t 2 = 1 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 1051) else (if t 3 = 0 then 591 else if t 3 = 1 then 589 else 601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 835) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2082) else (if t 3 = 0 then 1447 else if t 3 = 1 then 2101 else 2104)) else (if t 2 = 0 then (if t 3 = 0 then 50 else if t 3 = 1 then 48 else 75) else if t 2 = 1 then (if t 3 = 0 then 1342 else if t 3 = 1 then 2090 else 2098) else (if t 3 = 0 then 1780 else if t 3 = 1 then 2107 else 2111))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1815) else if t 2 = 1 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 1050) else (if t 3 = 0 then 590 else if t 3 = 1 then 588 else 600)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 834) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2081) else (if t 3 = 0 then 1446 else if t 3 = 1 then 2100 else 2103)) else (if t 2 = 0 then (if t 3 = 0 then 49 else if t 3 = 1 then 47 else 74) else if t 2 = 1 then (if t 3 = 0 then 1341 else if t 3 = 1 then 2089 else 2097) else (if t 3 = 0 then 1779 else if t 3 = 1 then 2106 else 2109))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1818) else if t 2 = 1 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 1056) else (if t 3 = 0 then 593 else if t 3 = 1 then 592 else 602)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 840) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2083) else (if t 3 = 0 then 1448 else if t 3 = 1 then 2102 else 2105)) else (if t 2 = 0 then (if t 3 = 0 then 54 else if t 3 = 1 then 53 else 77) else if t 2 = 1 then (if t 3 = 0 then 1344 else if t 3 = 1 then 2091 else 2099) else (if t 3 = 0 then 1781 else if t 3 = 1 then 2108 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2046 else (if jt.2.val < 2 then 2066 else 2068)) else (if jt.2.val < 4 then 2063 else (if jt.2.val < 5 then 2065 else 2064))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2322 else (if jt.2.val < 2 then 2332 else 2333)) else (if jt.2.val < 4 then 2329 else (if jt.2.val < 5 then 2331 else 2330)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2232 else (if jt.2.val < 2 then 2240 else 2243)) else (if jt.2.val < 4 then 2239 else (if jt.2.val < 5 then 2242 else 2241))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2358 else (if jt.2.val < 2 then 2362 else 2363)) else (if jt.2.val < 4 then 2359 else (if jt.2.val < 5 then 2361 else 2360)))))

checked_coverage fastCoverage0088 pairing0088 template0088 witness0088

theorem coverage0088 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0088) (maskBits m))
    cores template0088 witness0088 := by
  rw [← coresFast_eq]
  exact fastCoverage0088

theorem coverageSize0088 : ∀ q : Pattern,
    (cores (witness0088 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0088 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0088
#print axioms coverageSize0088

noncomputable def pairing0089 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0089 : List (Fin 4935) := templateData0089

noncomputable def witness0089 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 2146) else if t 2 = 1 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 1049) else (if t 3 = 0 then 780 else if t 3 = 1 then 778 else 790)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 833) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1730) else (if t 3 = 0 then 1450 else if t 3 = 1 then 1753 else 1756)) else (if t 2 = 0 then (if t 3 = 0 then 258 else if t 3 = 1 then 256 else 279) else if t 2 = 1 then (if t 3 = 0 then 1353 else if t 3 = 1 then 1747 else 1750) else (if t 3 = 0 then 2119 else if t 3 = 1 then 1762 else 1763))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 2145) else if t 2 = 1 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 1048) else (if t 3 = 0 then 779 else if t 3 = 1 then 777 else 789)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 832) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1729) else (if t 3 = 0 then 1449 else if t 3 = 1 then 1752 else 1755)) else (if t 2 = 0 then (if t 3 = 0 then 257 else if t 3 = 1 then 255 else 278) else if t 2 = 1 then (if t 3 = 0 then 1352 else if t 3 = 1 then 1746 else 1749) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1758 else 1760))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 2147) else if t 2 = 1 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 1055) else (if t 3 = 0 then 782 else if t 3 = 1 then 781 else 791)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 839) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1734) else (if t 3 = 0 then 1451 else if t 3 = 1 then 1754 else 1757)) else (if t 2 = 0 then (if t 3 = 0 then 262 else if t 3 = 1 then 261 else 281) else if t 2 = 1 then (if t 3 = 0 then 1355 else if t 3 = 1 then 1748 else 1751) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1759 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1695 else (if jt.2.val < 2 then 1715 else 1717)) else (if jt.2.val < 4 then 1712 else (if jt.2.val < 5 then 1714 else 1713))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2268 else (if jt.2.val < 2 then 2278 else 2279)) else (if jt.2.val < 4 then 2275 else (if jt.2.val < 5 then 2277 else 2276)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1917 else (if jt.2.val < 2 then 1923 else 1928)) else (if jt.2.val < 4 then 1922 else (if jt.2.val < 5 then 1927 else 1926))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2360 else (if jt.2.val < 2 then 2366 else 2363)) else (if jt.2.val < 4 then 2364 else (if jt.2.val < 5 then 2365 else 2358)))))

checked_coverage fastCoverage0089 pairing0089 template0089 witness0089

theorem coverage0089 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0089) (maskBits m))
    cores template0089 witness0089 := by
  rw [← coresFast_eq]
  exact fastCoverage0089

theorem coverageSize0089 : ∀ q : Pattern,
    (cores (witness0089 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0089 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0089
#print axioms coverageSize0089

noncomputable def pairing0090 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0090 : List (Fin 4935) := templateData0090

noncomputable def witness0090 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 183 else 201) else if t 2 = 1 then (if t 3 = 0 then 178 else if t 3 = 1 then 156 else 157) else (if t 3 = 0 then 2117 else if t 3 = 1 then 1537 else 1835)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 185 else if t 3 = 1 then 181 else 199) else if t 2 = 1 then (if t 3 = 0 then 170 else if t 3 = 1 then 136 else 140) else (if t 3 = 0 then 171 else if t 3 = 1 then 139 else 141)) else (if t 2 = 0 then (if t 3 = 0 then 1807 else if t 3 = 1 then 898 else 2129) else if t 2 = 1 then (if t 3 = 0 then 172 else if t 3 = 1 then 142 else 144) else (if t 3 = 0 then 173 else if t 3 = 1 then 143 else 145))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 182 else 200) else if t 2 = 1 then (if t 3 = 0 then 174 else if t 3 = 1 then 146 else 150) else (if t 3 = 0 then 2115 else if t 3 = 1 then 1531 else 1833)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 184 else if t 3 = 1 then 180 else 198) else if t 2 = 1 then (if t 3 = 0 then 160 else if t 3 = 1 then 117 else 124) else (if t 3 = 0 then 162 else if t 3 = 1 then 121 else 126)) else (if t 2 = 0 then (if t 3 = 0 then 1806 else if t 3 = 1 then 897 else 2127) else if t 2 = 1 then (if t 3 = 0 then 166 else if t 3 = 1 then 128 else 132) else (if t 3 = 0 then 168 else if t 3 = 1 then 130 else 134))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 189 else 203) else if t 2 = 1 then (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 151) else (if t 3 = 0 then 2116 else if t 3 = 1 then 1532 else 1834)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 202) else if t 2 = 1 then (if t 3 = 0 then 161 else if t 3 = 1 then 119 else 125) else (if t 3 = 0 then 163 else if t 3 = 1 then 122 else 127)) else (if t 2 = 0 then (if t 3 = 0 then 1808 else if t 3 = 1 then 901 else 2128) else if t 2 = 1 then (if t 3 = 0 then 167 else if t 3 = 1 then 129 else 133) else (if t 3 = 0 then 169 else if t 3 = 1 then 131 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 114 else (if jt.2.val < 2 then 116 else 138)) else (if jt.2.val < 4 then 115 else (if jt.2.val < 5 then 137 else 118))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2295 else (if jt.2.val < 2 then 2297 else 2300)) else (if jt.2.val < 4 then 2296 else (if jt.2.val < 5 then 2299 else 2298)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2241 else (if jt.2.val < 2 then 2249 else 2243)) else (if jt.2.val < 4 then 2247 else (if jt.2.val < 5 then 2248 else 2232))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 108 else (if jt.2.val < 2 then 110 else 165)) else (if jt.2.val < 4 then 109 else (if jt.2.val < 5 then 164 else 123)))))

checked_coverage fastCoverage0090 pairing0090 template0090 witness0090

theorem coverage0090 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0090) (maskBits m))
    cores template0090 witness0090 := by
  rw [← coresFast_eq]
  exact fastCoverage0090

theorem coverageSize0090 : ∀ q : Pattern,
    (cores (witness0090 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0090 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0090
#print axioms coverageSize0090

noncomputable def pairing0091 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0091 : List (Fin 4935) := templateData0091

noncomputable def witness0091 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 384 else 402) else if t 2 = 1 then (if t 3 = 0 then 379 else if t 3 = 1 then 356 else 357) else (if t 3 = 0 then 1775 else if t 3 = 1 then 1489 else 2159)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 386 else if t 3 = 1 then 382 else 400) else if t 2 = 1 then (if t 3 = 0 then 371 else if t 3 = 1 then 336 else 340) else (if t 3 = 0 then 372 else if t 3 = 1 then 339 else 341)) else (if t 2 = 0 then (if t 3 = 0 then 2140 else if t 3 = 1 then 928 else 1790) else if t 2 = 1 then (if t 3 = 0 then 373 else if t 3 = 1 then 342 else 344) else (if t 3 = 0 then 374 else if t 3 = 1 then 343 else 345))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 383 else 401) else if t 2 = 1 then (if t 3 = 0 then 375 else if t 3 = 1 then 346 else 350) else (if t 3 = 0 then 1773 else if t 3 = 1 then 1483 else 2157)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 385 else if t 3 = 1 then 381 else 399) else if t 2 = 1 then (if t 3 = 0 then 363 else if t 3 = 1 then 318 else 324) else (if t 3 = 0 then 365 else if t 3 = 1 then 322 else 326)) else (if t 2 = 0 then (if t 3 = 0 then 2139 else if t 3 = 1 then 924 else 1788) else if t 2 = 1 then (if t 3 = 0 then 367 else if t 3 = 1 then 328 else 332) else (if t 3 = 0 then 369 else if t 3 = 1 then 330 else 334))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 390 else 404) else if t 2 = 1 then (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 351) else (if t 3 = 0 then 1774 else if t 3 = 1 then 1484 else 2158)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 403) else if t 2 = 1 then (if t 3 = 0 then 364 else if t 3 = 1 then 320 else 325) else (if t 3 = 0 then 366 else if t 3 = 1 then 323 else 327)) else (if t 2 = 0 then (if t 3 = 0 then 2141 else if t 3 = 1 then 925 else 1789) else if t 2 = 1 then (if t 3 = 0 then 368 else if t 3 = 1 then 329 else 333) else (if t 3 = 0 then 370 else if t 3 = 1 then 331 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 315 else (if jt.2.val < 2 then 317 else 338)) else (if jt.2.val < 4 then 316 else (if jt.2.val < 5 then 337 else 319))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2337 else (if jt.2.val < 2 then 2339 else 2342)) else (if jt.2.val < 4 then 2338 else (if jt.2.val < 5 then 2341 else 2340)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1926 else (if jt.2.val < 2 then 1940 else 1928)) else (if jt.2.val < 4 then 1938 else (if jt.2.val < 5 then 1939 else 1917))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 123 else (if jt.2.val < 2 then 361 else 165)) else (if jt.2.val < 4 then 360 else (if jt.2.val < 5 then 362 else 108)))))

checked_coverage fastCoverage0091 pairing0091 template0091 witness0091

theorem coverage0091 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0091) (maskBits m))
    cores template0091 witness0091 := by
  rw [← coresFast_eq]
  exact fastCoverage0091

theorem coverageSize0091 : ∀ q : Pattern,
    (cores (witness0091 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0091 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0091
#print axioms coverageSize0091

noncomputable def pairing0092 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0092 : List (Fin 4935) := templateData0092

noncomputable def witness0092 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 428 else 469) else if t 2 = 1 then (if t 3 = 0 then 430 else if t 3 = 1 then 426 else 467) else (if t 3 = 0 then 1837 else if t 3 = 1 then 1114 else 2150)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 424 else if t 3 = 1 then 420 else 464) else if t 2 = 1 then (if t 3 = 0 then 422 else if t 3 = 1 then 418 else 462) else (if t 3 = 0 then 502 else if t 3 = 1 then 488 else 490)) else (if t 2 = 0 then (if t 3 = 0 then 2125 else if t 3 = 1 then 1507 else 1849) else if t 2 = 1 then (if t 3 = 0 then 448 else if t 3 = 1 then 445 else 475) else (if t 3 = 0 then 503 else if t 3 = 1 then 489 else 491))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 427 else 468) else if t 2 = 1 then (if t 3 = 0 then 429 else if t 3 = 1 then 425 else 466) else (if t 3 = 0 then 1836 else if t 3 = 1 then 1113 else 2148)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 423 else if t 3 = 1 then 419 else 463) else if t 2 = 1 then (if t 3 = 0 then 421 else if t 3 = 1 then 417 else 461) else (if t 3 = 0 then 498 else if t 3 = 1 then 480 else 484)) else (if t 2 = 0 then (if t 3 = 0 then 2124 else if t 3 = 1 then 1506 else 1848) else if t 2 = 1 then (if t 3 = 0 then 447 else if t 3 = 1 then 444 else 474) else (if t 3 = 0 then 500 else if t 3 = 1 then 482 else 486))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 441 else 473) else if t 2 = 1 then (if t 3 = 0 then 442 else if t 3 = 1 then 440 else 472) else (if t 3 = 0 then 1838 else if t 3 = 1 then 1117 else 2149)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 439 else if t 3 = 1 then 437 else 471) else if t 2 = 1 then (if t 3 = 0 then 438 else if t 3 = 1 then 436 else 470) else (if t 3 = 0 then 499 else if t 3 = 1 then 481 else 485)) else (if t 2 = 0 then (if t 3 = 0 then 2126 else if t 3 = 1 then 1511 else 1850) else if t 2 = 1 then (if t 3 = 0 then 454 else if t 3 = 1 then 453 else 478) else (if t 3 = 0 then 501 else if t 3 = 1 then 483 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 315 else (if jt.2.val < 2 then 435 else 338)) else (if jt.2.val < 4 then 433 else (if jt.2.val < 5 then 434 else 319))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2330 else (if jt.2.val < 2 then 2345 else 2333)) else (if jt.2.val < 4 then 2343 else (if jt.2.val < 5 then 2344 else 2322)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1950 else (if jt.2.val < 2 then 1952 else 1955)) else (if jt.2.val < 4 then 1951 else (if jt.2.val < 5 then 1954 else 1953))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 416 else (if jt.2.val < 2 then 460 else 465)) else (if jt.2.val < 4 then 457 else (if jt.2.val < 5 then 459 else 458)))))

checked_coverage fastCoverage0092 pairing0092 template0092 witness0092

theorem coverage0092 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0092) (maskBits m))
    cores template0092 witness0092 := by
  rw [← coresFast_eq]
  exact fastCoverage0092

theorem coverageSize0092 : ∀ q : Pattern,
    (cores (witness0092 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0092 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0092
#print axioms coverageSize0092

noncomputable def pairing0093 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0093 : List (Fin 4935) := templateData0093

noncomputable def witness0093 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 624 else 661) else if t 2 = 1 then (if t 3 = 0 then 626 else if t 3 = 1 then 622 else 659) else (if t 3 = 0 then 2161 else if t 3 = 1 then 1144 else 1826)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 620 else if t 3 = 1 then 616 else 656) else if t 2 = 1 then (if t 3 = 0 then 618 else if t 3 = 1 then 614 else 654) else (if t 3 = 0 then 694 else if t 3 = 1 then 680 else 682)) else (if t 2 = 0 then (if t 3 = 0 then 1786 else if t 3 = 1 then 1459 else 2170) else if t 2 = 1 then (if t 3 = 0 then 644 else if t 3 = 1 then 641 else 667) else (if t 3 = 0 then 695 else if t 3 = 1 then 681 else 683))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 623 else 660) else if t 2 = 1 then (if t 3 = 0 then 625 else if t 3 = 1 then 621 else 658) else (if t 3 = 0 then 2160 else if t 3 = 1 then 1140 else 1824)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 619 else if t 3 = 1 then 615 else 655) else if t 2 = 1 then (if t 3 = 0 then 617 else if t 3 = 1 then 613 else 653) else (if t 3 = 0 then 690 else if t 3 = 1 then 672 else 676)) else (if t 2 = 0 then (if t 3 = 0 then 1785 else if t 3 = 1 then 1458 else 2169) else if t 2 = 1 then (if t 3 = 0 then 643 else if t 3 = 1 then 640 else 666) else (if t 3 = 0 then 692 else if t 3 = 1 then 674 else 678))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 637 else 665) else if t 2 = 1 then (if t 3 = 0 then 638 else if t 3 = 1 then 636 else 664) else (if t 3 = 0 then 2162 else if t 3 = 1 then 1141 else 1825)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 635 else if t 3 = 1 then 633 else 663) else if t 2 = 1 then (if t 3 = 0 then 634 else if t 3 = 1 then 632 else 662) else (if t 3 = 0 then 691 else if t 3 = 1 then 673 else 677)) else (if t 2 = 0 then (if t 3 = 0 then 1787 else if t 3 = 1 then 1463 else 2171) else if t 2 = 1 then (if t 3 = 0 then 650 else if t 3 = 1 then 649 else 670) else (if t 3 = 0 then 693 else if t 3 = 1 then 675 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 114 else (if jt.2.val < 2 then 631 else 138)) else (if jt.2.val < 4 then 629 else (if jt.2.val < 5 then 630 else 118))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2276 else (if jt.2.val < 2 then 2303 else 2279)) else (if jt.2.val < 4 then 2301 else (if jt.2.val < 5 then 2302 else 2268)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2250 else (if jt.2.val < 2 then 2252 else 2255)) else (if jt.2.val < 4 then 2251 else (if jt.2.val < 5 then 2254 else 2253))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 458 else (if jt.2.val < 2 then 657 else 465)) else (if jt.2.val < 4 then 609 else (if jt.2.val < 5 then 610 else 416)))))

checked_coverage fastCoverage0093 pairing0093 template0093 witness0093

theorem coverage0093 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0093) (maskBits m))
    cores template0093 witness0093 := by
  rw [← coresFast_eq]
  exact fastCoverage0093

theorem coverageSize0093 : ∀ q : Pattern,
    (cores (witness0093 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0093 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0093
#print axioms coverageSize0093

noncomputable def pairing0094 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0094 : List (Fin 4935) := templateData0094

noncomputable def witness0094 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1912 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1901 else 1670) else (if t 3 = 0 then 575 else if t 3 = 1 then 554 else 555)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1907 else 1619) else if t 2 = 1 then (if t 3 = 0 then 1891 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 1188 else if t 3 = 1 then 1878 else 1882)) else (if t 2 = 0 then (if t 3 = 0 then 104 else if t 3 = 1 then 94 else 95) else if t 2 = 1 then (if t 3 = 0 then 978 else if t 3 = 1 then 1877 else 1881) else (if t 3 = 0 then 2138 else if t 3 = 1 then 1879 else 1883))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1911 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1899 else 1667) else (if t 3 = 0 then 572 else if t 3 = 1 then 548 else 550)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1905 else 1617) else if t 2 = 1 then (if t 3 = 0 then 1887 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 1181 else if t 3 = 1 then 1863 else 1871)) else (if t 2 = 0 then (if t 3 = 0 then 102 else if t 3 = 1 then 90 else 92) else if t 2 = 1 then (if t 3 = 0 then 971 else if t 3 = 1 then 1861 else 1869) else (if t 3 = 0 then 2136 else if t 3 = 1 then 1865 else 1873))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1915 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1900 else 1668) else (if t 3 = 0 then 573 else if t 3 = 1 then 549 else 551)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1906 else 1618) else if t 2 = 1 then (if t 3 = 0 then 1888 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 1182 else if t 3 = 1 then 1864 else 1872)) else (if t 2 = 0 then (if t 3 = 0 then 103 else if t 3 = 1 then 91 else 93) else if t 2 = 1 then (if t 3 = 0 then 972 else if t 3 = 1 then 1862 else 1870) else (if t 3 = 0 then 2137 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1695 else (if jt.2.val < 2 then 1858 else 1717)) else (if jt.2.val < 4 then 1857 else (if jt.2.val < 5 then 1876 else 1713))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2298 else (if jt.2.val < 2 then 2320 else 2300)) else (if jt.2.val < 4 then 2319 else (if jt.2.val < 5 then 2321 else 2295)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1953 else (if jt.2.val < 2 then 1970 else 1955)) else (if jt.2.val < 4 then 1967 else (if jt.2.val < 5 then 1968 else 1950))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2367 else (if jt.2.val < 2 then 2369 else 2372)) else (if jt.2.val < 4 then 2368 else (if jt.2.val < 5 then 2371 else 2370)))))

checked_coverage fastCoverage0094 pairing0094 template0094 witness0094

theorem coverage0094 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0094) (maskBits m))
    cores template0094 witness0094 := by
  rw [← coresFast_eq]
  exact fastCoverage0094

theorem coverageSize0094 : ∀ q : Pattern,
    (cores (witness0094 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0094 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0094
#print axioms coverageSize0094

noncomputable def pairing0095 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0095 : List (Fin 4935) := templateData0095

noncomputable def witness0095 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2228 else 1856) else if t 2 = 1 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2213 else 1661) else (if t 3 = 0 then 764 else if t 3 = 1 then 742 else 743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2222 else 1616) else if t 2 = 1 then (if t 3 = 0 then 2207 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 1189 else if t 3 = 1 then 2196 else 2200)) else (if t 2 = 0 then (if t 3 = 0 then 308 else if t 3 = 1 then 298 else 299) else if t 2 = 1 then (if t 3 = 0 then 979 else if t 3 = 1 then 2195 else 2199) else (if t 3 = 0 then 1802 else if t 3 = 1 then 2197 else 2201))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2226 else 1854) else if t 2 = 1 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2211 else 1658) else (if t 3 = 0 then 761 else if t 3 = 1 then 736 else 738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2220 else 1614) else if t 2 = 1 then (if t 3 = 0 then 2205 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 1183 else if t 3 = 1 then 2181 else 2189)) else (if t 2 = 0 then (if t 3 = 0 then 306 else if t 3 = 1 then 294 else 296) else if t 2 = 1 then (if t 3 = 0 then 973 else if t 3 = 1 then 2179 else 2187) else (if t 3 = 0 then 1799 else if t 3 = 1 then 2183 else 2191))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2227 else 1855) else if t 2 = 1 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2212 else 1659) else (if t 3 = 0 then 762 else if t 3 = 1 then 737 else 739)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2221 else 1615) else if t 2 = 1 then (if t 3 = 0 then 2206 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 1184 else if t 3 = 1 then 2182 else 2190)) else (if t 2 = 0 then (if t 3 = 0 then 307 else if t 3 = 1 then 295 else 297) else if t 2 = 1 then (if t 3 = 0 then 974 else if t 3 = 1 then 2180 else 2188) else (if t 3 = 0 then 1800 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2046 else (if jt.2.val < 2 then 2176 else 2068)) else (if jt.2.val < 4 then 2175 else (if jt.2.val < 5 then 2194 else 2064))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2340 else (if jt.2.val < 2 then 2356 else 2342)) else (if jt.2.val < 4 then 2355 else (if jt.2.val < 5 then 2357 else 2337)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2253 else (if jt.2.val < 2 then 2267 else 2255)) else (if jt.2.val < 4 then 2265 else (if jt.2.val < 5 then 2266 else 2250))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2370 else (if jt.2.val < 2 then 2374 else 2372)) else (if jt.2.val < 4 then 2373 else (if jt.2.val < 5 then 2375 else 2367)))))

checked_coverage fastCoverage0095 pairing0095 template0095 witness0095

theorem coverage0095 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0095) (maskBits m))
    cores template0095 witness0095 := by
  rw [← coresFast_eq]
  exact fastCoverage0095

theorem coverageSize0095 : ∀ q : Pattern,
    (cores (witness0095 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0095 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0095
#print axioms coverageSize0095

noncomputable def pairing0096 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0096 : List (Fin 4935) := templateData0096

noncomputable def witness0096 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 1462) else if t 2 = 1 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 646) else (if t 3 = 0 then 1053 else if t 3 = 1 then 1049 else 669)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 256) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1747) else (if t 3 = 0 then 1733 else if t 3 = 1 then 1730 else 1750)) else (if t 2 = 0 then (if t 3 = 0 then 396 else if t 3 = 1 then 394 else 929) else if t 2 = 1 then (if t 3 = 0 then 1450 else if t 3 = 1 then 1753 else 1762) else (if t 3 = 0 then 1453 else if t 3 = 1 then 1756 else 1763))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 1461) else if t 2 = 1 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 645) else (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 668)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 255) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1746) else (if t 3 = 0 then 1732 else if t 3 = 1 then 1729 else 1749)) else (if t 2 = 0 then (if t 3 = 0 then 395 else if t 3 = 1 then 393 else 926) else if t 2 = 1 then (if t 3 = 0 then 1449 else if t 3 = 1 then 1752 else 1758) else (if t 3 = 0 then 1452 else if t 3 = 1 then 1755 else 1760))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 1464) else if t 2 = 1 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 651) else (if t 3 = 0 then 1057 else if t 3 = 1 then 1055 else 671)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 261) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1748) else (if t 3 = 0 then 1735 else if t 3 = 1 then 1734 else 1751)) else (if t 2 = 0 then (if t 3 = 0 then 398 else if t 3 = 1 then 397 else 927) else if t 2 = 1 then (if t 3 = 0 then 1451 else if t 3 = 1 then 1754 else 1759) else (if t 3 = 0 then 1454 else if t 3 = 1 then 1757 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1695 else (if jt.2.val < 2 then 1715 else 1717)) else (if jt.2.val < 4 then 1712 else (if jt.2.val < 5 then 1714 else 1713))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2376 else (if jt.2.val < 2 then 2378 else 2381)) else (if jt.2.val < 4 then 2377 else (if jt.2.val < 5 then 2380 else 2379)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2269 else (if jt.2.val < 2 then 2273 else 2274)) else (if jt.2.val < 4 then 2270 else (if jt.2.val < 5 then 2272 else 2271))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1918 else (if jt.2.val < 2 then 1924 else 1925)) else (if jt.2.val < 4 then 1919 else (if jt.2.val < 5 then 1921 else 1920)))))

checked_coverage fastCoverage0096 pairing0096 template0096 witness0096

theorem coverage0096 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0096) (maskBits m))
    cores template0096 witness0096 := by
  rw [← coresFast_eq]
  exact fastCoverage0096

theorem coverageSize0096 : ∀ q : Pattern,
    (cores (witness0096 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0096 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0096
#print axioms coverageSize0096

noncomputable def pairing0097 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0097 : List (Fin 4935) := templateData0097

noncomputable def witness0097 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 1786) else if t 2 = 1 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 644) else (if t 3 = 0 then 452 else if t 3 = 1 then 448 else 1138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 254) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1350) else (if t 3 = 0 then 1342 else if t 3 = 1 then 1339 else 1357)) else (if t 2 = 0 then (if t 3 = 0 then 1012 else if t 3 = 1 then 1001 else 305) else if t 2 = 1 then (if t 3 = 0 then 1777 else if t 3 = 1 then 1370 else 1372) else (if t 3 = 0 then 1780 else if t 3 = 1 then 1371 else 1373))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 1785) else if t 2 = 1 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 643) else (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 1137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 253) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1349) else (if t 3 = 0 then 1341 else if t 3 = 1 then 1338 else 1356)) else (if t 2 = 0 then (if t 3 = 0 then 1011 else if t 3 = 1 then 998 else 302) else if t 2 = 1 then (if t 3 = 0 then 1776 else if t 3 = 1 then 1362 else 1366) else (if t 3 = 0 then 1779 else if t 3 = 1 then 1364 else 1368))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 1787) else if t 2 = 1 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 650) else (if t 3 = 0 then 456 else if t 3 = 1 then 454 else 1139)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 260) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1354) else (if t 3 = 0 then 1344 else if t 3 = 1 then 1343 else 1360)) else (if t 2 = 0 then (if t 3 = 0 then 1013 else if t 3 = 1 then 999 else 303) else if t 2 = 1 then (if t 3 = 0 then 1778 else if t 3 = 1 then 1363 else 1367) else (if t 3 = 0 then 1781 else if t 3 = 1 then 1365 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1304 else (if jt.2.val < 2 then 1324 else 1326)) else (if jt.2.val < 4 then 1321 else (if jt.2.val < 5 then 1323 else 1322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2382 else (if jt.2.val < 2 then 2384 else 2387)) else (if jt.2.val < 4 then 2383 else (if jt.2.val < 5 then 2386 else 2385)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1972 else (if jt.2.val < 2 then 1976 else 1977)) else (if jt.2.val < 4 then 1973 else (if jt.2.val < 5 then 1975 else 1974))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1920 else (if jt.2.val < 2 then 1934 else 1925)) else (if jt.2.val < 4 then 1929 else (if jt.2.val < 5 then 1930 else 1918)))))

checked_coverage fastCoverage0097 pairing0097 template0097 witness0097

theorem coverage0097 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0097) (maskBits m))
    cores template0097 witness0097 := by
  rw [← coresFast_eq]
  exact fastCoverage0097

theorem coverageSize0097 : ∀ q : Pattern,
    (cores (witness0097 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0097 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0097
#print axioms coverageSize0097

noncomputable def pairing0098 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0098 : List (Fin 4935) := templateData0098

noncomputable def witness0098 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 803 else 271) else if t 2 = 1 then (if t 3 = 0 then 807 else if t 3 = 1 then 799 else 855) else (if t 3 = 0 then 1816 else if t 3 = 1 then 1813 else 1599)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 809 else if t 3 = 1 then 801 else 269) else if t 2 = 1 then (if t 3 = 0 then 805 else if t 3 = 1 then 797 else 853) else (if t 3 = 0 then 835 else if t 3 = 1 then 830 else 859)) else (if t 2 = 0 then (if t 3 = 0 then 1501 else if t 3 = 1 then 400 else 1790) else if t 2 = 1 then (if t 3 = 0 then 199 else if t 3 = 1 then 862 else 874) else (if t 3 = 0 then 205 else if t 3 = 1 then 868 else 875))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 802 else 270) else if t 2 = 1 then (if t 3 = 0 then 806 else if t 3 = 1 then 798 else 854) else (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1598)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 808 else if t 3 = 1 then 800 else 268) else if t 2 = 1 then (if t 3 = 0 then 804 else if t 3 = 1 then 796 else 852) else (if t 3 = 0 then 834 else if t 3 = 1 then 829 else 858)) else (if t 2 = 0 then (if t 3 = 0 then 1500 else if t 3 = 1 then 399 else 1788) else if t 2 = 1 then (if t 3 = 0 then 198 else if t 3 = 1 then 861 else 870) else (if t 3 = 0 then 204 else if t 3 = 1 then 867 else 872))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 820 else 275) else if t 2 = 1 then (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 857) else (if t 3 = 0 then 1818 else if t 3 = 1 then 1817 else 1601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 274) else if t 2 = 1 then (if t 3 = 0 then 821 else if t 3 = 1 then 816 else 856) else (if t 3 = 0 then 840 else if t 3 = 1 then 838 else 860)) else (if t 2 = 0 then (if t 3 = 0 then 1502 else if t 3 = 1 then 403 else 1789) else if t 2 = 1 then (if t 3 = 0 then 202 else if t 3 = 1 then 865 else 871) else (if t 3 = 0 then 206 else if t 3 = 1 then 869 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 795 else (if jt.2.val < 2 then 815 else 817)) else (if jt.2.val < 4 then 812 else (if jt.2.val < 5 then 814 else 813))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2388 else (if jt.2.val < 2 then 2390 else 2393)) else (if jt.2.val < 4 then 2389 else (if jt.2.val < 5 then 2392 else 2391)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2271 else (if jt.2.val < 2 then 2289 else 2274)) else (if jt.2.val < 4 then 2286 else (if jt.2.val < 5 then 2287 else 2269))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1225 else (if jt.2.val < 2 then 1234 else 1235)) else (if jt.2.val < 4 then 1226 else (if jt.2.val < 5 then 1228 else 1227)))))

checked_coverage fastCoverage0098 pairing0098 template0098 witness0098

theorem coverage0098 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0098) (maskBits m))
    cores template0098 witness0098 := by
  rw [← coresFast_eq]
  exact fastCoverage0098

theorem coverageSize0098 : ∀ q : Pattern,
    (cores (witness0098 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0098 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0098
#print axioms coverageSize0098

noncomputable def pairing0099 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0099 : List (Fin 4935) := templateData0099

noncomputable def witness0099 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 16 else 918) else if t 2 = 1 then (if t 3 = 0 then 20 else if t 3 = 1 then 12 else 62) else (if t 3 = 0 then 1510 else if t 3 = 1 then 1507 else 1849)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 22 else if t 3 = 1 then 14 else 916) else if t 2 = 1 then (if t 3 = 0 then 18 else if t 3 = 1 then 10 else 60) else (if t 3 = 0 then 48 else if t 3 = 1 then 43 else 73)) else (if t 2 = 0 then (if t 3 = 0 then 1807 else if t 3 = 1 then 100 else 1478) else if t 2 = 1 then (if t 3 = 0 then 898 else if t 3 = 1 then 86 else 88) else (if t 3 = 0 then 904 else if t 3 = 1 then 87 else 89))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 15 else 917) else if t 2 = 1 then (if t 3 = 0 then 19 else if t 3 = 1 then 11 else 61) else (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1848)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 21 else if t 3 = 1 then 13 else 915) else if t 2 = 1 then (if t 3 = 0 then 17 else if t 3 = 1 then 9 else 59) else (if t 3 = 0 then 47 else if t 3 = 1 then 42 else 72)) else (if t 2 = 0 then (if t 3 = 0 then 1806 else if t 3 = 1 then 96 else 1476) else if t 2 = 1 then (if t 3 = 0 then 897 else if t 3 = 1 then 78 else 82) else (if t 3 = 0 then 903 else if t 3 = 1 then 80 else 84))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 33 else 920) else if t 2 = 1 then (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 69) else (if t 3 = 0 then 1512 else if t 3 = 1 then 1511 else 1850)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 919) else if t 2 = 1 then (if t 3 = 0 then 34 else if t 3 = 1 then 29 else 68) else (if t 3 = 0 then 53 else if t 3 = 1 then 51 else 76)) else (if t 2 = 0 then (if t 3 = 0 then 1808 else if t 3 = 1 then 97 else 1477) else if t 2 = 1 then (if t 3 = 0 then 901 else if t 3 = 1 then 79 else 83) else (if t 3 = 0 then 905 else if t 3 = 1 then 81 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 8 else (if jt.2.val < 2 then 28 else 30)) else (if jt.2.val < 4 then 25 else (if jt.2.val < 5 then 27 else 26))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2394 else (if jt.2.val < 2 then 2396 else 2399)) else (if jt.2.val < 4 then 2395 else (if jt.2.val < 5 then 2398 else 2397)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1974 else (if jt.2.val < 2 then 1998 else 1977)) else (if jt.2.val < 4 then 1995 else (if jt.2.val < 5 then 1996 else 1972))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1227 else (if jt.2.val < 2 then 1244 else 1235)) else (if jt.2.val < 4 then 1236 else (if jt.2.val < 5 then 1237 else 1225)))))

checked_coverage fastCoverage0099 pairing0099 template0099 witness0099

theorem coverage0099 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0099) (maskBits m))
    cores template0099 witness0099 := by
  rw [← coresFast_eq]
  exact fastCoverage0099

theorem coverageSize0099 : ∀ q : Pattern,
    (cores (witness0099 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0099 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0099
#print axioms coverageSize0099

noncomputable def pairing0100 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0100 : List (Fin 4935) := templateData0100

noncomputable def witness0100 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 768 else 1148) else if t 2 = 1 then (if t 3 = 0 then 770 else if t 3 = 1 then 766 else 1144) else (if t 3 = 0 then 1549 else if t 3 = 1 then 784 else 1826)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 763 else if t 3 = 1 then 740 else 742) else if t 2 = 1 then (if t 3 = 0 then 755 else if t 3 = 1 then 720 else 725) else (if t 3 = 0 then 1108 else if t 3 = 1 then 723 else 727)) else (if t 2 = 0 then (if t 3 = 0 then 1775 else if t 3 = 1 then 1489 else 1490) else if t 2 = 1 then (if t 3 = 0 then 756 else if t 3 = 1 then 722 else 726) else (if t 3 = 0 then 1109 else if t 3 = 1 then 724 else 728))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 767 else 1146) else if t 2 = 1 then (if t 3 = 0 then 769 else if t 3 = 1 then 765 else 1140) else (if t 3 = 0 then 1548 else if t 3 = 1 then 783 else 1824)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 759 else if t 3 = 1 then 732 else 736) else if t 2 = 1 then (if t 3 = 0 then 747 else if t 3 = 1 then 704 else 712) else (if t 3 = 0 then 1104 else if t 3 = 1 then 708 else 716)) else (if t 2 = 0 then (if t 3 = 0 then 1773 else if t 3 = 1 then 1483 else 1487) else if t 2 = 1 then (if t 3 = 0 then 749 else if t 3 = 1 then 706 else 714) else (if t 3 = 0 then 1106 else if t 3 = 1 then 710 else 718))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 774 else 1147) else if t 2 = 1 then (if t 3 = 0 then 775 else if t 3 = 1 then 773 else 1141) else (if t 3 = 0 then 1550 else if t 3 = 1 then 787 else 1825)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 760 else if t 3 = 1 then 733 else 737) else if t 2 = 1 then (if t 3 = 0 then 748 else if t 3 = 1 then 705 else 713) else (if t 3 = 0 then 1105 else if t 3 = 1 then 709 else 717)) else (if t 2 = 0 then (if t 3 = 0 then 1774 else if t 3 = 1 then 1484 else 1488) else if t 2 = 1 then (if t 3 = 0 then 750 else if t 3 = 1 then 707 else 715) else (if t 3 = 0 then 1107 else if t 3 = 1 then 711 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 8 else (if jt.2.val < 2 then 703 else 30)) else (if jt.2.val < 4 then 702 else (if jt.2.val < 5 then 721 else 26))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2379 else (if jt.2.val < 2 then 2402 else 2381)) else (if jt.2.val < 4 then 2400 else (if jt.2.val < 5 then 2401 else 2376)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2022 else (if jt.2.val < 2 then 2024 else 2027)) else (if jt.2.val < 4 then 2023 else (if jt.2.val < 5 then 2026 else 2025))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1281 else (if jt.2.val < 2 then 1283 else 1289)) else (if jt.2.val < 4 then 1282 else (if jt.2.val < 5 then 1288 else 1286)))))

checked_coverage fastCoverage0100 pairing0100 template0100 witness0100

theorem coverage0100 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0100) (maskBits m))
    cores template0100 witness0100 := by
  rw [← coresFast_eq]
  exact fastCoverage0100

theorem coverageSize0100 : ∀ q : Pattern,
    (cores (witness0100 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0100 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0100
#print axioms coverageSize0100

noncomputable def pairing0101 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0101 : List (Fin 4935) := templateData0101

noncomputable def witness0101 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1214 else 698) else if t 2 = 1 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1210 else 694) else (if t 3 = 0 then 1837 else if t 3 = 1 then 502 else 1526)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1205 else if t 3 = 1 then 1187 else 1189) else if t 2 = 1 then (if t 3 = 0 then 1201 else if t 3 = 1 then 1167 else 1172) else (if t 3 = 0 then 568 else if t 3 = 1 then 1170 else 1174)) else (if t 2 = 0 then (if t 3 = 0 then 1433 else if t 3 = 1 then 1801 else 1802) else if t 2 = 1 then (if t 3 = 0 then 1202 else if t 3 = 1 then 1169 else 1173) else (if t 3 = 0 then 569 else if t 3 = 1 then 1171 else 1175))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1212 else 696) else if t 2 = 1 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1206 else 690) else (if t 3 = 0 then 1836 else if t 3 = 1 then 498 else 1524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1203 else if t 3 = 1 then 1179 else 1183) else if t 2 = 1 then (if t 3 = 0 then 1197 else if t 3 = 1 then 1151 else 1159) else (if t 3 = 0 then 562 else if t 3 = 1 then 1155 else 1163)) else (if t 2 = 0 then (if t 3 = 0 then 1430 else if t 3 = 1 then 1795 else 1799) else if t 2 = 1 then (if t 3 = 0 then 1199 else if t 3 = 1 then 1153 else 1161) else (if t 3 = 0 then 564 else if t 3 = 1 then 1157 else 1165))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1213 else 697) else if t 2 = 1 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1207 else 691) else (if t 3 = 0 then 1838 else if t 3 = 1 then 499 else 1525)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1204 else if t 3 = 1 then 1180 else 1184) else if t 2 = 1 then (if t 3 = 0 then 1198 else if t 3 = 1 then 1152 else 1160) else (if t 3 = 0 then 563 else if t 3 = 1 then 1156 else 1164)) else (if t 2 = 0 then (if t 3 = 0 then 1431 else if t 3 = 1 then 1796 else 1800) else if t 2 = 1 then (if t 3 = 0 then 1200 else if t 3 = 1 then 1154 else 1162) else (if t 3 = 0 then 565 else if t 3 = 1 then 1158 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 795 else (if jt.2.val < 2 then 1150 else 817)) else (if jt.2.val < 4 then 1149 else (if jt.2.val < 5 then 1168 else 813))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2385 else (if jt.2.val < 2 then 2405 else 2387)) else (if jt.2.val < 4 then 2403 else (if jt.2.val < 5 then 2404 else 2382)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2304 else (if jt.2.val < 2 then 2306 else 2309)) else (if jt.2.val < 4 then 2305 else (if jt.2.val < 5 then 2308 else 2307))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1286 else (if jt.2.val < 2 then 1291 else 1289)) else (if jt.2.val < 4 then 1290 else (if jt.2.val < 5 then 1295 else 1281)))))

checked_coverage fastCoverage0101 pairing0101 template0101 witness0101

theorem coverage0101 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0101) (maskBits m))
    cores template0101 witness0101 := by
  rw [← coresFast_eq]
  exact fastCoverage0101

theorem coverageSize0101 : ∀ q : Pattern,
    (cores (witness0101 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0101 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0101
#print axioms coverageSize0101

noncomputable def pairing0102 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0102 : List (Fin 4935) := templateData0102

noncomputable def witness0102 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1680 else 1856) else if t 2 = 1 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1678 else 1853) else (if t 3 = 0 then 597 else if t 3 = 1 then 1080 else 1094)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1660 else 1661) else if t 2 = 1 then (if t 3 = 0 then 1669 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 553 else if t 3 = 1 then 1647 else 1651)) else (if t 2 = 0 then (if t 3 = 0 then 896 else if t 3 = 1 then 357 else 359) else if t 2 = 1 then (if t 3 = 0 then 157 else if t 3 = 1 then 1646 else 1650) else (if t 3 = 0 then 1835 else if t 3 = 1 then 1648 else 1652))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1679 else 1854) else if t 2 = 1 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1677 else 1851) else (if t 3 = 0 then 596 else if t 3 = 1 then 1079 else 1092)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1656 else 1658) else if t 2 = 1 then (if t 3 = 0 then 1665 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 546 else if t 3 = 1 then 1632 else 1640)) else (if t 2 = 0 then (if t 3 = 0 then 894 else if t 3 = 1 then 350 else 354) else if t 2 = 1 then (if t 3 = 0 then 150 else if t 3 = 1 then 1630 else 1638) else (if t 3 = 0 then 1833 else if t 3 = 1 then 1634 else 1642))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1686 else 1855) else if t 2 = 1 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1685 else 1852) else (if t 3 = 0 then 599 else if t 3 = 1 then 1082 else 1093)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1657 else 1659) else if t 2 = 1 then (if t 3 = 0 then 1666 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 547 else if t 3 = 1 then 1633 else 1641)) else (if t 2 = 0 then (if t 3 = 0 then 895 else if t 3 = 1 then 351 else 355) else if t 2 = 1 then (if t 3 = 0 then 151 else if t 3 = 1 then 1631 else 1639) else (if t 3 = 0 then 1834 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1304 else (if jt.2.val < 2 then 1627 else 1326)) else (if jt.2.val < 4 then 1626 else (if jt.2.val < 5 then 1645 else 1322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2391 else (if jt.2.val < 2 then 2408 else 2393)) else (if jt.2.val < 4 then 2406 else (if jt.2.val < 5 then 2407 else 2388)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2025 else (if jt.2.val < 2 then 2038 else 2027)) else (if jt.2.val < 4 then 2037 else (if jt.2.val < 5 then 2039 else 2022))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1956 else (if jt.2.val < 2 then 1958 else 1963)) else (if jt.2.val < 4 then 1957 else (if jt.2.val < 5 then 1962 else 1961)))))

checked_coverage fastCoverage0102 pairing0102 template0102 witness0102

theorem coverage0102 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0102) (maskBits m))
    cores template0102 witness0102 := by
  rw [← coresFast_eq]
  exact fastCoverage0102

theorem coverageSize0102 : ∀ q : Pattern,
    (cores (witness0102 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0102 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0102
#print axioms coverageSize0102

noncomputable def pairing0103 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0103 : List (Fin 4935) := templateData0103

noncomputable def witness0103 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1910 else 1622) else if t 2 = 1 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1907 else 1619) else (if t 3 = 0 then 1116 else if t 3 = 1 then 496 else 497)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1891 else 1892) else if t 2 = 1 then (if t 3 = 0 then 1901 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 554 else if t 3 = 1 then 1878 else 1882)) else (if t 2 = 0 then (if t 3 = 0 then 179 else if t 3 = 1 then 978 else 980) else if t 2 = 1 then (if t 3 = 0 then 158 else if t 3 = 1 then 1877 else 1881) else (if t 3 = 0 then 1538 else if t 3 = 1 then 1879 else 1883))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1908 else 1620) else if t 2 = 1 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1905 else 1617) else (if t 3 = 0 then 1115 else if t 3 = 1 then 492 else 494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1887 else 1889) else if t 2 = 1 then (if t 3 = 0 then 1899 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 548 else if t 3 = 1 then 1863 else 1871)) else (if t 2 = 0 then (if t 3 = 0 then 176 else if t 3 = 1 then 971 else 975) else if t 2 = 1 then (if t 3 = 0 then 152 else if t 3 = 1 then 1861 else 1869) else (if t 3 = 0 then 1535 else if t 3 = 1 then 1865 else 1873))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1909 else 1621) else if t 2 = 1 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1906 else 1618) else (if t 3 = 0 then 1118 else if t 3 = 1 then 493 else 495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1888 else 1890) else if t 2 = 1 then (if t 3 = 0 then 1900 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 549 else if t 3 = 1 then 1864 else 1872)) else (if t 2 = 0 then (if t 3 = 0 then 177 else if t 3 = 1 then 972 else 976) else if t 2 = 1 then (if t 3 = 0 then 153 else if t 3 = 1 then 1862 else 1870) else (if t 3 = 0 then 1536 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1695 else (if jt.2.val < 2 then 1858 else 1717)) else (if jt.2.val < 4 then 1857 else (if jt.2.val < 5 then 1876 else 1713))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2397 else (if jt.2.val < 2 then 2411 else 2399)) else (if jt.2.val < 4 then 2409 else (if jt.2.val < 5 then 2410 else 2394)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2307 else (if jt.2.val < 2 then 2317 else 2309)) else (if jt.2.val < 4 then 2316 else (if jt.2.val < 5 then 2318 else 2304))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1961 else (if jt.2.val < 2 then 1966 else 1963)) else (if jt.2.val < 4 then 1965 else (if jt.2.val < 5 then 1969 else 1956)))))

checked_coverage fastCoverage0103 pairing0103 template0103 witness0103

theorem coverage0103 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0103) (maskBits m))
    cores template0103 witness0103 := by
  rw [← coresFast_eq]
  exact fastCoverage0103

theorem coverageSize0103 : ∀ q : Pattern,
    (cores (witness0103 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0103 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0103
#print axioms coverageSize0103

noncomputable def pairing0104 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0104 : List (Fin 4935) := templateData0104

noncomputable def witness0104 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1510) else if t 2 = 1 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 450) else (if t 3 = 0 then 1053 else if t 3 = 1 then 1051 else 477)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 48) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2090) else (if t 3 = 0 then 1733 else if t 3 = 1 then 2082 else 2098)) else (if t 2 = 0 then (if t 3 = 0 then 195 else if t 3 = 1 then 193 else 904) else if t 2 = 1 then (if t 3 = 0 then 1447 else if t 3 = 1 then 2101 else 2107) else (if t 3 = 0 then 1453 else if t 3 = 1 then 2104 else 2111))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1509) else if t 2 = 1 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 449) else (if t 3 = 0 then 1052 else if t 3 = 1 then 1050 else 476)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 47) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2089) else (if t 3 = 0 then 1732 else if t 3 = 1 then 2081 else 2097)) else (if t 2 = 0 then (if t 3 = 0 then 194 else if t 3 = 1 then 192 else 903) else if t 2 = 1 then (if t 3 = 0 then 1446 else if t 3 = 1 then 2100 else 2106) else (if t 3 = 0 then 1452 else if t 3 = 1 then 2103 else 2109))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1512) else if t 2 = 1 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 455) else (if t 3 = 0 then 1057 else if t 3 = 1 then 1056 else 479)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 53) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2091) else (if t 3 = 0 then 1735 else if t 3 = 1 then 2083 else 2099)) else (if t 2 = 0 then (if t 3 = 0 then 197 else if t 3 = 1 then 196 else 905) else if t 2 = 1 then (if t 3 = 0 then 1448 else if t 3 = 1 then 2102 else 2108) else (if t 3 = 0 then 1454 else if t 3 = 1 then 2105 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2046 else (if jt.2.val < 2 then 2066 else 2068)) else (if jt.2.val < 4 then 2063 else (if jt.2.val < 5 then 2065 else 2064))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2412 else (if jt.2.val < 2 then 2414 else 2417)) else (if jt.2.val < 4 then 2413 else (if jt.2.val < 5 then 2416 else 2415)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2323 else (if jt.2.val < 2 then 2327 else 2328)) else (if jt.2.val < 4 then 2324 else (if jt.2.val < 5 then 2326 else 2325))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2233 else (if jt.2.val < 2 then 2237 else 2238)) else (if jt.2.val < 4 then 2234 else (if jt.2.val < 5 then 2236 else 2235)))))

checked_coverage fastCoverage0104 pairing0104 template0104 witness0104

theorem coverage0104 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0104) (maskBits m))
    cores template0104 witness0104 := by
  rw [← coresFast_eq]
  exact fastCoverage0104

theorem coverageSize0104 : ∀ q : Pattern,
    (cores (witness0104 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0104 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0104
#print axioms coverageSize0104

noncomputable def pairing0105 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0105 : List (Fin 4935) := templateData0105

noncomputable def witness0105 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 2125) else if t 2 = 1 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 448) else (if t 3 = 0 then 648 else if t 3 = 1 then 644 else 1138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 46) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1339) else (if t 3 = 0 then 1353 else if t 3 = 1 then 1350 else 1357)) else (if t 2 = 0 then (if t 3 = 0 then 1012 else if t 3 = 1 then 1001 else 101) else if t 2 = 1 then (if t 3 = 0 then 1777 else if t 3 = 1 then 1370 else 1371) else (if t 3 = 0 then 2119 else if t 3 = 1 then 1372 else 1373))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 2124) else if t 2 = 1 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 447) else (if t 3 = 0 then 647 else if t 3 = 1 then 643 else 1137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 45) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1338) else (if t 3 = 0 then 1352 else if t 3 = 1 then 1349 else 1356)) else (if t 2 = 0 then (if t 3 = 0 then 1011 else if t 3 = 1 then 998 else 98) else if t 2 = 1 then (if t 3 = 0 then 1776 else if t 3 = 1 then 1362 else 1364) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1366 else 1368))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 2126) else if t 2 = 1 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 454) else (if t 3 = 0 then 652 else if t 3 = 1 then 650 else 1139)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 52) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1343) else (if t 3 = 0 then 1355 else if t 3 = 1 then 1354 else 1360)) else (if t 2 = 0 then (if t 3 = 0 then 1013 else if t 3 = 1 then 999 else 99) else if t 2 = 1 then (if t 3 = 0 then 1778 else if t 3 = 1 then 1363 else 1365) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1367 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1304 else (if jt.2.val < 2 then 1324 else 1326)) else (if jt.2.val < 4 then 1321 else (if jt.2.val < 5 then 1323 else 1322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2382 else (if jt.2.val < 2 then 2384 else 2387)) else (if jt.2.val < 4 then 2383 else (if jt.2.val < 5 then 2386 else 2385)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1302 else (if jt.2.val < 2 then 1348 else 1351)) else (if jt.2.val < 4 then 1345 else (if jt.2.val < 5 then 1347 else 1346))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2235 else (if jt.2.val < 2 then 2246 else 2238)) else (if jt.2.val < 4 then 2244 else (if jt.2.val < 5 then 2245 else 2233)))))

checked_coverage fastCoverage0105 pairing0105 template0105 witness0105

theorem coverage0105 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0105) (maskBits m))
    cores template0105 witness0105 := by
  rw [← coresFast_eq]
  exact fastCoverage0105

theorem coverageSize0105 : ∀ q : Pattern,
    (cores (witness0105 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0105 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0105
#print axioms coverageSize0105

noncomputable def pairing0106 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0106 : List (Fin 4935) := templateData0106

noncomputable def witness0106 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 807 else 67) else if t 2 = 1 then (if t 3 = 0 then 803 else if t 3 = 1 then 799 else 855) else (if t 3 = 0 then 2146 else if t 3 = 1 then 1813 else 1599)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 809 else if t 3 = 1 then 805 else 65) else if t 2 = 1 then (if t 3 = 0 then 801 else if t 3 = 1 then 797 else 853) else (if t 3 = 0 then 833 else if t 3 = 1 then 830 else 859)) else (if t 2 = 0 then (if t 3 = 0 then 1501 else if t 3 = 1 then 199 else 2129) else if t 2 = 1 then (if t 3 = 0 then 400 else if t 3 = 1 then 862 else 874) else (if t 3 = 0 then 406 else if t 3 = 1 then 868 else 875))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 806 else 66) else if t 2 = 1 then (if t 3 = 0 then 802 else if t 3 = 1 then 798 else 854) else (if t 3 = 0 then 2145 else if t 3 = 1 then 1812 else 1598)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 808 else if t 3 = 1 then 804 else 64) else if t 2 = 1 then (if t 3 = 0 then 800 else if t 3 = 1 then 796 else 852) else (if t 3 = 0 then 832 else if t 3 = 1 then 829 else 858)) else (if t 2 = 0 then (if t 3 = 0 then 1500 else if t 3 = 1 then 198 else 2127) else if t 2 = 1 then (if t 3 = 0 then 399 else if t 3 = 1 then 861 else 870) else (if t 3 = 0 then 405 else if t 3 = 1 then 867 else 872))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 822 else 71) else if t 2 = 1 then (if t 3 = 0 then 820 else if t 3 = 1 then 818 else 857) else (if t 3 = 0 then 2147 else if t 3 = 1 then 1817 else 1601)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 823 else if t 3 = 1 then 821 else 70) else if t 2 = 1 then (if t 3 = 0 then 819 else if t 3 = 1 then 816 else 856) else (if t 3 = 0 then 839 else if t 3 = 1 then 838 else 860)) else (if t 2 = 0 then (if t 3 = 0 then 1502 else if t 3 = 1 then 202 else 2128) else if t 2 = 1 then (if t 3 = 0 then 403 else if t 3 = 1 then 865 else 871) else (if t 3 = 0 then 407 else if t 3 = 1 then 869 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 795 else (if jt.2.val < 2 then 815 else 817)) else (if jt.2.val < 4 then 812 else (if jt.2.val < 5 then 814 else 813))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2388 else (if jt.2.val < 2 then 2390 else 2393)) else (if jt.2.val < 4 then 2389 else (if jt.2.val < 5 then 2392 else 2391)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2325 else (if jt.2.val < 2 then 2336 else 2328)) else (if jt.2.val < 4 then 2334 else (if jt.2.val < 5 then 2335 else 2323))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 793 else (if jt.2.val < 2 then 850 else 851)) else (if jt.2.val < 4 then 847 else (if jt.2.val < 5 then 849 else 848)))))

checked_coverage fastCoverage0106 pairing0106 template0106 witness0106

theorem coverage0106 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0106) (maskBits m))
    cores template0106 witness0106 := by
  rw [← coresFast_eq]
  exact fastCoverage0106

theorem coverageSize0106 : ∀ q : Pattern,
    (cores (witness0106 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0106 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0106
#print axioms coverageSize0106

noncomputable def pairing0107 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0107 : List (Fin 4935) := templateData0107

noncomputable def witness0107 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 224 else 918) else if t 2 = 1 then (if t 3 = 0 then 228 else if t 3 = 1 then 220 else 266) else (if t 3 = 0 then 1462 else if t 3 = 1 then 1459 else 2170)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 230 else if t 3 = 1 then 222 else 916) else if t 2 = 1 then (if t 3 = 0 then 226 else if t 3 = 1 then 218 else 264) else (if t 3 = 0 then 256 else if t 3 = 1 then 251 else 277)) else (if t 2 = 0 then (if t 3 = 0 then 2140 else if t 3 = 1 then 304 else 1478) else if t 2 = 1 then (if t 3 = 0 then 928 else if t 3 = 1 then 290 else 292) else (if t 3 = 0 then 929 else if t 3 = 1 then 291 else 293))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 223 else 917) else if t 2 = 1 then (if t 3 = 0 then 227 else if t 3 = 1 then 219 else 265) else (if t 3 = 0 then 1461 else if t 3 = 1 then 1458 else 2169)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 229 else if t 3 = 1 then 221 else 915) else if t 2 = 1 then (if t 3 = 0 then 225 else if t 3 = 1 then 217 else 263) else (if t 3 = 0 then 255 else if t 3 = 1 then 250 else 276)) else (if t 2 = 0 then (if t 3 = 0 then 2139 else if t 3 = 1 then 300 else 1476) else if t 2 = 1 then (if t 3 = 0 then 924 else if t 3 = 1 then 282 else 286) else (if t 3 = 0 then 926 else if t 3 = 1 then 284 else 288))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 241 else 920) else if t 2 = 1 then (if t 3 = 0 then 243 else if t 3 = 1 then 239 else 273) else (if t 3 = 0 then 1464 else if t 3 = 1 then 1463 else 2171)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 244 else if t 3 = 1 then 240 else 919) else if t 2 = 1 then (if t 3 = 0 then 242 else if t 3 = 1 then 237 else 272) else (if t 3 = 0 then 261 else if t 3 = 1 then 259 else 280)) else (if t 2 = 0 then (if t 3 = 0 then 2141 else if t 3 = 1 then 301 else 1477) else if t 2 = 1 then (if t 3 = 0 then 925 else if t 3 = 1 then 283 else 287) else (if t 3 = 0 then 927 else if t 3 = 1 then 285 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 216 else (if jt.2.val < 2 then 236 else 238)) else (if jt.2.val < 4 then 233 else (if jt.2.val < 5 then 235 else 234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2418 else (if jt.2.val < 2 then 2420 else 2423)) else (if jt.2.val < 4 then 2419 else (if jt.2.val < 5 then 2422 else 2421)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1346 else (if jt.2.val < 2 then 1460 else 1351)) else (if jt.2.val < 4 then 1455 else (if jt.2.val < 5 then 1456 else 1302))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 848 else (if jt.2.val < 2 then 914 else 851)) else (if jt.2.val < 4 then 906 else (if jt.2.val < 5 then 907 else 793)))))

checked_coverage fastCoverage0107 pairing0107 template0107 witness0107

theorem coverage0107 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0107) (maskBits m))
    cores template0107 witness0107 := by
  rw [← coresFast_eq]
  exact fastCoverage0107

theorem coverageSize0107 : ∀ q : Pattern,
    (cores (witness0107 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0107 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0107
#print axioms coverageSize0107

noncomputable def pairing0108 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0108 : List (Fin 4935) := templateData0108

noncomputable def witness0108 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 579 else 1116) else if t 2 = 1 then (if t 3 = 0 then 581 else if t 3 = 1 then 577 else 1114) else (if t 3 = 0 then 1549 else if t 3 = 1 then 595 else 2150)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 574 else if t 3 = 1 then 552 else 554) else if t 2 = 1 then (if t 3 = 0 then 566 else if t 3 = 1 then 532 else 537) else (if t 3 = 0 then 1108 else if t 3 = 1 then 535 else 539)) else (if t 2 = 0 then (if t 3 = 0 then 2117 else if t 3 = 1 then 1537 else 1538) else if t 2 = 1 then (if t 3 = 0 then 567 else if t 3 = 1 then 534 else 538) else (if t 3 = 0 then 1109 else if t 3 = 1 then 536 else 540))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 578 else 1115) else if t 2 = 1 then (if t 3 = 0 then 580 else if t 3 = 1 then 576 else 1113) else (if t 3 = 0 then 1548 else if t 3 = 1 then 594 else 2148)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 570 else if t 3 = 1 then 544 else 548) else if t 2 = 1 then (if t 3 = 0 then 556 else if t 3 = 1 then 515 else 524) else (if t 3 = 0 then 1104 else if t 3 = 1 then 520 else 528)) else (if t 2 = 0 then (if t 3 = 0 then 2115 else if t 3 = 1 then 1531 else 1535) else if t 2 = 1 then (if t 3 = 0 then 558 else if t 3 = 1 then 517 else 526) else (if t 3 = 0 then 1106 else if t 3 = 1 then 522 else 530))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 585 else 1118) else if t 2 = 1 then (if t 3 = 0 then 586 else if t 3 = 1 then 584 else 1117) else (if t 3 = 0 then 1550 else if t 3 = 1 then 598 else 2149)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 571 else if t 3 = 1 then 545 else 549) else if t 2 = 1 then (if t 3 = 0 then 557 else if t 3 = 1 then 516 else 525) else (if t 3 = 0 then 1105 else if t 3 = 1 then 521 else 529)) else (if t 2 = 0 then (if t 3 = 0 then 2116 else if t 3 = 1 then 1532 else 1536) else if t 2 = 1 then (if t 3 = 0 then 559 else if t 3 = 1 then 518 else 527) else (if t 3 = 0 then 1107 else if t 3 = 1 then 523 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 216 else (if jt.2.val < 2 then 514 else 238)) else (if jt.2.val < 4 then 513 else (if jt.2.val < 5 then 533 else 234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2415 else (if jt.2.val < 2 then 2426 else 2417)) else (if jt.2.val < 4 then 2424 else (if jt.2.val < 5 then 2425 else 2412)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1527 else (if jt.2.val < 2 then 1529 else 1534)) else (if jt.2.val < 4 then 1528 else (if jt.2.val < 5 then 1533 else 1530))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1095 else (if jt.2.val < 2 then 1097 else 1103)) else (if jt.2.val < 4 then 1096 else (if jt.2.val < 5 then 1102 else 1101)))))

checked_coverage fastCoverage0108 pairing0108 template0108 witness0108

theorem coverage0108 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0108) (maskBits m))
    cores template0108 witness0108 := by
  rw [← coresFast_eq]
  exact fastCoverage0108

theorem coverageSize0108 : ∀ q : Pattern,
    (cores (witness0108 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0108 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0108
#print axioms coverageSize0108

noncomputable def pairing0109 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 5 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0109 : List (Fin 4935) := templateData0109

noncomputable def witness0109 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1214 else 506) else if t 2 = 1 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1210 else 502) else (if t 3 = 0 then 2161 else if t 3 = 1 then 694 else 1526)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1205 else if t 3 = 1 then 1187 else 1188) else if t 2 = 1 then (if t 3 = 0 then 1201 else if t 3 = 1 then 1167 else 1170) else (if t 3 = 0 then 757 else if t 3 = 1 then 1172 else 1174)) else (if t 2 = 0 then (if t 3 = 0 then 1433 else if t 3 = 1 then 1801 else 2138) else if t 2 = 1 then (if t 3 = 0 then 1202 else if t 3 = 1 then 1169 else 1171) else (if t 3 = 0 then 758 else if t 3 = 1 then 1173 else 1175))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1212 else 504) else if t 2 = 1 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1206 else 498) else (if t 3 = 0 then 2160 else if t 3 = 1 then 690 else 1524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1203 else if t 3 = 1 then 1179 else 1181) else if t 2 = 1 then (if t 3 = 0 then 1197 else if t 3 = 1 then 1151 else 1155) else (if t 3 = 0 then 751 else if t 3 = 1 then 1159 else 1163)) else (if t 2 = 0 then (if t 3 = 0 then 1430 else if t 3 = 1 then 1795 else 2136) else if t 2 = 1 then (if t 3 = 0 then 1199 else if t 3 = 1 then 1153 else 1157) else (if t 3 = 0 then 753 else if t 3 = 1 then 1161 else 1165))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1213 else 505) else if t 2 = 1 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1207 else 499) else (if t 3 = 0 then 2162 else if t 3 = 1 then 691 else 1525)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1204 else if t 3 = 1 then 1180 else 1182) else if t 2 = 1 then (if t 3 = 0 then 1198 else if t 3 = 1 then 1152 else 1156) else (if t 3 = 0 then 752 else if t 3 = 1 then 1160 else 1164)) else (if t 2 = 0 then (if t 3 = 0 then 1431 else if t 3 = 1 then 1796 else 2137) else if t 2 = 1 then (if t 3 = 0 then 1200 else if t 3 = 1 then 1154 else 1158) else (if t 3 = 0 then 754 else if t 3 = 1 then 1162 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 795 else (if jt.2.val < 2 then 1150 else 817)) else (if jt.2.val < 4 then 1149 else (if jt.2.val < 5 then 1168 else 813))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2385 else (if jt.2.val < 2 then 2405 else 2387)) else (if jt.2.val < 4 then 2403 else (if jt.2.val < 5 then 2404 else 2382)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2346 else (if jt.2.val < 2 then 2348 else 2351)) else (if jt.2.val < 4 then 2347 else (if jt.2.val < 5 then 2350 else 2349))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1101 else (if jt.2.val < 2 then 1195 else 1103)) else (if jt.2.val < 4 then 1194 else (if jt.2.val < 5 then 1196 else 1095)))))

checked_coverage fastCoverage0109 pairing0109 template0109 witness0109

theorem coverage0109 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0109) (maskBits m))
    cores template0109 witness0109 := by
  rw [← coresFast_eq]
  exact fastCoverage0109

theorem coverageSize0109 : ∀ q : Pattern,
    (cores (witness0109 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0109 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0109
#print axioms coverageSize0109

noncomputable def pairing0110 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0110 : List (Fin 4935) := templateData0110

noncomputable def witness0110 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1682 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1678 else 1853) else (if t 3 = 0 then 786 else if t 3 = 1 then 1080 else 1094)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1669 else 1670) else if t 2 = 1 then (if t 3 = 0 then 1660 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 741 else if t 3 = 1 then 1647 else 1651)) else (if t 2 = 0 then (if t 3 = 0 then 896 else if t 3 = 1 then 157 else 159) else if t 2 = 1 then (if t 3 = 0 then 357 else if t 3 = 1 then 1646 else 1650) else (if t 3 = 0 then 2159 else if t 3 = 1 then 1648 else 1652))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1681 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1677 else 1851) else (if t 3 = 0 then 785 else if t 3 = 1 then 1079 else 1092)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1665 else 1667) else if t 2 = 1 then (if t 3 = 0 then 1656 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 734 else if t 3 = 1 then 1632 else 1640)) else (if t 2 = 0 then (if t 3 = 0 then 894 else if t 3 = 1 then 150 else 154) else if t 2 = 1 then (if t 3 = 0 then 350 else if t 3 = 1 then 1630 else 1638) else (if t 3 = 0 then 2157 else if t 3 = 1 then 1634 else 1642))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1687 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1685 else 1852) else (if t 3 = 0 then 788 else if t 3 = 1 then 1082 else 1093)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1666 else 1668) else if t 2 = 1 then (if t 3 = 0 then 1657 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 735 else if t 3 = 1 then 1633 else 1641)) else (if t 2 = 0 then (if t 3 = 0 then 895 else if t 3 = 1 then 151 else 155) else if t 2 = 1 then (if t 3 = 0 then 351 else if t 3 = 1 then 1631 else 1639) else (if t 3 = 0 then 2158 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1304 else (if jt.2.val < 2 then 1627 else 1326)) else (if jt.2.val < 4 then 1626 else (if jt.2.val < 5 then 1645 else 1322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2391 else (if jt.2.val < 2 then 2408 else 2393)) else (if jt.2.val < 4 then 2406 else (if jt.2.val < 5 then 2407 else 2388)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1530 else (if jt.2.val < 2 then 1663 else 1534)) else (if jt.2.val < 4 then 1662 else (if jt.2.val < 5 then 1664 else 1527))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2256 else (if jt.2.val < 2 then 2258 else 2261)) else (if jt.2.val < 4 then 2257 else (if jt.2.val < 5 then 2260 else 2259)))))

checked_coverage fastCoverage0110 pairing0110 template0110 witness0110

theorem coverage0110 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0110) (maskBits m))
    cores template0110 witness0110 := by
  rw [← coresFast_eq]
  exact fastCoverage0110

theorem coverageSize0110 : ∀ q : Pattern,
    (cores (witness0110 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0110 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0110
#print axioms coverageSize0110

noncomputable def pairing0111 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 5) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0111 : List (Fin 4935) := templateData0111

noncomputable def witness0111 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2225 else 1622) else if t 2 = 1 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2222 else 1616) else (if t 3 = 0 then 1148 else if t 3 = 1 then 688 else 689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2207 else 1892) else if t 2 = 1 then (if t 3 = 0 then 2213 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 742 else if t 3 = 1 then 2196 else 2200)) else (if t 2 = 0 then (if t 3 = 0 then 380 else if t 3 = 1 then 979 else 980) else if t 2 = 1 then (if t 3 = 0 then 358 else if t 3 = 1 then 2195 else 2199) else (if t 3 = 0 then 1490 else if t 3 = 1 then 2197 else 2201))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2223 else 1620) else if t 2 = 1 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2220 else 1614) else (if t 3 = 0 then 1146 else if t 3 = 1 then 684 else 686)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2205 else 1889) else if t 2 = 1 then (if t 3 = 0 then 2211 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 736 else if t 3 = 1 then 2181 else 2189)) else (if t 2 = 0 then (if t 3 = 0 then 377 else if t 3 = 1 then 973 else 975) else if t 2 = 1 then (if t 3 = 0 then 352 else if t 3 = 1 then 2179 else 2187) else (if t 3 = 0 then 1487 else if t 3 = 1 then 2183 else 2191))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2224 else 1621) else if t 2 = 1 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2221 else 1615) else (if t 3 = 0 then 1147 else if t 3 = 1 then 685 else 687)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2206 else 1890) else if t 2 = 1 then (if t 3 = 0 then 2212 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 737 else if t 3 = 1 then 2182 else 2190)) else (if t 2 = 0 then (if t 3 = 0 then 378 else if t 3 = 1 then 974 else 976) else if t 2 = 1 then (if t 3 = 0 then 353 else if t 3 = 1 then 2180 else 2188) else (if t 3 = 0 then 1488 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2046 else (if jt.2.val < 2 then 2176 else 2068)) else (if jt.2.val < 4 then 2175 else (if jt.2.val < 5 then 2194 else 2064))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2421 else (if jt.2.val < 2 then 2429 else 2423)) else (if jt.2.val < 4 then 2427 else (if jt.2.val < 5 then 2428 else 2418)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2349 else (if jt.2.val < 2 then 2353 else 2351)) else (if jt.2.val < 4 then 2352 else (if jt.2.val < 5 then 2354 else 2346))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2259 else (if jt.2.val < 2 then 2263 else 2261)) else (if jt.2.val < 4 then 2262 else (if jt.2.val < 5 then 2264 else 2256)))))

checked_coverage fastCoverage0111 pairing0111 template0111 witness0111

theorem coverage0111 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0111) (maskBits m))
    cores template0111 witness0111 := by
  rw [← coresFast_eq]
  exact fastCoverage0111

theorem coverageSize0111 : ∀ q : Pattern,
    (cores (witness0111 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0111 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0111
#print axioms coverageSize0111

noncomputable def pairing0112 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0112 : List (Fin 4935) := templateData0112

noncomputable def witness0112 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1816) else if t 2 = 1 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 1051) else (if t 3 = 0 then 452 else if t 3 = 1 then 450 else 477)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 835) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2082) else (if t 3 = 0 then 1342 else if t 3 = 1 then 2090 else 2098)) else (if t 2 = 0 then (if t 3 = 0 then 195 else if t 3 = 1 then 193 else 205) else if t 2 = 1 then (if t 3 = 0 then 1447 else if t 3 = 1 then 2101 else 2104) else (if t 3 = 0 then 1780 else if t 3 = 1 then 2107 else 2111))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1815) else if t 2 = 1 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 1050) else (if t 3 = 0 then 451 else if t 3 = 1 then 449 else 476)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 834) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2081) else (if t 3 = 0 then 1341 else if t 3 = 1 then 2089 else 2097)) else (if t 2 = 0 then (if t 3 = 0 then 194 else if t 3 = 1 then 192 else 204) else if t 2 = 1 then (if t 3 = 0 then 1446 else if t 3 = 1 then 2100 else 2103) else (if t 3 = 0 then 1779 else if t 3 = 1 then 2106 else 2109))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1818) else if t 2 = 1 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 1056) else (if t 3 = 0 then 456 else if t 3 = 1 then 455 else 479)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 840) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2083) else (if t 3 = 0 then 1344 else if t 3 = 1 then 2091 else 2099)) else (if t 2 = 0 then (if t 3 = 0 then 197 else if t 3 = 1 then 196 else 206) else if t 2 = 1 then (if t 3 = 0 then 1448 else if t 3 = 1 then 2102 else 2105) else (if t 3 = 0 then 1781 else if t 3 = 1 then 2108 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2046 else (if jt.2.val < 2 then 2066 else 2068)) else (if jt.2.val < 4 then 2063 else (if jt.2.val < 5 then 2065 else 2064))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2412 else (if jt.2.val < 2 then 2414 else 2417)) else (if jt.2.val < 4 then 2413 else (if jt.2.val < 5 then 2416 else 2415)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2044 else (if jt.2.val < 2 then 2087 else 2088)) else (if jt.2.val < 4 then 2084 else (if jt.2.val < 5 then 2086 else 2085))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2358 else (if jt.2.val < 2 then 2362 else 2363)) else (if jt.2.val < 4 then 2359 else (if jt.2.val < 5 then 2361 else 2360)))))

checked_coverage fastCoverage0112 pairing0112 template0112 witness0112

theorem coverage0112 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0112) (maskBits m))
    cores template0112 witness0112 := by
  rw [← coresFast_eq]
  exact fastCoverage0112

theorem coverageSize0112 : ∀ q : Pattern,
    (cores (witness0112 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0112 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0112
#print axioms coverageSize0112

noncomputable def pairing0113 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0113 : List (Fin 4935) := templateData0113

noncomputable def witness0113 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 2146) else if t 2 = 1 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 1049) else (if t 3 = 0 then 648 else if t 3 = 1 then 646 else 669)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 833) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1730) else (if t 3 = 0 then 1353 else if t 3 = 1 then 1747 else 1750)) else (if t 2 = 0 then (if t 3 = 0 then 396 else if t 3 = 1 then 394 else 406) else if t 2 = 1 then (if t 3 = 0 then 1450 else if t 3 = 1 then 1753 else 1756) else (if t 3 = 0 then 2119 else if t 3 = 1 then 1762 else 1763))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 2145) else if t 2 = 1 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 1048) else (if t 3 = 0 then 647 else if t 3 = 1 then 645 else 668)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 832) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1729) else (if t 3 = 0 then 1352 else if t 3 = 1 then 1746 else 1749)) else (if t 2 = 0 then (if t 3 = 0 then 395 else if t 3 = 1 then 393 else 405) else if t 2 = 1 then (if t 3 = 0 then 1449 else if t 3 = 1 then 1752 else 1755) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1758 else 1760))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 2147) else if t 2 = 1 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 1055) else (if t 3 = 0 then 652 else if t 3 = 1 then 651 else 671)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 839) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1734) else (if t 3 = 0 then 1355 else if t 3 = 1 then 1748 else 1751)) else (if t 2 = 0 then (if t 3 = 0 then 398 else if t 3 = 1 then 397 else 407) else if t 2 = 1 then (if t 3 = 0 then 1451 else if t 3 = 1 then 1754 else 1757) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1759 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1695 else (if jt.2.val < 2 then 1715 else 1717)) else (if jt.2.val < 4 then 1712 else (if jt.2.val < 5 then 1714 else 1713))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2376 else (if jt.2.val < 2 then 2378 else 2381)) else (if jt.2.val < 4 then 2377 else (if jt.2.val < 5 then 2380 else 2379)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1693 else (if jt.2.val < 2 then 1744 else 1745)) else (if jt.2.val < 4 then 1741 else (if jt.2.val < 5 then 1743 else 1742))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2360 else (if jt.2.val < 2 then 2366 else 2363)) else (if jt.2.val < 4 then 2364 else (if jt.2.val < 5 then 2365 else 2358)))))

checked_coverage fastCoverage0113 pairing0113 template0113 witness0113

theorem coverage0113 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0113) (maskBits m))
    cores template0113 witness0113 := by
  rw [← coresFast_eq]
  exact fastCoverage0113

theorem coverageSize0113 : ∀ q : Pattern,
    (cores (witness0113 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0113 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0113
#print axioms coverageSize0113

noncomputable def pairing0114 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0114 : List (Fin 4935) := templateData0114

noncomputable def witness0114 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 20 else 67) else if t 2 = 1 then (if t 3 = 0 then 16 else if t 3 = 1 then 12 else 62) else (if t 3 = 0 then 2125 else if t 3 = 1 then 1507 else 1849)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 22 else if t 3 = 1 then 18 else 65) else if t 2 = 1 then (if t 3 = 0 then 14 else if t 3 = 1 then 10 else 60) else (if t 3 = 0 then 46 else if t 3 = 1 then 43 else 73)) else (if t 2 = 0 then (if t 3 = 0 then 1807 else if t 3 = 1 then 898 else 2129) else if t 2 = 1 then (if t 3 = 0 then 100 else if t 3 = 1 then 86 else 88) else (if t 3 = 0 then 101 else if t 3 = 1 then 87 else 89))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 19 else 66) else if t 2 = 1 then (if t 3 = 0 then 15 else if t 3 = 1 then 11 else 61) else (if t 3 = 0 then 2124 else if t 3 = 1 then 1506 else 1848)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 21 else if t 3 = 1 then 17 else 64) else if t 2 = 1 then (if t 3 = 0 then 13 else if t 3 = 1 then 9 else 59) else (if t 3 = 0 then 45 else if t 3 = 1 then 42 else 72)) else (if t 2 = 0 then (if t 3 = 0 then 1806 else if t 3 = 1 then 897 else 2127) else if t 2 = 1 then (if t 3 = 0 then 96 else if t 3 = 1 then 78 else 82) else (if t 3 = 0 then 98 else if t 3 = 1 then 80 else 84))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 35 else 71) else if t 2 = 1 then (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 69) else (if t 3 = 0 then 2126 else if t 3 = 1 then 1511 else 1850)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 70) else if t 2 = 1 then (if t 3 = 0 then 32 else if t 3 = 1 then 29 else 68) else (if t 3 = 0 then 52 else if t 3 = 1 then 51 else 76)) else (if t 2 = 0 then (if t 3 = 0 then 1808 else if t 3 = 1 then 901 else 2128) else if t 2 = 1 then (if t 3 = 0 then 97 else if t 3 = 1 then 79 else 83) else (if t 3 = 0 then 99 else if t 3 = 1 then 81 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 8 else (if jt.2.val < 2 then 28 else 30)) else (if jt.2.val < 4 then 25 else (if jt.2.val < 5 then 27 else 26))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2394 else (if jt.2.val < 2 then 2396 else 2399)) else (if jt.2.val < 4 then 2395 else (if jt.2.val < 5 then 2398 else 2397)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2085 else (if jt.2.val < 2 then 2123 else 2088)) else (if jt.2.val < 4 then 2121 else (if jt.2.val < 5 then 2122 else 2044))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 6 else (if jt.2.val < 2 then 58 else 63)) else (if jt.2.val < 4 then 55 else (if jt.2.val < 5 then 57 else 56)))))

checked_coverage fastCoverage0114 pairing0114 template0114 witness0114

theorem coverage0114 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0114) (maskBits m))
    cores template0114 witness0114 := by
  rw [← coresFast_eq]
  exact fastCoverage0114

theorem coverageSize0114 : ∀ q : Pattern,
    (cores (witness0114 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0114 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0114
#print axioms coverageSize0114

noncomputable def pairing0115 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 7 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0115 : List (Fin 4935) := templateData0115

noncomputable def witness0115 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 232 else if t 3 = 1 then 228 else 271) else if t 2 = 1 then (if t 3 = 0 then 224 else if t 3 = 1 then 220 else 266) else (if t 3 = 0 then 1786 else if t 3 = 1 then 1459 else 2170)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 230 else if t 3 = 1 then 226 else 269) else if t 2 = 1 then (if t 3 = 0 then 222 else if t 3 = 1 then 218 else 264) else (if t 3 = 0 then 254 else if t 3 = 1 then 251 else 277)) else (if t 2 = 0 then (if t 3 = 0 then 2140 else if t 3 = 1 then 928 else 1790) else if t 2 = 1 then (if t 3 = 0 then 304 else if t 3 = 1 then 290 else 292) else (if t 3 = 0 then 305 else if t 3 = 1 then 291 else 293))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 231 else if t 3 = 1 then 227 else 270) else if t 2 = 1 then (if t 3 = 0 then 223 else if t 3 = 1 then 219 else 265) else (if t 3 = 0 then 1785 else if t 3 = 1 then 1458 else 2169)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 229 else if t 3 = 1 then 225 else 268) else if t 2 = 1 then (if t 3 = 0 then 221 else if t 3 = 1 then 217 else 263) else (if t 3 = 0 then 253 else if t 3 = 1 then 250 else 276)) else (if t 2 = 0 then (if t 3 = 0 then 2139 else if t 3 = 1 then 924 else 1788) else if t 2 = 1 then (if t 3 = 0 then 300 else if t 3 = 1 then 282 else 286) else (if t 3 = 0 then 302 else if t 3 = 1 then 284 else 288))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 245 else if t 3 = 1 then 243 else 275) else if t 2 = 1 then (if t 3 = 0 then 241 else if t 3 = 1 then 239 else 273) else (if t 3 = 0 then 1787 else if t 3 = 1 then 1463 else 2171)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 244 else if t 3 = 1 then 242 else 274) else if t 2 = 1 then (if t 3 = 0 then 240 else if t 3 = 1 then 237 else 272) else (if t 3 = 0 then 260 else if t 3 = 1 then 259 else 280)) else (if t 2 = 0 then (if t 3 = 0 then 2141 else if t 3 = 1 then 925 else 1789) else if t 2 = 1 then (if t 3 = 0 then 301 else if t 3 = 1 then 283 else 287) else (if t 3 = 0 then 303 else if t 3 = 1 then 285 else 289))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 216 else (if jt.2.val < 2 then 236 else 238)) else (if jt.2.val < 4 then 233 else (if jt.2.val < 5 then 235 else 234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2418 else (if jt.2.val < 2 then 2420 else 2423)) else (if jt.2.val < 4 then 2419 else (if jt.2.val < 5 then 2422 else 2421)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1742 else (if jt.2.val < 2 then 1784 else 1745)) else (if jt.2.val < 4 then 1782 else (if jt.2.val < 5 then 1783 else 1693))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 56 else (if jt.2.val < 2 then 267 else 63)) else (if jt.2.val < 4 then 213 else (if jt.2.val < 5 then 214 else 6)))))

checked_coverage fastCoverage0115 pairing0115 template0115 witness0115

theorem coverage0115 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0115) (maskBits m))
    cores template0115 witness0115 := by
  rw [← coresFast_eq]
  exact fastCoverage0115

theorem coverageSize0115 : ∀ q : Pattern,
    (cores (witness0115 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0115 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0115
#print axioms coverageSize0115

noncomputable def pairing0116 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0116 : List (Fin 4935) := templateData0116

noncomputable def witness0116 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 583 else if t 3 = 1 then 579 else 597) else if t 2 = 1 then (if t 3 = 0 then 581 else if t 3 = 1 then 577 else 595) else (if t 3 = 0 then 1837 else if t 3 = 1 then 1114 else 2150)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 574 else if t 3 = 1 then 552 else 553) else if t 2 = 1 then (if t 3 = 0 then 566 else if t 3 = 1 then 532 else 535) else (if t 3 = 0 then 568 else if t 3 = 1 then 537 else 539)) else (if t 2 = 0 then (if t 3 = 0 then 2117 else if t 3 = 1 then 1537 else 1835) else if t 2 = 1 then (if t 3 = 0 then 567 else if t 3 = 1 then 534 else 536) else (if t 3 = 0 then 569 else if t 3 = 1 then 538 else 540))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 582 else if t 3 = 1 then 578 else 596) else if t 2 = 1 then (if t 3 = 0 then 580 else if t 3 = 1 then 576 else 594) else (if t 3 = 0 then 1836 else if t 3 = 1 then 1113 else 2148)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 570 else if t 3 = 1 then 544 else 546) else if t 2 = 1 then (if t 3 = 0 then 556 else if t 3 = 1 then 515 else 520) else (if t 3 = 0 then 562 else if t 3 = 1 then 524 else 528)) else (if t 2 = 0 then (if t 3 = 0 then 2115 else if t 3 = 1 then 1531 else 1833) else if t 2 = 1 then (if t 3 = 0 then 558 else if t 3 = 1 then 517 else 522) else (if t 3 = 0 then 564 else if t 3 = 1 then 526 else 530))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 587 else if t 3 = 1 then 585 else 599) else if t 2 = 1 then (if t 3 = 0 then 586 else if t 3 = 1 then 584 else 598) else (if t 3 = 0 then 1838 else if t 3 = 1 then 1117 else 2149)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 571 else if t 3 = 1 then 545 else 547) else if t 2 = 1 then (if t 3 = 0 then 557 else if t 3 = 1 then 516 else 521) else (if t 3 = 0 then 563 else if t 3 = 1 then 525 else 529)) else (if t 2 = 0 then (if t 3 = 0 then 2116 else if t 3 = 1 then 1532 else 1834) else if t 2 = 1 then (if t 3 = 0 then 559 else if t 3 = 1 then 518 else 523) else (if t 3 = 0 then 565 else if t 3 = 1 then 527 else 531))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 216 else (if jt.2.val < 2 then 514 else 238)) else (if jt.2.val < 4 then 513 else (if jt.2.val < 5 then 533 else 234))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2415 else (if jt.2.val < 2 then 2426 else 2417)) else (if jt.2.val < 4 then 2424 else (if jt.2.val < 5 then 2425 else 2412)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1827 else (if jt.2.val < 2 then 1829 else 1832)) else (if jt.2.val < 4 then 1828 else (if jt.2.val < 5 then 1831 else 1830))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 510 else (if jt.2.val < 2 then 512 else 561)) else (if jt.2.val < 4 then 511 else (if jt.2.val < 5 then 560 else 519)))))

checked_coverage fastCoverage0116 pairing0116 template0116 witness0116

theorem coverage0116 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0116) (maskBits m))
    cores template0116 witness0116 := by
  rw [← coresFast_eq]
  exact fastCoverage0116

theorem coverageSize0116 : ∀ q : Pattern,
    (cores (witness0116 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0116 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0116
#print axioms coverageSize0116

noncomputable def pairing0117 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0117 : List (Fin 4935) := templateData0117

noncomputable def witness0117 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 768 else 786) else if t 2 = 1 then (if t 3 = 0 then 770 else if t 3 = 1 then 766 else 784) else (if t 3 = 0 then 2161 else if t 3 = 1 then 1144 else 1826)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 763 else if t 3 = 1 then 740 else 741) else if t 2 = 1 then (if t 3 = 0 then 755 else if t 3 = 1 then 720 else 723) else (if t 3 = 0 then 757 else if t 3 = 1 then 725 else 727)) else (if t 2 = 0 then (if t 3 = 0 then 1775 else if t 3 = 1 then 1489 else 2159) else if t 2 = 1 then (if t 3 = 0 then 756 else if t 3 = 1 then 722 else 724) else (if t 3 = 0 then 758 else if t 3 = 1 then 726 else 728))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 767 else 785) else if t 2 = 1 then (if t 3 = 0 then 769 else if t 3 = 1 then 765 else 783) else (if t 3 = 0 then 2160 else if t 3 = 1 then 1140 else 1824)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 759 else if t 3 = 1 then 732 else 734) else if t 2 = 1 then (if t 3 = 0 then 747 else if t 3 = 1 then 704 else 708) else (if t 3 = 0 then 751 else if t 3 = 1 then 712 else 716)) else (if t 2 = 0 then (if t 3 = 0 then 1773 else if t 3 = 1 then 1483 else 2157) else if t 2 = 1 then (if t 3 = 0 then 749 else if t 3 = 1 then 706 else 710) else (if t 3 = 0 then 753 else if t 3 = 1 then 714 else 718))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 774 else 788) else if t 2 = 1 then (if t 3 = 0 then 775 else if t 3 = 1 then 773 else 787) else (if t 3 = 0 then 2162 else if t 3 = 1 then 1141 else 1825)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 760 else if t 3 = 1 then 733 else 735) else if t 2 = 1 then (if t 3 = 0 then 748 else if t 3 = 1 then 705 else 709) else (if t 3 = 0 then 752 else if t 3 = 1 then 713 else 717)) else (if t 2 = 0 then (if t 3 = 0 then 1774 else if t 3 = 1 then 1484 else 2158) else if t 2 = 1 then (if t 3 = 0 then 750 else if t 3 = 1 then 707 else 711) else (if t 3 = 0 then 754 else if t 3 = 1 then 715 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 8 else (if jt.2.val < 2 then 703 else 30)) else (if jt.2.val < 4 then 702 else (if jt.2.val < 5 then 721 else 26))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2379 else (if jt.2.val < 2 then 2402 else 2381)) else (if jt.2.val < 4 then 2400 else (if jt.2.val < 5 then 2401 else 2376)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2151 else (if jt.2.val < 2 then 2153 else 2156)) else (if jt.2.val < 4 then 2152 else (if jt.2.val < 5 then 2155 else 2154))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 519 else (if jt.2.val < 2 then 745 else 561)) else (if jt.2.val < 4 then 744 else (if jt.2.val < 5 then 746 else 510)))))

checked_coverage fastCoverage0117 pairing0117 template0117 witness0117

theorem coverage0117 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0117) (maskBits m))
    cores template0117 witness0117 := by
  rw [← coresFast_eq]
  exact fastCoverage0117

theorem coverageSize0117 : ∀ q : Pattern,
    (cores (witness0117 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0117 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0117
#print axioms coverageSize0117

noncomputable def pairing0118 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 5 else 4)))) (by decide +kernel)

noncomputable def template0118 : List (Fin 4935) := templateData0118

noncomputable def witness0118 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1912 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1907 else 1619) else (if t 3 = 0 then 506 else if t 3 = 1 then 496 else 497)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1901 else 1670) else if t 2 = 1 then (if t 3 = 0 then 1891 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 1188 else if t 3 = 1 then 1878 else 1882)) else (if t 2 = 0 then (if t 3 = 0 then 179 else if t 3 = 1 then 158 else 159) else if t 2 = 1 then (if t 3 = 0 then 978 else if t 3 = 1 then 1877 else 1881) else (if t 3 = 0 then 2138 else if t 3 = 1 then 1879 else 1883))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1911 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1905 else 1617) else (if t 3 = 0 then 504 else if t 3 = 1 then 492 else 494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1899 else 1667) else if t 2 = 1 then (if t 3 = 0 then 1887 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 1181 else if t 3 = 1 then 1863 else 1871)) else (if t 2 = 0 then (if t 3 = 0 then 176 else if t 3 = 1 then 152 else 154) else if t 2 = 1 then (if t 3 = 0 then 971 else if t 3 = 1 then 1861 else 1869) else (if t 3 = 0 then 2136 else if t 3 = 1 then 1865 else 1873))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1915 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1906 else 1618) else (if t 3 = 0 then 505 else if t 3 = 1 then 493 else 495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1900 else 1668) else if t 2 = 1 then (if t 3 = 0 then 1888 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 1182 else if t 3 = 1 then 1864 else 1872)) else (if t 2 = 0 then (if t 3 = 0 then 177 else if t 3 = 1 then 153 else 155) else if t 2 = 1 then (if t 3 = 0 then 972 else if t 3 = 1 then 1862 else 1870) else (if t 3 = 0 then 2137 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1695 else (if jt.2.val < 2 then 1858 else 1717)) else (if jt.2.val < 4 then 1857 else (if jt.2.val < 5 then 1876 else 1713))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2397 else (if jt.2.val < 2 then 2411 else 2399)) else (if jt.2.val < 4 then 2409 else (if jt.2.val < 5 then 2410 else 2394)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1830 else (if jt.2.val < 2 then 1897 else 1832)) else (if jt.2.val < 4 then 1896 else (if jt.2.val < 5 then 1898 else 1827))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2367 else (if jt.2.val < 2 then 2369 else 2372)) else (if jt.2.val < 4 then 2368 else (if jt.2.val < 5 then 2371 else 2370)))))

checked_coverage fastCoverage0118 pairing0118 template0118 witness0118

theorem coverage0118 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0118) (maskBits m))
    cores template0118 witness0118 := by
  rw [← coresFast_eq]
  exact fastCoverage0118

theorem coverageSize0118 : ∀ q : Pattern,
    (cores (witness0118 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0118 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0118
#print axioms coverageSize0118

noncomputable def pairing0119 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 7)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 5)))) (by decide +kernel)

noncomputable def template0119 : List (Fin 4935) := templateData0119

noncomputable def witness0119 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2228 else 1856) else if t 2 = 1 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2222 else 1616) else (if t 3 = 0 then 698 else if t 3 = 1 then 688 else 689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2213 else 1661) else if t 2 = 1 then (if t 3 = 0 then 2207 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 1189 else if t 3 = 1 then 2196 else 2200)) else (if t 2 = 0 then (if t 3 = 0 then 380 else if t 3 = 1 then 358 else 359) else if t 2 = 1 then (if t 3 = 0 then 979 else if t 3 = 1 then 2195 else 2199) else (if t 3 = 0 then 1802 else if t 3 = 1 then 2197 else 2201))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2226 else 1854) else if t 2 = 1 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2220 else 1614) else (if t 3 = 0 then 696 else if t 3 = 1 then 684 else 686)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2211 else 1658) else if t 2 = 1 then (if t 3 = 0 then 2205 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 1183 else if t 3 = 1 then 2181 else 2189)) else (if t 2 = 0 then (if t 3 = 0 then 377 else if t 3 = 1 then 352 else 354) else if t 2 = 1 then (if t 3 = 0 then 973 else if t 3 = 1 then 2179 else 2187) else (if t 3 = 0 then 1799 else if t 3 = 1 then 2183 else 2191))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2227 else 1855) else if t 2 = 1 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2221 else 1615) else (if t 3 = 0 then 697 else if t 3 = 1 then 685 else 687)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2212 else 1659) else if t 2 = 1 then (if t 3 = 0 then 2206 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 1184 else if t 3 = 1 then 2182 else 2190)) else (if t 2 = 0 then (if t 3 = 0 then 378 else if t 3 = 1 then 353 else 355) else if t 2 = 1 then (if t 3 = 0 then 974 else if t 3 = 1 then 2180 else 2188) else (if t 3 = 0 then 1800 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2046 else (if jt.2.val < 2 then 2176 else 2068)) else (if jt.2.val < 4 then 2175 else (if jt.2.val < 5 then 2194 else 2064))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2421 else (if jt.2.val < 2 then 2429 else 2423)) else (if jt.2.val < 4 then 2427 else (if jt.2.val < 5 then 2428 else 2418)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2154 else (if jt.2.val < 2 then 2209 else 2156)) else (if jt.2.val < 4 then 2208 else (if jt.2.val < 5 then 2210 else 2151))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2370 else (if jt.2.val < 2 then 2374 else 2372)) else (if jt.2.val < 4 then 2373 else (if jt.2.val < 5 then 2375 else 2367)))))

checked_coverage fastCoverage0119 pairing0119 template0119 witness0119

theorem coverage0119 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0119) (maskBits m))
    cores template0119 witness0119 := by
  rw [← coresFast_eq]
  exact fastCoverage0119

theorem coverageSize0119 : ∀ q : Pattern,
    (cores (witness0119 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0119 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0119
#print axioms coverageSize0119

end Crown.CertificateData
