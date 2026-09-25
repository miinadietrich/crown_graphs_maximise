import generated.CatalogueTemplates
import generated.CatalogueCoreLookup
import Crown.CertificateCoverageCheck
import generated.CatalogueBatch0001

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def pairing0040 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0040 : List (Fin 4935) := templateData0040

noncomputable def witness0040 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 1462) else if t 2 = 1 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 646) else (if t 3 = 0 then 780 else if t 3 = 1 then 778 else 1145)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 256) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1747) else (if t 3 = 0 then 1450 else if t 3 = 1 then 1753 else 1762)) else (if t 2 = 0 then (if t 3 = 0 then 837 else if t 3 = 1 then 833 else 279) else if t 2 = 1 then (if t 3 = 0 then 1733 else if t 3 = 1 then 1730 else 1750) else (if t 3 = 0 then 1453 else if t 3 = 1 then 1756 else 1763))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 1461) else if t 2 = 1 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 645) else (if t 3 = 0 then 779 else if t 3 = 1 then 777 else 1142)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 255) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1746) else (if t 3 = 0 then 1449 else if t 3 = 1 then 1752 else 1758)) else (if t 2 = 0 then (if t 3 = 0 then 836 else if t 3 = 1 then 832 else 278) else if t 2 = 1 then (if t 3 = 0 then 1732 else if t 3 = 1 then 1729 else 1749) else (if t 3 = 0 then 1452 else if t 3 = 1 then 1755 else 1760))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 1464) else if t 2 = 1 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 651) else (if t 3 = 0 then 782 else if t 3 = 1 then 781 else 1143)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 261) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1748) else (if t 3 = 0 then 1451 else if t 3 = 1 then 1754 else 1759)) else (if t 2 = 0 then (if t 3 = 0 then 841 else if t 3 = 1 then 839 else 281) else if t 2 = 1 then (if t 3 = 0 then 1735 else if t 3 = 1 then 1734 else 1751) else (if t 3 = 0 then 1454 else if t 3 = 1 then 1757 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1695 else (if jt.2.val < 2 then 1715 else 1717)) else (if jt.2.val < 4 then 1712 else (if jt.2.val < 5 then 1714 else 1713))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1694 else (if jt.2.val < 2 then 1728 else 1731)) else (if jt.2.val < 4 then 1725 else (if jt.2.val < 5 then 1727 else 1726)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1917 else (if jt.2.val < 2 then 1923 else 1928)) else (if jt.2.val < 4 then 1922 else (if jt.2.val < 5 then 1927 else 1926))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1918 else (if jt.2.val < 2 then 1924 else 1925)) else (if jt.2.val < 4 then 1919 else (if jt.2.val < 5 then 1921 else 1920)))))

checked_coverage fastCoverage0040 pairing0040 template0040 witness0040

theorem coverage0040 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0040) (maskBits m))
    cores template0040 witness0040 := by
  rw [← coresFast_eq]
  exact fastCoverage0040

theorem coverageSize0040 : ∀ q : Pattern,
    (cores (witness0040 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0040 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0040
#print axioms coverageSize0040

noncomputable def pairing0041 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0041 : List (Fin 4935) := templateData0041

noncomputable def witness0041 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 1786) else if t 2 = 1 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 644) else (if t 3 = 0 then 1222 else if t 3 = 1 then 1211 else 695)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 254) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1350) else (if t 3 = 0 then 1777 else if t 3 = 1 then 1370 else 1372)) else (if t 2 = 0 then (if t 3 = 0 then 50 else if t 3 = 1 then 46 else 922) else if t 2 = 1 then (if t 3 = 0 then 1342 else if t 3 = 1 then 1339 else 1357) else (if t 3 = 0 then 1780 else if t 3 = 1 then 1371 else 1373))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 1785) else if t 2 = 1 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 643) else (if t 3 = 0 then 1221 else if t 3 = 1 then 1208 else 692)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 253) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1349) else (if t 3 = 0 then 1776 else if t 3 = 1 then 1362 else 1366)) else (if t 2 = 0 then (if t 3 = 0 then 49 else if t 3 = 1 then 45 else 921) else if t 2 = 1 then (if t 3 = 0 then 1341 else if t 3 = 1 then 1338 else 1356) else (if t 3 = 0 then 1779 else if t 3 = 1 then 1364 else 1368))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 1787) else if t 2 = 1 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 650) else (if t 3 = 0 then 1223 else if t 3 = 1 then 1209 else 693)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 260) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1354) else (if t 3 = 0 then 1778 else if t 3 = 1 then 1363 else 1367)) else (if t 2 = 0 then (if t 3 = 0 then 54 else if t 3 = 1 then 52 else 923) else if t 2 = 1 then (if t 3 = 0 then 1344 else if t 3 = 1 then 1343 else 1360) else (if t 3 = 0 then 1781 else if t 3 = 1 then 1365 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1304 else (if jt.2.val < 2 then 1324 else 1326)) else (if jt.2.val < 4 then 1321 else (if jt.2.val < 5 then 1323 else 1322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1303 else (if jt.2.val < 2 then 1337 else 1340)) else (if jt.2.val < 4 then 1334 else (if jt.2.val < 5 then 1336 else 1335)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1931 else (if jt.2.val < 2 then 1933 else 1937)) else (if jt.2.val < 4 then 1932 else (if jt.2.val < 5 then 1936 else 1935))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1920 else (if jt.2.val < 2 then 1934 else 1925)) else (if jt.2.val < 4 then 1929 else (if jt.2.val < 5 then 1930 else 1918)))))

checked_coverage fastCoverage0041 pairing0041 template0041 witness0041

theorem coverage0041 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0041) (maskBits m))
    cores template0041 witness0041 := by
  rw [← coresFast_eq]
  exact fastCoverage0041

theorem coverageSize0041 : ∀ q : Pattern,
    (cores (witness0041 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0041 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0041
#print axioms coverageSize0041

noncomputable def pairing0042 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0042 : List (Fin 4935) := templateData0042

noncomputable def witness0042 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 388 else if t 3 = 1 then 384 else 932) else if t 2 = 1 then (if t 3 = 0 then 379 else if t 3 = 1 then 356 else 358) else (if t 3 = 0 then 1775 else if t 3 = 1 then 1489 else 1490)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 386 else if t 3 = 1 then 382 else 928) else if t 2 = 1 then (if t 3 = 0 then 371 else if t 3 = 1 then 336 else 342) else (if t 3 = 0 then 372 else if t 3 = 1 then 339 else 343)) else (if t 2 = 0 then (if t 3 = 0 then 1501 else if t 3 = 1 then 400 else 1790) else if t 2 = 1 then (if t 3 = 0 then 892 else if t 3 = 1 then 340 else 344) else (if t 3 = 0 then 893 else if t 3 = 1 then 341 else 345))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 387 else if t 3 = 1 then 383 else 930) else if t 2 = 1 then (if t 3 = 0 then 375 else if t 3 = 1 then 346 else 352) else (if t 3 = 0 then 1773 else if t 3 = 1 then 1483 else 1487)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 385 else if t 3 = 1 then 381 else 924) else if t 2 = 1 then (if t 3 = 0 then 363 else if t 3 = 1 then 318 else 328) else (if t 3 = 0 then 365 else if t 3 = 1 then 322 else 330)) else (if t 2 = 0 then (if t 3 = 0 then 1500 else if t 3 = 1 then 399 else 1788) else if t 2 = 1 then (if t 3 = 0 then 888 else if t 3 = 1 then 324 else 332) else (if t 3 = 0 then 890 else if t 3 = 1 then 326 else 334))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 392 else if t 3 = 1 then 390 else 931) else if t 2 = 1 then (if t 3 = 0 then 376 else if t 3 = 1 then 347 else 353) else (if t 3 = 0 then 1774 else if t 3 = 1 then 1484 else 1488)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 391 else if t 3 = 1 then 389 else 925) else if t 2 = 1 then (if t 3 = 0 then 364 else if t 3 = 1 then 320 else 329) else (if t 3 = 0 then 366 else if t 3 = 1 then 323 else 331)) else (if t 2 = 0 then (if t 3 = 0 then 1502 else if t 3 = 1 then 403 else 1789) else if t 2 = 1 then (if t 3 = 0 then 889 else if t 3 = 1 then 325 else 333) else (if t 3 = 0 then 891 else if t 3 = 1 then 327 else 335))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 315 else (if jt.2.val < 2 then 317 else 338)) else (if jt.2.val < 4 then 316 else (if jt.2.val < 5 then 337 else 319))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1479 else (if jt.2.val < 2 then 1481 else 1486)) else (if jt.2.val < 4 then 1480 else (if jt.2.val < 5 then 1485 else 1482)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1926 else (if jt.2.val < 2 then 1940 else 1928)) else (if jt.2.val < 4 then 1938 else (if jt.2.val < 5 then 1939 else 1917))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1247 else (if jt.2.val < 2 then 1249 else 1253)) else (if jt.2.val < 4 then 1248 else (if jt.2.val < 5 then 1252 else 1250)))))

checked_coverage fastCoverage0042 pairing0042 template0042 witness0042

theorem coverage0042 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0042) (maskBits m))
    cores template0042 witness0042 := by
  rw [← coresFast_eq]
  exact fastCoverage0042

theorem coverageSize0042 : ∀ q : Pattern,
    (cores (witness0042 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0042 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0042
#print axioms coverageSize0042

noncomputable def pairing0043 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 4 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0043 : List (Fin 4935) := templateData0043

noncomputable def witness0043 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 1004 else 308) else if t 2 = 1 then (if t 3 = 0 then 995 else if t 3 = 1 then 977 else 979) else (if t 3 = 0 then 1433 else if t 3 = 1 then 1801 else 1802)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1006 else if t 3 = 1 then 1000 else 304) else if t 2 = 1 then (if t 3 = 0 then 991 else if t 3 = 1 then 957 else 963) else (if t 3 = 0 then 992 else if t 3 = 1 then 960 else 964)) else (if t 2 = 0 then (if t 3 = 0 then 1807 else if t 3 = 1 then 100 else 1478) else if t 2 = 1 then (if t 3 = 0 then 172 else if t 3 = 1 then 961 else 965) else (if t 3 = 0 then 173 else if t 3 = 1 then 962 else 966))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 1002 else 306) else if t 2 = 1 then (if t 3 = 0 then 993 else if t 3 = 1 then 967 else 973) else (if t 3 = 0 then 1430 else if t 3 = 1 then 1795 else 1799)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1005 else if t 3 = 1 then 996 else 300) else if t 2 = 1 then (if t 3 = 0 then 987 else if t 3 = 1 then 939 else 949) else (if t 3 = 0 then 989 else if t 3 = 1 then 943 else 951)) else (if t 2 = 0 then (if t 3 = 0 then 1806 else if t 3 = 1 then 96 else 1476) else if t 2 = 1 then (if t 3 = 0 then 166 else if t 3 = 1 then 945 else 953) else (if t 3 = 0 then 168 else if t 3 = 1 then 947 else 955))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 1003 else 307) else if t 2 = 1 then (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 974) else (if t 3 = 0 then 1431 else if t 3 = 1 then 1796 else 1800)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 301) else if t 2 = 1 then (if t 3 = 0 then 988 else if t 3 = 1 then 941 else 950) else (if t 3 = 0 then 990 else if t 3 = 1 then 944 else 952)) else (if t 2 = 0 then (if t 3 = 0 then 1808 else if t 3 = 1 then 97 else 1477) else if t 2 = 1 then (if t 3 = 0 then 167 else if t 3 = 1 then 946 else 954) else (if t 3 = 0 then 169 else if t 3 = 1 then 948 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 936 else (if jt.2.val < 2 then 938 else 959)) else (if jt.2.val < 4 then 937 else (if jt.2.val < 5 then 958 else 940))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1791 else (if jt.2.val < 2 then 1793 else 1798)) else (if jt.2.val < 4 then 1792 else (if jt.2.val < 5 then 1797 else 1794)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1935 else (if jt.2.val < 2 then 1943 else 1937)) else (if jt.2.val < 4 then 1941 else (if jt.2.val < 5 then 1942 else 1931))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1250 else (if jt.2.val < 2 then 1257 else 1253)) else (if jt.2.val < 4 then 1256 else (if jt.2.val < 5 then 1259 else 1247)))))

checked_coverage fastCoverage0043 pairing0043 template0043 witness0043

theorem coverage0043 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0043) (maskBits m))
    cores template0043 witness0043 := by
  rw [← coresFast_eq]
  exact fastCoverage0043

theorem coverageSize0043 : ∀ q : Pattern,
    (cores (witness0043 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0043 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0043
#print axioms coverageSize0043

noncomputable def pairing0044 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0044 : List (Fin 4935) := templateData0044

noncomputable def witness0044 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1025 else 661) else if t 2 = 1 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1023 else 659) else (if t 3 = 0 then 1549 else if t 3 = 1 then 784 else 1826)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1029 else if t 3 = 1 then 1021 else 1071) else if t 2 = 1 then (if t 3 = 0 then 1027 else if t 3 = 1 then 1019 else 1069) else (if t 3 = 0 then 595 else if t 3 = 1 then 1078 else 1090)) else (if t 2 = 0 then (if t 3 = 0 then 1816 else if t 3 = 1 then 1813 else 1599) else if t 2 = 1 then (if t 3 = 0 then 1051 else if t 3 = 1 then 1046 else 1075) else (if t 3 = 0 then 601 else if t 3 = 1 then 1084 else 1091))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1024 else 660) else if t 2 = 1 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1022 else 658) else (if t 3 = 0 then 1548 else if t 3 = 1 then 783 else 1824)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1028 else if t 3 = 1 then 1020 else 1070) else if t 2 = 1 then (if t 3 = 0 then 1026 else if t 3 = 1 then 1018 else 1068) else (if t 3 = 0 then 594 else if t 3 = 1 then 1077 else 1086)) else (if t 2 = 0 then (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1598) else if t 2 = 1 then (if t 3 = 0 then 1050 else if t 3 = 1 then 1045 else 1074) else (if t 3 = 0 then 600 else if t 3 = 1 then 1083 else 1088))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1040 else 665) else if t 2 = 1 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1039 else 664) else (if t 3 = 0 then 1550 else if t 3 = 1 then 787 else 1825)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1042 else if t 3 = 1 then 1038 else 1073) else if t 2 = 1 then (if t 3 = 0 then 1041 else if t 3 = 1 then 1037 else 1072) else (if t 3 = 0 then 598 else if t 3 = 1 then 1081 else 1087)) else (if t 2 = 0 then (if t 3 = 0 then 1818 else if t 3 = 1 then 1817 else 1601) else if t 2 = 1 then (if t 3 = 0 then 1056 else if t 3 = 1 then 1054 else 1076) else (if t 3 = 0 then 602 else if t 3 = 1 then 1085 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 936 else (if jt.2.val < 2 then 1036 else 959)) else (if jt.2.val < 4 then 1034 else (if jt.2.val < 5 then 1035 else 940))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1726 else (if jt.2.val < 2 then 1814 else 1731)) else (if jt.2.val < 4 then 1809 else (if jt.2.val < 5 then 1810 else 1694)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1944 else (if jt.2.val < 2 then 1946 else 1949)) else (if jt.2.val < 4 then 1945 else (if jt.2.val < 5 then 1948 else 1947))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1261 else (if jt.2.val < 2 then 1270 else 1271)) else (if jt.2.val < 4 then 1264 else (if jt.2.val < 5 then 1266 else 1265)))))

checked_coverage fastCoverage0044 pairing0044 template0044 witness0044

theorem coverage0044 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0044) (maskBits m))
    cores template0044 witness0044 := by
  rw [← coresFast_eq]
  exact fastCoverage0044

theorem coverageSize0044 : ∀ q : Pattern,
    (cores (witness0044 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0044 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0044
#print axioms coverageSize0044

noncomputable def pairing0045 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0045 : List (Fin 4935) := templateData0045

noncomputable def witness0045 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 432 else if t 3 = 1 then 424 else 1134) else if t 2 = 1 then (if t 3 = 0 then 430 else if t 3 = 1 then 422 else 1132) else (if t 3 = 0 then 1837 else if t 3 = 1 then 502 else 1526)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 428 else if t 3 = 1 then 420 else 464) else if t 2 = 1 then (if t 3 = 0 then 426 else if t 3 = 1 then 418 else 462) else (if t 3 = 0 then 1114 else if t 3 = 1 then 488 else 490)) else (if t 2 = 0 then (if t 3 = 0 then 1510 else if t 3 = 1 then 1507 else 1849) else if t 2 = 1 then (if t 3 = 0 then 450 else if t 3 = 1 then 445 else 475) else (if t 3 = 0 then 1120 else if t 3 = 1 then 489 else 491))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 431 else if t 3 = 1 then 423 else 1133) else if t 2 = 1 then (if t 3 = 0 then 429 else if t 3 = 1 then 421 else 1131) else (if t 3 = 0 then 1836 else if t 3 = 1 then 498 else 1524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 427 else if t 3 = 1 then 419 else 463) else if t 2 = 1 then (if t 3 = 0 then 425 else if t 3 = 1 then 417 else 461) else (if t 3 = 0 then 1113 else if t 3 = 1 then 480 else 484)) else (if t 2 = 0 then (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1848) else if t 2 = 1 then (if t 3 = 0 then 449 else if t 3 = 1 then 444 else 474) else (if t 3 = 0 then 1119 else if t 3 = 1 then 482 else 486))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 443 else if t 3 = 1 then 439 else 1136) else if t 2 = 1 then (if t 3 = 0 then 442 else if t 3 = 1 then 438 else 1135) else (if t 3 = 0 then 1838 else if t 3 = 1 then 499 else 1525)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 441 else if t 3 = 1 then 437 else 471) else if t 2 = 1 then (if t 3 = 0 then 440 else if t 3 = 1 then 436 else 470) else (if t 3 = 0 then 1117 else if t 3 = 1 then 481 else 485)) else (if t 2 = 0 then (if t 3 = 0 then 1512 else if t 3 = 1 then 1511 else 1850) else if t 2 = 1 then (if t 3 = 0 then 455 else if t 3 = 1 then 453 else 478) else (if t 3 = 0 then 1121 else if t 3 = 1 then 483 else 487))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 315 else (if jt.2.val < 2 then 435 else 338)) else (if jt.2.val < 4 then 433 else (if jt.2.val < 5 then 434 else 319))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1335 else (if jt.2.val < 2 then 1508 else 1340)) else (if jt.2.val < 4 then 1503 else (if jt.2.val < 5 then 1504 else 1303)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1950 else (if jt.2.val < 2 then 1952 else 1955)) else (if jt.2.val < 4 then 1951 else (if jt.2.val < 5 then 1954 else 1953))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1265 else (if jt.2.val < 2 then 1280 else 1271)) else (if jt.2.val < 4 then 1275 else (if jt.2.val < 5 then 1276 else 1261)))))

checked_coverage fastCoverage0045 pairing0045 template0045 witness0045

theorem coverage0045 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0045) (maskBits m))
    cores template0045 witness0045 := by
  rw [← coresFast_eq]
  exact fastCoverage0045

theorem coverageSize0045 : ∀ q : Pattern,
    (cores (witness0045 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0045 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0045
#print axioms coverageSize0045

noncomputable def pairing0046 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 5)))) (by decide +kernel)

noncomputable def template0046 : List (Fin 4935) := templateData0046

noncomputable def witness0046 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1680 else 1856) else if t 2 = 1 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1660 else 1661) else (if t 3 = 0 then 1112 else if t 3 = 1 then 741 else 743)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1678 else 1853) else if t 2 = 1 then (if t 3 = 0 then 1669 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 553 else if t 3 = 1 then 1647 else 1651)) else (if t 2 = 0 then (if t 3 = 0 then 201 else if t 3 = 1 then 864 else 878) else if t 2 = 1 then (if t 3 = 0 then 157 else if t 3 = 1 then 1646 else 1650) else (if t 3 = 0 then 1835 else if t 3 = 1 then 1648 else 1652))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1679 else 1854) else if t 2 = 1 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1656 else 1658) else (if t 3 = 0 then 1110 else if t 3 = 1 then 734 else 738)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1677 else 1851) else if t 2 = 1 then (if t 3 = 0 then 1665 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 546 else if t 3 = 1 then 1632 else 1640)) else (if t 2 = 0 then (if t 3 = 0 then 200 else if t 3 = 1 then 863 else 876) else if t 2 = 1 then (if t 3 = 0 then 150 else if t 3 = 1 then 1630 else 1638) else (if t 3 = 0 then 1833 else if t 3 = 1 then 1634 else 1642))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1686 else 1855) else if t 2 = 1 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1657 else 1659) else (if t 3 = 0 then 1111 else if t 3 = 1 then 735 else 739)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1685 else 1852) else if t 2 = 1 then (if t 3 = 0 then 1666 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 547 else if t 3 = 1 then 1633 else 1641)) else (if t 2 = 0 then (if t 3 = 0 then 203 else if t 3 = 1 then 866 else 877) else if t 2 = 1 then (if t 3 = 0 then 151 else if t 3 = 1 then 1631 else 1639) else (if t 3 = 0 then 1834 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1304 else (if jt.2.val < 2 then 1627 else 1326)) else (if jt.2.val < 4 then 1626 else (if jt.2.val < 5 then 1645 else 1322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1482 else (if jt.2.val < 2 then 1654 else 1486)) else (if jt.2.val < 4 then 1653 else (if jt.2.val < 5 then 1655 else 1479)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1947 else (if jt.2.val < 2 then 1964 else 1949)) else (if jt.2.val < 4 then 1959 else (if jt.2.val < 5 then 1960 else 1944))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1956 else (if jt.2.val < 2 then 1958 else 1963)) else (if jt.2.val < 4 then 1957 else (if jt.2.val < 5 then 1962 else 1961)))))

checked_coverage fastCoverage0046 pairing0046 template0046 witness0046

theorem coverage0046 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0046) (maskBits m))
    cores template0046 witness0046 := by
  rw [← coresFast_eq]
  exact fastCoverage0046

theorem coverageSize0046 : ∀ q : Pattern,
    (cores (witness0046 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0046 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0046
#print axioms coverageSize0046

noncomputable def pairing0047 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 4)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 5 else 6)))) (by decide +kernel)

noncomputable def template0047 : List (Fin 4935) := templateData0047

noncomputable def witness0047 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1910 else 1622) else if t 2 = 1 then (if t 3 = 0 then 1904 else if t 3 = 1 then 1891 else 1892) else (if t 3 = 0 then 575 else if t 3 = 1 then 1188 else 1190)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1907 else 1619) else if t 2 = 1 then (if t 3 = 0 then 1901 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 554 else if t 3 = 1 then 1878 else 1882)) else (if t 2 = 0 then (if t 3 = 0 then 900 else if t 3 = 1 then 94 else 95) else if t 2 = 1 then (if t 3 = 0 then 158 else if t 3 = 1 then 1877 else 1881) else (if t 3 = 0 then 1538 else if t 3 = 1 then 1879 else 1883))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1908 else 1620) else if t 2 = 1 then (if t 3 = 0 then 1902 else if t 3 = 1 then 1887 else 1889) else (if t 3 = 0 then 572 else if t 3 = 1 then 1181 else 1185)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1905 else 1617) else if t 2 = 1 then (if t 3 = 0 then 1899 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 548 else if t 3 = 1 then 1863 else 1871)) else (if t 2 = 0 then (if t 3 = 0 then 899 else if t 3 = 1 then 90 else 92) else if t 2 = 1 then (if t 3 = 0 then 152 else if t 3 = 1 then 1861 else 1869) else (if t 3 = 0 then 1535 else if t 3 = 1 then 1865 else 1873))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1909 else 1621) else if t 2 = 1 then (if t 3 = 0 then 1903 else if t 3 = 1 then 1888 else 1890) else (if t 3 = 0 then 573 else if t 3 = 1 then 1182 else 1186)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1906 else 1618) else if t 2 = 1 then (if t 3 = 0 then 1900 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 549 else if t 3 = 1 then 1864 else 1872)) else (if t 2 = 0 then (if t 3 = 0 then 902 else if t 3 = 1 then 91 else 93) else if t 2 = 1 then (if t 3 = 0 then 153 else if t 3 = 1 then 1862 else 1870) else (if t 3 = 0 then 1536 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1695 else (if jt.2.val < 2 then 1858 else 1717)) else (if jt.2.val < 4 then 1857 else (if jt.2.val < 5 then 1876 else 1713))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1794 else (if jt.2.val < 2 then 1885 else 1798)) else (if jt.2.val < 4 then 1884 else (if jt.2.val < 5 then 1886 else 1791)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1953 else (if jt.2.val < 2 then 1970 else 1955)) else (if jt.2.val < 4 then 1967 else (if jt.2.val < 5 then 1968 else 1950))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1961 else (if jt.2.val < 2 then 1966 else 1963)) else (if jt.2.val < 4 then 1965 else (if jt.2.val < 5 then 1969 else 1956)))))

checked_coverage fastCoverage0047 pairing0047 template0047 witness0047

theorem coverage0047 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0047) (maskBits m))
    cores template0047 witness0047 := by
  rw [← coresFast_eq]
  exact fastCoverage0047

theorem coverageSize0047 : ∀ q : Pattern,
    (cores (witness0047 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0047 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0047
#print axioms coverageSize0047

noncomputable def pairing0048 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0048 : List (Fin 4935) := templateData0048

noncomputable def witness0048 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 1376) else if t 2 = 1 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 1211) else (if t 3 = 0 then 452 else if t 3 = 1 then 448 else 503)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 1001) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1370) else (if t 3 = 0 then 1342 else if t 3 = 1 then 1339 else 1371)) else (if t 2 = 0 then (if t 3 = 0 then 258 else if t 3 = 1 then 254 else 305) else if t 2 = 1 then (if t 3 = 0 then 1353 else if t 3 = 1 then 1350 else 1372) else (if t 3 = 0 then 1359 else if t 3 = 1 then 1357 else 1373))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 1374) else if t 2 = 1 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 1208) else (if t 3 = 0 then 451 else if t 3 = 1 then 447 else 500)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 998) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1362) else (if t 3 = 0 then 1341 else if t 3 = 1 then 1338 else 1364)) else (if t 2 = 0 then (if t 3 = 0 then 257 else if t 3 = 1 then 253 else 302) else if t 2 = 1 then (if t 3 = 0 then 1352 else if t 3 = 1 then 1349 else 1366) else (if t 3 = 0 then 1358 else if t 3 = 1 then 1356 else 1368))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 1375) else if t 2 = 1 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 1209) else (if t 3 = 0 then 456 else if t 3 = 1 then 454 else 501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 999) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1363) else (if t 3 = 0 then 1344 else if t 3 = 1 then 1343 else 1365)) else (if t 2 = 0 then (if t 3 = 0 then 262 else if t 3 = 1 then 260 else 303) else if t 2 = 1 then (if t 3 = 0 then 1355 else if t 3 = 1 then 1354 else 1367) else (if t 3 = 0 then 1361 else if t 3 = 1 then 1360 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1304 else (if jt.2.val < 2 then 1324 else 1326)) else (if jt.2.val < 4 then 1321 else (if jt.2.val < 5 then 1323 else 1322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1971 else (if jt.2.val < 2 then 1981 else 1982)) else (if jt.2.val < 4 then 1978 else (if jt.2.val < 5 then 1980 else 1979)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1972 else (if jt.2.val < 2 then 1976 else 1977)) else (if jt.2.val < 4 then 1973 else (if jt.2.val < 5 then 1975 else 1974))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1296 else (if jt.2.val < 2 then 1298 else 1301)) else (if jt.2.val < 4 then 1297 else (if jt.2.val < 5 then 1300 else 1299)))))

checked_coverage fastCoverage0048 pairing0048 template0048 witness0048

theorem coverage0048 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0048) (maskBits m))
    cores template0048 witness0048 := by
  rw [← coresFast_eq]
  exact fastCoverage0048

theorem coverageSize0048 : ∀ q : Pattern,
    (cores (witness0048 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0048 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0048
#print axioms coverageSize0048

noncomputable def pairing0049 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0049 : List (Fin 4935) := templateData0049

noncomputable def witness0049 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 1433) else if t 2 = 1 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 1202) else (if t 3 = 0 then 591 else if t 3 = 1 then 567 else 569)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 992) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1414) else (if t 3 = 0 then 1447 else if t 3 = 1 then 1411 else 1415)) else (if t 2 = 0 then (if t 3 = 0 then 396 else if t 3 = 1 then 372 else 374) else if t 2 = 1 then (if t 3 = 0 then 1450 else if t 3 = 1 then 1412 else 1416) else (if t 3 = 0 then 1453 else if t 3 = 1 then 1413 else 1417))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 1430) else if t 2 = 1 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 1199) else (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 564)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 989) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1400) else (if t 3 = 0 then 1446 else if t 3 = 1 then 1393 else 1402)) else (if t 2 = 0 then (if t 3 = 0 then 395 else if t 3 = 1 then 365 else 369) else if t 2 = 1 then (if t 3 = 0 then 1449 else if t 3 = 1 then 1396 else 1404) else (if t 3 = 0 then 1452 else if t 3 = 1 then 1398 else 1406))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 1431) else if t 2 = 1 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 1200) else (if t 3 = 0 then 593 else if t 3 = 1 then 559 else 565)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 990) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1401) else (if t 3 = 0 then 1448 else if t 3 = 1 then 1394 else 1403)) else (if t 2 = 0 then (if t 3 = 0 then 398 else if t 3 = 1 then 366 else 370) else if t 2 = 1 then (if t 3 = 0 then 1451 else if t 3 = 1 then 1397 else 1405) else (if t 3 = 0 then 1454 else if t 3 = 1 then 1399 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1386 else (if jt.2.val < 2 then 1388 else 1410)) else (if jt.2.val < 4 then 1387 else (if jt.2.val < 5 then 1409 else 1390))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1983 else (if jt.2.val < 2 then 1985 else 1992)) else (if jt.2.val < 4 then 1984 else (if jt.2.val < 5 then 1991 else 1990)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1986 else (if jt.2.val < 2 then 1988 else 1994)) else (if jt.2.val < 4 then 1987 else (if jt.2.val < 5 then 1993 else 1989))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1299 else (if jt.2.val < 2 then 1379 else 1301)) else (if jt.2.val < 4 then 1377 else (if jt.2.val < 5 then 1378 else 1296)))))

checked_coverage fastCoverage0049 pairing0049 template0049 witness0049

theorem coverage0049 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0049) (maskBits m))
    cores template0049 witness0049 := by
  rw [← coresFast_eq]
  exact fastCoverage0049

theorem coverageSize0049 : ∀ q : Pattern,
    (cores (witness0049 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0049 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0049
#print axioms coverageSize0049

noncomputable def pairing0050 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0050 : List (Fin 4935) := templateData0050

noncomputable def witness0050 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 16 else 104) else if t 2 = 1 then (if t 3 = 0 then 20 else if t 3 = 1 then 12 else 94) else (if t 3 = 0 then 1510 else if t 3 = 1 then 1507 else 1523)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 22 else if t 3 = 1 then 14 else 100) else if t 2 = 1 then (if t 3 = 0 then 18 else if t 3 = 1 then 10 else 86) else (if t 3 = 0 then 48 else if t 3 = 1 then 43 else 87)) else (if t 2 = 0 then (if t 3 = 0 then 1471 else if t 3 = 1 then 916 else 1478) else if t 2 = 1 then (if t 3 = 0 then 65 else if t 3 = 1 then 60 else 88) else (if t 3 = 0 then 75 else if t 3 = 1 then 73 else 89))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 15 else 102) else if t 2 = 1 then (if t 3 = 0 then 19 else if t 3 = 1 then 11 else 90) else (if t 3 = 0 then 1509 else if t 3 = 1 then 1506 else 1521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 21 else if t 3 = 1 then 13 else 96) else if t 2 = 1 then (if t 3 = 0 then 17 else if t 3 = 1 then 9 else 78) else (if t 3 = 0 then 47 else if t 3 = 1 then 42 else 80)) else (if t 2 = 0 then (if t 3 = 0 then 1470 else if t 3 = 1 then 915 else 1476) else if t 2 = 1 then (if t 3 = 0 then 64 else if t 3 = 1 then 59 else 82) else (if t 3 = 0 then 74 else if t 3 = 1 then 72 else 84))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 33 else 103) else if t 2 = 1 then (if t 3 = 0 then 35 else if t 3 = 1 then 31 else 91) else (if t 3 = 0 then 1512 else if t 3 = 1 then 1511 else 1522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 36 else if t 3 = 1 then 32 else 97) else if t 2 = 1 then (if t 3 = 0 then 34 else if t 3 = 1 then 29 else 79) else (if t 3 = 0 then 53 else if t 3 = 1 then 51 else 81)) else (if t 2 = 0 then (if t 3 = 0 then 1472 else if t 3 = 1 then 919 else 1477) else if t 2 = 1 then (if t 3 = 0 then 70 else if t 3 = 1 then 68 else 83) else (if t 3 = 0 then 77 else if t 3 = 1 then 76 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 8 else (if jt.2.val < 2 then 28 else 30)) else (if jt.2.val < 4 then 25 else (if jt.2.val < 5 then 27 else 26))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1997 else (if jt.2.val < 2 then 2002 else 2003)) else (if jt.2.val < 4 then 1999 else (if jt.2.val < 5 then 2001 else 2000)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1974 else (if jt.2.val < 2 then 1998 else 1977)) else (if jt.2.val < 4 then 1995 else (if jt.2.val < 5 then 1996 else 1972))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 0 else (if jt.2.val < 2 then 2 else 5)) else (if jt.2.val < 4 then 1 else (if jt.2.val < 5 then 4 else 3)))))

checked_coverage fastCoverage0050 pairing0050 template0050 witness0050

theorem coverage0050 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0050) (maskBits m))
    cores template0050 witness0050 := by
  rw [← coresFast_eq]
  exact fastCoverage0050

theorem coverageSize0050 : ∀ q : Pattern,
    (cores (witness0050 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0050 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0050
#print axioms coverageSize0050

noncomputable def pairing0051 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0051 : List (Fin 4935) := templateData0051

noncomputable def witness0051 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 178 else 179) else if t 2 = 1 then (if t 3 = 0 then 183 else if t 3 = 1 then 156 else 158) else (if t 3 = 0 then 1546 else if t 3 = 1 then 1537 else 1538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 185 else if t 3 = 1 then 170 else 172) else if t 2 = 1 then (if t 3 = 0 then 181 else if t 3 = 1 then 136 else 142) else (if t 3 = 0 then 193 else if t 3 = 1 then 139 else 143)) else (if t 2 = 0 then (if t 3 = 0 then 1501 else if t 3 = 1 then 892 else 1496) else if t 2 = 1 then (if t 3 = 0 then 199 else if t 3 = 1 then 140 else 144) else (if t 3 = 0 then 205 else if t 3 = 1 then 141 else 145))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 174 else 176) else if t 2 = 1 then (if t 3 = 0 then 182 else if t 3 = 1 then 146 else 152) else (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1535)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 184 else if t 3 = 1 then 160 else 166) else if t 2 = 1 then (if t 3 = 0 then 180 else if t 3 = 1 then 117 else 128) else (if t 3 = 0 then 192 else if t 3 = 1 then 121 else 130)) else (if t 2 = 0 then (if t 3 = 0 then 1500 else if t 3 = 1 then 888 else 1494) else if t 2 = 1 then (if t 3 = 0 then 198 else if t 3 = 1 then 124 else 132) else (if t 3 = 0 then 204 else if t 3 = 1 then 126 else 134))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 175 else 177) else if t 2 = 1 then (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 153) else (if t 3 = 0 then 1547 else if t 3 = 1 then 1532 else 1536)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 167) else if t 2 = 1 then (if t 3 = 0 then 188 else if t 3 = 1 then 119 else 129) else (if t 3 = 0 then 196 else if t 3 = 1 then 122 else 131)) else (if t 2 = 0 then (if t 3 = 0 then 1502 else if t 3 = 1 then 889 else 1495) else if t 2 = 1 then (if t 3 = 0 then 202 else if t 3 = 1 then 125 else 133) else (if t 3 = 0 then 206 else if t 3 = 1 then 127 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 114 else (if jt.2.val < 2 then 116 else 138)) else (if jt.2.val < 4 then 115 else (if jt.2.val < 5 then 137 else 118))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2004 else (if jt.2.val < 2 then 2006 else 2009)) else (if jt.2.val < 4 then 2005 else (if jt.2.val < 5 then 2008 else 2007)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1989 else (if jt.2.val < 2 then 2011 else 1994)) else (if jt.2.val < 4 then 2010 else (if jt.2.val < 5 then 2012 else 1986))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 3 else (if jt.2.val < 2 then 107 else 5)) else (if jt.2.val < 4 then 105 else (if jt.2.val < 5 then 106 else 0)))))

checked_coverage fastCoverage0051 pairing0051 template0051 witness0051

theorem coverage0051 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0051) (maskBits m))
    cores template0051 witness0051 := by
  rw [← coresFast_eq]
  exact fastCoverage0051

theorem coverageSize0051 : ∀ q : Pattern,
    (cores (witness0051 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0051 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0051
#print axioms coverageSize0051

noncomputable def pairing0052 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0052 : List (Fin 4935) := templateData0052

noncomputable def witness0052 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 620 else 698) else if t 2 = 1 then (if t 3 = 0 then 626 else if t 3 = 1 then 618 else 694) else (if t 3 = 0 then 1519 else if t 3 = 1 then 1132 else 1526)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 624 else if t 3 = 1 then 616 else 688) else if t 2 = 1 then (if t 3 = 0 then 622 else if t 3 = 1 then 614 else 680) else (if t 3 = 0 then 659 else if t 3 = 1 then 654 else 682)) else (if t 2 = 0 then (if t 3 = 0 then 1462 else if t 3 = 1 then 1459 else 1475) else if t 2 = 1 then (if t 3 = 0 then 646 else if t 3 = 1 then 641 else 681) else (if t 3 = 0 then 669 else if t 3 = 1 then 667 else 683))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 619 else 696) else if t 2 = 1 then (if t 3 = 0 then 625 else if t 3 = 1 then 617 else 690) else (if t 3 = 0 then 1518 else if t 3 = 1 then 1131 else 1524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 623 else if t 3 = 1 then 615 else 684) else if t 2 = 1 then (if t 3 = 0 then 621 else if t 3 = 1 then 613 else 672) else (if t 3 = 0 then 658 else if t 3 = 1 then 653 else 676)) else (if t 2 = 0 then (if t 3 = 0 then 1461 else if t 3 = 1 then 1458 else 1473) else if t 2 = 1 then (if t 3 = 0 then 645 else if t 3 = 1 then 640 else 674) else (if t 3 = 0 then 668 else if t 3 = 1 then 666 else 678))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 635 else 697) else if t 2 = 1 then (if t 3 = 0 then 638 else if t 3 = 1 then 634 else 691) else (if t 3 = 0 then 1520 else if t 3 = 1 then 1135 else 1525)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 637 else if t 3 = 1 then 633 else 685) else if t 2 = 1 then (if t 3 = 0 then 636 else if t 3 = 1 then 632 else 673) else (if t 3 = 0 then 664 else if t 3 = 1 then 662 else 677)) else (if t 2 = 0 then (if t 3 = 0 then 1464 else if t 3 = 1 then 1463 else 1474) else if t 2 = 1 then (if t 3 = 0 then 651 else if t 3 = 1 then 649 else 675) else (if t 3 = 0 then 671 else if t 3 = 1 then 670 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 114 else (if jt.2.val < 2 then 631 else 138)) else (if jt.2.val < 4 then 629 else (if jt.2.val < 5 then 630 else 118))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1979 else (if jt.2.val < 2 then 2016 else 1982)) else (if jt.2.val < 4 then 2013 else (if jt.2.val < 5 then 2014 else 1971)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2015 else (if jt.2.val < 2 then 2020 else 2021)) else (if jt.2.val < 4 then 2017 else (if jt.2.val < 5 then 2019 else 2018))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 603 else (if jt.2.val < 2 then 605 else 608)) else (if jt.2.val < 4 then 604 else (if jt.2.val < 5 then 607 else 606)))))

checked_coverage fastCoverage0052 pairing0052 template0052 witness0052

theorem coverage0052 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0052) (maskBits m))
    cores template0052 witness0052 := by
  rw [← coresFast_eq]
  exact fastCoverage0052

theorem coverageSize0052 : ∀ q : Pattern,
    (cores (witness0052 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0052 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0052
#print axioms coverageSize0052

noncomputable def pairing0053 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0053 : List (Fin 4935) := templateData0053

noncomputable def witness0053 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 763 else 764) else if t 2 = 1 then (if t 3 = 0 then 770 else if t 3 = 1 then 755 else 757) else (if t 3 = 0 then 1549 else if t 3 = 1 then 1108 else 1544)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 768 else if t 3 = 1 then 740 else 742) else if t 2 = 1 then (if t 3 = 0 then 766 else if t 3 = 1 then 720 else 725) else (if t 3 = 0 then 784 else if t 3 = 1 then 723 else 727)) else (if t 2 = 0 then (if t 3 = 0 then 1498 else if t 3 = 1 then 1489 else 1490) else if t 2 = 1 then (if t 3 = 0 then 778 else if t 3 = 1 then 722 else 726) else (if t 3 = 0 then 790 else if t 3 = 1 then 724 else 728))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 759 else 761) else if t 2 = 1 then (if t 3 = 0 then 769 else if t 3 = 1 then 747 else 751) else (if t 3 = 0 then 1548 else if t 3 = 1 then 1104 else 1542)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 767 else if t 3 = 1 then 732 else 736) else if t 2 = 1 then (if t 3 = 0 then 765 else if t 3 = 1 then 704 else 712) else (if t 3 = 0 then 783 else if t 3 = 1 then 708 else 716)) else (if t 2 = 0 then (if t 3 = 0 then 1497 else if t 3 = 1 then 1483 else 1487) else if t 2 = 1 then (if t 3 = 0 then 777 else if t 3 = 1 then 706 else 714) else (if t 3 = 0 then 789 else if t 3 = 1 then 710 else 718))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 760 else 762) else if t 2 = 1 then (if t 3 = 0 then 775 else if t 3 = 1 then 748 else 752) else (if t 3 = 0 then 1550 else if t 3 = 1 then 1105 else 1543)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 774 else if t 3 = 1 then 733 else 737) else if t 2 = 1 then (if t 3 = 0 then 773 else if t 3 = 1 then 705 else 713) else (if t 3 = 0 then 787 else if t 3 = 1 then 709 else 717)) else (if t 2 = 0 then (if t 3 = 0 then 1499 else if t 3 = 1 then 1484 else 1488) else if t 2 = 1 then (if t 3 = 0 then 781 else if t 3 = 1 then 707 else 715) else (if t 3 = 0 then 791 else if t 3 = 1 then 711 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 8 else (if jt.2.val < 2 then 703 else 30)) else (if jt.2.val < 4 then 702 else (if jt.2.val < 5 then 721 else 26))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1990 else (if jt.2.val < 2 then 2029 else 1992)) else (if jt.2.val < 4 then 2028 else (if jt.2.val < 5 then 2030 else 1983)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2022 else (if jt.2.val < 2 then 2024 else 2027)) else (if jt.2.val < 4 then 2023 else (if jt.2.val < 5 then 2026 else 2025))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 606 else (if jt.2.val < 2 then 701 else 608)) else (if jt.2.val < 4 then 699 else (if jt.2.val < 5 then 700 else 603)))))

checked_coverage fastCoverage0053 pairing0053 template0053 witness0053

theorem coverage0053 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0053) (maskBits m))
    cores template0053 witness0053 := by
  rw [← coresFast_eq]
  exact fastCoverage0053

theorem coverageSize0053 : ∀ q : Pattern,
    (cores (witness0053 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0053 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0053
#print axioms coverageSize0053

noncomputable def pairing0054 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 6)))) (by decide +kernel)

noncomputable def template0054 : List (Fin 4935) := templateData0054

noncomputable def witness0054 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1568 else 1622) else if t 2 = 1 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1566 else 1619) else (if t 3 = 0 then 469 else if t 3 = 1 then 464 else 497)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1564 else 1616) else if t 2 = 1 then (if t 3 = 0 then 1570 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 1071 else if t 3 = 1 then 1593 else 1612)) else (if t 2 = 0 then (if t 3 = 0 then 271 else if t 3 = 1 then 266 else 299) else if t 2 = 1 then (if t 3 = 0 then 855 else if t 3 = 1 then 1589 else 1611) else (if t 3 = 0 then 1599 else if t 3 = 1 then 1597 else 1613))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1567 else 1620) else if t 2 = 1 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1565 else 1617) else (if t 3 = 0 then 468 else if t 3 = 1 then 463 else 494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1563 else 1614) else if t 2 = 1 then (if t 3 = 0 then 1569 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 1070 else if t 3 = 1 then 1592 else 1606)) else (if t 2 = 0 then (if t 3 = 0 then 270 else if t 3 = 1 then 265 else 296) else if t 2 = 1 then (if t 3 = 0 then 854 else if t 3 = 1 then 1588 else 1604) else (if t 3 = 0 then 1598 else if t 3 = 1 then 1596 else 1608))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1583 else 1621) else if t 2 = 1 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1582 else 1618) else (if t 3 = 0 then 473 else if t 3 = 1 then 471 else 495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1581 else 1615) else if t 2 = 1 then (if t 3 = 0 then 1584 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 1073 else if t 3 = 1 then 1595 else 1607)) else (if t 2 = 0 then (if t 3 = 0 then 275 else if t 3 = 1 then 273 else 297) else if t 2 = 1 then (if t 3 = 0 then 857 else if t 3 = 1 then 1591 else 1605) else (if t 3 = 0 then 1601 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1386 else (if jt.2.val < 2 then 1579 else 1410)) else (if jt.2.val < 4 then 1577 else (if jt.2.val < 5 then 1578 else 1390))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2000 else (if jt.2.val < 2 then 2035 else 2003)) else (if jt.2.val < 4 then 2031 else (if jt.2.val < 5 then 2032 else 1997)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2018 else (if jt.2.val < 2 then 2036 else 2021)) else (if jt.2.val < 4 then 2033 else (if jt.2.val < 5 then 2034 else 2015))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1551 else (if jt.2.val < 2 then 1553 else 1556)) else (if jt.2.val < 4 then 1552 else (if jt.2.val < 5 then 1555 else 1554)))))

checked_coverage fastCoverage0054 pairing0054 template0054 witness0054

theorem coverage0054 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0054) (maskBits m))
    cores template0054 witness0054 := by
  rw [← coresFast_eq]
  exact fastCoverage0054

theorem coverageSize0054 : ∀ q : Pattern,
    (cores (witness0054 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0054 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0054
#print axioms coverageSize0054

noncomputable def pairing0055 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 6 else 7)))) (by decide +kernel)

noncomputable def template0055 : List (Fin 4935) := templateData0055

noncomputable def witness0055 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1675 else 1676) else if t 2 = 1 then (if t 3 = 0 then 1682 else if t 3 = 1 then 1669 else 1670) else (if t 3 = 0 then 597 else if t 3 = 1 then 553 else 555)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1660 else 1661) else if t 2 = 1 then (if t 3 = 0 then 1678 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 1080 else if t 3 = 1 then 1647 else 1651)) else (if t 2 = 0 then (if t 3 = 0 then 402 else if t 3 = 1 then 357 else 359) else if t 2 = 1 then (if t 3 = 0 then 864 else if t 3 = 1 then 1646 else 1650) else (if t 3 = 0 then 1690 else if t 3 = 1 then 1648 else 1652))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1671 else 1673) else if t 2 = 1 then (if t 3 = 0 then 1681 else if t 3 = 1 then 1665 else 1667) else (if t 3 = 0 then 596 else if t 3 = 1 then 546 else 550)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1656 else 1658) else if t 2 = 1 then (if t 3 = 0 then 1677 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 1079 else if t 3 = 1 then 1632 else 1640)) else (if t 2 = 0 then (if t 3 = 0 then 401 else if t 3 = 1 then 350 else 354) else if t 2 = 1 then (if t 3 = 0 then 863 else if t 3 = 1 then 1630 else 1638) else (if t 3 = 0 then 1689 else if t 3 = 1 then 1634 else 1642))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1672 else 1674) else if t 2 = 1 then (if t 3 = 0 then 1687 else if t 3 = 1 then 1666 else 1668) else (if t 3 = 0 then 599 else if t 3 = 1 then 547 else 551)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1657 else 1659) else if t 2 = 1 then (if t 3 = 0 then 1685 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 1082 else if t 3 = 1 then 1633 else 1641)) else (if t 2 = 0 then (if t 3 = 0 then 404 else if t 3 = 1 then 351 else 355) else if t 2 = 1 then (if t 3 = 0 then 866 else if t 3 = 1 then 1631 else 1639) else (if t 3 = 0 then 1691 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1304 else (if jt.2.val < 2 then 1627 else 1326)) else (if jt.2.val < 4 then 1626 else (if jt.2.val < 5 then 1645 else 1322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2007 else (if jt.2.val < 2 then 2041 else 2009)) else (if jt.2.val < 4 then 2040 else (if jt.2.val < 5 then 2042 else 2004)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2025 else (if jt.2.val < 2 then 2038 else 2027)) else (if jt.2.val < 4 then 2037 else (if jt.2.val < 5 then 2039 else 2022))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1554 else (if jt.2.val < 2 then 1625 else 1556)) else (if jt.2.val < 4 then 1623 else (if jt.2.val < 5 then 1624 else 1551)))))

checked_coverage fastCoverage0055 pairing0055 template0055 witness0055

theorem coverage0055 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0055) (maskBits m))
    cores template0055 witness0055 := by
  rw [← coresFast_eq]
  exact fastCoverage0055

theorem coverageSize0055 : ∀ q : Pattern,
    (cores (witness0055 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0055 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0055
#print axioms coverageSize0055

noncomputable def pairing0056 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0056 : List (Fin 4935) := templateData0056

noncomputable def witness0056 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1546) else if t 2 = 1 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 589) else (if t 3 = 0 then 452 else if t 3 = 1 then 450 else 1120)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 193) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2101) else (if t 3 = 0 then 1342 else if t 3 = 1 then 2090 else 2107)) else (if t 2 = 0 then (if t 3 = 0 then 837 else if t 3 = 1 then 835 else 205) else if t 2 = 1 then (if t 3 = 0 then 1733 else if t 3 = 1 then 2082 else 2104) else (if t 3 = 0 then 1359 else if t 3 = 1 then 2098 else 2111))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1545) else if t 2 = 1 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 588) else (if t 3 = 0 then 451 else if t 3 = 1 then 449 else 1119)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 192) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2100) else (if t 3 = 0 then 1341 else if t 3 = 1 then 2089 else 2106)) else (if t 2 = 0 then (if t 3 = 0 then 836 else if t 3 = 1 then 834 else 204) else if t 2 = 1 then (if t 3 = 0 then 1732 else if t 3 = 1 then 2081 else 2103) else (if t 3 = 0 then 1358 else if t 3 = 1 then 2097 else 2109))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1547) else if t 2 = 1 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 592) else (if t 3 = 0 then 456 else if t 3 = 1 then 455 else 1121)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 196) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2102) else (if t 3 = 0 then 1344 else if t 3 = 1 then 2091 else 2108)) else (if t 2 = 0 then (if t 3 = 0 then 841 else if t 3 = 1 then 840 else 206) else if t 2 = 1 then (if t 3 = 0 then 1735 else if t 3 = 1 then 2083 else 2105) else (if t 3 = 0 then 1361 else if t 3 = 1 then 2099 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2046 else (if jt.2.val < 2 then 2066 else 2068)) else (if jt.2.val < 4 then 2063 else (if jt.2.val < 5 then 2065 else 2064))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2045 else (if jt.2.val < 2 then 2079 else 2080)) else (if jt.2.val < 4 then 2076 else (if jt.2.val < 5 then 2078 else 2077)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2044 else (if jt.2.val < 2 then 2087 else 2088)) else (if jt.2.val < 4 then 2084 else (if jt.2.val < 5 then 2086 else 2085))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2043 else (if jt.2.val < 2 then 2093 else 2096)) else (if jt.2.val < 4 then 2092 else (if jt.2.val < 5 then 2095 else 2094)))))

checked_coverage fastCoverage0056 pairing0056 template0056 witness0056

theorem coverage0056 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0056) (maskBits m))
    cores template0056 witness0056 := by
  rw [← coresFast_eq]
  exact fastCoverage0056

theorem coverageSize0056 : ∀ q : Pattern,
    (cores (witness0056 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0056 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0056
#print axioms coverageSize0056

noncomputable def pairing0057 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0057 : List (Fin 4935) := templateData0057

noncomputable def witness0057 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 2117) else if t 2 = 1 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 567) else (if t 3 = 0 then 1222 else if t 3 = 1 then 1202 else 569)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 171) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1411) else (if t 3 = 0 then 1777 else if t 3 = 1 then 1414 else 1415)) else (if t 2 = 0 then (if t 3 = 0 then 396 else if t 3 = 1 then 372 else 893) else if t 2 = 1 then (if t 3 = 0 then 1450 else if t 3 = 1 then 1412 else 1413) else (if t 3 = 0 then 2119 else if t 3 = 1 then 1416 else 1417))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 2115) else if t 2 = 1 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 558) else (if t 3 = 0 then 1221 else if t 3 = 1 then 1199 else 564)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 162) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1393) else (if t 3 = 0 then 1776 else if t 3 = 1 then 1400 else 1402)) else (if t 2 = 0 then (if t 3 = 0 then 395 else if t 3 = 1 then 365 else 890) else if t 2 = 1 then (if t 3 = 0 then 1449 else if t 3 = 1 then 1396 else 1398) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1404 else 1406))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 2116) else if t 2 = 1 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 559) else (if t 3 = 0 then 1223 else if t 3 = 1 then 1200 else 565)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 163) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1394) else (if t 3 = 0 then 1778 else if t 3 = 1 then 1401 else 1403)) else (if t 2 = 0 then (if t 3 = 0 then 398 else if t 3 = 1 then 366 else 891) else if t 2 = 1 then (if t 3 = 0 then 1451 else if t 3 = 1 then 1397 else 1399) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1405 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1386 else (if jt.2.val < 2 then 1388 else 1410)) else (if jt.2.val < 4 then 1387 else (if jt.2.val < 5 then 1409 else 1390))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1983 else (if jt.2.val < 2 then 1985 else 1992)) else (if jt.2.val < 4 then 1984 else (if jt.2.val < 5 then 1991 else 1990)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1766 else (if jt.2.val < 2 then 1768 else 1772)) else (if jt.2.val < 4 then 1767 else (if jt.2.val < 5 then 1771 else 1770))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2094 else (if jt.2.val < 2 then 2114 else 2096)) else (if jt.2.val < 4 then 2112 else (if jt.2.val < 5 then 2113 else 2043)))))

checked_coverage fastCoverage0057 pairing0057 template0057 witness0057

theorem coverage0057 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0057) (maskBits m))
    cores template0057 witness0057 := by
  rw [← coresFast_eq]
  exact fastCoverage0057

theorem coverageSize0057 : ∀ q : Pattern,
    (cores (witness0057 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0057 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0057
#print axioms coverageSize0057

noncomputable def pairing0058 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0058 : List (Fin 4935) := templateData0058

noncomputable def witness0058 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 24 else if t 3 = 1 then 20 else 900) else if t 2 = 1 then (if t 3 = 0 then 16 else if t 3 = 1 then 12 else 94) else (if t 3 = 0 then 2125 else if t 3 = 1 then 1507 else 1523)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 22 else if t 3 = 1 then 18 else 898) else if t 2 = 1 then (if t 3 = 0 then 14 else if t 3 = 1 then 10 else 86) else (if t 3 = 0 then 46 else if t 3 = 1 then 43 else 87)) else (if t 2 = 0 then (if t 3 = 0 then 1471 else if t 3 = 1 then 65 else 2129) else if t 2 = 1 then (if t 3 = 0 then 916 else if t 3 = 1 then 60 else 88) else (if t 3 = 0 then 922 else if t 3 = 1 then 73 else 89))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 23 else if t 3 = 1 then 19 else 899) else if t 2 = 1 then (if t 3 = 0 then 15 else if t 3 = 1 then 11 else 90) else (if t 3 = 0 then 2124 else if t 3 = 1 then 1506 else 1521)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 21 else if t 3 = 1 then 17 else 897) else if t 2 = 1 then (if t 3 = 0 then 13 else if t 3 = 1 then 9 else 78) else (if t 3 = 0 then 45 else if t 3 = 1 then 42 else 80)) else (if t 2 = 0 then (if t 3 = 0 then 1470 else if t 3 = 1 then 64 else 2127) else if t 2 = 1 then (if t 3 = 0 then 915 else if t 3 = 1 then 59 else 82) else (if t 3 = 0 then 921 else if t 3 = 1 then 72 else 84))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 37 else if t 3 = 1 then 35 else 902) else if t 2 = 1 then (if t 3 = 0 then 33 else if t 3 = 1 then 31 else 91) else (if t 3 = 0 then 2126 else if t 3 = 1 then 1511 else 1522)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 36 else if t 3 = 1 then 34 else 901) else if t 2 = 1 then (if t 3 = 0 then 32 else if t 3 = 1 then 29 else 79) else (if t 3 = 0 then 52 else if t 3 = 1 then 51 else 81)) else (if t 2 = 0 then (if t 3 = 0 then 1472 else if t 3 = 1 then 70 else 2128) else if t 2 = 1 then (if t 3 = 0 then 919 else if t 3 = 1 then 68 else 83) else (if t 3 = 0 then 923 else if t 3 = 1 then 76 else 85))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 8 else (if jt.2.val < 2 then 28 else 30)) else (if jt.2.val < 4 then 25 else (if jt.2.val < 5 then 27 else 26))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1997 else (if jt.2.val < 2 then 2002 else 2003)) else (if jt.2.val < 4 then 1999 else (if jt.2.val < 5 then 2001 else 2000)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2085 else (if jt.2.val < 2 then 2123 else 2088)) else (if jt.2.val < 4 then 2121 else (if jt.2.val < 5 then 2122 else 2044))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1238 else (if jt.2.val < 2 then 1240 else 1243)) else (if jt.2.val < 4 then 1239 else (if jt.2.val < 5 then 1242 else 1241)))))

checked_coverage fastCoverage0058 pairing0058 template0058 witness0058

theorem coverage0058 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0058) (maskBits m))
    cores template0058 witness0058 := by
  rw [← coresFast_eq]
  exact fastCoverage0058

theorem coverageSize0058 : ∀ q : Pattern,
    (cores (witness0058 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0058 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0058
#print axioms coverageSize0058

noncomputable def pairing0059 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0059 : List (Fin 4935) := templateData0059

noncomputable def witness0059 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 995 else 179) else if t 2 = 1 then (if t 3 = 0 then 1004 else if t 3 = 1 then 977 else 978) else (if t 3 = 0 then 1376 else if t 3 = 1 then 1801 else 2138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1006 else if t 3 = 1 then 991 else 172) else if t 2 = 1 then (if t 3 = 0 then 1000 else if t 3 = 1 then 957 else 961) else (if t 3 = 0 then 1001 else if t 3 = 1 then 960 else 962)) else (if t 2 = 0 then (if t 3 = 0 then 2140 else if t 3 = 1 then 373 else 1496) else if t 2 = 1 then (if t 3 = 0 then 304 else if t 3 = 1 then 963 else 965) else (if t 3 = 0 then 305 else if t 3 = 1 then 964 else 966))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 993 else 176) else if t 2 = 1 then (if t 3 = 0 then 1002 else if t 3 = 1 then 967 else 971) else (if t 3 = 0 then 1374 else if t 3 = 1 then 1795 else 2136)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1005 else if t 3 = 1 then 987 else 166) else if t 2 = 1 then (if t 3 = 0 then 996 else if t 3 = 1 then 939 else 945) else (if t 3 = 0 then 998 else if t 3 = 1 then 943 else 947)) else (if t 2 = 0 then (if t 3 = 0 then 2139 else if t 3 = 1 then 367 else 1494) else if t 2 = 1 then (if t 3 = 0 then 300 else if t 3 = 1 then 949 else 953) else (if t 3 = 0 then 302 else if t 3 = 1 then 951 else 955))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 994 else 177) else if t 2 = 1 then (if t 3 = 0 then 1003 else if t 3 = 1 then 968 else 972) else (if t 3 = 0 then 1375 else if t 3 = 1 then 1796 else 2137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1009 else if t 3 = 1 then 988 else 167) else if t 2 = 1 then (if t 3 = 0 then 997 else if t 3 = 1 then 941 else 946) else (if t 3 = 0 then 999 else if t 3 = 1 then 944 else 948)) else (if t 2 = 0 then (if t 3 = 0 then 2141 else if t 3 = 1 then 368 else 1495) else if t 2 = 1 then (if t 3 = 0 then 301 else if t 3 = 1 then 950 else 954) else (if t 3 = 0 then 303 else if t 3 = 1 then 952 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 936 else (if jt.2.val < 2 then 938 else 959)) else (if jt.2.val < 4 then 937 else (if jt.2.val < 5 then 958 else 940))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2130 else (if jt.2.val < 2 then 2132 else 2135)) else (if jt.2.val < 4 then 2131 else (if jt.2.val < 5 then 2134 else 2133)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1770 else (if jt.2.val < 2 then 1804 else 1772)) else (if jt.2.val < 4 then 1803 else (if jt.2.val < 5 then 1805 else 1766))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1241 else (if jt.2.val < 2 then 1258 else 1243)) else (if jt.2.val < 4 then 1254 else (if jt.2.val < 5 then 1255 else 1238)))))

checked_coverage fastCoverage0059 pairing0059 template0059 witness0059

theorem coverage0059 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0059) (maskBits m))
    cores template0059 witness0059 := by
  rw [← coresFast_eq]
  exact fastCoverage0059

theorem coverageSize0059 : ∀ q : Pattern,
    (cores (witness0059 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0059 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0059
#print axioms coverageSize0059

noncomputable def pairing0060 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0060 : List (Fin 4935) := templateData0060

noncomputable def witness0060 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1029 else 597) else if t 2 = 1 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1027 else 595) else (if t 3 = 0 then 1519 else if t 3 = 1 then 467 else 2150)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1025 else if t 3 = 1 then 1021 else 1080) else if t 2 = 1 then (if t 3 = 0 then 1023 else if t 3 = 1 then 1019 else 1078) else (if t 3 = 0 then 659 else if t 3 = 1 then 1069 else 1090)) else (if t 2 = 0 then (if t 3 = 0 then 2146 else if t 3 = 1 then 1813 else 1690) else if t 2 = 1 then (if t 3 = 0 then 1049 else if t 3 = 1 then 1046 else 1084) else (if t 3 = 0 then 669 else if t 3 = 1 then 1075 else 1091))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1028 else 596) else if t 2 = 1 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1026 else 594) else (if t 3 = 0 then 1518 else if t 3 = 1 then 466 else 2148)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1024 else if t 3 = 1 then 1020 else 1079) else if t 2 = 1 then (if t 3 = 0 then 1022 else if t 3 = 1 then 1018 else 1077) else (if t 3 = 0 then 658 else if t 3 = 1 then 1068 else 1086)) else (if t 2 = 0 then (if t 3 = 0 then 2145 else if t 3 = 1 then 1812 else 1689) else if t 2 = 1 then (if t 3 = 0 then 1048 else if t 3 = 1 then 1045 else 1083) else (if t 3 = 0 then 668 else if t 3 = 1 then 1074 else 1088))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1042 else 599) else if t 2 = 1 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1041 else 598) else (if t 3 = 0 then 1520 else if t 3 = 1 then 472 else 2149)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1040 else if t 3 = 1 then 1038 else 1082) else if t 2 = 1 then (if t 3 = 0 then 1039 else if t 3 = 1 then 1037 else 1081) else (if t 3 = 0 then 664 else if t 3 = 1 then 1072 else 1087)) else (if t 2 = 0 then (if t 3 = 0 then 2147 else if t 3 = 1 then 1817 else 1691) else if t 2 = 1 then (if t 3 = 0 then 1055 else if t 3 = 1 then 1054 else 1085) else (if t 3 = 0 then 671 else if t 3 = 1 then 1076 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 936 else (if jt.2.val < 2 then 1036 else 959)) else (if jt.2.val < 4 then 1034 else (if jt.2.val < 5 then 1035 else 940))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2077 else (if jt.2.val < 2 then 2144 else 2080)) else (if jt.2.val < 4 then 2142 else (if jt.2.val < 5 then 2143 else 2045)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1811 else (if jt.2.val < 2 then 1822 else 1823)) else (if jt.2.val < 4 then 1819 else (if jt.2.val < 5 then 1821 else 1820))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1260 else (if jt.2.val < 2 then 1263 else 1269)) else (if jt.2.val < 4 then 1262 else (if jt.2.val < 5 then 1268 else 1267)))))

checked_coverage fastCoverage0060 pairing0060 template0060 witness0060

theorem coverage0060 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0060) (maskBits m))
    cores template0060 witness0060 := by
  rw [← coresFast_eq]
  exact fastCoverage0060

theorem coverageSize0060 : ∀ q : Pattern,
    (cores (witness0060 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0060 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0060
#print axioms coverageSize0060

noncomputable def pairing0061 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 6 else 3) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0061 : List (Fin 4935) := templateData0061

noncomputable def witness0061 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 772 else if t 3 = 1 then 763 else 1112) else if t 2 = 1 then (if t 3 = 0 then 770 else if t 3 = 1 then 755 else 1108) else (if t 3 = 0 then 2161 else if t 3 = 1 then 757 else 1544)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 768 else if t 3 = 1 then 740 else 741) else if t 2 = 1 then (if t 3 = 0 then 766 else if t 3 = 1 then 720 else 723) else (if t 3 = 0 then 1144 else if t 3 = 1 then 725 else 727)) else (if t 2 = 0 then (if t 3 = 0 then 1498 else if t 3 = 1 then 1489 else 2159) else if t 2 = 1 then (if t 3 = 0 then 778 else if t 3 = 1 then 722 else 724) else (if t 3 = 0 then 1145 else if t 3 = 1 then 726 else 728))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 771 else if t 3 = 1 then 759 else 1110) else if t 2 = 1 then (if t 3 = 0 then 769 else if t 3 = 1 then 747 else 1104) else (if t 3 = 0 then 2160 else if t 3 = 1 then 751 else 1542)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 767 else if t 3 = 1 then 732 else 734) else if t 2 = 1 then (if t 3 = 0 then 765 else if t 3 = 1 then 704 else 708) else (if t 3 = 0 then 1140 else if t 3 = 1 then 712 else 716)) else (if t 2 = 0 then (if t 3 = 0 then 1497 else if t 3 = 1 then 1483 else 2157) else if t 2 = 1 then (if t 3 = 0 then 777 else if t 3 = 1 then 706 else 710) else (if t 3 = 0 then 1142 else if t 3 = 1 then 714 else 718))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 776 else if t 3 = 1 then 760 else 1111) else if t 2 = 1 then (if t 3 = 0 then 775 else if t 3 = 1 then 748 else 1105) else (if t 3 = 0 then 2162 else if t 3 = 1 then 752 else 1543)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 774 else if t 3 = 1 then 733 else 735) else if t 2 = 1 then (if t 3 = 0 then 773 else if t 3 = 1 then 705 else 709) else (if t 3 = 0 then 1141 else if t 3 = 1 then 713 else 717)) else (if t 2 = 0 then (if t 3 = 0 then 1499 else if t 3 = 1 then 1484 else 2158) else if t 2 = 1 then (if t 3 = 0 then 781 else if t 3 = 1 then 707 else 711) else (if t 3 = 0 then 1143 else if t 3 = 1 then 715 else 719))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 8 else (if jt.2.val < 2 then 703 else 30)) else (if jt.2.val < 4 then 702 else (if jt.2.val < 5 then 721 else 26))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1990 else (if jt.2.val < 2 then 2029 else 1992)) else (if jt.2.val < 4 then 2028 else (if jt.2.val < 5 then 2030 else 1983)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2151 else (if jt.2.val < 2 then 2153 else 2156)) else (if jt.2.val < 4 then 2152 else (if jt.2.val < 5 then 2155 else 2154))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1267 else (if jt.2.val < 2 then 1287 else 1269)) else (if jt.2.val < 4 then 1284 else (if jt.2.val < 5 then 1285 else 1260)))))

checked_coverage fastCoverage0061 pairing0061 template0061 witness0061

theorem coverage0061 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0061) (maskBits m))
    cores template0061 witness0061 := by
  rw [← coresFast_eq]
  exact fastCoverage0061

theorem coverageSize0061 : ∀ q : Pattern,
    (cores (witness0061 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0061 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0061
#print axioms coverageSize0061

noncomputable def pairing0062 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 7 else 4)))) (by decide +kernel)

noncomputable def template0062 : List (Fin 4935) := templateData0062

noncomputable def witness0062 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1574 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1566 else 1619) else (if t 3 = 0 then 1134 else if t 3 = 1 then 464 else 497)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1572 else if t 3 = 1 then 1570 else 1853) else if t 2 = 1 then (if t 3 = 0 then 1564 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 656 else if t 3 = 1 then 1593 else 1612)) else (if t 2 = 0 then (if t 3 = 0 then 271 else if t 3 = 1 then 855 else 878) else if t 2 = 1 then (if t 3 = 0 then 266 else if t 3 = 1 then 1589 else 1611) else (if t 3 = 0 then 2170 else if t 3 = 1 then 1597 else 1613))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1573 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1565 else 1617) else (if t 3 = 0 then 1133 else if t 3 = 1 then 463 else 494)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1571 else if t 3 = 1 then 1569 else 1851) else if t 2 = 1 then (if t 3 = 0 then 1563 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 655 else if t 3 = 1 then 1592 else 1606)) else (if t 2 = 0 then (if t 3 = 0 then 270 else if t 3 = 1 then 854 else 876) else if t 2 = 1 then (if t 3 = 0 then 265 else if t 3 = 1 then 1588 else 1604) else (if t 3 = 0 then 2169 else if t 3 = 1 then 1596 else 1608))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1586 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1582 else 1618) else (if t 3 = 0 then 1136 else if t 3 = 1 then 471 else 495)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1585 else if t 3 = 1 then 1584 else 1852) else if t 2 = 1 then (if t 3 = 0 then 1581 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 663 else if t 3 = 1 then 1595 else 1607)) else (if t 2 = 0 then (if t 3 = 0 then 275 else if t 3 = 1 then 857 else 877) else if t 2 = 1 then (if t 3 = 0 then 273 else if t 3 = 1 then 1591 else 1605) else (if t 3 = 0 then 2171 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1386 else (if jt.2.val < 2 then 1579 else 1410)) else (if jt.2.val < 4 then 1577 else (if jt.2.val < 5 then 1578 else 1390))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2000 else (if jt.2.val < 2 then 2035 else 2003)) else (if jt.2.val < 4 then 2031 else (if jt.2.val < 5 then 2032 else 1997)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1820 else (if jt.2.val < 2 then 1847 else 1823)) else (if jt.2.val < 4 then 1842 else (if jt.2.val < 5 then 1843 else 1811))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2163 else (if jt.2.val < 2 then 2165 else 2168)) else (if jt.2.val < 4 then 2164 else (if jt.2.val < 5 then 2167 else 2166)))))

checked_coverage fastCoverage0062 pairing0062 template0062 witness0062

theorem coverage0062 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0062) (maskBits m))
    cores template0062 witness0062 := by
  rw [← coresFast_eq]
  exact fastCoverage0062

theorem coverageSize0062 : ∀ q : Pattern,
    (cores (witness0062 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0062 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0062
#print axioms coverageSize0062

noncomputable def pairing0063 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 6) else (if x.2 then 4 else 7)))) (by decide +kernel)

noncomputable def template0063 : List (Fin 4935) := templateData0063

noncomputable def witness0063 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2219 else 1676) else if t 2 = 1 then (if t 3 = 0 then 2225 else if t 3 = 1 then 2207 else 1892) else (if t 3 = 0 then 698 else if t 3 = 1 then 1189 else 1190)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2213 else 1661) else if t 2 = 1 then (if t 3 = 0 then 2222 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 688 else if t 3 = 1 then 2196 else 2200)) else (if t 2 = 0 then (if t 3 = 0 then 932 else if t 3 = 1 then 358 else 359) else if t 2 = 1 then (if t 3 = 0 then 298 else if t 3 = 1 then 2195 else 2199) else (if t 3 = 0 then 1475 else if t 3 = 1 then 2197 else 2201))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2217 else 1673) else if t 2 = 1 then (if t 3 = 0 then 2223 else if t 3 = 1 then 2205 else 1889) else (if t 3 = 0 then 696 else if t 3 = 1 then 1183 else 1185)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2211 else 1658) else if t 2 = 1 then (if t 3 = 0 then 2220 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 684 else if t 3 = 1 then 2181 else 2189)) else (if t 2 = 0 then (if t 3 = 0 then 930 else if t 3 = 1 then 352 else 354) else if t 2 = 1 then (if t 3 = 0 then 294 else if t 3 = 1 then 2179 else 2187) else (if t 3 = 0 then 1473 else if t 3 = 1 then 2183 else 2191))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2218 else 1674) else if t 2 = 1 then (if t 3 = 0 then 2224 else if t 3 = 1 then 2206 else 1890) else (if t 3 = 0 then 697 else if t 3 = 1 then 1184 else 1186)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2212 else 1659) else if t 2 = 1 then (if t 3 = 0 then 2221 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 685 else if t 3 = 1 then 2182 else 2190)) else (if t 2 = 0 then (if t 3 = 0 then 931 else if t 3 = 1 then 353 else 355) else if t 2 = 1 then (if t 3 = 0 then 295 else if t 3 = 1 then 2180 else 2188) else (if t 3 = 0 then 1474 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2046 else (if jt.2.val < 2 then 2176 else 2068)) else (if jt.2.val < 4 then 2175 else (if jt.2.val < 5 then 2194 else 2064))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2133 else (if jt.2.val < 2 then 2203 else 2135)) else (if jt.2.val < 4 then 2202 else (if jt.2.val < 5 then 2204 else 2130)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2154 else (if jt.2.val < 2 then 2209 else 2156)) else (if jt.2.val < 4 then 2208 else (if jt.2.val < 5 then 2210 else 2151))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2166 else (if jt.2.val < 2 then 2216 else 2168)) else (if jt.2.val < 4 then 2214 else (if jt.2.val < 5 then 2215 else 2163)))))

checked_coverage fastCoverage0063 pairing0063 template0063 witness0063

theorem coverage0063 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0063) (maskBits m))
    cores template0063 witness0063 := by
  rw [← coresFast_eq]
  exact fastCoverage0063

theorem coverageSize0063 : ∀ q : Pattern,
    (cores (witness0063 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0063 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0063
#print axioms coverageSize0063

noncomputable def pairing0064 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0064 : List (Fin 4935) := templateData0064

noncomputable def witness0064 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2062 else if t 3 = 1 then 2054 else 1510) else if t 2 = 1 then (if t 3 = 0 then 2058 else if t 3 = 1 then 2050 else 450) else (if t 3 = 0 then 591 else if t 3 = 1 then 589 else 1120)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2060 else if t 3 = 1 then 2052 else 48) else if t 2 = 1 then (if t 3 = 0 then 2056 else if t 3 = 1 then 2048 else 2090) else (if t 3 = 0 then 1447 else if t 3 = 1 then 2101 else 2107)) else (if t 2 = 0 then (if t 3 = 0 then 837 else if t 3 = 1 then 835 else 75) else if t 2 = 1 then (if t 3 = 0 then 1733 else if t 3 = 1 then 2082 else 2098) else (if t 3 = 0 then 1453 else if t 3 = 1 then 2104 else 2111))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2061 else if t 3 = 1 then 2053 else 1509) else if t 2 = 1 then (if t 3 = 0 then 2057 else if t 3 = 1 then 2049 else 449) else (if t 3 = 0 then 590 else if t 3 = 1 then 588 else 1119)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2059 else if t 3 = 1 then 2051 else 47) else if t 2 = 1 then (if t 3 = 0 then 2055 else if t 3 = 1 then 2047 else 2089) else (if t 3 = 0 then 1446 else if t 3 = 1 then 2100 else 2106)) else (if t 2 = 0 then (if t 3 = 0 then 836 else if t 3 = 1 then 834 else 74) else if t 2 = 1 then (if t 3 = 0 then 1732 else if t 3 = 1 then 2081 else 2097) else (if t 3 = 0 then 1452 else if t 3 = 1 then 2103 else 2109))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2075 else if t 3 = 1 then 2071 else 1512) else if t 2 = 1 then (if t 3 = 0 then 2073 else if t 3 = 1 then 2069 else 455) else (if t 3 = 0 then 593 else if t 3 = 1 then 592 else 1121)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2074 else if t 3 = 1 then 2070 else 53) else if t 2 = 1 then (if t 3 = 0 then 2072 else if t 3 = 1 then 2067 else 2091) else (if t 3 = 0 then 1448 else if t 3 = 1 then 2102 else 2108)) else (if t 2 = 0 then (if t 3 = 0 then 841 else if t 3 = 1 then 840 else 77) else if t 2 = 1 then (if t 3 = 0 then 1735 else if t 3 = 1 then 2083 else 2099) else (if t 3 = 0 then 1454 else if t 3 = 1 then 2105 else 2110))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2046 else (if jt.2.val < 2 then 2066 else 2068)) else (if jt.2.val < 4 then 2063 else (if jt.2.val < 5 then 2065 else 2064))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2045 else (if jt.2.val < 2 then 2079 else 2080)) else (if jt.2.val < 4 then 2076 else (if jt.2.val < 5 then 2078 else 2077)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2232 else (if jt.2.val < 2 then 2240 else 2243)) else (if jt.2.val < 4 then 2239 else (if jt.2.val < 5 then 2242 else 2241))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2233 else (if jt.2.val < 2 then 2237 else 2238)) else (if jt.2.val < 4 then 2234 else (if jt.2.val < 5 then 2236 else 2235)))))

checked_coverage fastCoverage0064 pairing0064 template0064 witness0064

theorem coverage0064 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0064) (maskBits m))
    cores template0064 witness0064 := by
  rw [← coresFast_eq]
  exact fastCoverage0064

theorem coverageSize0064 : ∀ q : Pattern,
    (cores (witness0064 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0064 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0064
#print axioms coverageSize0064

noncomputable def pairing0065 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0065 : List (Fin 4935) := templateData0065

noncomputable def witness0065 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1320 else if t 3 = 1 then 1312 else 2125) else if t 2 = 1 then (if t 3 = 0 then 1316 else if t 3 = 1 then 1308 else 448) else (if t 3 = 0 then 1222 else if t 3 = 1 then 1211 else 503)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1318 else if t 3 = 1 then 1310 else 46) else if t 2 = 1 then (if t 3 = 0 then 1314 else if t 3 = 1 then 1306 else 1339) else (if t 3 = 0 then 1777 else if t 3 = 1 then 1370 else 1371)) else (if t 2 = 0 then (if t 3 = 0 then 258 else if t 3 = 1 then 254 else 922) else if t 2 = 1 then (if t 3 = 0 then 1353 else if t 3 = 1 then 1350 else 1357) else (if t 3 = 0 then 2119 else if t 3 = 1 then 1372 else 1373))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1319 else if t 3 = 1 then 1311 else 2124) else if t 2 = 1 then (if t 3 = 0 then 1315 else if t 3 = 1 then 1307 else 447) else (if t 3 = 0 then 1221 else if t 3 = 1 then 1208 else 500)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1317 else if t 3 = 1 then 1309 else 45) else if t 2 = 1 then (if t 3 = 0 then 1313 else if t 3 = 1 then 1305 else 1338) else (if t 3 = 0 then 1776 else if t 3 = 1 then 1362 else 1364)) else (if t 2 = 0 then (if t 3 = 0 then 257 else if t 3 = 1 then 253 else 921) else if t 2 = 1 then (if t 3 = 0 then 1352 else if t 3 = 1 then 1349 else 1356) else (if t 3 = 0 then 2118 else if t 3 = 1 then 1366 else 1368))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1333 else if t 3 = 1 then 1329 else 2126) else if t 2 = 1 then (if t 3 = 0 then 1331 else if t 3 = 1 then 1327 else 454) else (if t 3 = 0 then 1223 else if t 3 = 1 then 1209 else 501)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1332 else if t 3 = 1 then 1328 else 52) else if t 2 = 1 then (if t 3 = 0 then 1330 else if t 3 = 1 then 1325 else 1343) else (if t 3 = 0 then 1778 else if t 3 = 1 then 1363 else 1365)) else (if t 2 = 0 then (if t 3 = 0 then 262 else if t 3 = 1 then 260 else 923) else if t 2 = 1 then (if t 3 = 0 then 1355 else if t 3 = 1 then 1354 else 1360) else (if t 3 = 0 then 2120 else if t 3 = 1 then 1367 else 1369))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1304 else (if jt.2.val < 2 then 1324 else 1326)) else (if jt.2.val < 4 then 1321 else (if jt.2.val < 5 then 1323 else 1322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1971 else (if jt.2.val < 2 then 1981 else 1982)) else (if jt.2.val < 4 then 1978 else (if jt.2.val < 5 then 1980 else 1979)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1931 else (if jt.2.val < 2 then 1933 else 1937)) else (if jt.2.val < 4 then 1932 else (if jt.2.val < 5 then 1936 else 1935))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2235 else (if jt.2.val < 2 then 2246 else 2238)) else (if jt.2.val < 4 then 2244 else (if jt.2.val < 5 then 2245 else 2233)))))

checked_coverage fastCoverage0065 pairing0065 template0065 witness0065

theorem coverage0065 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0065) (maskBits m))
    cores template0065 witness0065 := by
  rw [← coresFast_eq]
  exact fastCoverage0065

theorem coverageSize0065 : ∀ q : Pattern,
    (cores (witness0065 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0065 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0065
#print axioms coverageSize0065

noncomputable def pairing0066 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0066 : List (Fin 4935) := templateData0066

noncomputable def witness0066 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 183 else 900) else if t 2 = 1 then (if t 3 = 0 then 178 else if t 3 = 1 then 156 else 158) else (if t 3 = 0 then 2117 else if t 3 = 1 then 1537 else 1538)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 185 else if t 3 = 1 then 181 else 898) else if t 2 = 1 then (if t 3 = 0 then 170 else if t 3 = 1 then 136 else 142) else (if t 3 = 0 then 171 else if t 3 = 1 then 139 else 143)) else (if t 2 = 0 then (if t 3 = 0 then 1501 else if t 3 = 1 then 199 else 2129) else if t 2 = 1 then (if t 3 = 0 then 892 else if t 3 = 1 then 140 else 144) else (if t 3 = 0 then 893 else if t 3 = 1 then 141 else 145))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 182 else 899) else if t 2 = 1 then (if t 3 = 0 then 174 else if t 3 = 1 then 146 else 152) else (if t 3 = 0 then 2115 else if t 3 = 1 then 1531 else 1535)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 184 else if t 3 = 1 then 180 else 897) else if t 2 = 1 then (if t 3 = 0 then 160 else if t 3 = 1 then 117 else 128) else (if t 3 = 0 then 162 else if t 3 = 1 then 121 else 130)) else (if t 2 = 0 then (if t 3 = 0 then 1500 else if t 3 = 1 then 198 else 2127) else if t 2 = 1 then (if t 3 = 0 then 888 else if t 3 = 1 then 124 else 132) else (if t 3 = 0 then 890 else if t 3 = 1 then 126 else 134))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 189 else 902) else if t 2 = 1 then (if t 3 = 0 then 175 else if t 3 = 1 then 147 else 153) else (if t 3 = 0 then 2116 else if t 3 = 1 then 1532 else 1536)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 190 else if t 3 = 1 then 188 else 901) else if t 2 = 1 then (if t 3 = 0 then 161 else if t 3 = 1 then 119 else 129) else (if t 3 = 0 then 163 else if t 3 = 1 then 122 else 131)) else (if t 2 = 0 then (if t 3 = 0 then 1502 else if t 3 = 1 then 202 else 2128) else if t 2 = 1 then (if t 3 = 0 then 889 else if t 3 = 1 then 125 else 133) else (if t 3 = 0 then 891 else if t 3 = 1 then 127 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 114 else (if jt.2.val < 2 then 116 else 138)) else (if jt.2.val < 4 then 115 else (if jt.2.val < 5 then 137 else 118))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2004 else (if jt.2.val < 2 then 2006 else 2009)) else (if jt.2.val < 4 then 2005 else (if jt.2.val < 5 then 2008 else 2007)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2241 else (if jt.2.val < 2 then 2249 else 2243)) else (if jt.2.val < 4 then 2247 else (if jt.2.val < 5 then 2248 else 2232))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 881 else (if jt.2.val < 2 then 883 else 887)) else (if jt.2.val < 4 then 882 else (if jt.2.val < 5 then 886 else 885)))))

checked_coverage fastCoverage0066 pairing0066 template0066 witness0066

theorem coverage0066 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0066) (maskBits m))
    cores template0066 witness0066 := by
  rw [← coresFast_eq]
  exact fastCoverage0066

theorem coverageSize0066 : ∀ q : Pattern,
    (cores (witness0066 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0066 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0066
#print axioms coverageSize0066

noncomputable def pairing0067 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 5 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0067 : List (Fin 4935) := templateData0067

noncomputable def witness0067 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1008 else if t 3 = 1 then 1004 else 104) else if t 2 = 1 then (if t 3 = 0 then 995 else if t 3 = 1 then 977 else 978) else (if t 3 = 0 then 1433 else if t 3 = 1 then 1801 else 2138)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1006 else if t 3 = 1 then 1000 else 100) else if t 2 = 1 then (if t 3 = 0 then 991 else if t 3 = 1 then 957 else 961) else (if t 3 = 0 then 992 else if t 3 = 1 then 960 else 962)) else (if t 2 = 0 then (if t 3 = 0 then 2140 else if t 3 = 1 then 304 else 1478) else if t 2 = 1 then (if t 3 = 0 then 373 else if t 3 = 1 then 963 else 965) else (if t 3 = 0 then 374 else if t 3 = 1 then 964 else 966))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1007 else if t 3 = 1 then 1002 else 102) else if t 2 = 1 then (if t 3 = 0 then 993 else if t 3 = 1 then 967 else 971) else (if t 3 = 0 then 1430 else if t 3 = 1 then 1795 else 2136)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1005 else if t 3 = 1 then 996 else 96) else if t 2 = 1 then (if t 3 = 0 then 987 else if t 3 = 1 then 939 else 945) else (if t 3 = 0 then 989 else if t 3 = 1 then 943 else 947)) else (if t 2 = 0 then (if t 3 = 0 then 2139 else if t 3 = 1 then 300 else 1476) else if t 2 = 1 then (if t 3 = 0 then 367 else if t 3 = 1 then 949 else 953) else (if t 3 = 0 then 369 else if t 3 = 1 then 951 else 955))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1010 else if t 3 = 1 then 1003 else 103) else if t 2 = 1 then (if t 3 = 0 then 994 else if t 3 = 1 then 968 else 972) else (if t 3 = 0 then 1431 else if t 3 = 1 then 1796 else 2137)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1009 else if t 3 = 1 then 997 else 97) else if t 2 = 1 then (if t 3 = 0 then 988 else if t 3 = 1 then 941 else 946) else (if t 3 = 0 then 990 else if t 3 = 1 then 944 else 948)) else (if t 2 = 0 then (if t 3 = 0 then 2141 else if t 3 = 1 then 301 else 1477) else if t 2 = 1 then (if t 3 = 0 then 368 else if t 3 = 1 then 950 else 954) else (if t 3 = 0 then 370 else if t 3 = 1 then 952 else 956))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 936 else (if jt.2.val < 2 then 938 else 959)) else (if jt.2.val < 4 then 937 else (if jt.2.val < 5 then 958 else 940))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2130 else (if jt.2.val < 2 then 2132 else 2135)) else (if jt.2.val < 4 then 2131 else (if jt.2.val < 5 then 2134 else 2133)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1935 else (if jt.2.val < 2 then 1943 else 1937)) else (if jt.2.val < 4 then 1941 else (if jt.2.val < 5 then 1942 else 1931))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 885 else (if jt.2.val < 2 then 985 else 887)) else (if jt.2.val < 4 then 984 else (if jt.2.val < 5 then 986 else 881)))))

checked_coverage fastCoverage0067 pairing0067 template0067 witness0067

theorem coverage0067 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0067) (maskBits m))
    cores template0067 witness0067 := by
  rw [← coresFast_eq]
  exact fastCoverage0067

theorem coverageSize0067 : ∀ q : Pattern,
    (cores (witness0067 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0067 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0067
#print axioms coverageSize0067

noncomputable def pairing0068 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0068 : List (Fin 4935) := templateData0068

noncomputable def witness0068 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1033 else if t 3 = 1 then 1029 else 469) else if t 2 = 1 then (if t 3 = 0 then 1031 else if t 3 = 1 then 1027 else 467) else (if t 3 = 0 then 1549 else if t 3 = 1 then 595 else 2150)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1025 else if t 3 = 1 then 1021 else 1071) else if t 2 = 1 then (if t 3 = 0 then 1023 else if t 3 = 1 then 1019 else 1069) else (if t 3 = 0 then 784 else if t 3 = 1 then 1078 else 1090)) else (if t 2 = 0 then (if t 3 = 0 then 2146 else if t 3 = 1 then 1813 else 1599) else if t 2 = 1 then (if t 3 = 0 then 1049 else if t 3 = 1 then 1046 else 1075) else (if t 3 = 0 then 790 else if t 3 = 1 then 1084 else 1091))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1032 else if t 3 = 1 then 1028 else 468) else if t 2 = 1 then (if t 3 = 0 then 1030 else if t 3 = 1 then 1026 else 466) else (if t 3 = 0 then 1548 else if t 3 = 1 then 594 else 2148)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1024 else if t 3 = 1 then 1020 else 1070) else if t 2 = 1 then (if t 3 = 0 then 1022 else if t 3 = 1 then 1018 else 1068) else (if t 3 = 0 then 783 else if t 3 = 1 then 1077 else 1086)) else (if t 2 = 0 then (if t 3 = 0 then 2145 else if t 3 = 1 then 1812 else 1598) else if t 2 = 1 then (if t 3 = 0 then 1048 else if t 3 = 1 then 1045 else 1074) else (if t 3 = 0 then 789 else if t 3 = 1 then 1083 else 1088))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1044 else if t 3 = 1 then 1042 else 473) else if t 2 = 1 then (if t 3 = 0 then 1043 else if t 3 = 1 then 1041 else 472) else (if t 3 = 0 then 1550 else if t 3 = 1 then 598 else 2149)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1040 else if t 3 = 1 then 1038 else 1073) else if t 2 = 1 then (if t 3 = 0 then 1039 else if t 3 = 1 then 1037 else 1072) else (if t 3 = 0 then 787 else if t 3 = 1 then 1081 else 1087)) else (if t 2 = 0 then (if t 3 = 0 then 2147 else if t 3 = 1 then 1817 else 1601) else if t 2 = 1 then (if t 3 = 0 then 1055 else if t 3 = 1 then 1054 else 1076) else (if t 3 = 0 then 791 else if t 3 = 1 then 1085 else 1089))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 936 else (if jt.2.val < 2 then 1036 else 959)) else (if jt.2.val < 4 then 1034 else (if jt.2.val < 5 then 1035 else 940))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2077 else (if jt.2.val < 2 then 2144 else 2080)) else (if jt.2.val < 4 then 2142 else (if jt.2.val < 5 then 2143 else 2045)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1944 else (if jt.2.val < 2 then 1946 else 1949)) else (if jt.2.val < 4 then 1945 else (if jt.2.val < 5 then 1948 else 1947))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1017 else (if jt.2.val < 2 then 1066 else 1067)) else (if jt.2.val < 4 then 1063 else (if jt.2.val < 5 then 1065 else 1064)))))

checked_coverage fastCoverage0068 pairing0068 template0068 witness0068

theorem coverage0068 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0068) (maskBits m))
    cores template0068 witness0068 := by
  rw [← coresFast_eq]
  exact fastCoverage0068

theorem coverageSize0068 : ∀ q : Pattern,
    (cores (witness0068 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0068 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0068
#print axioms coverageSize0068

noncomputable def pairing0069 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 7 else 3) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0069 : List (Fin 4935) := templateData0069

noncomputable def witness0069 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 620 else 1134) else if t 2 = 1 then (if t 3 = 0 then 626 else if t 3 = 1 then 618 else 1132) else (if t 3 = 0 then 2161 else if t 3 = 1 then 694 else 1526)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 624 else if t 3 = 1 then 616 else 656) else if t 2 = 1 then (if t 3 = 0 then 622 else if t 3 = 1 then 614 else 654) else (if t 3 = 0 then 1144 else if t 3 = 1 then 680 else 682)) else (if t 2 = 0 then (if t 3 = 0 then 1462 else if t 3 = 1 then 1459 else 2170) else if t 2 = 1 then (if t 3 = 0 then 646 else if t 3 = 1 then 641 else 667) else (if t 3 = 0 then 1145 else if t 3 = 1 then 681 else 683))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 619 else 1133) else if t 2 = 1 then (if t 3 = 0 then 625 else if t 3 = 1 then 617 else 1131) else (if t 3 = 0 then 2160 else if t 3 = 1 then 690 else 1524)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 623 else if t 3 = 1 then 615 else 655) else if t 2 = 1 then (if t 3 = 0 then 621 else if t 3 = 1 then 613 else 653) else (if t 3 = 0 then 1140 else if t 3 = 1 then 672 else 676)) else (if t 2 = 0 then (if t 3 = 0 then 1461 else if t 3 = 1 then 1458 else 2169) else if t 2 = 1 then (if t 3 = 0 then 645 else if t 3 = 1 then 640 else 666) else (if t 3 = 0 then 1142 else if t 3 = 1 then 674 else 678))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 635 else 1136) else if t 2 = 1 then (if t 3 = 0 then 638 else if t 3 = 1 then 634 else 1135) else (if t 3 = 0 then 2162 else if t 3 = 1 then 691 else 1525)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 637 else if t 3 = 1 then 633 else 663) else if t 2 = 1 then (if t 3 = 0 then 636 else if t 3 = 1 then 632 else 662) else (if t 3 = 0 then 1141 else if t 3 = 1 then 673 else 677)) else (if t 2 = 0 then (if t 3 = 0 then 1464 else if t 3 = 1 then 1463 else 2171) else if t 2 = 1 then (if t 3 = 0 then 651 else if t 3 = 1 then 649 else 670) else (if t 3 = 0 then 1143 else if t 3 = 1 then 675 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 114 else (if jt.2.val < 2 then 631 else 138)) else (if jt.2.val < 4 then 629 else (if jt.2.val < 5 then 630 else 118))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1979 else (if jt.2.val < 2 then 2016 else 1982)) else (if jt.2.val < 4 then 2013 else (if jt.2.val < 5 then 2014 else 1971)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2250 else (if jt.2.val < 2 then 2252 else 2255)) else (if jt.2.val < 4 then 2251 else (if jt.2.val < 5 then 2254 else 2253))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1064 else (if jt.2.val < 2 then 1130 else 1067)) else (if jt.2.val < 4 then 1125 else (if jt.2.val < 5 then 1126 else 1017)))))

checked_coverage fastCoverage0069 pairing0069 template0069 witness0069

theorem coverage0069 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0069) (maskBits m))
    cores template0069 witness0069 := by
  rw [← coresFast_eq]
  exact fastCoverage0069

theorem coverageSize0069 : ∀ q : Pattern,
    (cores (witness0069 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0069 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0069
#print axioms coverageSize0069

noncomputable def pairing0070 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 6 else 4)))) (by decide +kernel)

noncomputable def template0070 : List (Fin 4935) := templateData0070

noncomputable def witness0070 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1684 else if t 3 = 1 then 1682 else 2174) else if t 2 = 1 then (if t 3 = 0 then 1675 else if t 3 = 1 then 1669 else 1670) else (if t 3 = 0 then 1112 else if t 3 = 1 then 553 else 555)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1680 else if t 3 = 1 then 1678 else 1853) else if t 2 = 1 then (if t 3 = 0 then 1660 else if t 3 = 1 then 1644 else 1649) else (if t 3 = 0 then 741 else if t 3 = 1 then 1647 else 1651)) else (if t 2 = 0 then (if t 3 = 0 then 402 else if t 3 = 1 then 864 else 878) else if t 2 = 1 then (if t 3 = 0 then 357 else if t 3 = 1 then 1646 else 1650) else (if t 3 = 0 then 2159 else if t 3 = 1 then 1648 else 1652))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1683 else if t 3 = 1 then 1681 else 2172) else if t 2 = 1 then (if t 3 = 0 then 1671 else if t 3 = 1 then 1665 else 1667) else (if t 3 = 0 then 1110 else if t 3 = 1 then 546 else 550)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1679 else if t 3 = 1 then 1677 else 1851) else if t 2 = 1 then (if t 3 = 0 then 1656 else if t 3 = 1 then 1628 else 1636) else (if t 3 = 0 then 734 else if t 3 = 1 then 1632 else 1640)) else (if t 2 = 0 then (if t 3 = 0 then 401 else if t 3 = 1 then 863 else 876) else if t 2 = 1 then (if t 3 = 0 then 350 else if t 3 = 1 then 1630 else 1638) else (if t 3 = 0 then 2157 else if t 3 = 1 then 1634 else 1642))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1688 else if t 3 = 1 then 1687 else 2173) else if t 2 = 1 then (if t 3 = 0 then 1672 else if t 3 = 1 then 1666 else 1668) else (if t 3 = 0 then 1111 else if t 3 = 1 then 547 else 551)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1686 else if t 3 = 1 then 1685 else 1852) else if t 2 = 1 then (if t 3 = 0 then 1657 else if t 3 = 1 then 1629 else 1637) else (if t 3 = 0 then 735 else if t 3 = 1 then 1633 else 1641)) else (if t 2 = 0 then (if t 3 = 0 then 404 else if t 3 = 1 then 866 else 877) else if t 2 = 1 then (if t 3 = 0 then 351 else if t 3 = 1 then 1631 else 1639) else (if t 3 = 0 then 2158 else if t 3 = 1 then 1635 else 1643))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1304 else (if jt.2.val < 2 then 1627 else 1326)) else (if jt.2.val < 4 then 1626 else (if jt.2.val < 5 then 1645 else 1322))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2007 else (if jt.2.val < 2 then 2041 else 2009)) else (if jt.2.val < 4 then 2040 else (if jt.2.val < 5 then 2042 else 2004)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1947 else (if jt.2.val < 2 then 1964 else 1949)) else (if jt.2.val < 4 then 1959 else (if jt.2.val < 5 then 1960 else 1944))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2256 else (if jt.2.val < 2 then 2258 else 2261)) else (if jt.2.val < 4 then 2257 else (if jt.2.val < 5 then 2260 else 2259)))))

checked_coverage fastCoverage0070 pairing0070 template0070 witness0070

theorem coverage0070 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0070) (maskBits m))
    cores template0070 witness0070 := by
  rw [← coresFast_eq]
  exact fastCoverage0070

theorem coverageSize0070 : ∀ q : Pattern,
    (cores (witness0070 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0070 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0070
#print axioms coverageSize0070

noncomputable def pairing0071 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 5)) else (if x.1.val < 3 then (if x.2 then 3 else 7) else (if x.2 then 4 else 6)))) (by decide +kernel)

noncomputable def template0071 : List (Fin 4935) := templateData0071

noncomputable def witness0071 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2230 else if t 3 = 1 then 2225 else 1622) else if t 2 = 1 then (if t 3 = 0 then 2219 else if t 3 = 1 then 2207 else 1892) else (if t 3 = 0 then 764 else if t 3 = 1 then 1189 else 1190)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2228 else if t 3 = 1 then 2222 else 1616) else if t 2 = 1 then (if t 3 = 0 then 2213 else if t 3 = 1 then 2193 else 2198) else (if t 3 = 0 then 742 else if t 3 = 1 then 2196 else 2200)) else (if t 2 = 0 then (if t 3 = 0 then 932 else if t 3 = 1 then 298 else 299) else if t 2 = 1 then (if t 3 = 0 then 358 else if t 3 = 1 then 2195 else 2199) else (if t 3 = 0 then 1490 else if t 3 = 1 then 2197 else 2201))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2229 else if t 3 = 1 then 2223 else 1620) else if t 2 = 1 then (if t 3 = 0 then 2217 else if t 3 = 1 then 2205 else 1889) else (if t 3 = 0 then 761 else if t 3 = 1 then 1183 else 1185)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2226 else if t 3 = 1 then 2220 else 1614) else if t 2 = 1 then (if t 3 = 0 then 2211 else if t 3 = 1 then 2177 else 2185) else (if t 3 = 0 then 736 else if t 3 = 1 then 2181 else 2189)) else (if t 2 = 0 then (if t 3 = 0 then 930 else if t 3 = 1 then 294 else 296) else if t 2 = 1 then (if t 3 = 0 then 352 else if t 3 = 1 then 2179 else 2187) else (if t 3 = 0 then 1487 else if t 3 = 1 then 2183 else 2191))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 2231 else if t 3 = 1 then 2224 else 1621) else if t 2 = 1 then (if t 3 = 0 then 2218 else if t 3 = 1 then 2206 else 1890) else (if t 3 = 0 then 762 else if t 3 = 1 then 1184 else 1186)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 2227 else if t 3 = 1 then 2221 else 1615) else if t 2 = 1 then (if t 3 = 0 then 2212 else if t 3 = 1 then 2178 else 2186) else (if t 3 = 0 then 737 else if t 3 = 1 then 2182 else 2190)) else (if t 2 = 0 then (if t 3 = 0 then 931 else if t 3 = 1 then 295 else 297) else if t 2 = 1 then (if t 3 = 0 then 353 else if t 3 = 1 then 2180 else 2188) else (if t 3 = 0 then 1488 else if t 3 = 1 then 2184 else 2192))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2046 else (if jt.2.val < 2 then 2176 else 2068)) else (if jt.2.val < 4 then 2175 else (if jt.2.val < 5 then 2194 else 2064))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2133 else (if jt.2.val < 2 then 2203 else 2135)) else (if jt.2.val < 4 then 2202 else (if jt.2.val < 5 then 2204 else 2130)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2253 else (if jt.2.val < 2 then 2267 else 2255)) else (if jt.2.val < 4 then 2265 else (if jt.2.val < 5 then 2266 else 2250))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2259 else (if jt.2.val < 2 then 2263 else 2261)) else (if jt.2.val < 4 then 2262 else (if jt.2.val < 5 then 2264 else 2256)))))

checked_coverage fastCoverage0071 pairing0071 template0071 witness0071

theorem coverage0071 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0071) (maskBits m))
    cores template0071 witness0071 := by
  rw [← coresFast_eq]
  exact fastCoverage0071

theorem coverageSize0071 : ∀ q : Pattern,
    (cores (witness0071 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0071 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0071
#print axioms coverageSize0071

noncomputable def pairing0072 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0072 : List (Fin 4935) := templateData0072

noncomputable def witness0072 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1711 else if t 3 = 1 then 1703 else 1498) else if t 2 = 1 then (if t 3 = 0 then 1707 else if t 3 = 1 then 1699 else 778) else (if t 3 = 0 then 1053 else if t 3 = 1 then 1049 else 790)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1709 else if t 3 = 1 then 1701 else 394) else if t 2 = 1 then (if t 3 = 0 then 1705 else if t 3 = 1 then 1697 else 1753) else (if t 3 = 0 then 1733 else if t 3 = 1 then 1730 else 1756)) else (if t 2 = 0 then (if t 3 = 0 then 258 else if t 3 = 1 then 256 else 929) else if t 2 = 1 then (if t 3 = 0 then 1353 else if t 3 = 1 then 1747 else 1762) else (if t 3 = 0 then 1359 else if t 3 = 1 then 1750 else 1763))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1710 else if t 3 = 1 then 1702 else 1497) else if t 2 = 1 then (if t 3 = 0 then 1706 else if t 3 = 1 then 1698 else 777) else (if t 3 = 0 then 1052 else if t 3 = 1 then 1048 else 789)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1708 else if t 3 = 1 then 1700 else 393) else if t 2 = 1 then (if t 3 = 0 then 1704 else if t 3 = 1 then 1696 else 1752) else (if t 3 = 0 then 1732 else if t 3 = 1 then 1729 else 1755)) else (if t 2 = 0 then (if t 3 = 0 then 257 else if t 3 = 1 then 255 else 926) else if t 2 = 1 then (if t 3 = 0 then 1352 else if t 3 = 1 then 1746 else 1758) else (if t 3 = 0 then 1358 else if t 3 = 1 then 1749 else 1760))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1724 else if t 3 = 1 then 1720 else 1499) else if t 2 = 1 then (if t 3 = 0 then 1722 else if t 3 = 1 then 1718 else 781) else (if t 3 = 0 then 1057 else if t 3 = 1 then 1055 else 791)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1723 else if t 3 = 1 then 1719 else 397) else if t 2 = 1 then (if t 3 = 0 then 1721 else if t 3 = 1 then 1716 else 1754) else (if t 3 = 0 then 1735 else if t 3 = 1 then 1734 else 1757)) else (if t 2 = 0 then (if t 3 = 0 then 262 else if t 3 = 1 then 261 else 927) else if t 2 = 1 then (if t 3 = 0 then 1355 else if t 3 = 1 then 1748 else 1759) else (if t 3 = 0 then 1361 else if t 3 = 1 then 1751 else 1761))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1695 else (if jt.2.val < 2 then 1715 else 1717)) else (if jt.2.val < 4 then 1712 else (if jt.2.val < 5 then 1714 else 1713))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2268 else (if jt.2.val < 2 then 2278 else 2279)) else (if jt.2.val < 4 then 2275 else (if jt.2.val < 5 then 2277 else 2276)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2269 else (if jt.2.val < 2 then 2273 else 2274)) else (if jt.2.val < 4 then 2270 else (if jt.2.val < 5 then 2272 else 2271))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1692 else (if jt.2.val < 2 then 1737 else 1740)) else (if jt.2.val < 4 then 1736 else (if jt.2.val < 5 then 1739 else 1738)))))

checked_coverage fastCoverage0072 pairing0072 template0072 witness0072

theorem coverage0072 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0072) (maskBits m))
    cores template0072 witness0072 := by
  rw [← coresFast_eq]
  exact fastCoverage0072

theorem coverageSize0072 : ∀ q : Pattern,
    (cores (witness0072 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0072 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0072
#print axioms coverageSize0072

noncomputable def pairing0073 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0073 : List (Fin 4935) := templateData0073

noncomputable def witness0073 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1441 else if t 3 = 1 then 1432 else 1775) else if t 2 = 1 then (if t 3 = 0 then 1437 else if t 3 = 1 then 1422 else 756) else (if t 3 = 0 then 591 else if t 3 = 1 then 567 else 1109)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1439 else if t 3 = 1 then 1427 else 372) else if t 2 = 1 then (if t 3 = 0 then 1435 else if t 3 = 1 then 1408 else 1412) else (if t 3 = 0 then 1447 else if t 3 = 1 then 1411 else 1413)) else (if t 2 = 0 then (if t 3 = 0 then 1012 else if t 3 = 1 then 992 else 374) else if t 2 = 1 then (if t 3 = 0 then 1777 else if t 3 = 1 then 1414 else 1416) else (if t 3 = 0 then 1780 else if t 3 = 1 then 1415 else 1417))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1440 else if t 3 = 1 then 1428 else 1773) else if t 2 = 1 then (if t 3 = 0 then 1436 else if t 3 = 1 then 1418 else 749) else (if t 3 = 0 then 590 else if t 3 = 1 then 558 else 1106)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1438 else if t 3 = 1 then 1423 else 365) else if t 2 = 1 then (if t 3 = 0 then 1434 else if t 3 = 1 then 1389 else 1396) else (if t 3 = 0 then 1446 else if t 3 = 1 then 1393 else 1398)) else (if t 2 = 0 then (if t 3 = 0 then 1011 else if t 3 = 1 then 989 else 369) else if t 2 = 1 then (if t 3 = 0 then 1776 else if t 3 = 1 then 1400 else 1404) else (if t 3 = 0 then 1779 else if t 3 = 1 then 1402 else 1406))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1445 else if t 3 = 1 then 1429 else 1774) else if t 2 = 1 then (if t 3 = 0 then 1443 else if t 3 = 1 then 1419 else 750) else (if t 3 = 0 then 593 else if t 3 = 1 then 559 else 1107)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1444 else if t 3 = 1 then 1424 else 366) else if t 2 = 1 then (if t 3 = 0 then 1442 else if t 3 = 1 then 1391 else 1397) else (if t 3 = 0 then 1448 else if t 3 = 1 then 1394 else 1399)) else (if t 2 = 0 then (if t 3 = 0 then 1013 else if t 3 = 1 then 990 else 370) else if t 2 = 1 then (if t 3 = 0 then 1778 else if t 3 = 1 then 1401 else 1405) else (if t 3 = 0 then 1781 else if t 3 = 1 then 1403 else 1407))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1386 else (if jt.2.val < 2 then 1388 else 1410)) else (if jt.2.val < 4 then 1387 else (if jt.2.val < 5 then 1409 else 1390))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2280 else (if jt.2.val < 2 then 2282 else 2285)) else (if jt.2.val < 4 then 2281 else (if jt.2.val < 5 then 2284 else 2283)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1986 else (if jt.2.val < 2 then 1988 else 1994)) else (if jt.2.val < 4 then 1987 else (if jt.2.val < 5 then 1993 else 1989))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1738 else (if jt.2.val < 2 then 1769 else 1740)) else (if jt.2.val < 4 then 1764 else (if jt.2.val < 5 then 1765 else 1692)))))

checked_coverage fastCoverage0073 pairing0073 template0073 witness0073

theorem coverage0073 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0073) (maskBits m))
    cores template0073 witness0073 := by
  rw [← coresFast_eq]
  exact fastCoverage0073

theorem coverageSize0073 : ∀ q : Pattern,
    (cores (witness0073 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0073 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0073
#print axioms coverageSize0073

noncomputable def pairing0074 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0074 : List (Fin 4935) := templateData0074

noncomputable def witness0074 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 811 else if t 3 = 1 then 803 else 402) else if t 2 = 1 then (if t 3 = 0 then 807 else if t 3 = 1 then 799 else 864) else (if t 3 = 0 then 1816 else if t 3 = 1 then 1813 else 1690)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 809 else if t 3 = 1 then 801 else 400) else if t 2 = 1 then (if t 3 = 0 then 805 else if t 3 = 1 then 797 else 862) else (if t 3 = 0 then 835 else if t 3 = 1 then 830 else 868)) else (if t 2 = 0 then (if t 3 = 0 then 1471 else if t 3 = 1 then 269 else 1790) else if t 2 = 1 then (if t 3 = 0 then 65 else if t 3 = 1 then 853 else 874) else (if t 3 = 0 then 75 else if t 3 = 1 then 859 else 875))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 810 else if t 3 = 1 then 802 else 401) else if t 2 = 1 then (if t 3 = 0 then 806 else if t 3 = 1 then 798 else 863) else (if t 3 = 0 then 1815 else if t 3 = 1 then 1812 else 1689)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 808 else if t 3 = 1 then 800 else 399) else if t 2 = 1 then (if t 3 = 0 then 804 else if t 3 = 1 then 796 else 861) else (if t 3 = 0 then 834 else if t 3 = 1 then 829 else 867)) else (if t 2 = 0 then (if t 3 = 0 then 1470 else if t 3 = 1 then 268 else 1788) else if t 2 = 1 then (if t 3 = 0 then 64 else if t 3 = 1 then 852 else 870) else (if t 3 = 0 then 74 else if t 3 = 1 then 858 else 872))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 824 else if t 3 = 1 then 820 else 404) else if t 2 = 1 then (if t 3 = 0 then 822 else if t 3 = 1 then 818 else 866) else (if t 3 = 0 then 1818 else if t 3 = 1 then 1817 else 1691)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 823 else if t 3 = 1 then 819 else 403) else if t 2 = 1 then (if t 3 = 0 then 821 else if t 3 = 1 then 816 else 865) else (if t 3 = 0 then 840 else if t 3 = 1 then 838 else 869)) else (if t 2 = 0 then (if t 3 = 0 then 1472 else if t 3 = 1 then 274 else 1789) else if t 2 = 1 then (if t 3 = 0 then 70 else if t 3 = 1 then 856 else 871) else (if t 3 = 0 then 77 else if t 3 = 1 then 860 else 873))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 795 else (if jt.2.val < 2 then 815 else 817)) else (if jt.2.val < 4 then 812 else (if jt.2.val < 5 then 814 else 813))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2288 else (if jt.2.val < 2 then 2293 else 2294)) else (if jt.2.val < 4 then 2290 else (if jt.2.val < 5 then 2292 else 2291)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2271 else (if jt.2.val < 2 then 2289 else 2274)) else (if jt.2.val < 4 then 2286 else (if jt.2.val < 5 then 2287 else 2269))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 792 else (if jt.2.val < 2 then 843 else 846)) else (if jt.2.val < 4 then 842 else (if jt.2.val < 5 then 845 else 844)))))

checked_coverage fastCoverage0074 pairing0074 template0074 witness0074

theorem coverage0074 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0074) (maskBits m))
    cores template0074 witness0074 := by
  rw [← coresFast_eq]
  exact fastCoverage0074

theorem coverageSize0074 : ∀ q : Pattern,
    (cores (witness0074 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0074 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0074
#print axioms coverageSize0074

noncomputable def pairing0075 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 6 else 2)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0075 : List (Fin 4935) := templateData0075

noncomputable def witness0075 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 187 else if t 3 = 1 then 178 else 896) else if t 2 = 1 then (if t 3 = 0 then 183 else if t 3 = 1 then 156 else 157) else (if t 3 = 0 then 1546 else if t 3 = 1 then 1537 else 1835)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 185 else if t 3 = 1 then 170 else 892) else if t 2 = 1 then (if t 3 = 0 then 181 else if t 3 = 1 then 136 else 140) else (if t 3 = 0 then 193 else if t 3 = 1 then 139 else 141)) else (if t 2 = 0 then (if t 3 = 0 then 1807 else if t 3 = 1 then 172 else 1496) else if t 2 = 1 then (if t 3 = 0 then 898 else if t 3 = 1 then 142 else 144) else (if t 3 = 0 then 904 else if t 3 = 1 then 143 else 145))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 186 else if t 3 = 1 then 174 else 894) else if t 2 = 1 then (if t 3 = 0 then 182 else if t 3 = 1 then 146 else 150) else (if t 3 = 0 then 1545 else if t 3 = 1 then 1531 else 1833)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 184 else if t 3 = 1 then 160 else 888) else if t 2 = 1 then (if t 3 = 0 then 180 else if t 3 = 1 then 117 else 124) else (if t 3 = 0 then 192 else if t 3 = 1 then 121 else 126)) else (if t 2 = 0 then (if t 3 = 0 then 1806 else if t 3 = 1 then 166 else 1494) else if t 2 = 1 then (if t 3 = 0 then 897 else if t 3 = 1 then 128 else 132) else (if t 3 = 0 then 903 else if t 3 = 1 then 130 else 134))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 191 else if t 3 = 1 then 175 else 895) else if t 2 = 1 then (if t 3 = 0 then 189 else if t 3 = 1 then 147 else 151) else (if t 3 = 0 then 1547 else if t 3 = 1 then 1532 else 1834)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 190 else if t 3 = 1 then 161 else 889) else if t 2 = 1 then (if t 3 = 0 then 188 else if t 3 = 1 then 119 else 125) else (if t 3 = 0 then 196 else if t 3 = 1 then 122 else 127)) else (if t 2 = 0 then (if t 3 = 0 then 1808 else if t 3 = 1 then 167 else 1495) else if t 2 = 1 then (if t 3 = 0 then 901 else if t 3 = 1 then 129 else 133) else (if t 3 = 0 then 905 else if t 3 = 1 then 131 else 135))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 114 else (if jt.2.val < 2 then 116 else 138)) else (if jt.2.val < 4 then 115 else (if jt.2.val < 5 then 137 else 118))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2295 else (if jt.2.val < 2 then 2297 else 2300)) else (if jt.2.val < 4 then 2296 else (if jt.2.val < 5 then 2299 else 2298)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1989 else (if jt.2.val < 2 then 2011 else 1994)) else (if jt.2.val < 4 then 2010 else (if jt.2.val < 5 then 2012 else 1986))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 844 else (if jt.2.val < 2 then 884 else 846)) else (if jt.2.val < 4 then 879 else (if jt.2.val < 5 then 880 else 792)))))

checked_coverage fastCoverage0075 pairing0075 template0075 witness0075

theorem coverage0075 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0075) (maskBits m))
    cores template0075 witness0075 := by
  rw [← coresFast_eq]
  exact fastCoverage0075

theorem coverageSize0075 : ∀ q : Pattern,
    (cores (witness0075 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0075 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0075
#print axioms coverageSize0075

noncomputable def pairing0076 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0076 : List (Fin 4935) := templateData0076

noncomputable def witness0076 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 628 else if t 3 = 1 then 624 else 1148) else if t 2 = 1 then (if t 3 = 0 then 626 else if t 3 = 1 then 622 else 1144) else (if t 3 = 0 then 1519 else if t 3 = 1 then 659 else 1826)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 620 else if t 3 = 1 then 616 else 688) else if t 2 = 1 then (if t 3 = 0 then 618 else if t 3 = 1 then 614 else 680) else (if t 3 = 0 then 1132 else if t 3 = 1 then 654 else 682)) else (if t 2 = 0 then (if t 3 = 0 then 1786 else if t 3 = 1 then 1459 else 1475) else if t 2 = 1 then (if t 3 = 0 then 644 else if t 3 = 1 then 641 else 681) else (if t 3 = 0 then 1138 else if t 3 = 1 then 667 else 683))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 627 else if t 3 = 1 then 623 else 1146) else if t 2 = 1 then (if t 3 = 0 then 625 else if t 3 = 1 then 621 else 1140) else (if t 3 = 0 then 1518 else if t 3 = 1 then 658 else 1824)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 619 else if t 3 = 1 then 615 else 684) else if t 2 = 1 then (if t 3 = 0 then 617 else if t 3 = 1 then 613 else 672) else (if t 3 = 0 then 1131 else if t 3 = 1 then 653 else 676)) else (if t 2 = 0 then (if t 3 = 0 then 1785 else if t 3 = 1 then 1458 else 1473) else if t 2 = 1 then (if t 3 = 0 then 643 else if t 3 = 1 then 640 else 674) else (if t 3 = 0 then 1137 else if t 3 = 1 then 666 else 678))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 639 else if t 3 = 1 then 637 else 1147) else if t 2 = 1 then (if t 3 = 0 then 638 else if t 3 = 1 then 636 else 1141) else (if t 3 = 0 then 1520 else if t 3 = 1 then 664 else 1825)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 635 else if t 3 = 1 then 633 else 685) else if t 2 = 1 then (if t 3 = 0 then 634 else if t 3 = 1 then 632 else 673) else (if t 3 = 0 then 1135 else if t 3 = 1 then 662 else 677)) else (if t 2 = 0 then (if t 3 = 0 then 1787 else if t 3 = 1 then 1463 else 1474) else if t 2 = 1 then (if t 3 = 0 then 650 else if t 3 = 1 then 649 else 675) else (if t 3 = 0 then 1139 else if t 3 = 1 then 670 else 679))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 114 else (if jt.2.val < 2 then 631 else 138)) else (if jt.2.val < 4 then 629 else (if jt.2.val < 5 then 630 else 118))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2276 else (if jt.2.val < 2 then 2303 else 2279)) else (if jt.2.val < 4 then 2301 else (if jt.2.val < 5 then 2302 else 2268)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2015 else (if jt.2.val < 2 then 2020 else 2021)) else (if jt.2.val < 4 then 2017 else (if jt.2.val < 5 then 2019 else 2018))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1122 else (if jt.2.val < 2 then 1124 else 1129)) else (if jt.2.val < 4 then 1123 else (if jt.2.val < 5 then 1128 else 1127)))))

checked_coverage fastCoverage0076 pairing0076 template0076 witness0076

theorem coverage0076 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0076) (maskBits m))
    cores template0076 witness0076 := by
  rw [← coresFast_eq]
  exact fastCoverage0076

theorem coverageSize0076 : ∀ q : Pattern,
    (cores (witness0076 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0076 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0076
#print axioms coverageSize0076

noncomputable def pairing0077 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 4 else 3) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0077 : List (Fin 4935) := templateData0077

noncomputable def witness0077 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1218 else if t 3 = 1 then 1205 else 764) else if t 2 = 1 then (if t 3 = 0 then 1216 else if t 3 = 1 then 1201 else 757) else (if t 3 = 0 then 1837 else if t 3 = 1 then 568 else 1544)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1214 else if t 3 = 1 then 1187 else 1189) else if t 2 = 1 then (if t 3 = 0 then 1210 else if t 3 = 1 then 1167 else 1172) else (if t 3 = 0 then 502 else if t 3 = 1 then 1170 else 1174)) else (if t 2 = 0 then (if t 3 = 0 then 1376 else if t 3 = 1 then 1801 else 1802) else if t 2 = 1 then (if t 3 = 0 then 1211 else if t 3 = 1 then 1169 else 1173) else (if t 3 = 0 then 503 else if t 3 = 1 then 1171 else 1175))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1217 else if t 3 = 1 then 1203 else 761) else if t 2 = 1 then (if t 3 = 0 then 1215 else if t 3 = 1 then 1197 else 751) else (if t 3 = 0 then 1836 else if t 3 = 1 then 562 else 1542)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1212 else if t 3 = 1 then 1179 else 1183) else if t 2 = 1 then (if t 3 = 0 then 1206 else if t 3 = 1 then 1151 else 1159) else (if t 3 = 0 then 498 else if t 3 = 1 then 1155 else 1163)) else (if t 2 = 0 then (if t 3 = 0 then 1374 else if t 3 = 1 then 1795 else 1799) else if t 2 = 1 then (if t 3 = 0 then 1208 else if t 3 = 1 then 1153 else 1161) else (if t 3 = 0 then 500 else if t 3 = 1 then 1157 else 1165))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1220 else if t 3 = 1 then 1204 else 762) else if t 2 = 1 then (if t 3 = 0 then 1219 else if t 3 = 1 then 1198 else 752) else (if t 3 = 0 then 1838 else if t 3 = 1 then 563 else 1543)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1213 else if t 3 = 1 then 1180 else 1184) else if t 2 = 1 then (if t 3 = 0 then 1207 else if t 3 = 1 then 1152 else 1160) else (if t 3 = 0 then 499 else if t 3 = 1 then 1156 else 1164)) else (if t 2 = 0 then (if t 3 = 0 then 1375 else if t 3 = 1 then 1796 else 1800) else if t 2 = 1 then (if t 3 = 0 then 1209 else if t 3 = 1 then 1154 else 1162) else (if t 3 = 0 then 501 else if t 3 = 1 then 1158 else 1166))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 795 else (if jt.2.val < 2 then 1150 else 817)) else (if jt.2.val < 4 then 1149 else (if jt.2.val < 5 then 1168 else 813))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2283 else (if jt.2.val < 2 then 2311 else 2285)) else (if jt.2.val < 4 then 2310 else (if jt.2.val < 5 then 2312 else 2280)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2304 else (if jt.2.val < 2 then 2306 else 2309)) else (if jt.2.val < 4 then 2305 else (if jt.2.val < 5 then 2308 else 2307))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1127 else (if jt.2.val < 2 then 1193 else 1129)) else (if jt.2.val < 4 then 1191 else (if jt.2.val < 5 then 1192 else 1122)))))

checked_coverage fastCoverage0077 pairing0077 template0077 witness0077

theorem coverage0077 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0077) (maskBits m))
    cores template0077 witness0077 := by
  rw [← coresFast_eq]
  exact fastCoverage0077

theorem coverageSize0077 : ∀ q : Pattern,
    (cores (witness0077 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0077 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0077
#print axioms coverageSize0077

noncomputable def pairing0078 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 7 else 5)))) (by decide +kernel)

noncomputable def template0078 : List (Fin 4935) := templateData0078

noncomputable def witness0078 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1576 else if t 3 = 1 then 1572 else 1856) else if t 2 = 1 then (if t 3 = 0 then 1574 else if t 3 = 1 then 1570 else 1853) else (if t 3 = 0 then 469 else if t 3 = 1 then 1071 else 1094)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1568 else if t 3 = 1 then 1564 else 1616) else if t 2 = 1 then (if t 3 = 0 then 1566 else if t 3 = 1 then 1562 else 1610) else (if t 3 = 0 then 464 else if t 3 = 1 then 1593 else 1612)) else (if t 2 = 0 then (if t 3 = 0 then 918 else if t 3 = 1 then 266 else 299) else if t 2 = 1 then (if t 3 = 0 then 62 else if t 3 = 1 then 1589 else 1611) else (if t 3 = 0 then 1849 else if t 3 = 1 then 1597 else 1613))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1575 else if t 3 = 1 then 1571 else 1854) else if t 2 = 1 then (if t 3 = 0 then 1573 else if t 3 = 1 then 1569 else 1851) else (if t 3 = 0 then 468 else if t 3 = 1 then 1070 else 1092)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1567 else if t 3 = 1 then 1563 else 1614) else if t 2 = 1 then (if t 3 = 0 then 1565 else if t 3 = 1 then 1561 else 1602) else (if t 3 = 0 then 463 else if t 3 = 1 then 1592 else 1606)) else (if t 2 = 0 then (if t 3 = 0 then 917 else if t 3 = 1 then 265 else 296) else if t 2 = 1 then (if t 3 = 0 then 61 else if t 3 = 1 then 1588 else 1604) else (if t 3 = 0 then 1848 else if t 3 = 1 then 1596 else 1608))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1587 else if t 3 = 1 then 1585 else 1855) else if t 2 = 1 then (if t 3 = 0 then 1586 else if t 3 = 1 then 1584 else 1852) else (if t 3 = 0 then 473 else if t 3 = 1 then 1073 else 1093)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1583 else if t 3 = 1 then 1581 else 1615) else if t 2 = 1 then (if t 3 = 0 then 1582 else if t 3 = 1 then 1580 else 1603) else (if t 3 = 0 then 471 else if t 3 = 1 then 1595 else 1607)) else (if t 2 = 0 then (if t 3 = 0 then 920 else if t 3 = 1 then 273 else 297) else if t 2 = 1 then (if t 3 = 0 then 69 else if t 3 = 1 then 1591 else 1605) else (if t 3 = 0 then 1850 else if t 3 = 1 then 1600 else 1609))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1386 else (if jt.2.val < 2 then 1579 else 1410)) else (if jt.2.val < 4 then 1577 else (if jt.2.val < 5 then 1578 else 1390))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2291 else (if jt.2.val < 2 then 2315 else 2294)) else (if jt.2.val < 4 then 2313 else (if jt.2.val < 5 then 2314 else 2288)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2018 else (if jt.2.val < 2 then 2036 else 2021)) else (if jt.2.val < 4 then 2033 else (if jt.2.val < 5 then 2034 else 2015))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1839 else (if jt.2.val < 2 then 1841 else 1846)) else (if jt.2.val < 4 then 1840 else (if jt.2.val < 5 then 1845 else 1844)))))

checked_coverage fastCoverage0078 pairing0078 template0078 witness0078

theorem coverage0078 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0078) (maskBits m))
    cores template0078 witness0078 := by
  rw [← coresFast_eq]
  exact fastCoverage0078

theorem coverageSize0078 : ∀ q : Pattern,
    (cores (witness0078 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0078 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0078
#print axioms coverageSize0078

noncomputable def pairing0079 : Pairing8 :=
  Equiv.ofBijective (fun x => (if x.1.val < 2 then (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.2 then 2 else 6)) else (if x.1.val < 3 then (if x.2 then 3 else 4) else (if x.2 then 5 else 7)))) (by decide +kernel)

noncomputable def template0079 : List (Fin 4935) := templateData0079

noncomputable def witness0079 : Pattern → Fin 4935
  | .inl t => (if t 0 = 0 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1914 else if t 3 = 1 then 1904 else 1676) else if t 2 = 1 then (if t 3 = 0 then 1912 else if t 3 = 1 then 1901 else 1670) else (if t 3 = 0 then 1116 else if t 3 = 1 then 554 else 555)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1910 else if t 3 = 1 then 1891 else 1892) else if t 2 = 1 then (if t 3 = 0 then 1907 else if t 3 = 1 then 1875 else 1880) else (if t 3 = 0 then 496 else if t 3 = 1 then 1878 else 1882)) else (if t 2 = 0 then (if t 3 = 0 then 104 else if t 3 = 1 then 978 else 980) else if t 2 = 1 then (if t 3 = 0 then 94 else if t 3 = 1 then 1877 else 1881) else (if t 3 = 0 then 1523 else if t 3 = 1 then 1879 else 1883))) else if t 0 = 1 then (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1913 else if t 3 = 1 then 1902 else 1673) else if t 2 = 1 then (if t 3 = 0 then 1911 else if t 3 = 1 then 1899 else 1667) else (if t 3 = 0 then 1115 else if t 3 = 1 then 548 else 550)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1908 else if t 3 = 1 then 1887 else 1889) else if t 2 = 1 then (if t 3 = 0 then 1905 else if t 3 = 1 then 1859 else 1867) else (if t 3 = 0 then 492 else if t 3 = 1 then 1863 else 1871)) else (if t 2 = 0 then (if t 3 = 0 then 102 else if t 3 = 1 then 971 else 975) else if t 2 = 1 then (if t 3 = 0 then 90 else if t 3 = 1 then 1861 else 1869) else (if t 3 = 0 then 1521 else if t 3 = 1 then 1865 else 1873))) else (if t 1 = 0 then (if t 2 = 0 then (if t 3 = 0 then 1916 else if t 3 = 1 then 1903 else 1674) else if t 2 = 1 then (if t 3 = 0 then 1915 else if t 3 = 1 then 1900 else 1668) else (if t 3 = 0 then 1118 else if t 3 = 1 then 549 else 551)) else if t 1 = 1 then (if t 2 = 0 then (if t 3 = 0 then 1909 else if t 3 = 1 then 1888 else 1890) else if t 2 = 1 then (if t 3 = 0 then 1906 else if t 3 = 1 then 1860 else 1868) else (if t 3 = 0 then 493 else if t 3 = 1 then 1864 else 1872)) else (if t 2 = 0 then (if t 3 = 0 then 103 else if t 3 = 1 then 972 else 976) else if t 2 = 1 then (if t 3 = 0 then 91 else if t 3 = 1 then 1862 else 1870) else (if t 3 = 0 then 1522 else if t 3 = 1 then 1866 else 1874))))
  | .inr jt => (if jt.1.val < 2 then (if jt.1.val < 1 then (if jt.2.val < 3 then (if jt.2.val < 1 then 1695 else (if jt.2.val < 2 then 1858 else 1717)) else (if jt.2.val < 4 then 1857 else (if jt.2.val < 5 then 1876 else 1713))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 2298 else (if jt.2.val < 2 then 2320 else 2300)) else (if jt.2.val < 4 then 2319 else (if jt.2.val < 5 then 2321 else 2295)))) else (if jt.1.val < 3 then (if jt.2.val < 3 then (if jt.2.val < 1 then 2307 else (if jt.2.val < 2 then 2317 else 2309)) else (if jt.2.val < 4 then 2316 else (if jt.2.val < 5 then 2318 else 2304))) else (if jt.2.val < 3 then (if jt.2.val < 1 then 1844 else (if jt.2.val < 2 then 1895 else 1846)) else (if jt.2.val < 4 then 1893 else (if jt.2.val < 5 then 1894 else 1839)))))

checked_coverage fastCoverage0079 pairing0079 template0079 witness0079

theorem coverage0079 : Coverage
    (fun m => rowOfMask (pairsOfEquiv pairing0079) (maskBits m))
    cores template0079 witness0079 := by
  rw [← coresFast_eq]
  exact fastCoverage0079

theorem coverageSize0079 : ∀ q : Pattern,
    (cores (witness0079 q)).length = (patternRows q).length := by
  rw [← coresFast_eq]
  have h : patterns.all (fun q =>
      (coresFast (witness0079 q)).length == (patternRows q).length) = true := rfl
  intro q
  exact beq_iff_eq.mp (List.all_eq_true.mp h q (patterns_complete q))

#print axioms coverage0079
#print axioms coverageSize0079

end Crown.CertificateData
