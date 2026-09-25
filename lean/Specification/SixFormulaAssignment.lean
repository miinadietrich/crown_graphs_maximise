import Specification.FormulaDefinitions

import Specification.SixCatalogueCores

namespace Crown.CertificateSixData

open Crown.CertificateSemantics Crown.CertificateSixSemantics Crown.CertificateSixValuation

set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option Elab.async false

def permutation0 : Fin 6 ≃ Fin 6 where
  toFun i := (if i.val < 3 then (if i.val < 1 then 1 else (if i.val < 2 then 0 else 2)) else (if i.val < 4 then 3 else (if i.val < 5 then 4 else 5)))
  invFun i := (if i.val < 3 then (if i.val < 1 then 1 else (if i.val < 2 then 0 else 2)) else (if i.val < 4 then 3 else (if i.val < 5 then 4 else 5)))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

noncomputable def image0 (i : Fin 64) : Fin 64 :=
  (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 0 else 2) else (if i.val < 3 then 1 else 3)) else (if i.val < 6 then (if i.val < 5 then 4 else 6) else (if i.val < 7 then 5 else 7))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 8 else 10) else (if i.val < 11 then 9 else 11)) else (if i.val < 14 then (if i.val < 13 then 12 else 14) else (if i.val < 15 then 13 else 15)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 16 else 18) else (if i.val < 19 then 17 else 19)) else (if i.val < 22 then (if i.val < 21 then 20 else 22) else (if i.val < 23 then 21 else 23))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 24 else 26) else (if i.val < 27 then 25 else 27)) else (if i.val < 30 then (if i.val < 29 then 28 else 30) else (if i.val < 31 then 29 else 31))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 32 else 34) else (if i.val < 35 then 33 else 35)) else (if i.val < 38 then (if i.val < 37 then 36 else 38) else (if i.val < 39 then 37 else 39))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 40 else 42) else (if i.val < 43 then 41 else 43)) else (if i.val < 46 then (if i.val < 45 then 44 else 46) else (if i.val < 47 then 45 else 47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 48 else 50) else (if i.val < 51 then 49 else 51)) else (if i.val < 54 then (if i.val < 53 then 52 else 54) else (if i.val < 55 then 53 else 55))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 56 else 58) else (if i.val < 59 then 57 else 59)) else (if i.val < 62 then (if i.val < 61 then 60 else 62) else (if i.val < 63 then 61 else 63))))))

def lexIndex0 (n : Nat) : Fin 64 :=
  (if (n-492) < 16 then (if (n-492) < 8 then (if (n-492) < 4 then (if (n-492) < 2 then (if (n-492) < 1 then 62 else 61) else (if (n-492) < 3 then 58 else 57)) else (if (n-492) < 6 then (if (n-492) < 5 then 54 else 53) else (if (n-492) < 7 then 50 else 49))) else (if (n-492) < 12 then (if (n-492) < 10 then (if (n-492) < 9 then 46 else 45) else (if (n-492) < 11 then 42 else 41)) else (if (n-492) < 14 then (if (n-492) < 13 then 38 else 37) else (if (n-492) < 15 then 34 else 33)))) else (if (n-492) < 24 then (if (n-492) < 20 then (if (n-492) < 18 then (if (n-492) < 17 then 30 else 29) else (if (n-492) < 19 then 26 else 25)) else (if (n-492) < 22 then (if (n-492) < 21 then 22 else 21) else (if (n-492) < 23 then 18 else 17))) else (if (n-492) < 28 then (if (n-492) < 26 then (if (n-492) < 25 then 14 else 13) else (if (n-492) < 27 then 10 else 9)) else (if (n-492) < 30 then (if (n-492) < 29 then 6 else 5) else (if (n-492) < 31 then 2 else 1)))))

def permutation1 : Fin 6 ≃ Fin 6 where
  toFun i := (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 2 else 1)) else (if i.val < 4 then 3 else (if i.val < 5 then 4 else 5)))
  invFun i := (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 2 else 1)) else (if i.val < 4 then 3 else (if i.val < 5 then 4 else 5)))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def lexIndex1 (n : Nat) : Fin 64 :=
  (if (n-524) < 16 then (if (n-524) < 8 then (if (n-524) < 4 then (if (n-524) < 2 then (if (n-524) < 1 then 61 else 60) else (if (n-524) < 3 then 59 else 58)) else (if (n-524) < 6 then (if (n-524) < 5 then 53 else 52) else (if (n-524) < 7 then 51 else 50))) else (if (n-524) < 12 then (if (n-524) < 10 then (if (n-524) < 9 then 45 else 44) else (if (n-524) < 11 then 43 else 42)) else (if (n-524) < 14 then (if (n-524) < 13 then 37 else 36) else (if (n-524) < 15 then 35 else 34)))) else (if (n-524) < 24 then (if (n-524) < 20 then (if (n-524) < 18 then (if (n-524) < 17 then 29 else 28) else (if (n-524) < 19 then 27 else 26)) else (if (n-524) < 22 then (if (n-524) < 21 then 21 else 20) else (if (n-524) < 23 then 19 else 18))) else (if (n-524) < 28 then (if (n-524) < 26 then (if (n-524) < 25 then 13 else 12) else (if (n-524) < 27 then 11 else 10)) else (if (n-524) < 30 then (if (n-524) < 29 then 5 else 4) else (if (n-524) < 31 then 3 else 2)))))

def permutation2 : Fin 6 ≃ Fin 6 where
  toFun i := (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 1 else 3)) else (if i.val < 4 then 2 else (if i.val < 5 then 4 else 5)))
  invFun i := (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 1 else 3)) else (if i.val < 4 then 2 else (if i.val < 5 then 4 else 5)))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def lexIndex2 (n : Nat) : Fin 64 :=
  (if (n-556) < 16 then (if (n-556) < 8 then (if (n-556) < 4 then (if (n-556) < 2 then (if (n-556) < 1 then 59 else 58) else (if (n-556) < 3 then 57 else 56)) else (if (n-556) < 6 then (if (n-556) < 5 then 55 else 54) else (if (n-556) < 7 then 53 else 52))) else (if (n-556) < 12 then (if (n-556) < 10 then (if (n-556) < 9 then 43 else 42) else (if (n-556) < 11 then 41 else 40)) else (if (n-556) < 14 then (if (n-556) < 13 then 39 else 38) else (if (n-556) < 15 then 37 else 36)))) else (if (n-556) < 24 then (if (n-556) < 20 then (if (n-556) < 18 then (if (n-556) < 17 then 27 else 26) else (if (n-556) < 19 then 25 else 24)) else (if (n-556) < 22 then (if (n-556) < 21 then 23 else 22) else (if (n-556) < 23 then 21 else 20))) else (if (n-556) < 28 then (if (n-556) < 26 then (if (n-556) < 25 then 11 else 10) else (if (n-556) < 27 then 9 else 8)) else (if (n-556) < 30 then (if (n-556) < 29 then 7 else 6) else (if (n-556) < 31 then 5 else 4)))))

def permutation3 : Fin 6 ≃ Fin 6 where
  toFun i := (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 1 else 2)) else (if i.val < 4 then 4 else (if i.val < 5 then 3 else 5)))
  invFun i := (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 1 else 2)) else (if i.val < 4 then 4 else (if i.val < 5 then 3 else 5)))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def lexIndex3 (n : Nat) : Fin 64 :=
  (if (n-588) < 16 then (if (n-588) < 8 then (if (n-588) < 4 then (if (n-588) < 2 then (if (n-588) < 1 then 55 else 54) else (if (n-588) < 3 then 53 else 52)) else (if (n-588) < 6 then (if (n-588) < 5 then 51 else 50) else (if (n-588) < 7 then 49 else 48))) else (if (n-588) < 12 then (if (n-588) < 10 then (if (n-588) < 9 then 47 else 46) else (if (n-588) < 11 then 45 else 44)) else (if (n-588) < 14 then (if (n-588) < 13 then 43 else 42) else (if (n-588) < 15 then 41 else 40)))) else (if (n-588) < 24 then (if (n-588) < 20 then (if (n-588) < 18 then (if (n-588) < 17 then 23 else 22) else (if (n-588) < 19 then 21 else 20)) else (if (n-588) < 22 then (if (n-588) < 21 then 19 else 18) else (if (n-588) < 23 then 17 else 16))) else (if (n-588) < 28 then (if (n-588) < 26 then (if (n-588) < 25 then 15 else 14) else (if (n-588) < 27 then 13 else 12)) else (if (n-588) < 30 then (if (n-588) < 29 then 11 else 10) else (if (n-588) < 31 then 9 else 8)))))

def permutation4 : Fin 6 ≃ Fin 6 where
  toFun i := (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 1 else 2)) else (if i.val < 4 then 3 else (if i.val < 5 then 5 else 4)))
  invFun i := (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 1 else 2)) else (if i.val < 4 then 3 else (if i.val < 5 then 5 else 4)))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def lexIndex4 (n : Nat) : Fin 64 :=
  (if (n-620) < 16 then (if (n-620) < 8 then (if (n-620) < 4 then (if (n-620) < 2 then (if (n-620) < 1 then 47 else 46) else (if (n-620) < 3 then 45 else 44)) else (if (n-620) < 6 then (if (n-620) < 5 then 43 else 42) else (if (n-620) < 7 then 41 else 40))) else (if (n-620) < 12 then (if (n-620) < 10 then (if (n-620) < 9 then 39 else 38) else (if (n-620) < 11 then 37 else 36)) else (if (n-620) < 14 then (if (n-620) < 13 then 35 else 34) else (if (n-620) < 15 then 33 else 32)))) else (if (n-620) < 24 then (if (n-620) < 20 then (if (n-620) < 18 then (if (n-620) < 17 then 31 else 30) else (if (n-620) < 19 then 29 else 28)) else (if (n-620) < 22 then (if (n-620) < 21 then 27 else 26) else (if (n-620) < 23 then 25 else 24))) else (if (n-620) < 28 then (if (n-620) < 26 then (if (n-620) < 25 then 23 else 22) else (if (n-620) < 27 then 21 else 20)) else (if (n-620) < 30 then (if (n-620) < 29 then 19 else 18) else (if (n-620) < 31 then 17 else 16)))))

def permutation5 : Fin 6 ≃ Fin 6 where
  toFun i := (if i.val < 3 then (if i.val < 1 then 1 else (if i.val < 2 then 2 else 3)) else (if i.val < 4 then 4 else (if i.val < 5 then 5 else 0)))
  invFun i := (if i.val < 3 then (if i.val < 1 then 5 else (if i.val < 2 then 0 else 1)) else (if i.val < 4 then 2 else (if i.val < 5 then 3 else 4)))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def lexIndex5 (n : Nat) : Fin 64 :=
  (if (n-652) < 31 then (if (n-652) < 15 then (if (n-652) < 7 then (if (n-652) < 3 then (if (n-652) < 1 then 62 else (if (n-652) < 2 then 61 else 60)) else (if (n-652) < 5 then (if (n-652) < 4 then 59 else 58) else (if (n-652) < 6 then 57 else 56))) else (if (n-652) < 11 then (if (n-652) < 9 then (if (n-652) < 8 then 55 else 54) else (if (n-652) < 10 then 53 else 52)) else (if (n-652) < 13 then (if (n-652) < 12 then 51 else 50) else (if (n-652) < 14 then 49 else 48)))) else (if (n-652) < 23 then (if (n-652) < 19 then (if (n-652) < 17 then (if (n-652) < 16 then 47 else 46) else (if (n-652) < 18 then 45 else 44)) else (if (n-652) < 21 then (if (n-652) < 20 then 43 else 42) else (if (n-652) < 22 then 41 else 40))) else (if (n-652) < 27 then (if (n-652) < 25 then (if (n-652) < 24 then 39 else 38) else (if (n-652) < 26 then 37 else 36)) else (if (n-652) < 29 then (if (n-652) < 28 then 35 else 34) else (if (n-652) < 30 then 33 else 32))))) else (if (n-652) < 46 then (if (n-652) < 38 then (if (n-652) < 34 then (if (n-652) < 32 then 31 else (if (n-652) < 33 then 30 else 29)) else (if (n-652) < 36 then (if (n-652) < 35 then 28 else 27) else (if (n-652) < 37 then 26 else 25))) else (if (n-652) < 42 then (if (n-652) < 40 then (if (n-652) < 39 then 24 else 23) else (if (n-652) < 41 then 22 else 21)) else (if (n-652) < 44 then (if (n-652) < 43 then 20 else 19) else (if (n-652) < 45 then 18 else 17)))) else (if (n-652) < 54 then (if (n-652) < 50 then (if (n-652) < 48 then (if (n-652) < 47 then 16 else 15) else (if (n-652) < 49 then 14 else 13)) else (if (n-652) < 52 then (if (n-652) < 51 then 12 else 11) else (if (n-652) < 53 then 10 else 9))) else (if (n-652) < 58 then (if (n-652) < 56 then (if (n-652) < 55 then 8 else 7) else (if (n-652) < 57 then 6 else 5)) else (if (n-652) < 60 then (if (n-652) < 59 then 4 else 3) else (if (n-652) < 61 then 2 else 1))))))

def permutation6 : Fin 6 ≃ Fin 6 where
  toFun i := (if i.val < 3 then (if i.val < 1 then 2 else (if i.val < 2 then 3 else 4)) else (if i.val < 4 then 5 else (if i.val < 5 then 0 else 1)))
  invFun i := (if i.val < 3 then (if i.val < 1 then 4 else (if i.val < 2 then 5 else 0)) else (if i.val < 4 then 1 else (if i.val < 5 then 2 else 3)))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def lexIndex6 (n : Nat) : Fin 64 :=
  (if (n-714) < 30 then (if (n-714) < 15 then (if (n-714) < 7 then (if (n-714) < 3 then (if (n-714) < 1 then 62 else (if (n-714) < 2 then 61 else 60)) else (if (n-714) < 5 then (if (n-714) < 4 then 59 else 58) else (if (n-714) < 6 then 57 else 56))) else (if (n-714) < 11 then (if (n-714) < 9 then (if (n-714) < 8 then 55 else 54) else (if (n-714) < 10 then 53 else 52)) else (if (n-714) < 13 then (if (n-714) < 12 then 51 else 50) else (if (n-714) < 14 then 49 else 48)))) else (if (n-714) < 22 then (if (n-714) < 18 then (if (n-714) < 16 then 47 else (if (n-714) < 17 then 46 else 45)) else (if (n-714) < 20 then (if (n-714) < 19 then 44 else 43) else (if (n-714) < 21 then 41 else 40))) else (if (n-714) < 26 then (if (n-714) < 24 then (if (n-714) < 23 then 39 else 38) else (if (n-714) < 25 then 37 else 36)) else (if (n-714) < 28 then (if (n-714) < 27 then 35 else 34) else (if (n-714) < 29 then 33 else 32))))) else (if (n-714) < 45 then (if (n-714) < 37 then (if (n-714) < 33 then (if (n-714) < 31 then 31 else (if (n-714) < 32 then 30 else 29)) else (if (n-714) < 35 then (if (n-714) < 34 then 28 else 27) else (if (n-714) < 36 then 26 else 25))) else (if (n-714) < 41 then (if (n-714) < 39 then (if (n-714) < 38 then 24 else 23) else (if (n-714) < 40 then 22 else 20)) else (if (n-714) < 43 then (if (n-714) < 42 then 19 else 18) else (if (n-714) < 44 then 17 else 16)))) else (if (n-714) < 52 then (if (n-714) < 48 then (if (n-714) < 46 then 15 else (if (n-714) < 47 then 14 else 13)) else (if (n-714) < 50 then (if (n-714) < 49 then 12 else 11) else (if (n-714) < 51 then 10 else 9))) else (if (n-714) < 56 then (if (n-714) < 54 then (if (n-714) < 53 then 8 else 7) else (if (n-714) < 55 then 6 else 5)) else (if (n-714) < 58 then (if (n-714) < 57 then 4 else 3) else (if (n-714) < 59 then 2 else 1))))))

def permutation7 : Fin 6 ≃ Fin 6 where
  toFun i := (if i.val < 3 then (if i.val < 1 then 3 else (if i.val < 2 then 4 else 5)) else (if i.val < 4 then 0 else (if i.val < 5 then 1 else 2)))
  invFun i := (if i.val < 3 then (if i.val < 1 then 3 else (if i.val < 2 then 4 else 5)) else (if i.val < 4 then 0 else (if i.val < 5 then 1 else 2)))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def lexIndex7 (n : Nat) : Fin 64 :=
  (if (n-774) < 28 then (if (n-774) < 14 then (if (n-774) < 7 then (if (n-774) < 3 then (if (n-774) < 1 then 62 else (if (n-774) < 2 then 61 else 60)) else (if (n-774) < 5 then (if (n-774) < 4 then 59 else 58) else (if (n-774) < 6 then 57 else 56))) else (if (n-774) < 10 then (if (n-774) < 8 then 55 else (if (n-774) < 9 then 53 else 52)) else (if (n-774) < 12 then (if (n-774) < 11 then 51 else 50) else (if (n-774) < 13 then 49 else 48)))) else (if (n-774) < 21 then (if (n-774) < 17 then (if (n-774) < 15 then 47 else (if (n-774) < 16 then 46 else 44)) else (if (n-774) < 19 then (if (n-774) < 18 then 43 else 42) else (if (n-774) < 20 then 41 else 40))) else (if (n-774) < 24 then (if (n-774) < 22 then 39 else (if (n-774) < 23 then 38 else 37)) else (if (n-774) < 26 then (if (n-774) < 25 then 35 else 34) else (if (n-774) < 27 then 33 else 32))))) else (if (n-774) < 42 then (if (n-774) < 35 then (if (n-774) < 31 then (if (n-774) < 29 then 31 else (if (n-774) < 30 then 30 else 29)) else (if (n-774) < 33 then (if (n-774) < 32 then 28 else 26) else (if (n-774) < 34 then 25 else 24))) else (if (n-774) < 38 then (if (n-774) < 36 then 23 else (if (n-774) < 37 then 22 else 21)) else (if (n-774) < 40 then (if (n-774) < 39 then 20 else 19) else (if (n-774) < 41 then 17 else 16)))) else (if (n-774) < 49 then (if (n-774) < 45 then (if (n-774) < 43 then 15 else (if (n-774) < 44 then 14 else 13)) else (if (n-774) < 47 then (if (n-774) < 46 then 12 else 11) else (if (n-774) < 48 then 10 else 8))) else (if (n-774) < 52 then (if (n-774) < 50 then 7 else (if (n-774) < 51 then 6 else 5)) else (if (n-774) < 54 then (if (n-774) < 53 then 4 else 3) else (if (n-774) < 55 then 2 else 1))))))

def permutation8 : Fin 6 ≃ Fin 6 where
  toFun i := (if i.val < 3 then (if i.val < 1 then 4 else (if i.val < 2 then 5 else 0)) else (if i.val < 4 then 1 else (if i.val < 5 then 2 else 3)))
  invFun i := (if i.val < 3 then (if i.val < 1 then 2 else (if i.val < 2 then 3 else 4)) else (if i.val < 4 then 5 else (if i.val < 5 then 0 else 1)))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def lexIndex8 (n : Nat) : Fin 64 :=
  (if (n-830) < 30 then (if (n-830) < 15 then (if (n-830) < 7 then (if (n-830) < 3 then (if (n-830) < 1 then 62 else (if (n-830) < 2 then 61 else 60)) else (if (n-830) < 5 then (if (n-830) < 4 then 59 else 58) else (if (n-830) < 6 then 57 else 56))) else (if (n-830) < 11 then (if (n-830) < 9 then (if (n-830) < 8 then 55 else 54) else (if (n-830) < 10 then 53 else 52)) else (if (n-830) < 13 then (if (n-830) < 12 then 51 else 50) else (if (n-830) < 14 then 49 else 48)))) else (if (n-830) < 22 then (if (n-830) < 18 then (if (n-830) < 16 then 47 else (if (n-830) < 17 then 46 else 45)) else (if (n-830) < 20 then (if (n-830) < 19 then 44 else 43) else (if (n-830) < 21 then 41 else 40))) else (if (n-830) < 26 then (if (n-830) < 24 then (if (n-830) < 23 then 39 else 38) else (if (n-830) < 25 then 37 else 36)) else (if (n-830) < 28 then (if (n-830) < 27 then 35 else 34) else (if (n-830) < 29 then 33 else 32))))) else (if (n-830) < 45 then (if (n-830) < 37 then (if (n-830) < 33 then (if (n-830) < 31 then 31 else (if (n-830) < 32 then 30 else 29)) else (if (n-830) < 35 then (if (n-830) < 34 then 28 else 27) else (if (n-830) < 36 then 26 else 25))) else (if (n-830) < 41 then (if (n-830) < 39 then (if (n-830) < 38 then 24 else 23) else (if (n-830) < 40 then 22 else 20)) else (if (n-830) < 43 then (if (n-830) < 42 then 19 else 18) else (if (n-830) < 44 then 17 else 16)))) else (if (n-830) < 52 then (if (n-830) < 48 then (if (n-830) < 46 then 15 else (if (n-830) < 47 then 14 else 13)) else (if (n-830) < 50 then (if (n-830) < 49 then 12 else 11) else (if (n-830) < 51 then 10 else 9))) else (if (n-830) < 56 then (if (n-830) < 54 then (if (n-830) < 53 then 8 else 7) else (if (n-830) < 55 then 6 else 5)) else (if (n-830) < 58 then (if (n-830) < 57 then 4 else 3) else (if (n-830) < 59 then 2 else 1))))))

def permutation9 : Fin 6 ≃ Fin 6 where
  toFun i := (if i.val < 3 then (if i.val < 1 then 5 else (if i.val < 2 then 0 else 1)) else (if i.val < 4 then 2 else (if i.val < 5 then 3 else 4)))
  invFun i := (if i.val < 3 then (if i.val < 1 then 1 else (if i.val < 2 then 2 else 3)) else (if i.val < 4 then 4 else (if i.val < 5 then 5 else 0)))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def lexIndex9 (n : Nat) : Fin 64 :=
  (if (n-890) < 31 then (if (n-890) < 15 then (if (n-890) < 7 then (if (n-890) < 3 then (if (n-890) < 1 then 62 else (if (n-890) < 2 then 61 else 60)) else (if (n-890) < 5 then (if (n-890) < 4 then 59 else 58) else (if (n-890) < 6 then 57 else 56))) else (if (n-890) < 11 then (if (n-890) < 9 then (if (n-890) < 8 then 55 else 54) else (if (n-890) < 10 then 53 else 52)) else (if (n-890) < 13 then (if (n-890) < 12 then 51 else 50) else (if (n-890) < 14 then 49 else 48)))) else (if (n-890) < 23 then (if (n-890) < 19 then (if (n-890) < 17 then (if (n-890) < 16 then 47 else 46) else (if (n-890) < 18 then 45 else 44)) else (if (n-890) < 21 then (if (n-890) < 20 then 43 else 42) else (if (n-890) < 22 then 41 else 40))) else (if (n-890) < 27 then (if (n-890) < 25 then (if (n-890) < 24 then 39 else 38) else (if (n-890) < 26 then 37 else 36)) else (if (n-890) < 29 then (if (n-890) < 28 then 35 else 34) else (if (n-890) < 30 then 33 else 32))))) else (if (n-890) < 46 then (if (n-890) < 38 then (if (n-890) < 34 then (if (n-890) < 32 then 31 else (if (n-890) < 33 then 30 else 29)) else (if (n-890) < 36 then (if (n-890) < 35 then 28 else 27) else (if (n-890) < 37 then 26 else 25))) else (if (n-890) < 42 then (if (n-890) < 40 then (if (n-890) < 39 then 24 else 23) else (if (n-890) < 41 then 22 else 21)) else (if (n-890) < 44 then (if (n-890) < 43 then 20 else 19) else (if (n-890) < 45 then 18 else 17)))) else (if (n-890) < 54 then (if (n-890) < 50 then (if (n-890) < 48 then (if (n-890) < 47 then 16 else 15) else (if (n-890) < 49 then 14 else 13)) else (if (n-890) < 52 then (if (n-890) < 51 then 12 else 11) else (if (n-890) < 53 then 10 else 9))) else (if (n-890) < 58 then (if (n-890) < 56 then (if (n-890) < 55 then 8 else 7) else (if (n-890) < 57 then 6 else 5)) else (if (n-890) < 60 then (if (n-890) < 59 then 4 else 3) else (if (n-890) < 61 then 2 else 1))))))

noncomputable def descriptor (n : Nat) : Variable :=
  if hs : n < 64 then .select ⟨n, hs⟩ else
  if n = 64 then .falsum else
  if n < 492 then
    if n < 66 then Variable.count 1 (n-65+1) else
    if n < 68 then Variable.count 2 (n-66+1) else
    if n < 71 then Variable.count 3 (n-68+1) else
    if n < 75 then Variable.count 4 (n-71+1) else
    if n < 80 then Variable.count 5 (n-75+1) else
    if n < 86 then Variable.count 6 (n-80+1) else
    Variable.count (7+(n-86)/7) (1+(n-86)%7)
  else if n < 952 then
    if n < 524 then Variable.lex permutation0 (lexIndex0 n) else
    if n < 556 then Variable.lex permutation1 (lexIndex1 n) else
    if n < 588 then Variable.lex permutation2 (lexIndex2 n) else
    if n < 620 then Variable.lex permutation3 (lexIndex3 n) else
    if n < 652 then Variable.lex permutation4 (lexIndex4 n) else
    if n < 714 then Variable.lex permutation5 (lexIndex5 n) else
    if n < 774 then Variable.lex permutation6 (lexIndex6 n) else
    if n < 830 then Variable.lex permutation7 (lexIndex7 n) else
    if n < 890 then Variable.lex permutation8 (lexIndex8 n) else
    if n < 952 then Variable.lex permutation9 (lexIndex9 n) else
    Variable.falsum
  else if hc : n < 39382 then .core (cores ⟨n-952, by omega⟩)
  else .falsum

noncomputable def assignment (s : Fin 64 → Bool) (n : Nat) : Bool := value s (descriptor n)

end Crown.CertificateSixData
