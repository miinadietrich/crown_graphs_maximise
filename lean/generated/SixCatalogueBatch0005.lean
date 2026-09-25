import generated.SixCatalogueCores
import generated.SixCatalogueTemplates
import generated.ThreeClosureData
import Crown.ThreeClosureTransport
import Crown.SixCatalogueSelection
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0020 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.1.val < 2 then (if x.2 then 5 else 1) else (if x.2 then 4 else 3)))) (by decide +kernel)
noncomputable def code0020 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 48 else 32) else (if m.val < 7 then 52 else 36))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 5 else 21)) else (if m.val < 14 then (if m.val < 13 then 49 else 33) else (if m.val < 15 then 53 else 37)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 3 else 19) else (if m.val < 19 then 7 else 23)) else (if m.val < 22 then (if m.val < 21 then 51 else 35) else (if m.val < 23 then 55 else 39))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 2 else 18) else (if m.val < 27 then 6 else 22)) else (if m.val < 30 then (if m.val < 29 then 50 else 34) else (if m.val < 31 then 54 else 38))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 12 else 28) else (if m.val < 35 then 8 else 24)) else (if m.val < 38 then (if m.val < 37 then 60 else 44) else (if m.val < 39 then 56 else 40))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 13 else 29) else (if m.val < 43 then 9 else 25)) else (if m.val < 46 then (if m.val < 45 then 61 else 45) else (if m.val < 47 then 57 else 41)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 15 else 31) else (if m.val < 51 then 11 else 27)) else (if m.val < 54 then (if m.val < 53 then 63 else 47) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 14 else 30) else (if m.val < 59 then 10 else 26)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0020_correct : ∀ m, Crown.ThreeClosure.rows (code0020 m) =
    rowOfMask (pairsOfEquiv pairing0020) (maskBits m) := by decide +kernel
theorem coverage0020 : ∀ c, witness0020 c ∈ template0020 ∧
    ∀ m ∈ cores (witness0020 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0020) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0020 cores witness0020 code0020
    code0020_correct (by decide +kernel)
#print axioms coverage0020

theorem selected0020 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0020, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0020 cores
    template0020 witness0020 coverage0020 s hs hb
#print axioms selected0020
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0021 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.1.val < 2 then (if x.2 then 5 else 1) else (if x.2 then 3 else 4)))) (by decide +kernel)
noncomputable def code0021 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 48 else 32) else (if m.val < 7 then 52 else 36))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 7 else 23)) else (if m.val < 14 then (if m.val < 13 then 51 else 35) else (if m.val < 15 then 55 else 39)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 1 else 17) else (if m.val < 19 then 5 else 21)) else (if m.val < 22 then (if m.val < 21 then 49 else 33) else (if m.val < 23 then 53 else 37))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 2 else 18) else (if m.val < 27 then 6 else 22)) else (if m.val < 30 then (if m.val < 29 then 50 else 34) else (if m.val < 31 then 54 else 38))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 12 else 28) else (if m.val < 35 then 8 else 24)) else (if m.val < 38 then (if m.val < 37 then 60 else 44) else (if m.val < 39 then 56 else 40))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 15 else 31) else (if m.val < 43 then 11 else 27)) else (if m.val < 46 then (if m.val < 45 then 63 else 47) else (if m.val < 47 then 59 else 43)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 13 else 29) else (if m.val < 51 then 9 else 25)) else (if m.val < 54 then (if m.val < 53 then 61 else 45) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 14 else 30) else (if m.val < 59 then 10 else 26)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0021_correct : ∀ m, Crown.ThreeClosure.rows (code0021 m) =
    rowOfMask (pairsOfEquiv pairing0021) (maskBits m) := by decide +kernel
theorem coverage0021 : ∀ c, witness0021 c ∈ template0021 ∧
    ∀ m ∈ cores (witness0021 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0021) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0021 cores witness0021 code0021
    code0021_correct (by decide +kernel)
#print axioms coverage0021

theorem selected0021 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0021, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0021 cores
    template0021 witness0021 coverage0021 s hs hb
#print axioms selected0021
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0022 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 5) else (if x.2 then 4 else 3)))) (by decide +kernel)
noncomputable def code0022 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 48 else 32) else (if m.val < 7 then 60 else 44))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 13 else 29)) else (if m.val < 14 then (if m.val < 13 then 49 else 33) else (if m.val < 15 then 61 else 45)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 3 else 19) else (if m.val < 19 then 15 else 31)) else (if m.val < 22 then (if m.val < 21 then 51 else 35) else (if m.val < 23 then 63 else 47))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 2 else 18) else (if m.val < 27 then 14 else 30)) else (if m.val < 30 then (if m.val < 29 then 50 else 34) else (if m.val < 31 then 62 else 46))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 4 else 20) else (if m.val < 35 then 8 else 24)) else (if m.val < 38 then (if m.val < 37 then 52 else 36) else (if m.val < 39 then 56 else 40))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 5 else 21) else (if m.val < 43 then 9 else 25)) else (if m.val < 46 then (if m.val < 45 then 53 else 37) else (if m.val < 47 then 57 else 41)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 7 else 23) else (if m.val < 51 then 11 else 27)) else (if m.val < 54 then (if m.val < 53 then 55 else 39) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 6 else 22) else (if m.val < 59 then 10 else 26)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0022_correct : ∀ m, Crown.ThreeClosure.rows (code0022 m) =
    rowOfMask (pairsOfEquiv pairing0022) (maskBits m) := by decide +kernel
theorem coverage0022 : ∀ c, witness0022 c ∈ template0022 ∧
    ∀ m ∈ cores (witness0022 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0022) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0022 cores witness0022 code0022
    code0022_correct (by decide +kernel)
#print axioms coverage0022

theorem selected0022 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0022, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0022 cores
    template0022 witness0022 coverage0022 s hs hb
#print axioms selected0022
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0023 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 5) else (if x.2 then 3 else 4)))) (by decide +kernel)
noncomputable def code0023 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 48 else 32) else (if m.val < 7 then 60 else 44))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 15 else 31)) else (if m.val < 14 then (if m.val < 13 then 51 else 35) else (if m.val < 15 then 63 else 47)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 1 else 17) else (if m.val < 19 then 13 else 29)) else (if m.val < 22 then (if m.val < 21 then 49 else 33) else (if m.val < 23 then 61 else 45))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 2 else 18) else (if m.val < 27 then 14 else 30)) else (if m.val < 30 then (if m.val < 29 then 50 else 34) else (if m.val < 31 then 62 else 46))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 4 else 20) else (if m.val < 35 then 8 else 24)) else (if m.val < 38 then (if m.val < 37 then 52 else 36) else (if m.val < 39 then 56 else 40))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 7 else 23) else (if m.val < 43 then 11 else 27)) else (if m.val < 46 then (if m.val < 45 then 55 else 39) else (if m.val < 47 then 59 else 43)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 5 else 21) else (if m.val < 51 then 9 else 25)) else (if m.val < 54 then (if m.val < 53 then 53 else 37) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 6 else 22) else (if m.val < 59 then 10 else 26)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0023_correct : ∀ m, Crown.ThreeClosure.rows (code0023 m) =
    rowOfMask (pairsOfEquiv pairing0023) (maskBits m) := by decide +kernel
theorem coverage0023 : ∀ c, witness0023 c ∈ template0023 ∧
    ∀ m ∈ cores (witness0023 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0023) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0023 cores witness0023 code0023
    code0023_correct (by decide +kernel)
#print axioms coverage0023

theorem selected0023 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0023, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0023 cores
    template0023 witness0023 coverage0023 s hs hb
#print axioms selected0023
end Crown.CertificateSixData
