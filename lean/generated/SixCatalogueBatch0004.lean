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
noncomputable def pairing0016 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.1.val < 2 then (if x.2 then 4 else 1) else (if x.2 then 5 else 3)))) (by decide +kernel)
noncomputable def code0016 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 48 else 32) else (if m.val < 7 then 52 else 36))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 5 else 21)) else (if m.val < 14 then (if m.val < 13 then 49 else 33) else (if m.val < 15 then 53 else 37)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 12 else 28) else (if m.val < 19 then 8 else 24)) else (if m.val < 22 then (if m.val < 21 then 60 else 44) else (if m.val < 23 then 56 else 40))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 13 else 29) else (if m.val < 27 then 9 else 25)) else (if m.val < 30 then (if m.val < 29 then 61 else 45) else (if m.val < 31 then 57 else 41))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 3 else 19) else (if m.val < 35 then 7 else 23)) else (if m.val < 38 then (if m.val < 37 then 51 else 35) else (if m.val < 39 then 55 else 39))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 2 else 18) else (if m.val < 43 then 6 else 22)) else (if m.val < 46 then (if m.val < 45 then 50 else 34) else (if m.val < 47 then 54 else 38)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 15 else 31) else (if m.val < 51 then 11 else 27)) else (if m.val < 54 then (if m.val < 53 then 63 else 47) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 14 else 30) else (if m.val < 59 then 10 else 26)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0016_correct : ∀ m, Crown.ThreeClosure.rows (code0016 m) =
    rowOfMask (pairsOfEquiv pairing0016) (maskBits m) := by decide +kernel
theorem coverage0016 : ∀ c, witness0016 c ∈ template0016 ∧
    ∀ m ∈ cores (witness0016 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0016) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0016 cores witness0016 code0016
    code0016_correct (by decide +kernel)
#print axioms coverage0016

theorem selected0016 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0016, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0016 cores
    template0016 witness0016 coverage0016 s hs hb
#print axioms selected0016
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0017 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.1.val < 2 then (if x.2 then 4 else 1) else (if x.2 then 3 else 5)))) (by decide +kernel)
noncomputable def code0017 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 48 else 32) else (if m.val < 7 then 52 else 36))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 7 else 23)) else (if m.val < 14 then (if m.val < 13 then 51 else 35) else (if m.val < 15 then 55 else 39)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 12 else 28) else (if m.val < 19 then 8 else 24)) else (if m.val < 22 then (if m.val < 21 then 60 else 44) else (if m.val < 23 then 56 else 40))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 15 else 31) else (if m.val < 27 then 11 else 27)) else (if m.val < 30 then (if m.val < 29 then 63 else 47) else (if m.val < 31 then 59 else 43))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 1 else 17) else (if m.val < 35 then 5 else 21)) else (if m.val < 38 then (if m.val < 37 then 49 else 33) else (if m.val < 39 then 53 else 37))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 2 else 18) else (if m.val < 43 then 6 else 22)) else (if m.val < 46 then (if m.val < 45 then 50 else 34) else (if m.val < 47 then 54 else 38)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 13 else 29) else (if m.val < 51 then 9 else 25)) else (if m.val < 54 then (if m.val < 53 then 61 else 45) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 14 else 30) else (if m.val < 59 then 10 else 26)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0017_correct : ∀ m, Crown.ThreeClosure.rows (code0017 m) =
    rowOfMask (pairsOfEquiv pairing0017) (maskBits m) := by decide +kernel
theorem coverage0017 : ∀ c, witness0017 c ∈ template0017 ∧
    ∀ m ∈ cores (witness0017 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0017) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0017 cores witness0017 code0017
    code0017_correct (by decide +kernel)
#print axioms coverage0017

theorem selected0017 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0017, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0017 cores
    template0017 witness0017 coverage0017 s hs hb
#print axioms selected0017
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0018 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 4) else (if x.2 then 5 else 3)))) (by decide +kernel)
noncomputable def code0018 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 48 else 32) else (if m.val < 7 then 60 else 44))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 13 else 29)) else (if m.val < 14 then (if m.val < 13 then 49 else 33) else (if m.val < 15 then 61 else 45)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 4 else 20) else (if m.val < 19 then 8 else 24)) else (if m.val < 22 then (if m.val < 21 then 52 else 36) else (if m.val < 23 then 56 else 40))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 5 else 21) else (if m.val < 27 then 9 else 25)) else (if m.val < 30 then (if m.val < 29 then 53 else 37) else (if m.val < 31 then 57 else 41))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 3 else 19) else (if m.val < 35 then 15 else 31)) else (if m.val < 38 then (if m.val < 37 then 51 else 35) else (if m.val < 39 then 63 else 47))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 2 else 18) else (if m.val < 43 then 14 else 30)) else (if m.val < 46 then (if m.val < 45 then 50 else 34) else (if m.val < 47 then 62 else 46)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 7 else 23) else (if m.val < 51 then 11 else 27)) else (if m.val < 54 then (if m.val < 53 then 55 else 39) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 6 else 22) else (if m.val < 59 then 10 else 26)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0018_correct : ∀ m, Crown.ThreeClosure.rows (code0018 m) =
    rowOfMask (pairsOfEquiv pairing0018) (maskBits m) := by decide +kernel
theorem coverage0018 : ∀ c, witness0018 c ∈ template0018 ∧
    ∀ m ∈ cores (witness0018 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0018) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0018 cores witness0018 code0018
    code0018_correct (by decide +kernel)
#print axioms coverage0018

theorem selected0018 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0018, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0018 cores
    template0018 witness0018 coverage0018 s hs hb
#print axioms selected0018
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0019 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 4) else (if x.2 then 3 else 5)))) (by decide +kernel)
noncomputable def code0019 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 48 else 32) else (if m.val < 7 then 60 else 44))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 15 else 31)) else (if m.val < 14 then (if m.val < 13 then 51 else 35) else (if m.val < 15 then 63 else 47)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 4 else 20) else (if m.val < 19 then 8 else 24)) else (if m.val < 22 then (if m.val < 21 then 52 else 36) else (if m.val < 23 then 56 else 40))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 7 else 23) else (if m.val < 27 then 11 else 27)) else (if m.val < 30 then (if m.val < 29 then 55 else 39) else (if m.val < 31 then 59 else 43))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 1 else 17) else (if m.val < 35 then 13 else 29)) else (if m.val < 38 then (if m.val < 37 then 49 else 33) else (if m.val < 39 then 61 else 45))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 2 else 18) else (if m.val < 43 then 14 else 30)) else (if m.val < 46 then (if m.val < 45 then 50 else 34) else (if m.val < 47 then 62 else 46)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 5 else 21) else (if m.val < 51 then 9 else 25)) else (if m.val < 54 then (if m.val < 53 then 53 else 37) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 6 else 22) else (if m.val < 59 then 10 else 26)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0019_correct : ∀ m, Crown.ThreeClosure.rows (code0019 m) =
    rowOfMask (pairsOfEquiv pairing0019) (maskBits m) := by decide +kernel
theorem coverage0019 : ∀ c, witness0019 c ∈ template0019 ∧
    ∀ m ∈ cores (witness0019 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0019) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0019 cores witness0019 code0019
    code0019_correct (by decide +kernel)
#print axioms coverage0019

theorem selected0019 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0019, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0019 cores
    template0019 witness0019 coverage0019 s hs hb
#print axioms selected0019
end Crown.CertificateSixData
