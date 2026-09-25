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
noncomputable def pairing0024 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.1.val < 2 then (if x.2 then 2 else 1) else (if x.2 then 5 else 4)))) (by decide +kernel)
noncomputable def code0024 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 12 else 28) else (if m.val < 7 then 8 else 24))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 48 else 32) else (if m.val < 11 then 52 else 36)) else (if m.val < 14 then (if m.val < 13 then 60 else 44) else (if m.val < 15 then 56 else 40)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 1 else 17) else (if m.val < 19 then 5 else 21)) else (if m.val < 22 then (if m.val < 21 then 13 else 29) else (if m.val < 23 then 9 else 25))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 49 else 33) else (if m.val < 27 then 53 else 37)) else (if m.val < 30 then (if m.val < 29 then 61 else 45) else (if m.val < 31 then 57 else 41))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 3 else 19) else (if m.val < 35 then 7 else 23)) else (if m.val < 38 then (if m.val < 37 then 15 else 31) else (if m.val < 39 then 11 else 27))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 51 else 35) else (if m.val < 43 then 55 else 39)) else (if m.val < 46 then (if m.val < 45 then 63 else 47) else (if m.val < 47 then 59 else 43)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 2 else 18) else (if m.val < 51 then 6 else 22)) else (if m.val < 54 then (if m.val < 53 then 14 else 30) else (if m.val < 55 then 10 else 26))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 50 else 34) else (if m.val < 59 then 54 else 38)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0024_correct : ∀ m, Crown.ThreeClosure.rows (code0024 m) =
    rowOfMask (pairsOfEquiv pairing0024) (maskBits m) := by decide +kernel
theorem coverage0024 : ∀ c, witness0024 c ∈ template0024 ∧
    ∀ m ∈ cores (witness0024 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0024) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0024 cores witness0024 code0024
    code0024_correct (by decide +kernel)
#print axioms coverage0024

theorem selected0024 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0024, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0024 cores
    template0024 witness0024 coverage0024 s hs hb
#print axioms selected0024
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0025 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.1.val < 2 then (if x.2 then 2 else 1) else (if x.2 then 4 else 5)))) (by decide +kernel)
noncomputable def code0025 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 12 else 28) else (if m.val < 7 then 8 else 24))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 48 else 32) else (if m.val < 11 then 52 else 36)) else (if m.val < 14 then (if m.val < 13 then 60 else 44) else (if m.val < 15 then 56 else 40)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 3 else 19) else (if m.val < 19 then 7 else 23)) else (if m.val < 22 then (if m.val < 21 then 15 else 31) else (if m.val < 23 then 11 else 27))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 51 else 35) else (if m.val < 27 then 55 else 39)) else (if m.val < 30 then (if m.val < 29 then 63 else 47) else (if m.val < 31 then 59 else 43))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 1 else 17) else (if m.val < 35 then 5 else 21)) else (if m.val < 38 then (if m.val < 37 then 13 else 29) else (if m.val < 39 then 9 else 25))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 49 else 33) else (if m.val < 43 then 53 else 37)) else (if m.val < 46 then (if m.val < 45 then 61 else 45) else (if m.val < 47 then 57 else 41)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 2 else 18) else (if m.val < 51 then 6 else 22)) else (if m.val < 54 then (if m.val < 53 then 14 else 30) else (if m.val < 55 then 10 else 26))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 50 else 34) else (if m.val < 59 then 54 else 38)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0025_correct : ∀ m, Crown.ThreeClosure.rows (code0025 m) =
    rowOfMask (pairsOfEquiv pairing0025) (maskBits m) := by decide +kernel
theorem coverage0025 : ∀ c, witness0025 c ∈ template0025 ∧
    ∀ m ∈ cores (witness0025 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0025) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0025 cores witness0025 code0025
    code0025_correct (by decide +kernel)
#print axioms coverage0025

theorem selected0025 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0025, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0025 cores
    template0025 witness0025 coverage0025 s hs hb
#print axioms selected0025
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0026 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 2) else (if x.2 then 5 else 4)))) (by decide +kernel)
noncomputable def code0026 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 4 else 20) else (if m.val < 7 then 8 else 24))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 48 else 32) else (if m.val < 11 then 60 else 44)) else (if m.val < 14 then (if m.val < 13 then 52 else 36) else (if m.val < 15 then 56 else 40)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 1 else 17) else (if m.val < 19 then 13 else 29)) else (if m.val < 22 then (if m.val < 21 then 5 else 21) else (if m.val < 23 then 9 else 25))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 49 else 33) else (if m.val < 27 then 61 else 45)) else (if m.val < 30 then (if m.val < 29 then 53 else 37) else (if m.val < 31 then 57 else 41))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 3 else 19) else (if m.val < 35 then 15 else 31)) else (if m.val < 38 then (if m.val < 37 then 7 else 23) else (if m.val < 39 then 11 else 27))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 51 else 35) else (if m.val < 43 then 63 else 47)) else (if m.val < 46 then (if m.val < 45 then 55 else 39) else (if m.val < 47 then 59 else 43)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 2 else 18) else (if m.val < 51 then 14 else 30)) else (if m.val < 54 then (if m.val < 53 then 6 else 22) else (if m.val < 55 then 10 else 26))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 50 else 34) else (if m.val < 59 then 62 else 46)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0026_correct : ∀ m, Crown.ThreeClosure.rows (code0026 m) =
    rowOfMask (pairsOfEquiv pairing0026) (maskBits m) := by decide +kernel
theorem coverage0026 : ∀ c, witness0026 c ∈ template0026 ∧
    ∀ m ∈ cores (witness0026 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0026) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0026 cores witness0026 code0026
    code0026_correct (by decide +kernel)
#print axioms coverage0026

theorem selected0026 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0026, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0026 cores
    template0026 witness0026 coverage0026 s hs hb
#print axioms selected0026
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0027 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 2) else (if x.2 then 4 else 5)))) (by decide +kernel)
noncomputable def code0027 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 4 else 20) else (if m.val < 7 then 8 else 24))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 48 else 32) else (if m.val < 11 then 60 else 44)) else (if m.val < 14 then (if m.val < 13 then 52 else 36) else (if m.val < 15 then 56 else 40)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 3 else 19) else (if m.val < 19 then 15 else 31)) else (if m.val < 22 then (if m.val < 21 then 7 else 23) else (if m.val < 23 then 11 else 27))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 51 else 35) else (if m.val < 27 then 63 else 47)) else (if m.val < 30 then (if m.val < 29 then 55 else 39) else (if m.val < 31 then 59 else 43))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 1 else 17) else (if m.val < 35 then 13 else 29)) else (if m.val < 38 then (if m.val < 37 then 5 else 21) else (if m.val < 39 then 9 else 25))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 49 else 33) else (if m.val < 43 then 61 else 45)) else (if m.val < 46 then (if m.val < 45 then 53 else 37) else (if m.val < 47 then 57 else 41)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 2 else 18) else (if m.val < 51 then 14 else 30)) else (if m.val < 54 then (if m.val < 53 then 6 else 22) else (if m.val < 55 then 10 else 26))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 50 else 34) else (if m.val < 59 then 62 else 46)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0027_correct : ∀ m, Crown.ThreeClosure.rows (code0027 m) =
    rowOfMask (pairsOfEquiv pairing0027) (maskBits m) := by decide +kernel
theorem coverage0027 : ∀ c, witness0027 c ∈ template0027 ∧
    ∀ m ∈ cores (witness0027 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0027) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0027 cores witness0027 code0027
    code0027_correct (by decide +kernel)
#print axioms coverage0027

theorem selected0027 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0027, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0027 cores
    template0027 witness0027 coverage0027 s hs hb
#print axioms selected0027
end Crown.CertificateSixData
