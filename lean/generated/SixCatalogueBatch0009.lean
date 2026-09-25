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
noncomputable def pairing0036 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.1.val < 2 then (if x.2 then 2 else 1) else (if x.2 then 5 else 3)))) (by decide +kernel)
noncomputable def code0036 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 12 else 28) else (if m.val < 7 then 8 else 24))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 5 else 21)) else (if m.val < 14 then (if m.val < 13 then 13 else 29) else (if m.val < 15 then 9 else 25)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 48 else 32) else (if m.val < 19 then 52 else 36)) else (if m.val < 22 then (if m.val < 21 then 60 else 44) else (if m.val < 23 then 56 else 40))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 49 else 33) else (if m.val < 27 then 53 else 37)) else (if m.val < 30 then (if m.val < 29 then 61 else 45) else (if m.val < 31 then 57 else 41))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 3 else 19) else (if m.val < 35 then 7 else 23)) else (if m.val < 38 then (if m.val < 37 then 15 else 31) else (if m.val < 39 then 11 else 27))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 2 else 18) else (if m.val < 43 then 6 else 22)) else (if m.val < 46 then (if m.val < 45 then 14 else 30) else (if m.val < 47 then 10 else 26)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 51 else 35) else (if m.val < 51 then 55 else 39)) else (if m.val < 54 then (if m.val < 53 then 63 else 47) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 50 else 34) else (if m.val < 59 then 54 else 38)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0036_correct : ∀ m, Crown.ThreeClosure.rows (code0036 m) =
    rowOfMask (pairsOfEquiv pairing0036) (maskBits m) := by decide +kernel
theorem coverage0036 : ∀ c, witness0036 c ∈ template0036 ∧
    ∀ m ∈ cores (witness0036 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0036) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0036 cores witness0036 code0036
    code0036_correct (by decide +kernel)
#print axioms coverage0036

theorem selected0036 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0036, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0036 cores
    template0036 witness0036 coverage0036 s hs hb
#print axioms selected0036
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0037 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.1.val < 2 then (if x.2 then 2 else 1) else (if x.2 then 3 else 5)))) (by decide +kernel)
noncomputable def code0037 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 12 else 28) else (if m.val < 7 then 8 else 24))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 7 else 23)) else (if m.val < 14 then (if m.val < 13 then 15 else 31) else (if m.val < 15 then 11 else 27)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 48 else 32) else (if m.val < 19 then 52 else 36)) else (if m.val < 22 then (if m.val < 21 then 60 else 44) else (if m.val < 23 then 56 else 40))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 51 else 35) else (if m.val < 27 then 55 else 39)) else (if m.val < 30 then (if m.val < 29 then 63 else 47) else (if m.val < 31 then 59 else 43))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 1 else 17) else (if m.val < 35 then 5 else 21)) else (if m.val < 38 then (if m.val < 37 then 13 else 29) else (if m.val < 39 then 9 else 25))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 2 else 18) else (if m.val < 43 then 6 else 22)) else (if m.val < 46 then (if m.val < 45 then 14 else 30) else (if m.val < 47 then 10 else 26)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 49 else 33) else (if m.val < 51 then 53 else 37)) else (if m.val < 54 then (if m.val < 53 then 61 else 45) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 50 else 34) else (if m.val < 59 then 54 else 38)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0037_correct : ∀ m, Crown.ThreeClosure.rows (code0037 m) =
    rowOfMask (pairsOfEquiv pairing0037) (maskBits m) := by decide +kernel
theorem coverage0037 : ∀ c, witness0037 c ∈ template0037 ∧
    ∀ m ∈ cores (witness0037 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0037) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0037 cores witness0037 code0037
    code0037_correct (by decide +kernel)
#print axioms coverage0037

theorem selected0037 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0037, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0037 cores
    template0037 witness0037 coverage0037 s hs hb
#print axioms selected0037
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0038 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)
noncomputable def code0038 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 4 else 20) else (if m.val < 7 then 8 else 24))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 13 else 29)) else (if m.val < 14 then (if m.val < 13 then 5 else 21) else (if m.val < 15 then 9 else 25)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 48 else 32) else (if m.val < 19 then 60 else 44)) else (if m.val < 22 then (if m.val < 21 then 52 else 36) else (if m.val < 23 then 56 else 40))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 49 else 33) else (if m.val < 27 then 61 else 45)) else (if m.val < 30 then (if m.val < 29 then 53 else 37) else (if m.val < 31 then 57 else 41))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 3 else 19) else (if m.val < 35 then 15 else 31)) else (if m.val < 38 then (if m.val < 37 then 7 else 23) else (if m.val < 39 then 11 else 27))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 2 else 18) else (if m.val < 43 then 14 else 30)) else (if m.val < 46 then (if m.val < 45 then 6 else 22) else (if m.val < 47 then 10 else 26)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 51 else 35) else (if m.val < 51 then 63 else 47)) else (if m.val < 54 then (if m.val < 53 then 55 else 39) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 50 else 34) else (if m.val < 59 then 62 else 46)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0038_correct : ∀ m, Crown.ThreeClosure.rows (code0038 m) =
    rowOfMask (pairsOfEquiv pairing0038) (maskBits m) := by decide +kernel
theorem coverage0038 : ∀ c, witness0038 c ∈ template0038 ∧
    ∀ m ∈ cores (witness0038 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0038) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0038 cores witness0038 code0038
    code0038_correct (by decide +kernel)
#print axioms coverage0038

theorem selected0038 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0038, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0038 cores
    template0038 witness0038 coverage0038 s hs hb
#print axioms selected0038
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0039 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)
noncomputable def code0039 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 4 else 20) else (if m.val < 7 then 8 else 24))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 15 else 31)) else (if m.val < 14 then (if m.val < 13 then 7 else 23) else (if m.val < 15 then 11 else 27)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 48 else 32) else (if m.val < 19 then 60 else 44)) else (if m.val < 22 then (if m.val < 21 then 52 else 36) else (if m.val < 23 then 56 else 40))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 51 else 35) else (if m.val < 27 then 63 else 47)) else (if m.val < 30 then (if m.val < 29 then 55 else 39) else (if m.val < 31 then 59 else 43))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 1 else 17) else (if m.val < 35 then 13 else 29)) else (if m.val < 38 then (if m.val < 37 then 5 else 21) else (if m.val < 39 then 9 else 25))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 2 else 18) else (if m.val < 43 then 14 else 30)) else (if m.val < 46 then (if m.val < 45 then 6 else 22) else (if m.val < 47 then 10 else 26)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 49 else 33) else (if m.val < 51 then 61 else 45)) else (if m.val < 54 then (if m.val < 53 then 53 else 37) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 50 else 34) else (if m.val < 59 then 62 else 46)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0039_correct : ∀ m, Crown.ThreeClosure.rows (code0039 m) =
    rowOfMask (pairsOfEquiv pairing0039) (maskBits m) := by decide +kernel
theorem coverage0039 : ∀ c, witness0039 c ∈ template0039 ∧
    ∀ m ∈ cores (witness0039 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0039) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0039 cores witness0039 code0039
    code0039_correct (by decide +kernel)
#print axioms coverage0039

theorem selected0039 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0039, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0039 cores
    template0039 witness0039 coverage0039 s hs hb
#print axioms selected0039
end Crown.CertificateSixData
