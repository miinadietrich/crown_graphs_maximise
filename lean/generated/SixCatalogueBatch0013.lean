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
noncomputable def pairing0052 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 3 else 1) else (if x.2 then 4 else 2)))) (by decide +kernel)
noncomputable def code0052 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 1 else 17) else (if m.val < 7 then 5 else 21))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 12 else 28) else (if m.val < 11 then 8 else 24)) else (if m.val < 14 then (if m.val < 13 then 13 else 29) else (if m.val < 15 then 9 else 25)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 3 else 19) else (if m.val < 19 then 7 else 23)) else (if m.val < 22 then (if m.val < 21 then 2 else 18) else (if m.val < 23 then 6 else 22))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 15 else 31) else (if m.val < 27 then 11 else 27)) else (if m.val < 30 then (if m.val < 29 then 14 else 30) else (if m.val < 31 then 10 else 26))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 48 else 32) else (if m.val < 35 then 52 else 36)) else (if m.val < 38 then (if m.val < 37 then 49 else 33) else (if m.val < 39 then 53 else 37))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 60 else 44) else (if m.val < 43 then 56 else 40)) else (if m.val < 46 then (if m.val < 45 then 61 else 45) else (if m.val < 47 then 57 else 41)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 51 else 35) else (if m.val < 51 then 55 else 39)) else (if m.val < 54 then (if m.val < 53 then 50 else 34) else (if m.val < 55 then 54 else 38))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 63 else 47) else (if m.val < 59 then 59 else 43)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0052_correct : ∀ m, Crown.ThreeClosure.rows (code0052 m) =
    rowOfMask (pairsOfEquiv pairing0052) (maskBits m) := by decide +kernel
theorem coverage0052 : ∀ c, witness0052 c ∈ template0052 ∧
    ∀ m ∈ cores (witness0052 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0052) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0052 cores witness0052 code0052
    code0052_correct (by decide +kernel)
#print axioms coverage0052

theorem selected0052 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0052, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0052 cores
    template0052 witness0052 coverage0052 s hs hb
#print axioms selected0052
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0053 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 3 else 1) else (if x.2 then 2 else 4)))) (by decide +kernel)
noncomputable def code0053 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 3 else 19) else (if m.val < 7 then 7 else 23))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 12 else 28) else (if m.val < 11 then 8 else 24)) else (if m.val < 14 then (if m.val < 13 then 15 else 31) else (if m.val < 15 then 11 else 27)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 1 else 17) else (if m.val < 19 then 5 else 21)) else (if m.val < 22 then (if m.val < 21 then 2 else 18) else (if m.val < 23 then 6 else 22))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 13 else 29) else (if m.val < 27 then 9 else 25)) else (if m.val < 30 then (if m.val < 29 then 14 else 30) else (if m.val < 31 then 10 else 26))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 48 else 32) else (if m.val < 35 then 52 else 36)) else (if m.val < 38 then (if m.val < 37 then 51 else 35) else (if m.val < 39 then 55 else 39))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 60 else 44) else (if m.val < 43 then 56 else 40)) else (if m.val < 46 then (if m.val < 45 then 63 else 47) else (if m.val < 47 then 59 else 43)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 49 else 33) else (if m.val < 51 then 53 else 37)) else (if m.val < 54 then (if m.val < 53 then 50 else 34) else (if m.val < 55 then 54 else 38))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 61 else 45) else (if m.val < 59 then 57 else 41)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0053_correct : ∀ m, Crown.ThreeClosure.rows (code0053 m) =
    rowOfMask (pairsOfEquiv pairing0053) (maskBits m) := by decide +kernel
theorem coverage0053 : ∀ c, witness0053 c ∈ template0053 ∧
    ∀ m ∈ cores (witness0053 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0053) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0053 cores witness0053 code0053
    code0053_correct (by decide +kernel)
#print axioms coverage0053

theorem selected0053 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0053, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0053 cores
    template0053 witness0053 coverage0053 s hs hb
#print axioms selected0053
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0054 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 3) else (if x.2 then 4 else 2)))) (by decide +kernel)
noncomputable def code0054 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 1 else 17) else (if m.val < 7 then 13 else 29))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 4 else 20) else (if m.val < 11 then 8 else 24)) else (if m.val < 14 then (if m.val < 13 then 5 else 21) else (if m.val < 15 then 9 else 25)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 3 else 19) else (if m.val < 19 then 15 else 31)) else (if m.val < 22 then (if m.val < 21 then 2 else 18) else (if m.val < 23 then 14 else 30))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 7 else 23) else (if m.val < 27 then 11 else 27)) else (if m.val < 30 then (if m.val < 29 then 6 else 22) else (if m.val < 31 then 10 else 26))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 48 else 32) else (if m.val < 35 then 60 else 44)) else (if m.val < 38 then (if m.val < 37 then 49 else 33) else (if m.val < 39 then 61 else 45))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 52 else 36) else (if m.val < 43 then 56 else 40)) else (if m.val < 46 then (if m.val < 45 then 53 else 37) else (if m.val < 47 then 57 else 41)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 51 else 35) else (if m.val < 51 then 63 else 47)) else (if m.val < 54 then (if m.val < 53 then 50 else 34) else (if m.val < 55 then 62 else 46))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 55 else 39) else (if m.val < 59 then 59 else 43)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0054_correct : ∀ m, Crown.ThreeClosure.rows (code0054 m) =
    rowOfMask (pairsOfEquiv pairing0054) (maskBits m) := by decide +kernel
theorem coverage0054 : ∀ c, witness0054 c ∈ template0054 ∧
    ∀ m ∈ cores (witness0054 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0054) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0054 cores witness0054 code0054
    code0054_correct (by decide +kernel)
#print axioms coverage0054

theorem selected0054 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0054, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0054 cores
    template0054 witness0054 coverage0054 s hs hb
#print axioms selected0054
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0055 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 3) else (if x.2 then 2 else 4)))) (by decide +kernel)
noncomputable def code0055 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 3 else 19) else (if m.val < 7 then 15 else 31))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 4 else 20) else (if m.val < 11 then 8 else 24)) else (if m.val < 14 then (if m.val < 13 then 7 else 23) else (if m.val < 15 then 11 else 27)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 1 else 17) else (if m.val < 19 then 13 else 29)) else (if m.val < 22 then (if m.val < 21 then 2 else 18) else (if m.val < 23 then 14 else 30))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 5 else 21) else (if m.val < 27 then 9 else 25)) else (if m.val < 30 then (if m.val < 29 then 6 else 22) else (if m.val < 31 then 10 else 26))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 48 else 32) else (if m.val < 35 then 60 else 44)) else (if m.val < 38 then (if m.val < 37 then 51 else 35) else (if m.val < 39 then 63 else 47))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 52 else 36) else (if m.val < 43 then 56 else 40)) else (if m.val < 46 then (if m.val < 45 then 55 else 39) else (if m.val < 47 then 59 else 43)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 49 else 33) else (if m.val < 51 then 61 else 45)) else (if m.val < 54 then (if m.val < 53 then 50 else 34) else (if m.val < 55 then 62 else 46))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 53 else 37) else (if m.val < 59 then 57 else 41)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0055_correct : ∀ m, Crown.ThreeClosure.rows (code0055 m) =
    rowOfMask (pairsOfEquiv pairing0055) (maskBits m) := by decide +kernel
theorem coverage0055 : ∀ c, witness0055 c ∈ template0055 ∧
    ∀ m ∈ cores (witness0055 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0055) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0055 cores witness0055 code0055
    code0055_correct (by decide +kernel)
#print axioms coverage0055

theorem selected0055 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0055, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0055 cores
    template0055 witness0055 coverage0055 s hs hb
#print axioms selected0055
end Crown.CertificateSixData
