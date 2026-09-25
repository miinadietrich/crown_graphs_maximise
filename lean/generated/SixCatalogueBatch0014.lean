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
noncomputable def pairing0056 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 4 else 1) else (if x.2 then 3 else 2)))) (by decide +kernel)
noncomputable def code0056 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 1 else 17) else (if m.val < 7 then 5 else 21))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 7 else 23)) else (if m.val < 14 then (if m.val < 13 then 2 else 18) else (if m.val < 15 then 6 else 22)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 12 else 28) else (if m.val < 19 then 8 else 24)) else (if m.val < 22 then (if m.val < 21 then 13 else 29) else (if m.val < 23 then 9 else 25))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 15 else 31) else (if m.val < 27 then 11 else 27)) else (if m.val < 30 then (if m.val < 29 then 14 else 30) else (if m.val < 31 then 10 else 26))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 48 else 32) else (if m.val < 35 then 52 else 36)) else (if m.val < 38 then (if m.val < 37 then 49 else 33) else (if m.val < 39 then 53 else 37))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 51 else 35) else (if m.val < 43 then 55 else 39)) else (if m.val < 46 then (if m.val < 45 then 50 else 34) else (if m.val < 47 then 54 else 38)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 60 else 44) else (if m.val < 51 then 56 else 40)) else (if m.val < 54 then (if m.val < 53 then 61 else 45) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 63 else 47) else (if m.val < 59 then 59 else 43)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0056_correct : ∀ m, Crown.ThreeClosure.rows (code0056 m) =
    rowOfMask (pairsOfEquiv pairing0056) (maskBits m) := by decide +kernel
theorem coverage0056 : ∀ c, witness0056 c ∈ template0056 ∧
    ∀ m ∈ cores (witness0056 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0056) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0056 cores witness0056 code0056
    code0056_correct (by decide +kernel)
#print axioms coverage0056

theorem selected0056 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0056, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0056 cores
    template0056 witness0056 coverage0056 s hs hb
#print axioms selected0056
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0057 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 4 else 1) else (if x.2 then 2 else 3)))) (by decide +kernel)
noncomputable def code0057 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 3 else 19) else (if m.val < 7 then 7 else 23))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 5 else 21)) else (if m.val < 14 then (if m.val < 13 then 2 else 18) else (if m.val < 15 then 6 else 22)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 12 else 28) else (if m.val < 19 then 8 else 24)) else (if m.val < 22 then (if m.val < 21 then 15 else 31) else (if m.val < 23 then 11 else 27))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 13 else 29) else (if m.val < 27 then 9 else 25)) else (if m.val < 30 then (if m.val < 29 then 14 else 30) else (if m.val < 31 then 10 else 26))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 48 else 32) else (if m.val < 35 then 52 else 36)) else (if m.val < 38 then (if m.val < 37 then 51 else 35) else (if m.val < 39 then 55 else 39))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 49 else 33) else (if m.val < 43 then 53 else 37)) else (if m.val < 46 then (if m.val < 45 then 50 else 34) else (if m.val < 47 then 54 else 38)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 60 else 44) else (if m.val < 51 then 56 else 40)) else (if m.val < 54 then (if m.val < 53 then 63 else 47) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 61 else 45) else (if m.val < 59 then 57 else 41)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0057_correct : ∀ m, Crown.ThreeClosure.rows (code0057 m) =
    rowOfMask (pairsOfEquiv pairing0057) (maskBits m) := by decide +kernel
theorem coverage0057 : ∀ c, witness0057 c ∈ template0057 ∧
    ∀ m ∈ cores (witness0057 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0057) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0057 cores witness0057 code0057
    code0057_correct (by decide +kernel)
#print axioms coverage0057

theorem selected0057 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0057, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0057 cores
    template0057 witness0057 coverage0057 s hs hb
#print axioms selected0057
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0058 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 4) else (if x.2 then 3 else 2)))) (by decide +kernel)
noncomputable def code0058 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 1 else 17) else (if m.val < 7 then 13 else 29))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 15 else 31)) else (if m.val < 14 then (if m.val < 13 then 2 else 18) else (if m.val < 15 then 14 else 30)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 4 else 20) else (if m.val < 19 then 8 else 24)) else (if m.val < 22 then (if m.val < 21 then 5 else 21) else (if m.val < 23 then 9 else 25))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 7 else 23) else (if m.val < 27 then 11 else 27)) else (if m.val < 30 then (if m.val < 29 then 6 else 22) else (if m.val < 31 then 10 else 26))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 48 else 32) else (if m.val < 35 then 60 else 44)) else (if m.val < 38 then (if m.val < 37 then 49 else 33) else (if m.val < 39 then 61 else 45))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 51 else 35) else (if m.val < 43 then 63 else 47)) else (if m.val < 46 then (if m.val < 45 then 50 else 34) else (if m.val < 47 then 62 else 46)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 52 else 36) else (if m.val < 51 then 56 else 40)) else (if m.val < 54 then (if m.val < 53 then 53 else 37) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 55 else 39) else (if m.val < 59 then 59 else 43)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0058_correct : ∀ m, Crown.ThreeClosure.rows (code0058 m) =
    rowOfMask (pairsOfEquiv pairing0058) (maskBits m) := by decide +kernel
theorem coverage0058 : ∀ c, witness0058 c ∈ template0058 ∧
    ∀ m ∈ cores (witness0058 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0058) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0058 cores witness0058 code0058
    code0058_correct (by decide +kernel)
#print axioms coverage0058

theorem selected0058 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0058, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0058 cores
    template0058 witness0058 coverage0058 s hs hb
#print axioms selected0058
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0059 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 4) else (if x.2 then 2 else 3)))) (by decide +kernel)
noncomputable def code0059 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 3 else 19) else (if m.val < 7 then 15 else 31))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 13 else 29)) else (if m.val < 14 then (if m.val < 13 then 2 else 18) else (if m.val < 15 then 14 else 30)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 4 else 20) else (if m.val < 19 then 8 else 24)) else (if m.val < 22 then (if m.val < 21 then 7 else 23) else (if m.val < 23 then 11 else 27))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 5 else 21) else (if m.val < 27 then 9 else 25)) else (if m.val < 30 then (if m.val < 29 then 6 else 22) else (if m.val < 31 then 10 else 26))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 48 else 32) else (if m.val < 35 then 60 else 44)) else (if m.val < 38 then (if m.val < 37 then 51 else 35) else (if m.val < 39 then 63 else 47))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 49 else 33) else (if m.val < 43 then 61 else 45)) else (if m.val < 46 then (if m.val < 45 then 50 else 34) else (if m.val < 47 then 62 else 46)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 52 else 36) else (if m.val < 51 then 56 else 40)) else (if m.val < 54 then (if m.val < 53 then 55 else 39) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 53 else 37) else (if m.val < 59 then 57 else 41)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0059_correct : ∀ m, Crown.ThreeClosure.rows (code0059 m) =
    rowOfMask (pairsOfEquiv pairing0059) (maskBits m) := by decide +kernel
theorem coverage0059 : ∀ c, witness0059 c ∈ template0059 ∧
    ∀ m ∈ cores (witness0059 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0059) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0059 cores witness0059 code0059
    code0059_correct (by decide +kernel)
#print axioms coverage0059

theorem selected0059 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0059, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0059 cores
    template0059 witness0059 coverage0059 s hs hb
#print axioms selected0059
end Crown.CertificateSixData
