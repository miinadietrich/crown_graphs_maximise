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
noncomputable def pairing0012 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.1.val < 2 then (if x.2 then 3 else 1) else (if x.2 then 5 else 4)))) (by decide +kernel)
noncomputable def code0012 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 48 else 32) else (if m.val < 7 then 52 else 36))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 12 else 28) else (if m.val < 11 then 8 else 24)) else (if m.val < 14 then (if m.val < 13 then 60 else 44) else (if m.val < 15 then 56 else 40)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 1 else 17) else (if m.val < 19 then 5 else 21)) else (if m.val < 22 then (if m.val < 21 then 49 else 33) else (if m.val < 23 then 53 else 37))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 13 else 29) else (if m.val < 27 then 9 else 25)) else (if m.val < 30 then (if m.val < 29 then 61 else 45) else (if m.val < 31 then 57 else 41))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 3 else 19) else (if m.val < 35 then 7 else 23)) else (if m.val < 38 then (if m.val < 37 then 51 else 35) else (if m.val < 39 then 55 else 39))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 15 else 31) else (if m.val < 43 then 11 else 27)) else (if m.val < 46 then (if m.val < 45 then 63 else 47) else (if m.val < 47 then 59 else 43)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 2 else 18) else (if m.val < 51 then 6 else 22)) else (if m.val < 54 then (if m.val < 53 then 50 else 34) else (if m.val < 55 then 54 else 38))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 14 else 30) else (if m.val < 59 then 10 else 26)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0012_correct : ∀ m, Crown.ThreeClosure.rows (code0012 m) =
    rowOfMask (pairsOfEquiv pairing0012) (maskBits m) := by decide +kernel
theorem coverage0012 : ∀ c, witness0012 c ∈ template0012 ∧
    ∀ m ∈ cores (witness0012 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0012) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0012 cores witness0012 code0012
    code0012_correct (by decide +kernel)
#print axioms coverage0012

theorem selected0012 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0012, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0012 cores
    template0012 witness0012 coverage0012 s hs hb
#print axioms selected0012
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0013 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.1.val < 2 then (if x.2 then 3 else 1) else (if x.2 then 4 else 5)))) (by decide +kernel)
noncomputable def code0013 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 48 else 32) else (if m.val < 7 then 52 else 36))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 12 else 28) else (if m.val < 11 then 8 else 24)) else (if m.val < 14 then (if m.val < 13 then 60 else 44) else (if m.val < 15 then 56 else 40)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 3 else 19) else (if m.val < 19 then 7 else 23)) else (if m.val < 22 then (if m.val < 21 then 51 else 35) else (if m.val < 23 then 55 else 39))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 15 else 31) else (if m.val < 27 then 11 else 27)) else (if m.val < 30 then (if m.val < 29 then 63 else 47) else (if m.val < 31 then 59 else 43))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 1 else 17) else (if m.val < 35 then 5 else 21)) else (if m.val < 38 then (if m.val < 37 then 49 else 33) else (if m.val < 39 then 53 else 37))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 13 else 29) else (if m.val < 43 then 9 else 25)) else (if m.val < 46 then (if m.val < 45 then 61 else 45) else (if m.val < 47 then 57 else 41)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 2 else 18) else (if m.val < 51 then 6 else 22)) else (if m.val < 54 then (if m.val < 53 then 50 else 34) else (if m.val < 55 then 54 else 38))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 14 else 30) else (if m.val < 59 then 10 else 26)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0013_correct : ∀ m, Crown.ThreeClosure.rows (code0013 m) =
    rowOfMask (pairsOfEquiv pairing0013) (maskBits m) := by decide +kernel
theorem coverage0013 : ∀ c, witness0013 c ∈ template0013 ∧
    ∀ m ∈ cores (witness0013 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0013) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0013 cores witness0013 code0013
    code0013_correct (by decide +kernel)
#print axioms coverage0013

theorem selected0013 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0013, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0013 cores
    template0013 witness0013 coverage0013 s hs hb
#print axioms selected0013
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0014 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 3) else (if x.2 then 5 else 4)))) (by decide +kernel)
noncomputable def code0014 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 48 else 32) else (if m.val < 7 then 60 else 44))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 4 else 20) else (if m.val < 11 then 8 else 24)) else (if m.val < 14 then (if m.val < 13 then 52 else 36) else (if m.val < 15 then 56 else 40)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 1 else 17) else (if m.val < 19 then 13 else 29)) else (if m.val < 22 then (if m.val < 21 then 49 else 33) else (if m.val < 23 then 61 else 45))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 5 else 21) else (if m.val < 27 then 9 else 25)) else (if m.val < 30 then (if m.val < 29 then 53 else 37) else (if m.val < 31 then 57 else 41))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 3 else 19) else (if m.val < 35 then 15 else 31)) else (if m.val < 38 then (if m.val < 37 then 51 else 35) else (if m.val < 39 then 63 else 47))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 7 else 23) else (if m.val < 43 then 11 else 27)) else (if m.val < 46 then (if m.val < 45 then 55 else 39) else (if m.val < 47 then 59 else 43)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 2 else 18) else (if m.val < 51 then 14 else 30)) else (if m.val < 54 then (if m.val < 53 then 50 else 34) else (if m.val < 55 then 62 else 46))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 6 else 22) else (if m.val < 59 then 10 else 26)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0014_correct : ∀ m, Crown.ThreeClosure.rows (code0014 m) =
    rowOfMask (pairsOfEquiv pairing0014) (maskBits m) := by decide +kernel
theorem coverage0014 : ∀ c, witness0014 c ∈ template0014 ∧
    ∀ m ∈ cores (witness0014 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0014) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0014 cores witness0014 code0014
    code0014_correct (by decide +kernel)
#print axioms coverage0014

theorem selected0014 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0014, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0014 cores
    template0014 witness0014 coverage0014 s hs hb
#print axioms selected0014
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0015 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 2 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 3) else (if x.2 then 4 else 5)))) (by decide +kernel)
noncomputable def code0015 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 48 else 32) else (if m.val < 7 then 60 else 44))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 4 else 20) else (if m.val < 11 then 8 else 24)) else (if m.val < 14 then (if m.val < 13 then 52 else 36) else (if m.val < 15 then 56 else 40)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 3 else 19) else (if m.val < 19 then 15 else 31)) else (if m.val < 22 then (if m.val < 21 then 51 else 35) else (if m.val < 23 then 63 else 47))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 7 else 23) else (if m.val < 27 then 11 else 27)) else (if m.val < 30 then (if m.val < 29 then 55 else 39) else (if m.val < 31 then 59 else 43))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 1 else 17) else (if m.val < 35 then 13 else 29)) else (if m.val < 38 then (if m.val < 37 then 49 else 33) else (if m.val < 39 then 61 else 45))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 5 else 21) else (if m.val < 43 then 9 else 25)) else (if m.val < 46 then (if m.val < 45 then 53 else 37) else (if m.val < 47 then 57 else 41)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 2 else 18) else (if m.val < 51 then 14 else 30)) else (if m.val < 54 then (if m.val < 53 then 50 else 34) else (if m.val < 55 then 62 else 46))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 6 else 22) else (if m.val < 59 then 10 else 26)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0015_correct : ∀ m, Crown.ThreeClosure.rows (code0015 m) =
    rowOfMask (pairsOfEquiv pairing0015) (maskBits m) := by decide +kernel
theorem coverage0015 : ∀ c, witness0015 c ∈ template0015 ∧
    ∀ m ∈ cores (witness0015 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0015) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0015 cores witness0015 code0015
    code0015_correct (by decide +kernel)
#print axioms coverage0015

theorem selected0015 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0015, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0015 cores
    template0015 witness0015 coverage0015 s hs hb
#print axioms selected0015
end Crown.CertificateSixData
