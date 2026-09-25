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
noncomputable def pairing0032 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.1.val < 2 then (if x.2 then 5 else 1) else (if x.2 then 4 else 2)))) (by decide +kernel)
noncomputable def code0032 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 1 else 17) else (if m.val < 7 then 5 else 21))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 48 else 32) else (if m.val < 11 then 52 else 36)) else (if m.val < 14 then (if m.val < 13 then 49 else 33) else (if m.val < 15 then 53 else 37)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 3 else 19) else (if m.val < 19 then 7 else 23)) else (if m.val < 22 then (if m.val < 21 then 2 else 18) else (if m.val < 23 then 6 else 22))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 51 else 35) else (if m.val < 27 then 55 else 39)) else (if m.val < 30 then (if m.val < 29 then 50 else 34) else (if m.val < 31 then 54 else 38))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 12 else 28) else (if m.val < 35 then 8 else 24)) else (if m.val < 38 then (if m.val < 37 then 13 else 29) else (if m.val < 39 then 9 else 25))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 60 else 44) else (if m.val < 43 then 56 else 40)) else (if m.val < 46 then (if m.val < 45 then 61 else 45) else (if m.val < 47 then 57 else 41)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 15 else 31) else (if m.val < 51 then 11 else 27)) else (if m.val < 54 then (if m.val < 53 then 14 else 30) else (if m.val < 55 then 10 else 26))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 63 else 47) else (if m.val < 59 then 59 else 43)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0032_correct : ∀ m, Crown.ThreeClosure.rows (code0032 m) =
    rowOfMask (pairsOfEquiv pairing0032) (maskBits m) := by decide +kernel
theorem coverage0032 : ∀ c, witness0032 c ∈ template0032 ∧
    ∀ m ∈ cores (witness0032 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0032) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0032 cores witness0032 code0032
    code0032_correct (by decide +kernel)
#print axioms coverage0032

theorem selected0032 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0032, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0032 cores
    template0032 witness0032 coverage0032 s hs hb
#print axioms selected0032
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0033 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.1.val < 2 then (if x.2 then 5 else 1) else (if x.2 then 2 else 4)))) (by decide +kernel)
noncomputable def code0033 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 3 else 19) else (if m.val < 7 then 7 else 23))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 48 else 32) else (if m.val < 11 then 52 else 36)) else (if m.val < 14 then (if m.val < 13 then 51 else 35) else (if m.val < 15 then 55 else 39)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 1 else 17) else (if m.val < 19 then 5 else 21)) else (if m.val < 22 then (if m.val < 21 then 2 else 18) else (if m.val < 23 then 6 else 22))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 49 else 33) else (if m.val < 27 then 53 else 37)) else (if m.val < 30 then (if m.val < 29 then 50 else 34) else (if m.val < 31 then 54 else 38))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 12 else 28) else (if m.val < 35 then 8 else 24)) else (if m.val < 38 then (if m.val < 37 then 15 else 31) else (if m.val < 39 then 11 else 27))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 60 else 44) else (if m.val < 43 then 56 else 40)) else (if m.val < 46 then (if m.val < 45 then 63 else 47) else (if m.val < 47 then 59 else 43)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 13 else 29) else (if m.val < 51 then 9 else 25)) else (if m.val < 54 then (if m.val < 53 then 14 else 30) else (if m.val < 55 then 10 else 26))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 61 else 45) else (if m.val < 59 then 57 else 41)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0033_correct : ∀ m, Crown.ThreeClosure.rows (code0033 m) =
    rowOfMask (pairsOfEquiv pairing0033) (maskBits m) := by decide +kernel
theorem coverage0033 : ∀ c, witness0033 c ∈ template0033 ∧
    ∀ m ∈ cores (witness0033 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0033) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0033 cores witness0033 code0033
    code0033_correct (by decide +kernel)
#print axioms coverage0033

theorem selected0033 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0033, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0033 cores
    template0033 witness0033 coverage0033 s hs hb
#print axioms selected0033
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0034 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 5) else (if x.2 then 4 else 2)))) (by decide +kernel)
noncomputable def code0034 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 1 else 17) else (if m.val < 7 then 13 else 29))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 48 else 32) else (if m.val < 11 then 60 else 44)) else (if m.val < 14 then (if m.val < 13 then 49 else 33) else (if m.val < 15 then 61 else 45)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 3 else 19) else (if m.val < 19 then 15 else 31)) else (if m.val < 22 then (if m.val < 21 then 2 else 18) else (if m.val < 23 then 14 else 30))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 51 else 35) else (if m.val < 27 then 63 else 47)) else (if m.val < 30 then (if m.val < 29 then 50 else 34) else (if m.val < 31 then 62 else 46))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 4 else 20) else (if m.val < 35 then 8 else 24)) else (if m.val < 38 then (if m.val < 37 then 5 else 21) else (if m.val < 39 then 9 else 25))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 52 else 36) else (if m.val < 43 then 56 else 40)) else (if m.val < 46 then (if m.val < 45 then 53 else 37) else (if m.val < 47 then 57 else 41)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 7 else 23) else (if m.val < 51 then 11 else 27)) else (if m.val < 54 then (if m.val < 53 then 6 else 22) else (if m.val < 55 then 10 else 26))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 55 else 39) else (if m.val < 59 then 59 else 43)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0034_correct : ∀ m, Crown.ThreeClosure.rows (code0034 m) =
    rowOfMask (pairsOfEquiv pairing0034) (maskBits m) := by decide +kernel
theorem coverage0034 : ∀ c, witness0034 c ∈ template0034 ∧
    ∀ m ∈ cores (witness0034 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0034) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0034 cores witness0034 code0034
    code0034_correct (by decide +kernel)
#print axioms coverage0034

theorem selected0034 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0034, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0034 cores
    template0034 witness0034 coverage0034 s hs hb
#print axioms selected0034
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0035 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 3 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 5) else (if x.2 then 2 else 4)))) (by decide +kernel)
noncomputable def code0035 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 3 else 19) else (if m.val < 7 then 15 else 31))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 48 else 32) else (if m.val < 11 then 60 else 44)) else (if m.val < 14 then (if m.val < 13 then 51 else 35) else (if m.val < 15 then 63 else 47)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 1 else 17) else (if m.val < 19 then 13 else 29)) else (if m.val < 22 then (if m.val < 21 then 2 else 18) else (if m.val < 23 then 14 else 30))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 49 else 33) else (if m.val < 27 then 61 else 45)) else (if m.val < 30 then (if m.val < 29 then 50 else 34) else (if m.val < 31 then 62 else 46))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 4 else 20) else (if m.val < 35 then 8 else 24)) else (if m.val < 38 then (if m.val < 37 then 7 else 23) else (if m.val < 39 then 11 else 27))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 52 else 36) else (if m.val < 43 then 56 else 40)) else (if m.val < 46 then (if m.val < 45 then 55 else 39) else (if m.val < 47 then 59 else 43)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 5 else 21) else (if m.val < 51 then 9 else 25)) else (if m.val < 54 then (if m.val < 53 then 6 else 22) else (if m.val < 55 then 10 else 26))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 53 else 37) else (if m.val < 59 then 57 else 41)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0035_correct : ∀ m, Crown.ThreeClosure.rows (code0035 m) =
    rowOfMask (pairsOfEquiv pairing0035) (maskBits m) := by decide +kernel
theorem coverage0035 : ∀ c, witness0035 c ∈ template0035 ∧
    ∀ m ∈ cores (witness0035 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0035) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0035 cores witness0035 code0035
    code0035_correct (by decide +kernel)
#print axioms coverage0035

theorem selected0035 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0035, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0035 cores
    template0035 witness0035 coverage0035 s hs hb
#print axioms selected0035
end Crown.CertificateSixData
