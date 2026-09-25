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
noncomputable def pairing0048 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 2 else 1) else (if x.2 then 4 else 3)))) (by decide +kernel)
noncomputable def code0048 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 12 else 28) else (if m.val < 7 then 8 else 24))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 5 else 21)) else (if m.val < 14 then (if m.val < 13 then 13 else 29) else (if m.val < 15 then 9 else 25)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 3 else 19) else (if m.val < 19 then 7 else 23)) else (if m.val < 22 then (if m.val < 21 then 15 else 31) else (if m.val < 23 then 11 else 27))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 2 else 18) else (if m.val < 27 then 6 else 22)) else (if m.val < 30 then (if m.val < 29 then 14 else 30) else (if m.val < 31 then 10 else 26))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 48 else 32) else (if m.val < 35 then 52 else 36)) else (if m.val < 38 then (if m.val < 37 then 60 else 44) else (if m.val < 39 then 56 else 40))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 49 else 33) else (if m.val < 43 then 53 else 37)) else (if m.val < 46 then (if m.val < 45 then 61 else 45) else (if m.val < 47 then 57 else 41)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 51 else 35) else (if m.val < 51 then 55 else 39)) else (if m.val < 54 then (if m.val < 53 then 63 else 47) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 50 else 34) else (if m.val < 59 then 54 else 38)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0048_correct : ∀ m, Crown.ThreeClosure.rows (code0048 m) =
    rowOfMask (pairsOfEquiv pairing0048) (maskBits m) := by decide +kernel
theorem coverage0048 : ∀ c, witness0048 c ∈ template0048 ∧
    ∀ m ∈ cores (witness0048 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0048) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0048 cores witness0048 code0048
    code0048_correct (by decide +kernel)
#print axioms coverage0048

theorem selected0048 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0048, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0048 cores
    template0048 witness0048 coverage0048 s hs hb
#print axioms selected0048
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0049 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 2 else 1) else (if x.2 then 3 else 4)))) (by decide +kernel)
noncomputable def code0049 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 12 else 28) else (if m.val < 7 then 8 else 24))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 7 else 23)) else (if m.val < 14 then (if m.val < 13 then 15 else 31) else (if m.val < 15 then 11 else 27)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 1 else 17) else (if m.val < 19 then 5 else 21)) else (if m.val < 22 then (if m.val < 21 then 13 else 29) else (if m.val < 23 then 9 else 25))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 2 else 18) else (if m.val < 27 then 6 else 22)) else (if m.val < 30 then (if m.val < 29 then 14 else 30) else (if m.val < 31 then 10 else 26))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 48 else 32) else (if m.val < 35 then 52 else 36)) else (if m.val < 38 then (if m.val < 37 then 60 else 44) else (if m.val < 39 then 56 else 40))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 51 else 35) else (if m.val < 43 then 55 else 39)) else (if m.val < 46 then (if m.val < 45 then 63 else 47) else (if m.val < 47 then 59 else 43)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 49 else 33) else (if m.val < 51 then 53 else 37)) else (if m.val < 54 then (if m.val < 53 then 61 else 45) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 50 else 34) else (if m.val < 59 then 54 else 38)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0049_correct : ∀ m, Crown.ThreeClosure.rows (code0049 m) =
    rowOfMask (pairsOfEquiv pairing0049) (maskBits m) := by decide +kernel
theorem coverage0049 : ∀ c, witness0049 c ∈ template0049 ∧
    ∀ m ∈ cores (witness0049 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0049) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0049 cores witness0049 code0049
    code0049_correct (by decide +kernel)
#print axioms coverage0049

theorem selected0049 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0049, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0049 cores
    template0049 witness0049 coverage0049 s hs hb
#print axioms selected0049
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0050 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)
noncomputable def code0050 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 4 else 20) else (if m.val < 7 then 8 else 24))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 13 else 29)) else (if m.val < 14 then (if m.val < 13 then 5 else 21) else (if m.val < 15 then 9 else 25)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 3 else 19) else (if m.val < 19 then 15 else 31)) else (if m.val < 22 then (if m.val < 21 then 7 else 23) else (if m.val < 23 then 11 else 27))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 2 else 18) else (if m.val < 27 then 14 else 30)) else (if m.val < 30 then (if m.val < 29 then 6 else 22) else (if m.val < 31 then 10 else 26))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 48 else 32) else (if m.val < 35 then 60 else 44)) else (if m.val < 38 then (if m.val < 37 then 52 else 36) else (if m.val < 39 then 56 else 40))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 49 else 33) else (if m.val < 43 then 61 else 45)) else (if m.val < 46 then (if m.val < 45 then 53 else 37) else (if m.val < 47 then 57 else 41)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 51 else 35) else (if m.val < 51 then 63 else 47)) else (if m.val < 54 then (if m.val < 53 then 55 else 39) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 50 else 34) else (if m.val < 59 then 62 else 46)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0050_correct : ∀ m, Crown.ThreeClosure.rows (code0050 m) =
    rowOfMask (pairsOfEquiv pairing0050) (maskBits m) := by decide +kernel
theorem coverage0050 : ∀ c, witness0050 c ∈ template0050 ∧
    ∀ m ∈ cores (witness0050 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0050) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0050 cores witness0050 code0050
    code0050_correct (by decide +kernel)
#print axioms coverage0050

theorem selected0050 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0050, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0050 cores
    template0050 witness0050 coverage0050 s hs hb
#print axioms selected0050
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0051 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 5 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)
noncomputable def code0051 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 4 else 20) else (if m.val < 7 then 8 else 24))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 15 else 31)) else (if m.val < 14 then (if m.val < 13 then 7 else 23) else (if m.val < 15 then 11 else 27)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 1 else 17) else (if m.val < 19 then 13 else 29)) else (if m.val < 22 then (if m.val < 21 then 5 else 21) else (if m.val < 23 then 9 else 25))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 2 else 18) else (if m.val < 27 then 14 else 30)) else (if m.val < 30 then (if m.val < 29 then 6 else 22) else (if m.val < 31 then 10 else 26))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 48 else 32) else (if m.val < 35 then 60 else 44)) else (if m.val < 38 then (if m.val < 37 then 52 else 36) else (if m.val < 39 then 56 else 40))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 51 else 35) else (if m.val < 43 then 63 else 47)) else (if m.val < 46 then (if m.val < 45 then 55 else 39) else (if m.val < 47 then 59 else 43)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 49 else 33) else (if m.val < 51 then 61 else 45)) else (if m.val < 54 then (if m.val < 53 then 53 else 37) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 50 else 34) else (if m.val < 59 then 62 else 46)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0051_correct : ∀ m, Crown.ThreeClosure.rows (code0051 m) =
    rowOfMask (pairsOfEquiv pairing0051) (maskBits m) := by decide +kernel
theorem coverage0051 : ∀ c, witness0051 c ∈ template0051 ∧
    ∀ m ∈ cores (witness0051 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0051) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0051 cores witness0051 code0051
    code0051_correct (by decide +kernel)
#print axioms coverage0051

theorem selected0051 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0051, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0051 cores
    template0051 witness0051 coverage0051 s hs hb
#print axioms selected0051
end Crown.CertificateSixData
