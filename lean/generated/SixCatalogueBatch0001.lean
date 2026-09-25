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
noncomputable def pairing0004 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.1.val < 2 then (if x.2 then 4 else 2) else (if x.2 then 5 else 3)))) (by decide +kernel)
noncomputable def code0004 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 48 else 32)) else (if m.val < 6 then (if m.val < 5 then 4 else 20) else (if m.val < 7 then 52 else 36))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 49 else 33)) else (if m.val < 14 then (if m.val < 13 then 5 else 21) else (if m.val < 15 then 53 else 37)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 12 else 28) else (if m.val < 19 then 60 else 44)) else (if m.val < 22 then (if m.val < 21 then 8 else 24) else (if m.val < 23 then 56 else 40))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 13 else 29) else (if m.val < 27 then 61 else 45)) else (if m.val < 30 then (if m.val < 29 then 9 else 25) else (if m.val < 31 then 57 else 41))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 3 else 19) else (if m.val < 35 then 51 else 35)) else (if m.val < 38 then (if m.val < 37 then 7 else 23) else (if m.val < 39 then 55 else 39))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 2 else 18) else (if m.val < 43 then 50 else 34)) else (if m.val < 46 then (if m.val < 45 then 6 else 22) else (if m.val < 47 then 54 else 38)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 15 else 31) else (if m.val < 51 then 63 else 47)) else (if m.val < 54 then (if m.val < 53 then 11 else 27) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 14 else 30) else (if m.val < 59 then 62 else 46)) else (if m.val < 62 then (if m.val < 61 then 10 else 26) else (if m.val < 63 then 58 else 42))))))
theorem code0004_correct : ∀ m, Crown.ThreeClosure.rows (code0004 m) =
    rowOfMask (pairsOfEquiv pairing0004) (maskBits m) := by decide +kernel
theorem coverage0004 : ∀ c, witness0004 c ∈ template0004 ∧
    ∀ m ∈ cores (witness0004 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0004) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0004 cores witness0004 code0004
    code0004_correct (by decide +kernel)
#print axioms coverage0004

theorem selected0004 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0004, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0004 cores
    template0004 witness0004 coverage0004 s hs hb
#print axioms selected0004
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0005 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.1.val < 2 then (if x.2 then 4 else 2) else (if x.2 then 3 else 5)))) (by decide +kernel)
noncomputable def code0005 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 48 else 32)) else (if m.val < 6 then (if m.val < 5 then 4 else 20) else (if m.val < 7 then 52 else 36))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 51 else 35)) else (if m.val < 14 then (if m.val < 13 then 7 else 23) else (if m.val < 15 then 55 else 39)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 12 else 28) else (if m.val < 19 then 60 else 44)) else (if m.val < 22 then (if m.val < 21 then 8 else 24) else (if m.val < 23 then 56 else 40))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 15 else 31) else (if m.val < 27 then 63 else 47)) else (if m.val < 30 then (if m.val < 29 then 11 else 27) else (if m.val < 31 then 59 else 43))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 1 else 17) else (if m.val < 35 then 49 else 33)) else (if m.val < 38 then (if m.val < 37 then 5 else 21) else (if m.val < 39 then 53 else 37))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 2 else 18) else (if m.val < 43 then 50 else 34)) else (if m.val < 46 then (if m.val < 45 then 6 else 22) else (if m.val < 47 then 54 else 38)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 13 else 29) else (if m.val < 51 then 61 else 45)) else (if m.val < 54 then (if m.val < 53 then 9 else 25) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 14 else 30) else (if m.val < 59 then 62 else 46)) else (if m.val < 62 then (if m.val < 61 then 10 else 26) else (if m.val < 63 then 58 else 42))))))
theorem code0005_correct : ∀ m, Crown.ThreeClosure.rows (code0005 m) =
    rowOfMask (pairsOfEquiv pairing0005) (maskBits m) := by decide +kernel
theorem coverage0005 : ∀ c, witness0005 c ∈ template0005 ∧
    ∀ m ∈ cores (witness0005 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0005) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0005 cores witness0005 code0005
    code0005_correct (by decide +kernel)
#print axioms coverage0005

theorem selected0005 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0005, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0005 cores
    template0005 witness0005 coverage0005 s hs hb
#print axioms selected0005
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0006 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.1.val < 2 then (if x.2 then 2 else 4) else (if x.2 then 5 else 3)))) (by decide +kernel)
noncomputable def code0006 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 48 else 32)) else (if m.val < 6 then (if m.val < 5 then 12 else 28) else (if m.val < 7 then 60 else 44))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 49 else 33)) else (if m.val < 14 then (if m.val < 13 then 13 else 29) else (if m.val < 15 then 61 else 45)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 4 else 20) else (if m.val < 19 then 52 else 36)) else (if m.val < 22 then (if m.val < 21 then 8 else 24) else (if m.val < 23 then 56 else 40))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 5 else 21) else (if m.val < 27 then 53 else 37)) else (if m.val < 30 then (if m.val < 29 then 9 else 25) else (if m.val < 31 then 57 else 41))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 3 else 19) else (if m.val < 35 then 51 else 35)) else (if m.val < 38 then (if m.val < 37 then 15 else 31) else (if m.val < 39 then 63 else 47))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 2 else 18) else (if m.val < 43 then 50 else 34)) else (if m.val < 46 then (if m.val < 45 then 14 else 30) else (if m.val < 47 then 62 else 46)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 7 else 23) else (if m.val < 51 then 55 else 39)) else (if m.val < 54 then (if m.val < 53 then 11 else 27) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 6 else 22) else (if m.val < 59 then 54 else 38)) else (if m.val < 62 then (if m.val < 61 then 10 else 26) else (if m.val < 63 then 58 else 42))))))
theorem code0006_correct : ∀ m, Crown.ThreeClosure.rows (code0006 m) =
    rowOfMask (pairsOfEquiv pairing0006) (maskBits m) := by decide +kernel
theorem coverage0006 : ∀ c, witness0006 c ∈ template0006 ∧
    ∀ m ∈ cores (witness0006 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0006) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0006 cores witness0006 code0006
    code0006_correct (by decide +kernel)
#print axioms coverage0006

theorem selected0006 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0006, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0006 cores
    template0006 witness0006 coverage0006 s hs hb
#print axioms selected0006
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0007 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.1.val < 2 then (if x.2 then 2 else 4) else (if x.2 then 3 else 5)))) (by decide +kernel)
noncomputable def code0007 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 48 else 32)) else (if m.val < 6 then (if m.val < 5 then 12 else 28) else (if m.val < 7 then 60 else 44))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 51 else 35)) else (if m.val < 14 then (if m.val < 13 then 15 else 31) else (if m.val < 15 then 63 else 47)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 4 else 20) else (if m.val < 19 then 52 else 36)) else (if m.val < 22 then (if m.val < 21 then 8 else 24) else (if m.val < 23 then 56 else 40))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 7 else 23) else (if m.val < 27 then 55 else 39)) else (if m.val < 30 then (if m.val < 29 then 11 else 27) else (if m.val < 31 then 59 else 43))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 1 else 17) else (if m.val < 35 then 49 else 33)) else (if m.val < 38 then (if m.val < 37 then 13 else 29) else (if m.val < 39 then 61 else 45))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 2 else 18) else (if m.val < 43 then 50 else 34)) else (if m.val < 46 then (if m.val < 45 then 14 else 30) else (if m.val < 47 then 62 else 46)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 5 else 21) else (if m.val < 51 then 53 else 37)) else (if m.val < 54 then (if m.val < 53 then 9 else 25) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 6 else 22) else (if m.val < 59 then 54 else 38)) else (if m.val < 62 then (if m.val < 61 then 10 else 26) else (if m.val < 63 then 58 else 42))))))
theorem code0007_correct : ∀ m, Crown.ThreeClosure.rows (code0007 m) =
    rowOfMask (pairsOfEquiv pairing0007) (maskBits m) := by decide +kernel
theorem coverage0007 : ∀ c, witness0007 c ∈ template0007 ∧
    ∀ m ∈ cores (witness0007 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0007) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0007 cores witness0007 code0007
    code0007_correct (by decide +kernel)
#print axioms coverage0007

theorem selected0007 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0007, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0007 cores
    template0007 witness0007 coverage0007 s hs hb
#print axioms selected0007
end Crown.CertificateSixData
