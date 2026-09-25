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
noncomputable def pairing0008 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.1.val < 2 then (if x.2 then 5 else 2) else (if x.2 then 4 else 3)))) (by decide +kernel)
noncomputable def code0008 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 48 else 32)) else (if m.val < 6 then (if m.val < 5 then 4 else 20) else (if m.val < 7 then 52 else 36))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 49 else 33)) else (if m.val < 14 then (if m.val < 13 then 5 else 21) else (if m.val < 15 then 53 else 37)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 3 else 19) else (if m.val < 19 then 51 else 35)) else (if m.val < 22 then (if m.val < 21 then 7 else 23) else (if m.val < 23 then 55 else 39))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 2 else 18) else (if m.val < 27 then 50 else 34)) else (if m.val < 30 then (if m.val < 29 then 6 else 22) else (if m.val < 31 then 54 else 38))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 12 else 28) else (if m.val < 35 then 60 else 44)) else (if m.val < 38 then (if m.val < 37 then 8 else 24) else (if m.val < 39 then 56 else 40))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 13 else 29) else (if m.val < 43 then 61 else 45)) else (if m.val < 46 then (if m.val < 45 then 9 else 25) else (if m.val < 47 then 57 else 41)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 15 else 31) else (if m.val < 51 then 63 else 47)) else (if m.val < 54 then (if m.val < 53 then 11 else 27) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 14 else 30) else (if m.val < 59 then 62 else 46)) else (if m.val < 62 then (if m.val < 61 then 10 else 26) else (if m.val < 63 then 58 else 42))))))
theorem code0008_correct : ∀ m, Crown.ThreeClosure.rows (code0008 m) =
    rowOfMask (pairsOfEquiv pairing0008) (maskBits m) := by decide +kernel
theorem coverage0008 : ∀ c, witness0008 c ∈ template0008 ∧
    ∀ m ∈ cores (witness0008 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0008) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0008 cores witness0008 code0008
    code0008_correct (by decide +kernel)
#print axioms coverage0008

theorem selected0008 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0008, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0008 cores
    template0008 witness0008 coverage0008 s hs hb
#print axioms selected0008
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0009 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.1.val < 2 then (if x.2 then 5 else 2) else (if x.2 then 3 else 4)))) (by decide +kernel)
noncomputable def code0009 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 48 else 32)) else (if m.val < 6 then (if m.val < 5 then 4 else 20) else (if m.val < 7 then 52 else 36))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 51 else 35)) else (if m.val < 14 then (if m.val < 13 then 7 else 23) else (if m.val < 15 then 55 else 39)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 1 else 17) else (if m.val < 19 then 49 else 33)) else (if m.val < 22 then (if m.val < 21 then 5 else 21) else (if m.val < 23 then 53 else 37))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 2 else 18) else (if m.val < 27 then 50 else 34)) else (if m.val < 30 then (if m.val < 29 then 6 else 22) else (if m.val < 31 then 54 else 38))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 12 else 28) else (if m.val < 35 then 60 else 44)) else (if m.val < 38 then (if m.val < 37 then 8 else 24) else (if m.val < 39 then 56 else 40))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 15 else 31) else (if m.val < 43 then 63 else 47)) else (if m.val < 46 then (if m.val < 45 then 11 else 27) else (if m.val < 47 then 59 else 43)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 13 else 29) else (if m.val < 51 then 61 else 45)) else (if m.val < 54 then (if m.val < 53 then 9 else 25) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 14 else 30) else (if m.val < 59 then 62 else 46)) else (if m.val < 62 then (if m.val < 61 then 10 else 26) else (if m.val < 63 then 58 else 42))))))
theorem code0009_correct : ∀ m, Crown.ThreeClosure.rows (code0009 m) =
    rowOfMask (pairsOfEquiv pairing0009) (maskBits m) := by decide +kernel
theorem coverage0009 : ∀ c, witness0009 c ∈ template0009 ∧
    ∀ m ∈ cores (witness0009 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0009) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0009 cores witness0009 code0009
    code0009_correct (by decide +kernel)
#print axioms coverage0009

theorem selected0009 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0009, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0009 cores
    template0009 witness0009 coverage0009 s hs hb
#print axioms selected0009
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0010 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.1.val < 2 then (if x.2 then 2 else 5) else (if x.2 then 4 else 3)))) (by decide +kernel)
noncomputable def code0010 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 48 else 32)) else (if m.val < 6 then (if m.val < 5 then 12 else 28) else (if m.val < 7 then 60 else 44))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 49 else 33)) else (if m.val < 14 then (if m.val < 13 then 13 else 29) else (if m.val < 15 then 61 else 45)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 3 else 19) else (if m.val < 19 then 51 else 35)) else (if m.val < 22 then (if m.val < 21 then 15 else 31) else (if m.val < 23 then 63 else 47))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 2 else 18) else (if m.val < 27 then 50 else 34)) else (if m.val < 30 then (if m.val < 29 then 14 else 30) else (if m.val < 31 then 62 else 46))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 4 else 20) else (if m.val < 35 then 52 else 36)) else (if m.val < 38 then (if m.val < 37 then 8 else 24) else (if m.val < 39 then 56 else 40))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 5 else 21) else (if m.val < 43 then 53 else 37)) else (if m.val < 46 then (if m.val < 45 then 9 else 25) else (if m.val < 47 then 57 else 41)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 7 else 23) else (if m.val < 51 then 55 else 39)) else (if m.val < 54 then (if m.val < 53 then 11 else 27) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 6 else 22) else (if m.val < 59 then 54 else 38)) else (if m.val < 62 then (if m.val < 61 then 10 else 26) else (if m.val < 63 then 58 else 42))))))
theorem code0010_correct : ∀ m, Crown.ThreeClosure.rows (code0010 m) =
    rowOfMask (pairsOfEquiv pairing0010) (maskBits m) := by decide +kernel
theorem coverage0010 : ∀ c, witness0010 c ∈ template0010 ∧
    ∀ m ∈ cores (witness0010 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0010) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0010 cores witness0010 code0010
    code0010_correct (by decide +kernel)
#print axioms coverage0010

theorem selected0010 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0010, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0010 cores
    template0010 witness0010 coverage0010 s hs hb
#print axioms selected0010
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0011 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 1 else 0) else (if x.1.val < 2 then (if x.2 then 2 else 5) else (if x.2 then 3 else 4)))) (by decide +kernel)
noncomputable def code0011 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 48 else 32)) else (if m.val < 6 then (if m.val < 5 then 12 else 28) else (if m.val < 7 then 60 else 44))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 51 else 35)) else (if m.val < 14 then (if m.val < 13 then 15 else 31) else (if m.val < 15 then 63 else 47)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 1 else 17) else (if m.val < 19 then 49 else 33)) else (if m.val < 22 then (if m.val < 21 then 13 else 29) else (if m.val < 23 then 61 else 45))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 2 else 18) else (if m.val < 27 then 50 else 34)) else (if m.val < 30 then (if m.val < 29 then 14 else 30) else (if m.val < 31 then 62 else 46))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 4 else 20) else (if m.val < 35 then 52 else 36)) else (if m.val < 38 then (if m.val < 37 then 8 else 24) else (if m.val < 39 then 56 else 40))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 7 else 23) else (if m.val < 43 then 55 else 39)) else (if m.val < 46 then (if m.val < 45 then 11 else 27) else (if m.val < 47 then 59 else 43)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 5 else 21) else (if m.val < 51 then 53 else 37)) else (if m.val < 54 then (if m.val < 53 then 9 else 25) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 6 else 22) else (if m.val < 59 then 54 else 38)) else (if m.val < 62 then (if m.val < 61 then 10 else 26) else (if m.val < 63 then 58 else 42))))))
theorem code0011_correct : ∀ m, Crown.ThreeClosure.rows (code0011 m) =
    rowOfMask (pairsOfEquiv pairing0011) (maskBits m) := by decide +kernel
theorem coverage0011 : ∀ c, witness0011 c ∈ template0011 ∧
    ∀ m ∈ cores (witness0011 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0011) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0011 cores witness0011 code0011
    code0011_correct (by decide +kernel)
#print axioms coverage0011

theorem selected0011 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0011, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0011 cores
    template0011 witness0011 coverage0011 s hs hb
#print axioms selected0011
end Crown.CertificateSixData
