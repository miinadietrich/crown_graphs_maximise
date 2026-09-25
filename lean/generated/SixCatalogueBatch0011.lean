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
noncomputable def pairing0044 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.1.val < 2 then (if x.2 then 5 else 1) else (if x.2 then 3 else 2)))) (by decide +kernel)
noncomputable def code0044 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 1 else 17) else (if m.val < 7 then 5 else 21))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 7 else 23)) else (if m.val < 14 then (if m.val < 13 then 2 else 18) else (if m.val < 15 then 6 else 22)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 48 else 32) else (if m.val < 19 then 52 else 36)) else (if m.val < 22 then (if m.val < 21 then 49 else 33) else (if m.val < 23 then 53 else 37))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 51 else 35) else (if m.val < 27 then 55 else 39)) else (if m.val < 30 then (if m.val < 29 then 50 else 34) else (if m.val < 31 then 54 else 38))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 12 else 28) else (if m.val < 35 then 8 else 24)) else (if m.val < 38 then (if m.val < 37 then 13 else 29) else (if m.val < 39 then 9 else 25))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 15 else 31) else (if m.val < 43 then 11 else 27)) else (if m.val < 46 then (if m.val < 45 then 14 else 30) else (if m.val < 47 then 10 else 26)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 60 else 44) else (if m.val < 51 then 56 else 40)) else (if m.val < 54 then (if m.val < 53 then 61 else 45) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 63 else 47) else (if m.val < 59 then 59 else 43)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0044_correct : ∀ m, Crown.ThreeClosure.rows (code0044 m) =
    rowOfMask (pairsOfEquiv pairing0044) (maskBits m) := by decide +kernel
theorem coverage0044 : ∀ c, witness0044 c ∈ template0044 ∧
    ∀ m ∈ cores (witness0044 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0044) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0044 cores witness0044 code0044
    code0044_correct (by decide +kernel)
#print axioms coverage0044

theorem selected0044 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0044, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0044 cores
    template0044 witness0044 coverage0044 s hs hb
#print axioms selected0044
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0045 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.1.val < 2 then (if x.2 then 5 else 1) else (if x.2 then 2 else 3)))) (by decide +kernel)
noncomputable def code0045 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 3 else 19) else (if m.val < 7 then 7 else 23))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 5 else 21)) else (if m.val < 14 then (if m.val < 13 then 2 else 18) else (if m.val < 15 then 6 else 22)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 48 else 32) else (if m.val < 19 then 52 else 36)) else (if m.val < 22 then (if m.val < 21 then 51 else 35) else (if m.val < 23 then 55 else 39))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 49 else 33) else (if m.val < 27 then 53 else 37)) else (if m.val < 30 then (if m.val < 29 then 50 else 34) else (if m.val < 31 then 54 else 38))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 12 else 28) else (if m.val < 35 then 8 else 24)) else (if m.val < 38 then (if m.val < 37 then 15 else 31) else (if m.val < 39 then 11 else 27))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 13 else 29) else (if m.val < 43 then 9 else 25)) else (if m.val < 46 then (if m.val < 45 then 14 else 30) else (if m.val < 47 then 10 else 26)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 60 else 44) else (if m.val < 51 then 56 else 40)) else (if m.val < 54 then (if m.val < 53 then 63 else 47) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 61 else 45) else (if m.val < 59 then 57 else 41)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0045_correct : ∀ m, Crown.ThreeClosure.rows (code0045 m) =
    rowOfMask (pairsOfEquiv pairing0045) (maskBits m) := by decide +kernel
theorem coverage0045 : ∀ c, witness0045 c ∈ template0045 ∧
    ∀ m ∈ cores (witness0045 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0045) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0045 cores witness0045 code0045
    code0045_correct (by decide +kernel)
#print axioms coverage0045

theorem selected0045 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0045, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0045 cores
    template0045 witness0045 coverage0045 s hs hb
#print axioms selected0045
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0046 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 5) else (if x.2 then 3 else 2)))) (by decide +kernel)
noncomputable def code0046 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 1 else 17) else (if m.val < 7 then 13 else 29))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 3 else 19) else (if m.val < 11 then 15 else 31)) else (if m.val < 14 then (if m.val < 13 then 2 else 18) else (if m.val < 15 then 14 else 30)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 48 else 32) else (if m.val < 19 then 60 else 44)) else (if m.val < 22 then (if m.val < 21 then 49 else 33) else (if m.val < 23 then 61 else 45))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 51 else 35) else (if m.val < 27 then 63 else 47)) else (if m.val < 30 then (if m.val < 29 then 50 else 34) else (if m.val < 31 then 62 else 46))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 4 else 20) else (if m.val < 35 then 8 else 24)) else (if m.val < 38 then (if m.val < 37 then 5 else 21) else (if m.val < 39 then 9 else 25))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 7 else 23) else (if m.val < 43 then 11 else 27)) else (if m.val < 46 then (if m.val < 45 then 6 else 22) else (if m.val < 47 then 10 else 26)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 52 else 36) else (if m.val < 51 then 56 else 40)) else (if m.val < 54 then (if m.val < 53 then 53 else 37) else (if m.val < 55 then 57 else 41))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 55 else 39) else (if m.val < 59 then 59 else 43)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0046_correct : ∀ m, Crown.ThreeClosure.rows (code0046 m) =
    rowOfMask (pairsOfEquiv pairing0046) (maskBits m) := by decide +kernel
theorem coverage0046 : ∀ c, witness0046 c ∈ template0046 ∧
    ∀ m ∈ cores (witness0046 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0046) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0046 cores witness0046 code0046
    code0046_correct (by decide +kernel)
#print axioms coverage0046

theorem selected0046 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0046, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0046 cores
    template0046 witness0046 coverage0046 s hs hb
#print axioms selected0046
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0047 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 5) else (if x.2 then 2 else 3)))) (by decide +kernel)
noncomputable def code0047 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 3 else 19) else (if m.val < 7 then 15 else 31))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 1 else 17) else (if m.val < 11 then 13 else 29)) else (if m.val < 14 then (if m.val < 13 then 2 else 18) else (if m.val < 15 then 14 else 30)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 48 else 32) else (if m.val < 19 then 60 else 44)) else (if m.val < 22 then (if m.val < 21 then 51 else 35) else (if m.val < 23 then 63 else 47))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 49 else 33) else (if m.val < 27 then 61 else 45)) else (if m.val < 30 then (if m.val < 29 then 50 else 34) else (if m.val < 31 then 62 else 46))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 4 else 20) else (if m.val < 35 then 8 else 24)) else (if m.val < 38 then (if m.val < 37 then 7 else 23) else (if m.val < 39 then 11 else 27))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 5 else 21) else (if m.val < 43 then 9 else 25)) else (if m.val < 46 then (if m.val < 45 then 6 else 22) else (if m.val < 47 then 10 else 26)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 52 else 36) else (if m.val < 51 then 56 else 40)) else (if m.val < 54 then (if m.val < 53 then 55 else 39) else (if m.val < 55 then 59 else 43))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 53 else 37) else (if m.val < 59 then 57 else 41)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0047_correct : ∀ m, Crown.ThreeClosure.rows (code0047 m) =
    rowOfMask (pairsOfEquiv pairing0047) (maskBits m) := by decide +kernel
theorem coverage0047 : ∀ c, witness0047 c ∈ template0047 ∧
    ∀ m ∈ cores (witness0047 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0047) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0047 cores witness0047 code0047
    code0047_correct (by decide +kernel)
#print axioms coverage0047

theorem selected0047 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0047, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0047 cores
    template0047 witness0047 coverage0047 s hs hb
#print axioms selected0047
end Crown.CertificateSixData
