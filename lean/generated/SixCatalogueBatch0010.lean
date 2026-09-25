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
noncomputable def pairing0040 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.1.val < 2 then (if x.2 then 3 else 1) else (if x.2 then 5 else 2)))) (by decide +kernel)
noncomputable def code0040 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 1 else 17) else (if m.val < 7 then 5 else 21))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 12 else 28) else (if m.val < 11 then 8 else 24)) else (if m.val < 14 then (if m.val < 13 then 13 else 29) else (if m.val < 15 then 9 else 25)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 48 else 32) else (if m.val < 19 then 52 else 36)) else (if m.val < 22 then (if m.val < 21 then 49 else 33) else (if m.val < 23 then 53 else 37))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 60 else 44) else (if m.val < 27 then 56 else 40)) else (if m.val < 30 then (if m.val < 29 then 61 else 45) else (if m.val < 31 then 57 else 41))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 3 else 19) else (if m.val < 35 then 7 else 23)) else (if m.val < 38 then (if m.val < 37 then 2 else 18) else (if m.val < 39 then 6 else 22))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 15 else 31) else (if m.val < 43 then 11 else 27)) else (if m.val < 46 then (if m.val < 45 then 14 else 30) else (if m.val < 47 then 10 else 26)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 51 else 35) else (if m.val < 51 then 55 else 39)) else (if m.val < 54 then (if m.val < 53 then 50 else 34) else (if m.val < 55 then 54 else 38))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 63 else 47) else (if m.val < 59 then 59 else 43)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0040_correct : ∀ m, Crown.ThreeClosure.rows (code0040 m) =
    rowOfMask (pairsOfEquiv pairing0040) (maskBits m) := by decide +kernel
theorem coverage0040 : ∀ c, witness0040 c ∈ template0040 ∧
    ∀ m ∈ cores (witness0040 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0040) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0040 cores witness0040 code0040
    code0040_correct (by decide +kernel)
#print axioms coverage0040

theorem selected0040 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0040, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0040 cores
    template0040 witness0040 coverage0040 s hs hb
#print axioms selected0040
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0041 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.1.val < 2 then (if x.2 then 3 else 1) else (if x.2 then 2 else 5)))) (by decide +kernel)
noncomputable def code0041 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 4 else 20)) else (if m.val < 6 then (if m.val < 5 then 3 else 19) else (if m.val < 7 then 7 else 23))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 12 else 28) else (if m.val < 11 then 8 else 24)) else (if m.val < 14 then (if m.val < 13 then 15 else 31) else (if m.val < 15 then 11 else 27)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 48 else 32) else (if m.val < 19 then 52 else 36)) else (if m.val < 22 then (if m.val < 21 then 51 else 35) else (if m.val < 23 then 55 else 39))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 60 else 44) else (if m.val < 27 then 56 else 40)) else (if m.val < 30 then (if m.val < 29 then 63 else 47) else (if m.val < 31 then 59 else 43))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 1 else 17) else (if m.val < 35 then 5 else 21)) else (if m.val < 38 then (if m.val < 37 then 2 else 18) else (if m.val < 39 then 6 else 22))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 13 else 29) else (if m.val < 43 then 9 else 25)) else (if m.val < 46 then (if m.val < 45 then 14 else 30) else (if m.val < 47 then 10 else 26)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 49 else 33) else (if m.val < 51 then 53 else 37)) else (if m.val < 54 then (if m.val < 53 then 50 else 34) else (if m.val < 55 then 54 else 38))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 61 else 45) else (if m.val < 59 then 57 else 41)) else (if m.val < 62 then (if m.val < 61 then 62 else 46) else (if m.val < 63 then 58 else 42))))))
theorem code0041_correct : ∀ m, Crown.ThreeClosure.rows (code0041 m) =
    rowOfMask (pairsOfEquiv pairing0041) (maskBits m) := by decide +kernel
theorem coverage0041 : ∀ c, witness0041 c ∈ template0041 ∧
    ∀ m ∈ cores (witness0041 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0041) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0041 cores witness0041 code0041
    code0041_correct (by decide +kernel)
#print axioms coverage0041

theorem selected0041 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0041, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0041 cores
    template0041 witness0041 coverage0041 s hs hb
#print axioms selected0041
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0042 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 3) else (if x.2 then 5 else 2)))) (by decide +kernel)
noncomputable def code0042 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 1 else 17) else (if m.val < 7 then 13 else 29))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 4 else 20) else (if m.val < 11 then 8 else 24)) else (if m.val < 14 then (if m.val < 13 then 5 else 21) else (if m.val < 15 then 9 else 25)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 48 else 32) else (if m.val < 19 then 60 else 44)) else (if m.val < 22 then (if m.val < 21 then 49 else 33) else (if m.val < 23 then 61 else 45))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 52 else 36) else (if m.val < 27 then 56 else 40)) else (if m.val < 30 then (if m.val < 29 then 53 else 37) else (if m.val < 31 then 57 else 41))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 3 else 19) else (if m.val < 35 then 15 else 31)) else (if m.val < 38 then (if m.val < 37 then 2 else 18) else (if m.val < 39 then 14 else 30))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 7 else 23) else (if m.val < 43 then 11 else 27)) else (if m.val < 46 then (if m.val < 45 then 6 else 22) else (if m.val < 47 then 10 else 26)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 51 else 35) else (if m.val < 51 then 63 else 47)) else (if m.val < 54 then (if m.val < 53 then 50 else 34) else (if m.val < 55 then 62 else 46))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 55 else 39) else (if m.val < 59 then 59 else 43)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0042_correct : ∀ m, Crown.ThreeClosure.rows (code0042 m) =
    rowOfMask (pairsOfEquiv pairing0042) (maskBits m) := by decide +kernel
theorem coverage0042 : ∀ c, witness0042 c ∈ template0042 ∧
    ∀ m ∈ cores (witness0042 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0042) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0042 cores witness0042 code0042
    code0042_correct (by decide +kernel)
#print axioms coverage0042

theorem selected0042 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0042, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0042 cores
    template0042 witness0042 coverage0042 s hs hb
#print axioms selected0042
end Crown.CertificateSixData
namespace Crown.CertificateSixData
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable def pairing0043 : Pairing6 :=
  Equiv.ofBijective (fun x => (if x.1.val < 1 then (if x.2 then 4 else 0) else (if x.1.val < 2 then (if x.2 then 1 else 3) else (if x.2 then 2 else 5)))) (by decide +kernel)
noncomputable def code0043 (m : Fin 64) : Fin 64 :=
  (if m.val < 32 then (if m.val < 16 then (if m.val < 8 then (if m.val < 4 then (if m.val < 2 then (if m.val < 1 then 0 else 16) else (if m.val < 3 then 12 else 28)) else (if m.val < 6 then (if m.val < 5 then 3 else 19) else (if m.val < 7 then 15 else 31))) else (if m.val < 12 then (if m.val < 10 then (if m.val < 9 then 4 else 20) else (if m.val < 11 then 8 else 24)) else (if m.val < 14 then (if m.val < 13 then 7 else 23) else (if m.val < 15 then 11 else 27)))) else (if m.val < 24 then (if m.val < 20 then (if m.val < 18 then (if m.val < 17 then 48 else 32) else (if m.val < 19 then 60 else 44)) else (if m.val < 22 then (if m.val < 21 then 51 else 35) else (if m.val < 23 then 63 else 47))) else (if m.val < 28 then (if m.val < 26 then (if m.val < 25 then 52 else 36) else (if m.val < 27 then 56 else 40)) else (if m.val < 30 then (if m.val < 29 then 55 else 39) else (if m.val < 31 then 59 else 43))))) else (if m.val < 48 then (if m.val < 40 then (if m.val < 36 then (if m.val < 34 then (if m.val < 33 then 1 else 17) else (if m.val < 35 then 13 else 29)) else (if m.val < 38 then (if m.val < 37 then 2 else 18) else (if m.val < 39 then 14 else 30))) else (if m.val < 44 then (if m.val < 42 then (if m.val < 41 then 5 else 21) else (if m.val < 43 then 9 else 25)) else (if m.val < 46 then (if m.val < 45 then 6 else 22) else (if m.val < 47 then 10 else 26)))) else (if m.val < 56 then (if m.val < 52 then (if m.val < 50 then (if m.val < 49 then 49 else 33) else (if m.val < 51 then 61 else 45)) else (if m.val < 54 then (if m.val < 53 then 50 else 34) else (if m.val < 55 then 62 else 46))) else (if m.val < 60 then (if m.val < 58 then (if m.val < 57 then 53 else 37) else (if m.val < 59 then 57 else 41)) else (if m.val < 62 then (if m.val < 61 then 54 else 38) else (if m.val < 63 then 58 else 42))))))
theorem code0043_correct : ∀ m, Crown.ThreeClosure.rows (code0043 m) =
    rowOfMask (pairsOfEquiv pairing0043) (maskBits m) := by decide +kernel
theorem coverage0043 : ∀ c, witness0043 c ∈ template0043 ∧
    ∀ m ∈ cores (witness0043 c), ∃ x ∈ Crown.ThreeClosure.core c,
      Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv pairing0043) (maskBits m) :=
  Crown.ThreeClosureTransport.coverage_of_check Crown.ThreeClosure.rows
    Crown.ThreeClosure.core pairing0043 cores witness0043 code0043
    code0043_correct (by decide +kernel)
#print axioms coverage0043

theorem selected0043 (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template0043, ∀ m ∈ cores c, s m = true :=
  Crown.SixCatalogueSelection.selected_of_coverage pairing0043 cores
    template0043 witness0043 coverage0043 s hs hb
#print axioms selected0043
end Crown.CertificateSixData
