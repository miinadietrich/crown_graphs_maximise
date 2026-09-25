import Specification.CatalogueDefinitions

namespace Crown.CertificateData
open Crown.CertificateSemantics

theorem catalogueUnion_iff_minimal (M : Finset (Fin 256)) :
    M ∈ catalogueUnion ↔ ∃ p : Pairing8, MinimalMaskFamily (pairingRows p) M := by
  sorry

theorem minimal_obstruction_union_count :
    Nat.card {M : Finset (Fin 256) //
      ∃ p : Pairing8, MinimalMaskFamily (pairingRows p) M} = 4935 := by
  sorry

theorem minimal_obstruction_pair_count :
    Nat.card {M : Finset (Fin 256) //
      (∃ p : Pairing8, MinimalMaskFamily (pairingRows p) M) ∧ M.card = 2} = 2415 := by
  sorry

theorem minimal_obstruction_triple_count :
    Nat.card {M : Finset (Fin 256) //
      (∃ p : Pairing8, MinimalMaskFamily (pairingRows p) M) ∧ M.card = 3} = 2520 := by
  sorry

theorem all_templates_selected_iff (s : Fin 256 → Bool) :
    (∀ t, ∃ c ∈ templates t, ∀ m ∈ cores c, s m = true) ↔
      AllPairingsBad (fun m : {m // s m = true} => m.val) := by
  sorry

end Crown.CertificateData

namespace Crown.ObstructionEncoding
open Crown.CertificateSemantics Crown.CertificateData

theorem encoding_iff_actual_obstruction (cap : ℕ) (s : Fin 256 → Bool) :
    (∃ c, Encoding cores templates cap s c) ↔
      Fintype.card {m // s m = true} ≤ cap ∧
        AllPairingsBad (fun m : {m // s m = true} => m.val) := by
  sorry

theorem satisfiable_iff_actual_obstruction (cap : ℕ) :
    (∃ s c, Encoding cores templates cap s c) ↔
      ∃ s : Fin 256 → Bool, Fintype.card {m // s m = true} ≤ cap ∧
        AllPairingsBad (fun m : {m // s m = true} => m.val) := by
  sorry

end Crown.ObstructionEncoding
