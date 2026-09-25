import generated.CatalogueConverse
import generated.CatalogueExact
import Crown.SelectedCoreSoundness
import Crown.ObstructionEncoding

/-! Both directions of the concrete obstruction encoding. These arguments use
catalogue completeness and soundness, independently of the SAT refutation. -/
namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics Crown.PairingCoverage

theorem all_templates_selected_iff (s : Fin 256 → Bool) :
    (∀ t, ∃ c ∈ templates t, ∀ m ∈ cores c, s m = true) ↔
      AllPairingsBad (fun m : {m // s m = true} => m.val) := by
  constructor
  · intro h
    have ht : ∀ t, ¬ Feasible (rankRows (Crown.PairingStored4.stored t)
        (fun m : {m // s m = true} => maskBits m.val)) := by
      intro t
      change ¬ Feasible (fun m : {m // s m = true} =>
        rankRows (pairings t) maskBits m.val)
      rw [← pairingRows_eq_rankRows]
      obtain ⟨c,hc,hs⟩ := h t
      exact selected_core_infeasible (pairingRows (pairings t)) s (cores c) hs
        (all_template_cores_minimal t c hc).1
    have ha := (Crown.PairingStored4.all_bad_iff
      (fun m : {m // s m = true} => maskBits m.val)).mpr ht
    intro p hp
    apply ha p
    change Feasible (fun m : {m // s m = true} => rankRows p maskBits m.val)
    rw [← pairingRows_eq_rankRows]
    exact hp
  · exact all_templates_selected s

#print axioms all_templates_selected_iff
end Crown.CertificateData

namespace Crown.ObstructionEncoding
open Crown.CertificateSemantics Crown.CertificateData

theorem encoding_iff_actual_obstruction (cap : ℕ) (s : Fin 256 → Bool) :
    (∃ c, Encoding cores templates cap s c) ↔
      Fintype.card {m // s m = true} ≤ cap ∧
        AllPairingsBad (fun m : {m // s m = true} => m.val) := by
  rw [encoding_iff,all_templates_selected_iff]

theorem satisfiable_iff_actual_obstruction (cap : ℕ) :
    (∃ s c, Encoding cores templates cap s c) ↔
      ∃ s : Fin 256 → Bool, Fintype.card {m // s m = true} ≤ cap ∧
        AllPairingsBad (fun m : {m // s m = true} => m.val) := by
  exact exists_congr (fun s => encoding_iff_actual_obstruction cap s)

#print axioms encoding_iff_actual_obstruction
#print axioms satisfiable_iff_actual_obstruction
end Crown.ObstructionEncoding
