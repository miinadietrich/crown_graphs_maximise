import generated.ThreeClosureFast
import generated.ThreeClosureRelations
import Crown.ThreeClosureTransport

namespace Crown.SixCatalogueSelection
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics

theorem selected_of_coverage {g : ℕ} (p : Pairing6)
    (cores : Fin g → List (Fin 64)) (template : List (Fin g))
    (witness : Fin 759 → Fin g)
    (hcover : ∀ c, witness c ∈ template ∧ ∀ m ∈ cores (witness c),
      ∃ x ∈ Crown.ThreeClosure.core c,
        Crown.ThreeClosure.rows x = rowOfMask (pairsOfEquiv p) (maskBits m))
    (s : Fin 64 → Bool) (hs : Fintype.card {m // s m = true} ≤ 6)
    (hb : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ c ∈ template, ∀ m ∈ cores c, s m = true := by
  classical
  let t : Finset (Fin 64) := Finset.univ.filter (fun m => s m = true)
  have ht : t.card ≤ 6 := by simpa [t,Fintype.card_subtype] using hs
  have hbad : ¬ Feasible (fun m : {m // m ∈ t} =>
      rowOfMask (pairsOfEquiv p) (maskBits m.val)) := by
    rintro ⟨r,hr,hn⟩
    apply hb p
    let f : {m // s m = true} → {m // m ∈ t} :=
      fun m => ⟨m.val, by simpa [t] using m.property⟩
    exact ⟨fun m => r (f m), fun m => hr (f m), fun m n => hn (f m) (f n)⟩
  obtain ⟨c,hc,h⟩ := Crown.ThreeClosureTransport.selected_core
    Crown.ThreeClosure.rows Crown.ThreeClosure.rows_bijective
    Crown.ThreeClosure.owner Crown.ThreeClosure.support Crown.ThreeClosure.core
    Crown.ThreeClosure.certificate p cores template witness hcover t ht hbad
  exact ⟨c,hc,fun m hm => by simpa [t] using h m hm⟩

#print axioms selected_of_coverage
end Crown.SixCatalogueSelection
