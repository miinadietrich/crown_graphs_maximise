import Crown.CertificateExactCatalogue

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

/-- A feasible selected family makes every contained set of rank rows feasible.
Repeated masks and repeated rows do not affect the implication. -/
theorem rowSetFeasible_of_selected (rows : Fin 256 → RankRow)
    (s : Fin 256 → Bool) (core : List (Fin 256))
    (hcore : ∀ m ∈ core, s m = true)
    (h : Feasible (fun m : {m // s m = true} => rows m.val)) :
    rowSetFeasible {r | r ∈ core.map rows} := by
  classical
  obtain ⟨r,hr,hn⟩ := h
  have hex : ∀ x : {r | r ∈ core.map rows},
      ∃ m : {m // s m = true}, rows m.val = x.val := by
    intro x
    obtain ⟨m,hm,he⟩ := List.mem_map.mp x.property
    exact ⟨⟨m,hcore m hm⟩,he⟩
  let f := fun x => Classical.choose (hex x)
  have hf := fun x => Classical.choose_spec (hex x)
  refine ⟨fun x => r (f x),?_,fun x y => hn (f x) (f y)⟩
  intro x
  have hh := hr (f x)
  change Completes (rows (f x).val) (r (f x)) at hh
  rw [hf x] at hh
  exact hh

theorem selected_core_infeasible (rows : Fin 256 → RankRow)
    (s : Fin 256 → Bool) (core : List (Fin 256))
    (hcore : ∀ m ∈ core, s m = true)
    (hbad : ¬ rowSetFeasible {r | r ∈ core.map rows}) :
    ¬ Feasible (fun m : {m // s m = true} => rows m.val) :=
  fun h => hbad (rowSetFeasible_of_selected rows s core hcore h)

/-- Exact catalogue completeness and soundness give both directions of the
selected-core condition for an individual pairing. -/
theorem selected_core_iff (rows : Fin 256 → RankRow) (hinj : Function.Injective rows)
    (s : Fin 256 → Bool) (cores : Fin 4935 → List (Fin 256))
    (template : List (Fin 4935)) (witness : Pattern → Fin 4935)
    (hcov : Coverage rows cores template witness)
    (hbad : ∀ c ∈ template, ¬ rowSetFeasible {r | r ∈ (cores c).map rows}) :
    (∃ c ∈ template, ∀ m ∈ cores c, s m = true) ↔
      ¬ Feasible (fun m : {m // s m = true} => rows m.val) := by
  constructor
  · rintro ⟨c,hc,hs⟩
    exact selected_core_infeasible rows s (cores c) hs (hbad c hc)
  · exact selected_core_of_coverage rows hinj s cores template witness hcov

#print axioms rowSetFeasible_of_selected
#print axioms selected_core_infeasible
#print axioms selected_core_iff
end Crown.CertificateData
