import Crown.CertificateSemantics

namespace Crown.CertificateData

open Crown.Ranks Crown.CertificateSemantics

abbrev Pattern := (Fin 4 → Fin 3) ⊕ (Fin 4 × Fin 6)

def patternRows : Pattern → List (InitialRow (Fin 4))
  | .inl t => [pairLower t, pairUpper t]
  | .inr (j, t) => [tripleLower j (decreasingRanks t).1,
      tripleCenter j, tripleUpper j (decreasingRanks t).2]

theorem selected_pattern_of_bad (rows : Fin 256 → InitialRow (Fin 4))
    (s : Fin 256 → Bool)
    (h : ¬ Feasible (fun m : {m // s m = true} => rows m.val)) :
    ∃ q : Pattern, ∀ r ∈ patternRows q, ∃ m, s m = true ∧ rows m = r := by
  rcases (selected_infeasible_iff rows s).mp h with
    ⟨l, u, hl, hu, t, el, eu⟩ | ⟨l, c, u, hl, hc, hu, j, t, el, ec, eu⟩
  · refine ⟨.inl t, ?_⟩
    intro r hr
    simp only [patternRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨l, hl, el⟩
    · exact ⟨u, hu, eu⟩
  · refine ⟨.inr (j, t), ?_⟩
    intro r hr
    simp only [patternRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨l, hl, el⟩
    · exact ⟨c, hc, ec⟩
    · exact ⟨u, hu, eu⟩

def Coverage (rows : Fin 256 → InitialRow (Fin 4))
    (cores : Fin 4935 → List (Fin 256)) (template : List (Fin 4935))
    (witness : Pattern → Fin 4935) : Prop :=
  ∀ q, witness q ∈ template ∧
    ∀ m ∈ cores (witness q), rows m ∈ patternRows q

theorem selected_core_of_coverage (rows : Fin 256 → InitialRow (Fin 4))
    (hinj : Function.Injective rows) (s : Fin 256 → Bool)
    (cores : Fin 4935 → List (Fin 256)) (template : List (Fin 4935))
    (witness : Pattern → Fin 4935) (hcov : Coverage rows cores template witness)
    (hbad : ¬ Feasible (fun m : {m // s m = true} => rows m.val)) :
    ∃ c ∈ template, ∀ m ∈ cores c, s m = true := by
  obtain ⟨q, hq⟩ := selected_pattern_of_bad rows s hbad
  refine ⟨witness q, (hcov q).1, ?_⟩
  intro m hm
  obtain ⟨n, hn, he⟩ := hq (rows m) ((hcov q).2 m hm)
  simpa only [hinj he] using hn

#print axioms selected_pattern_of_bad
#print axioms selected_core_of_coverage

end Crown.CertificateData
