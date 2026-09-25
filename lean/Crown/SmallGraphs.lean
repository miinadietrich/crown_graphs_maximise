import Crown.SmallGraphsSix

/-! H08: the supporting classification on at most six vertices. The manuscript
cites Akgün, Gent, Kitaev and Zantema, J. Integer Seq. 22 (2019),
Article 19.2.5, Section 2, Table 1. The proof here independently checks
all labelled graphs and derives both obstructions from actual words.
Statements
use actual two-uniform representatives. The representation-number formulation
assumes representability, so its default zero cannot classify a nonrepresentable
graph as having a short representative. -/

namespace Crown.SmallGraphs

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem classify_at_most_six (G : SimpleGraph V) (hc : Fintype.card V ≤ 6) :
    Crown.KRepresentable G 2 ∨ Nonempty (prism ≃g G) ∨ Nonempty (wheel ≃g G) := by
  classical
  by_cases h5 : Fintype.card V ≤ 5
  · exact Or.inl (at_most_five G h5)
  have h6 : Fintype.card V = 6 := by omega
  let e : V ≃ Fin 6 := Fintype.equivFinOfCardEq h6
  let H := G.comap e.symm
  let eg : H ≃g G := { toEquiv := e.symm, map_rel_iff' := by intro a b; rfl }
  rcases classify_six H with h | he
  · exact Or.inl (representable_iso eg h)
  · rcases he with hp | hw
    · obtain ⟨ep⟩ := hp
      exact Or.inr (Or.inl ⟨ep.trans eg⟩)
    · obtain ⟨ew⟩ := hw
      exact Or.inr (Or.inr ⟨ew.trans eg⟩)

theorem at_most_six_iff (G : SimpleGraph V) (hc : Fintype.card V ≤ 6) :
    Crown.KRepresentable G 2 ↔ ¬Nonempty (prism ≃g G) ∧ ¬Nonempty (wheel ≃g G) := by
  constructor
  · intro h
    constructor
    · rintro ⟨e⟩; exact prism_not_two (representable_iso e.symm h)
    · rintro ⟨e⟩; exact wheel_not_two (representable_iso e.symm h)
  · intro h
    rcases classify_at_most_six G hc with hp | hp | hw
    · exact hp
    · exact False.elim (h.1 hp)
    · exact False.elim (h.2 hw)

theorem number_at_most_six_iff (G : SimpleGraph V) (hc : Fintype.card V ≤ 6)
    (hr : Crown.Representable G) :
    Crown.representationNumber G ≤ 2 ↔
      ¬Nonempty (prism ≃g G) ∧ ¬Nonempty (wheel ≃g G) := by
  rw [number_le_two_iff hr,at_most_six_iff G hc]

theorem triangle_not_bipartite (G : SimpleGraph (Fin 6))
    (h01 : G.Adj 0 1) (h02 : G.Adj 0 2) (h12 : G.Adj 1 2) : ¬G.IsBipartite := by
  rintro ⟨c,hc⟩
  have h1 := hc h01
  have h2 := hc h02
  have h3 := hc h12
  have hb0 := (c 0).isLt
  have hb1 := (c 1).isLt
  have hb2 := (c 2).isLt
  change c 0 ≠ c 1 at h1
  change c 0 ≠ c 2 at h2
  change c 1 ≠ c 2 at h3
  have hv01 : (c 0).val ≠ (c 1).val := fun he => h1 (Fin.ext he)
  have hv02 : (c 0).val ≠ (c 2).val := fun he => h2 (Fin.ext he)
  have hv12 : (c 1).val ≠ (c 2).val := fun he => h3 (Fin.ext he)
  omega

theorem prism_not_bipartite : ¬prism.IsBipartite :=
  triangle_not_bipartite prism (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem wheel_not_bipartite : ¬wheel.IsBipartite :=
  triangle_not_bipartite wheel (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms classify_at_most_six
#print axioms at_most_six_iff
#print axioms number_at_most_six_iff
#print axioms prism_not_bipartite
#print axioms wheel_not_bipartite
end Crown.SmallGraphs
