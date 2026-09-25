import Crown.Definitions

/-! Full bipartitions, including isolated vertices, and the crown's bipartiteness.
Mathlib's IsBipartiteWith permits uncovered isolated vertices; the coverage
condition in this module is therefore explicit. -/

namespace Crown

theorem exists_covering_bipartition {V : Type*} (G : SimpleGraph V)
    (h : G.IsBipartite) :
    ∃ A B : Set V, G.IsBipartiteWith A B ∧ A ∪ B = Set.univ := by
  obtain ⟨c, hc⟩ := h
  refine ⟨{v | c v = 0}, {v | c v = 1}, ?_, ?_⟩
  · constructor
    · apply Set.disjoint_left.mpr
      intro v hv hw
      change c v = 0 at hv
      change c v = 1 at hw
      omega
    · intro v w hvw
      have hn := hc hvw
      change c v ≠ c w at hn
      change (c v = 0 ∧ c w = 1) ∨ (c v = 1 ∧ c w = 0)
      omega
  · ext v
    change (c v = 0 ∨ c v = 1) ↔ True
    constructor
    · intro _; trivial
    · intro _; omega

theorem crown_isBipartite (n : ℕ) : (crownGraph n).IsBipartite := by
  refine ⟨fun v => if v.1 then (1 : Fin 2) else 0, ?_⟩
  intro a b hab
  have hside : a.1 ≠ b.1 := hab.1
  cases ha : a.1 <;> cases hb : b.1 <;> simp_all

theorem crown_card (n : ℕ) : Fintype.card (Bool × Fin n) = 2 * n := by simp

#print axioms exists_covering_bipartition
#print axioms crown_isBipartite

end Crown
