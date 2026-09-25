import Crown.Definitions
import Mathlib.Combinatorics.SimpleGraph.Sum

namespace Crown
section Words
variable {V : Type*} [DecidableEq V]
def restrictVertices (p : V → Prop) [DecidablePred p] (w : List V) : List {v // p v} :=
  w.filterMap fun v => if h : p v then some ⟨v, h⟩ else none

theorem uniform_length [Fintype V] {k : ℕ} {w : List V}
    (h : Uniform k w) : w.length = Fintype.card V * k := by
  sorry

theorem represents_equiv {W : Type*} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (he : ∀ a b, H.Adj (e a) (e b) ↔ G.Adj a b)
    {k : ℕ} {w : List V} (h : Represents G k w) :
    Represents H k (w.map e) := by
  sorry

theorem represents_induce {G : SimpleGraph V} {k : ℕ} {w : List V}
    (h : Represents G k w) (p : V → Prop) [DecidablePred p] :
    Represents (G.induce {v | p v}) k (restrictVertices p w) := by
  sorry

theorem kRepresentable_induce {G : SimpleGraph V} {k : ℕ}
    (h : KRepresentable G k) (p : V → Prop) [DecidablePred p] :
    KRepresentable (G.induce {v | p v}) k := by
  sorry

theorem minimum_uniform_length [Fintype V] {G : SimpleGraph V}
    (hr : Representable G) :
    ∃ w, Represents G (representationNumber G) w ∧
      w.length = Fintype.card V * representationNumber G ∧
      ∀ k u, Represents G k u → w.length ≤ u.length := by
  sorry

theorem balanced_chain_endpoints (a b : V) (hab : a ≠ b) (w : List V)
    (hm : ∀ x ∈ w, x = a ∨ x = b) (he : w.count a = w.count b)
    (hc : w.IsChain (· ≠ ·)) :
    ∀ x ∈ w.head?, ∀ y ∈ w.getLast?, x ≠ y := by
  sorry

theorem alternates_append_swap {u v : List V} {a b : V} (hab : a ≠ b)
    (he : (u ++ v).count a = (u ++ v).count b) :
    Alternates (u ++ v) a b ↔ Alternates (v ++ u) a b := by
  sorry

theorem represents_append_swap {G : SimpleGraph V} {k : ℕ} {u v : List V}
    (h : Represents G k (u ++ v)) : Represents G k (v ++ u) := by
  sorry

end Words

section Components
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

theorem represents_sum_two {G : SimpleGraph V} {H : SimpleGraph W}
    {u : List V} {v : List W} (hu : Represents G 2 u) (hv : Represents H 2 v) :
    Represents (G.sum H) 2 (u.map Sum.inl ++ v.map Sum.inr) := by
  sorry

theorem represents_complete_twice (l : List V) (hl : l.Nodup) (hall : ∀ a, a ∈ l) :
    Represents (⊤ : SimpleGraph V) 2 (l ++ l) := by
  sorry

end Components
end Crown
