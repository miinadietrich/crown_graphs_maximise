import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Crown.BalancedLarge

variable {k : ℕ} {B : Type*}

/-- A bipartite graph with arbitrary Boolean adjacency matrix. -/
def matrixGraph {A B : Type*} (M : A → B → Bool) : SimpleGraph (A ⊕ B) where
  Adj a b := match a, b with
    | Sum.inl a, Sum.inr b => M a b = true
    | Sum.inr b, Sum.inl a => M a b = true
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> exact id⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

end Crown.BalancedLarge
