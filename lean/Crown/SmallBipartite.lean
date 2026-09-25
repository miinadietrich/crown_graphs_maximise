import Crown.SmallBipartiteData
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Crown.SmallBipartite

def crossGraph {A B : Type*} (edge : A → B → Bool) : SimpleGraph (A ⊕ B) where
  Adj
    | .inl a, .inr b => edge a b = true
    | .inr b, .inl a => edge a b = true
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> simp⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

instance {A B : Type*} (edge : A → B → Bool) : DecidableRel (crossGraph edge).Adj :=
  fun a b => by cases a <;> cases b <;> dsimp [crossGraph] <;> infer_instance

def edgeIndex (m : ℕ) (edge : Fin m → Fin (6-m) → Bool) : ℕ :=
  ∑ a : Fin m, ∑ b : Fin (6-m), if edge a b then 2 ^ (a.val * (6-m) + b.val) else 0

def decodeVertex (m : ℕ) (hm : m ≤ 6) (v : Fin 6) : Fin m ⊕ Fin (6-m) :=
  if h : v.val < m then .inl ⟨v.val, h⟩ else .inr ⟨v.val - m, by omega⟩

def candidate (m : ℕ) (hm : m ≤ 6) (table : Array (List (Fin 6)))
    (edge : Fin m → Fin (6-m) → Bool) : List (Fin m ⊕ Fin (6-m)) :=
  (table.getD (edgeIndex m edge) []).map (decodeVertex m hm)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem all_zero_six : ∀ edge : Fin 0 → Fin 6 → Bool,
    Represents (crossGraph edge) 2 (candidate 0 (by decide) words0 edge) := by
  unfold Represents Uniform Alternates restrictPair
  decide

theorem all_one_five : ∀ edge : Fin 1 → Fin 5 → Bool,
    Represents (crossGraph edge) 2 (candidate 1 (by decide) words1 edge) := by
  unfold Represents Uniform Alternates restrictPair
  decide

theorem all_two_four : ∀ edge : Fin 2 → Fin 4 → Bool,
    Represents (crossGraph edge) 2 (candidate 2 (by decide) words2 edge) := by
  unfold Represents Uniform Alternates restrictPair
  decide

theorem all_three_three : ∀ edge : Fin 3 → Fin 3 → Bool,
    Represents (crossGraph edge) 2 (candidate 3 (by decide) words3 edge) := by
  unfold Represents Uniform Alternates restrictPair
  decide

#print axioms all_zero_six
#print axioms all_one_five
#print axioms all_two_four
#print axioms all_three_three

end Crown.SmallBipartite
