import Mathlib.Data.List.GetD

namespace Crown.SmallGraphs

/-- A finite lookup tree whose branch stores the number of entries on its left. -/
inductive LookupTree (α : Type*) where
  | leaf : α → LookupTree α
  | node : Nat → LookupTree α → LookupTree α → LookupTree α
  deriving DecidableEq

namespace LookupTree

def toList : LookupTree α → List α
  | leaf a => [a]
  | node _ l r => l.toList ++ r.toList

def getD : LookupTree α → Nat → α → α
  | leaf a, i, d => if i = 0 then a else d
  | node n l r, i, d => if i < n then l.getD i d else r.getD (i-n) d

def Valid : LookupTree α → Prop
  | leaf _ => True
  | node n l r => n = l.toList.length ∧ l.Valid ∧ r.Valid

def validDecidable : (t : LookupTree α) → Decidable t.Valid
  | leaf _ => isTrue trivial
  | node n l r => by
    letI := validDecidable l
    letI := validDecidable r
    unfold Valid
    infer_instance

instance (t : LookupTree α) : Decidable t.Valid := validDecidable t
theorem getD_eq (t : LookupTree α) (hv : t.Valid) (i : Nat) (d : α) :
    t.getD i d = t.toList.getD i d := by
  induction t generalizing i with
  | leaf a => cases i <;> simp [getD,toList]
  | node n l r ihl ihr =>
    obtain ⟨hn,hl,hr⟩ := hv
    subst n
    by_cases hi : i < l.toList.length
    · simp only [getD,hi,if_pos,toList]
      rw [List.getD_append _ _ _ _ hi]
      exact ihl hl i
    · simp only [getD,hi,if_neg,toList]
      rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hi)]
      exact ihr hr (i-l.toList.length)

#print axioms getD_eq
end LookupTree
end Crown.SmallGraphs
