import Specification.RankDetailDefinitions

namespace Crown.RankExample
open Crown.Ranks

-- Statement copied from Crown/RankExample.lean
theorem example_obstruction :
    ¬ StrictBelow (complete (exampleRows 0) false) (complete (exampleRows 2) false) ∧
    ¬ StrictBelow (complete (exampleRows 2) false) (complete (exampleRows 0) false) ∧
    StrictBelow (complete (exampleRows 1) false) (complete (exampleRows 2) false) ∧
    StrictBelow (complete (exampleRows 0) false) (complete (exampleRows 1) true) ∧
    ¬ Feasible exampleRows := by
  sorry

end Crown.RankExample

namespace Crown.RankLocalDetails
open Crown.Blocks
variable {k : ℕ} {B : Type*} [DecidableEq B]

local instance : BEq (Alphabet k B) := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq (Alphabet k B) where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

-- Statement copied from Crown/RankLocalDetails.lean
theorem restrict_block_three (r : B → Ranks.CompletedRow (Fin k))
    (π : Fin k → List B) (i : Fin k) (b : B) (hb : (π i).count b = 1) :
    restrictTriple (block r π i) i b = localTriple (r b i) i b := by
  sorry

-- Statement copied from Crown/RankLocalDetails.lean
theorem strict_forces_order (r : B → Ranks.CompletedRow (Fin k))
    (π : Fin k → List B) (hπ : ∀ i b, b ∈ π i)
    (hm : ∀ i b c, Orders.Before (π i) b c → r b i ≤ r c i)
    (a b : B) (h : Ranks.StrictBelow (r a) (r b)) :
    ∀ i, Orders.Before (π i) a b := by
  sorry

-- Statement copied from Crown/RankLocalDetails.lean
theorem permutations_alternates_iff (π : Fin k → List B)
    (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i) (a b : B) (hab : a ≠ b) :
    Crown.Alternates ((List.finRange k).flatMap π) a b ↔
      (∀ i, Orders.Before (π i) a b) ∨ (∀ i, Orders.Before (π i) b a) := by
  sorry

end Crown.RankLocalDetails
