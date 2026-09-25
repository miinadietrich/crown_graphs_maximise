import Crown.Definitions
import Specification.BlockDefinitions
import Specification.OrientationDefinitions

/-! Challenge-only definitions. These preserve original names in a separate
environment and must never be imported by solution modules. No solved theorem
is imported here. Literal source provenance is listed below each definition. -/

namespace Crown.BalancedLarge

variable {k : ℕ} {B : Type*}

def bit (p : Bool × Bool) (side : Bool) : Bool := if side then p.2 else p.1

def rawGraph (N : B → Orientations.NeighbourRow (Fin k)) :
    SimpleGraph (Blocks.Alphabet k B) where
  Adj a b := match a, b with
    | Sum.inl p, Sum.inr b => bit (N b p.1) p.2 = true
    | Sum.inr b, Sum.inl p => bit (N b p.1) p.2 = true
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> exact id⟩
  loopless := ⟨by intro a; cases a <;> simp⟩



def matrixGraph {A B : Type*} (M : A → B → Bool) : SimpleGraph (A ⊕ B) where
  Adj a b := match a, b with
    | Sum.inl a, Sum.inr b => M a b = true
    | Sum.inr b, Sum.inl a => M a b = true
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> exact id⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

end Crown.BalancedLarge
