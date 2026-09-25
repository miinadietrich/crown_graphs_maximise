import Specification.BlockDefinitions
import Mathlib.Data.Fin.VecNotation

/-! Challenge-only literal L03/L14 definitions; no solution imports. -/

namespace Crown.RankExample
open Crown.Ranks

-- Literal definition from Crown/RankExample.lean
def exampleRows : Fin 3 → InitialRow (Fin 4) :=
  ![ ![some 1, some 0, some 0, some 0],
     ![none, some 1, some 1, some 1],
     ![some 0, some 2, some 2, some 2] ]

end Crown.RankExample

namespace Crown.RankLocalDetails
open Crown.Blocks
variable {k : ℕ} {B : Type*} [DecidableEq B]

-- Literal definition from Crown/RankLocalDetails.lean
def restrictTriple (w : List (Alphabet k B)) (i : Fin k) (b : B) : List (Alphabet k B) :=
  w.filter fun a => a = x i ∨ a = y i ∨ a = Sum.inr b

-- Literal definition from Crown/RankLocalDetails.lean
def localTriple (q : Fin 5) (i : Fin k) (b : B) : List (Alphabet k B) :=
  match q.val with
  | 0 => [Sum.inr b, x i, y i, x i, y i]
  | 1 => [x i, Sum.inr b, y i, x i, y i]
  | 2 => [x i, y i, Sum.inr b, x i, y i]
  | 3 => [x i, y i, x i, Sum.inr b, y i]
  | _ => [x i, y i, x i, y i, Sum.inr b]

end Crown.RankLocalDetails
