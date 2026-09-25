import Crown.Definitions
import Specification.OrderDefinitions
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.List.FinRange

/-! Challenge-only definitions. These preserve original names in a separate
environment and must never be imported by solution modules. No solved theorem
is imported here. Literal source provenance is listed below each definition. -/

namespace Crown.Blocks
variable {k : ℕ} {B : Type*} [DecidableEq B]

abbrev Alphabet (k : ℕ) (B : Type*) := Sum (Fin k × Bool) B

-- Use the equality test chosen by `Crown.Uniform`, including on the sum type.

def x (i : Fin k) : Alphabet k B := Sum.inl (i, false)

def y (i : Fin k) : Alphabet k B := Sum.inl (i, true)

def gap (rank : B → Fin 5) (π : List B) (j : Fin 5) : List (Alphabet k B) :=
  (π.filter fun b => rank b = j).map Sum.inr

def block (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B) (i : Fin k) :
    List (Alphabet k B) :=
  gap (fun b => r b i) (π i) 0 ++ [x i] ++
  gap (fun b => r b i) (π i) 1 ++ [y i] ++
  gap (fun b => r b i) (π i) 2 ++ [x i] ++
  gap (fun b => r b i) (π i) 3 ++ [y i] ++
  gap (fun b => r b i) (π i) 4

def retained (i : Fin k) : List (Fin k) :=
  (List.finRange k).filter fun j => j ≠ i ∧ j ≠ finRotate k i

def separator (i : Fin k) : List (Alphabet k B) :=
  (retained i).map y ++ (retained i).map x

def word (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B) :
    List (Alphabet k B) :=
  (List.finRange k).flatMap fun i => block r π i ++ separator i

def RankAdjacent (q : Fin 5) (side : Bool) : Prop :=
  if side then q = 2 ∨ q = 3 else q = 1 ∨ q = 2

def beforeCount (q : Fin 5) (side : Bool) : ℕ :=
  (q.val + if side then 0 else 1) / 2

def crossLocal (q : Fin 5) (side : Bool) (a b : Alphabet k B) : List (Alphabet k B) :=
  List.replicate (beforeCount q side) a ++ [b] ++
    List.replicate (2 - beforeCount q side) a

def rankGraph (r : B → Ranks.CompletedRow (Fin k)) : SimpleGraph (Alphabet k B) where
  Adj a b := match a, b with
    | Sum.inl p, Sum.inr b => RankAdjacent (r b p.1) p.2
    | Sum.inr b, Sum.inl p => RankAdjacent (r b p.1) p.2
    | _, _ => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

def initialRankGraph (rows : B → Ranks.InitialRow (Fin k)) : SimpleGraph (Alphabet k B) :=
  rankGraph (fun b => Ranks.complete (rows b) false)

end Crown.Blocks

namespace Crown.BaselineLiteral
open Crown.Blocks
variable {k : ℕ} {B : Type*} [DecidableEq B]

def extra (π : Fin k → List B) : List (Alphabet k B) :=
  (List.finRange k).flatMap fun i =>
    [y i,x i] ++ if i.val = 0 then (π i).reverse.map Sum.inr else []

def word (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B) :
    List (Alphabet k B) := Blocks.word r π ++ extra π

end Crown.BaselineLiteral
