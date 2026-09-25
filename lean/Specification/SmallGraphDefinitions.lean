import Crown.Definitions
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Init.Data.BitVec.Lemmas

/-! Challenge-only definitions. These preserve original names in a separate
environment and must never be imported by solution modules. No solved theorem
is imported here. Literal source provenance is listed below each definition. -/

namespace Crown.SmallGraphs

def pairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun a =>
    ((List.finRange n).filter (fun b => a < b)).map (fun b => (a,b))

def pairIndex {n : ℕ} (a b : Fin n) : ℕ :=
  (pairs n).idxOf (min a b,max a b)

def graph (n mask : ℕ) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ mask.testBit (pairIndex a b) = true
  symm := ⟨by intro a b h; simpa [pairIndex,min_comm,max_comm,ne_comm] using h⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

end Crown.SmallGraphs

namespace Crown.SmallGraphs

def prism : SimpleGraph (Fin 6) := graph 6 30887

def wheel : SimpleGraph (Fin 6) := graph 6 21311

end Crown.SmallGraphs
