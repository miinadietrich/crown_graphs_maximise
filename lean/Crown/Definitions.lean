import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Count
import Mathlib.Data.Nat.Find

/-!
# Uniform word representations

These definitions express the graph invariant used by Colbrook and Drysdale,
*Crown graphs maximise the representation number of bipartite graphs*.
The alternation relation concerns distinct vertices; a uniform representation
uses every vertex with positive multiplicity. Lists and simple graphs use
Mathlib's standard definitions.
-/

namespace Crown

/-- Restrict a word to two letters, retaining their original order. -/
def restrictPair {V : Type*} [DecidableEq V] (w : List V) (a b : V) : List V :=
  w.filter fun x => x = a ∨ x = b

/-- Two letters alternate when their restricted word has unequal neighbours. -/
def Alternates {V : Type*} [DecidableEq V] (w : List V) (a b : V) : Prop :=
  (restrictPair w a b).IsChain (· ≠ ·)

/-- Every letter occurs exactly `k` times. Positivity is supplied by `Represents`. -/
def Uniform {V : Type*} [DecidableEq V] (k : ℕ) (w : List V) : Prop :=
  ∀ v, w.count v = k

/-- A positive uniform representation captures every edge and every nonedge. -/
def Represents {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (w : List V) : Prop :=
  0 < k ∧ Uniform k w ∧ ∀ a b, a ≠ b → (G.Adj a b ↔ Alternates w a b)

/-- A graph has a representation in which every letter occurs `k` times. -/
def KRepresentable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ w, Represents G k w

/-- Existence of a positive uniform word representation. -/
def Representable {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ k, KRepresentable G k

/-- Least positive uniform multiplicity, or zero for a nonrepresentable graph.
Results using this invariant must establish representability independently. -/
noncomputable def representationNumber {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) : ℕ := by
  classical
  exact if h : Representable G then Nat.find h else 0

/-- The crown has two sides of size `n`, with only equal-index cross edges deleted. -/
def crownGraph (n : ℕ) : SimpleGraph (Bool × Fin n) where
  Adj a b := a.1 ≠ b.1 ∧ a.2 ≠ b.2
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, Ne.symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Natural-number ceiling of division by four. -/
def quarterCeil (n : ℕ) : ℕ := (n + 3) / 4

/-- Natural-number ceiling of division by two. -/
def halfCeil (n : ℕ) : ℕ := (n + 1) / 2

/-- Exact crown value claimed in the manuscript, including all small orders. -/
def crownValue (n : ℕ) : ℕ :=
  if n ≤ 3 then 2 else if n = 4 then 3 else halfCeil n

end Crown
