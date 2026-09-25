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

namespace Crown

/-- The balanced matrix case, stated directly on the Boolean bipartite graph. -/
theorem balanced_matrix_representation_bound (k : ℕ) (hk : 3 ≤ k)
    (M : Fin (2*k) → Fin (2*k) → Bool) :
    KRepresentable (BalancedLarge.matrixGraph M) k := by
  sorry

/-- H01: every bipartite graph of order at least nine has the asserted word. -/
theorem bipartite_representation_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hb : G.IsBipartite) (hN : 9 ≤ Fintype.card V) :
    ∃ k, k ≤ quarterCeil (Fintype.card V) ∧ KRepresentable G k := by
  sorry

/-- H01 in terms of the least multiplicity, with existence retained explicitly. -/
theorem bipartite_representation_number_bound {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hb : G.IsBipartite) (hN : 9 ≤ Fintype.card V) :
    Representable G ∧ representationNumber G ≤ quarterCeil (Fintype.card V) := by
  sorry

/-- H03, H05 and H06: the exact crown values at every positive part size. -/
theorem crown_representation_number (n : ℕ) (hn : 1 ≤ n) :
    Representable (crownGraph n) ∧ representationNumber (crownGraph n) = crownValue n := by
  sorry

/-- H02: crowns attain the largest representation number at each even order. -/
theorem crown_extremal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n) (hcard : Fintype.card V = 2 * n)
    (hb : G.IsBipartite) :
    Representable G ∧ representationNumber G ≤ representationNumber (crownGraph n) := by
  sorry

/-- H04: the maximum minimum uniform length at each even order at least ten. -/
theorem crown_extremal_uniform_length (n : ℕ) (hn : 5 ≤ n) :
    (∃ w, Represents (crownGraph n) (halfCeil n) w ∧
      w.length = (2 * n) * halfCeil n ∧
      ∀ k u, Represents (crownGraph n) k u → w.length ≤ u.length) ∧
    (∀ (G : SimpleGraph (Fin (2 * n))), G.IsBipartite →
      ∃ k w, Represents G k w ∧ w.length ≤ (2 * n) * halfCeil n) := by
  sorry

/-- H07: the required small bipartite graphs admit two-uniform representations. -/
theorem small_bipartite_two_uniform {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hb : G.IsBipartite) (hcard : Fintype.card V ≤ 6) :
    KRepresentable G 2 := by
  sorry

end Crown
