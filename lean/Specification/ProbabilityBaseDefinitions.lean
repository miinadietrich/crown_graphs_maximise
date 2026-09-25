import Specification.OrientationDefinitions
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite

/-! Challenge-only probability definitions. These imports contain no project
proofs. Coordinates are explicit equivalence parameters with a realization
predicate; no cardinality or coordinate-existence theorem enters a definition.
The residual-firstset predicate is direct membership outside two endpoints. -/

set_option synthInstance.maxSize 1024

namespace Crown.Matchings
abbrev FirstSets (k : ℕ) := {s : Finset (Fin (2*k)) // s.card = k}
abbrev First {k : ℕ} (s : FirstSets k) := {v : Fin (2*k) // v ∈ s.val}
abbrev Second {k : ℕ} (s : FirstSets k) := {v : Fin (2*k) // v ∉ s.val}
abbrev OrientedPairing (k : ℕ) := Σ s : FirstSets k, First s ≃ Second s
abbrev PairingOn (V : Type*) [DecidableEq V] :=
  Σ s : Finset V, {v : V // v ∈ s} ≃ {v : V // v ∉ s}
section
universe u_2
def DirectedPair {V : Type u_2} [DecidableEq V] (p : PairingOn V) (a b : V) : Prop :=
  a ∈ p.1 ∧ b ∉ p.1 ∧ ∀ ha hb, p.2 ⟨a,ha⟩ = ⟨b,hb⟩
end
end Crown.Matchings

namespace Crown.PairTypes
open Crown.Ranks Crown.Orientations
inductive Colour where
  | X | Y | Z | T
  deriving DecidableEq
open Colour
def bits : Colour → Bool × Bool
  | X => (true,false) | Y => (false,true)
  | Z => (true,true) | T => (false,false)
def colourOfBits : Bool × Bool → Colour
  | (true,false) => X | (false,true) => Y
  | (true,true) => Z | (false,false) => T
def smallerEntry (a b : Colour) : Option (Fin 3) := entry ((bits a).1,(bits b).1) false
def largerEntry (a b : Colour) : Option (Fin 3) := entry ((bits a).2,(bits b).2) false
def Ordinary (a b : Colour) : Prop :=
  (a = X ∧ b = Y) ∨ (a = X ∧ b = Z) ∨ (a = Z ∧ b = Y)
def Exceptional (a b : Colour) : Prop :=
  (a = Y ∧ b = Y) ∨ (a = T ∧ b = Y) ∨ (a = Y ∧ b = T)
def Allowed (a b : Colour) : Prop := Ordinary a b ∨ Exceptional a b
def smaller {I : Type*} (p : I → Colour × Colour) : NeighbourRow I :=
  fun i => ((bits (p i).1).1,(bits (p i).2).1)
def larger {I : Type*} (p : I → Colour × Colour) : NeighbourRow I :=
  fun i => ((bits (p i).1).2,(bits (p i).2).2)
def AtMostOneExceptional {I : Type*} (p : I → Colour × Colour) : Prop :=
  ∀ i j, Exceptional (p i).1 (p i).2 → Exceptional (p j).1 (p j).2 → i = j
def endpoint {I : Type*} (p : I → Colour × Colour) (v : I × Bool) : Colour :=
  if v.2 then (p v.1).2 else (p v.1).1
end Crown.PairTypes

namespace Crown.MatchingProbabilities
open Crown.Matchings Crown.PairTypes
abbrev ColourClass {V : Type*} (col : V → Colour) (c : Colour) := {v : V // col v = c}
def Comparison {V : Type*} [DecidableEq V] (col : V → Colour) (p : PairingOn V) : Prop :=
  (∀ a b, DirectedPair p a b → Allowed (col a) (col b)) ∧
    ∀ a b c d, DirectedPair p a b → DirectedPair p c d →
      Exceptional (col a) (col b) → Exceptional (col c) (col d) → a = c
end Crown.MatchingProbabilities

