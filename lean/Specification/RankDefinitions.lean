import Lean

/-! Challenge-only definitions. These preserve original names in a separate
environment and must never be imported by solution modules. No solved theorem
is imported here. Literal source provenance is listed below each definition. -/

namespace Crown.Ranks
universe u v w
variable {I : Type u} {V : Type v} {X : Type w}

abbrev InitialRow (I : Type u) := I → Option (Fin 3)

abbrev CompletedRow (I : Type u) := I → Fin 5

def prescribed (u : Fin 3) : Fin 5 := ⟨u.val + 1, by omega⟩

def completeEntry (a : Option (Fin 3)) (t : Bool) : Fin 5 :=
  match a with
  | none => if t then 4 else 0
  | some u => prescribed u

def complete (ρ : InitialRow I) (t : Bool) : CompletedRow I :=
  fun i => completeEntry (ρ i) t

def Completes (ρ : InitialRow I) (r : CompletedRow I) : Prop :=
  ∀ i, match ρ i with
  | none => r i = 0 ∨ r i = 4
  | some u => r i = prescribed u

def StrictBelow (r s : CompletedRow I) : Prop := ∀ i, r i < s i

def PotentialEntry (a b : Option (Fin 3)) : Prop :=
  ∀ u v : Fin 3, a = some u → b = some v → u < v

def PotentialBelow (ρ σ : InitialRow I) : Prop :=
  ∀ i, PotentialEntry (ρ i) (σ i)

def Fixed (ρ : InitialRow I) : Prop := ∀ i, ρ i ≠ none

def HasStar (ρ : InitialRow I) : Prop := ∃ i, ρ i = none

def OneStar (ρ : InitialRow I) : Prop :=
  ∃ j, ρ j = none ∧ ∀ i, ρ i = none → i = j

def MultiStar (ρ : InitialRow I) : Prop :=
  ∃ i j, i ≠ j ∧ ρ i = none ∧ ρ j = none

inductive Forced (one : X → Prop) (edge : X → X → Prop) : X → Prop
  | seed {x} : one x → Forced one edge x
  | step {x y} : Forced one edge x → edge x y → Forced one edge y

def ValidChoice (one zero : X → Prop) (edge : X → X → Prop) (t : X → Bool) : Prop :=
  (∀ x, one x → t x = true) ∧ (∀ x, zero x → t x = false) ∧
    (∀ x y, edge x y → t x = true → t y = true)

def DirectOne (rows : V → InitialRow I) (b : V) : Prop :=
  OneStar (rows b) ∧ ∃ u, Fixed (rows u) ∧ PotentialBelow (rows b) (rows u)

def DirectZero (rows : V → InitialRow I) (b : V) : Prop :=
  OneStar (rows b) ∧ ∃ l, Fixed (rows l) ∧ PotentialBelow (rows l) (rows b)

def Implies (rows : V → InitialRow I) (b c : V) : Prop :=
  OneStar (rows b) ∧ OneStar (rows c) ∧ PotentialBelow (rows c) (rows b)

def Feasible (rows : V → InitialRow I) : Prop :=
  ∃ r : V → CompletedRow I, (∀ b, Completes (rows b) (r b)) ∧
    ∀ b c, ¬ StrictBelow (r b) (r c)

def NoFixedPair (rows : V → InitialRow I) : Prop :=
  ∀ b c, Fixed (rows b) → Fixed (rows c) → ¬ PotentialBelow (rows b) (rows c)

end Crown.Ranks
