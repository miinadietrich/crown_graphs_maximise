import Crown.IndexedFiniteClosure
import Mathlib.Data.List.FinRange

namespace Crown.FiniteClosureChecks
open Crown.Ranks

instance {I : Type*} [Fintype I] (r : InitialRow I) : Decidable (Fixed r) :=
  inferInstanceAs (Decidable (∀ i, r i ≠ none))
instance {I : Type*} [Fintype I] [DecidableEq I] (r : InitialRow I) : Decidable (OneStar r) :=
  inferInstanceAs (Decidable (∃ j, r j = none ∧ ∀ i, r i = none → i = j))
instance (a b : Option (Fin 3)) : Decidable (PotentialEntry a b) :=
  inferInstanceAs (Decidable (∀ u v : Fin 3, a = some u → b = some v → u < v))
instance {I : Type*} [Fintype I] (r s : InitialRow I) : Decidable (PotentialBelow r s) :=
  inferInstanceAs (Decidable (∀ i, PotentialEntry (r i) (s i)))
instance {I V : Type*} [Fintype I] [DecidableEq I] (r : V → InitialRow I) (b c : V) :
    Decidable (Implies r b c) :=
  inferInstanceAs (Decidable (OneStar (r b) ∧ OneStar (r c) ∧ PotentialBelow (r c) (r b)))

variable {v i j q : ℕ}

def SeedCheck (r : Fin v → InitialRow (Fin i)) (owner : Fin j → Fin v)
    (support : Fin j → Finset (Fin v)) (hint : Fin v → Fin v → Fin j) : Prop :=
  ∀ b u, OneStar (r b) → Fixed (r u) → PotentialBelow (r b) (r u) →
    owner (hint b u) = b ∧ support (hint b u) ⊆ {b,u}

def FixedCheck (r : Fin v → InitialRow (Fin i)) (core : Fin q → Finset (Fin v))
    (hint : Fin v → Fin v → Fin q) : Prop :=
  ∀ b c, Fixed (r b) → Fixed (r c) → PotentialBelow (r b) (r c) →
    core (hint b c) ⊆ {b,c}

def StepCheck (r : Fin v → InitialRow (Fin i)) (owner : Fin j → Fin v)
    (support : Fin j → Finset (Fin v)) (core : Fin q → Finset (Fin v))
    (next : Fin j → Fin v → Fin j) (last : Fin j → Fin v → Fin q) (limit : ℕ)
    (a : Fin j) : Prop :=
  ∀ c,
    (Implies r (owner a) c → (insert c (support a)).card ≤ limit →
      owner (next a c) = c ∧ support (next a c) ⊆ insert c (support a)) ∧
    (OneStar (r (owner a)) → Fixed (r c) → PotentialBelow (r c) (r (owner a)) →
      (insert c (support a)).card ≤ limit → core (last a c) ⊆ insert c (support a))

instance (r : Fin v → InitialRow (Fin i)) (owner : Fin j → Fin v)
    (support : Fin j → Finset (Fin v)) (hint : Fin v → Fin v → Fin j) :
    Decidable (SeedCheck r owner support hint) := inferInstanceAs (Decidable (∀ b u,
      OneStar (r b) → Fixed (r u) → PotentialBelow (r b) (r u) →
      owner (hint b u) = b ∧ support (hint b u) ⊆ {b,u}))

instance (r : Fin v → InitialRow (Fin i)) (core : Fin q → Finset (Fin v))
    (hint : Fin v → Fin v → Fin q) : Decidable (FixedCheck r core hint) :=
  inferInstanceAs (Decidable (∀ b c, Fixed (r b) → Fixed (r c) →
    PotentialBelow (r b) (r c) → core (hint b c) ⊆ {b,c}))

instance (r : Fin v → InitialRow (Fin i)) (owner : Fin j → Fin v)
    (support : Fin j → Finset (Fin v)) (core : Fin q → Finset (Fin v))
    (next : Fin j → Fin v → Fin j) (last : Fin j → Fin v → Fin q) (limit : ℕ)
    (a : Fin j) : Decidable (StepCheck r owner support core next last limit a) :=
  inferInstanceAs (Decidable (∀ c,
    (Implies r (owner a) c → (insert c (support a)).card ≤ limit →
      owner (next a c) = c ∧ support (next a c) ⊆ insert c (support a)) ∧
    (OneStar (r (owner a)) → Fixed (r c) → PotentialBelow (r c) (r (owner a)) →
      (insert c (support a)).card ≤ limit → core (last a c) ⊆ insert c (support a))))

theorem certificate_of_checks (r : Fin v → InitialRow (Fin i)) (owner : Fin j → Fin v)
    (support : Fin j → Finset (Fin v)) (core : Fin q → Finset (Fin v))
    (seed : Fin v → Fin v → Fin j) (fixed : Fin v → Fin v → Fin q)
    (next : Fin j → Fin v → Fin j) (last : Fin j → Fin v → Fin q) (limit : ℕ)
    (hs : SeedCheck r owner support seed) (hf : FixedCheck r core fixed)
    (ht : ∀ a, StepCheck r owner support core next last limit a) :
    IndexedFiniteClosure.Certificate r owner support ((List.finRange q).map core) limit := by
  constructor
  · intro b u hb hu hbu
    exact ⟨seed b u, hs b u hb hu hbu⟩
  · intro a c hac hn
    exact ⟨next a c, (ht a c).1 hac hn⟩
  · intro a c ha hc hca hn
    exact ⟨core (last a c), List.mem_map.mpr ⟨last a c, List.mem_finRange _, rfl⟩,
      (ht a c).2 ha hc hca hn⟩
  · intro b c hb hc hbc
    exact ⟨core (fixed b c), List.mem_map.mpr ⟨fixed b c, List.mem_finRange _, rfl⟩,
      hf b c hb hc hbc⟩

#print axioms certificate_of_checks
end Crown.FiniteClosureChecks
