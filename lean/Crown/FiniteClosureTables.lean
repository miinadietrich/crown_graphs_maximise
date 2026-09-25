import Crown.FiniteClosureChecks

namespace Crown.FiniteClosureTables
open Crown.Ranks Crown.FiniteClosureChecks

def FastStep {v j q : ℕ} (owner : Fin j → Fin v) (support : Fin j → Finset (Fin v))
    (core : Fin q → Finset (Fin v)) (next : Fin j → Fin v → Fin j)
    (last : Fin j → Fin v → Fin q) (implies lower : Fin v → Fin v → Bool)
    (limit : ℕ) (a : Fin j) : Prop :=
  ∀ c,
    (implies (owner a) c = true → (insert c (support a)).card ≤ limit →
      owner (next a c) = c ∧ support (next a c) ⊆ insert c (support a)) ∧
    (lower (owner a) c = true → (insert c (support a)).card ≤ limit →
      core (last a c) ⊆ insert c (support a))

instance {v j q : ℕ} (owner : Fin j → Fin v) (support : Fin j → Finset (Fin v))
    (core : Fin q → Finset (Fin v)) (next : Fin j → Fin v → Fin j)
    (last : Fin j → Fin v → Fin q) (implies lower : Fin v → Fin v → Bool)
    (limit : ℕ) (a : Fin j) :
    Decidable (FastStep owner support core next last implies lower limit a) :=
  inferInstanceAs (Decidable (∀ c,
    (implies (owner a) c = true → (insert c (support a)).card ≤ limit →
      owner (next a c) = c ∧ support (next a c) ⊆ insert c (support a)) ∧
    (lower (owner a) c = true → (insert c (support a)).card ≤ limit →
      core (last a c) ⊆ insert c (support a))))

theorem step_of_fast {v i j q : ℕ} (rows : Fin v → InitialRow (Fin i))
    (owner : Fin j → Fin v) (support : Fin j → Finset (Fin v))
    (core : Fin q → Finset (Fin v)) (next : Fin j → Fin v → Fin j)
    (last : Fin j → Fin v → Fin q) (implies lower : Fin v → Fin v → Bool)
    (hi : ∀ b c, implies b c = true ↔ Implies rows b c)
    (hl : ∀ b c, lower b c = true ↔
      OneStar (rows b) ∧ Fixed (rows c) ∧ PotentialBelow (rows c) (rows b))
    (limit : ℕ) (a : Fin j)
    (h : FastStep owner support core next last implies lower limit a) :
    StepCheck rows owner support core next last limit a := by
  intro c
  constructor
  · intro hac hn
    exact (h c).1 ((hi _ _).mpr hac) hn
  · intro ha hc hca hn
    exact (h c).2 ((hl _ _).mpr ⟨ha,hc,hca⟩) hn

#print axioms step_of_fast
end Crown.FiniteClosureTables
