import Specification.ProbabilityDefinitions
import Specification.MatrixDefinitions

open scoped Classical
namespace Crown.ProbabilitySpecification
open Crown.Matchings Crown.Ranks Crown.Orientations Crown.PairTypes
open Crown.MatchingProbabilities

/-- Every actual oriented unordered pairing admits a coordinate presentation. -/
theorem coordinates_exist (k : ℕ) (p : PairingOn (Fin (2*k))) :
    ∃ e : Coordinates k, Realizes p e := by
  sorry

/-- The count refers to actual strict rank comparisons with the stipulated
completion rule, independently of the coordinate enumeration. -/
theorem bad_pair_card (k : ℕ) (hk : 1 ≤ k) (N M : Fin (2*k) → Bool) :
    Nat.card {p : PairingOn (Fin (2*k)) // BadPairEvent N M p} =
      Arithmetic.P k
        (Nat.card {v : Fin (2*k) // N v = true ∧ M v = false})
        (Nat.card {v : Fin (2*k) // N v = false ∧ M v = true})
        (Nat.card {v : Fin (2*k) // N v = true ∧ M v = true})
        (Nat.card {v : Fin (2*k) // N v = false ∧ M v = false}) := by
  sorry

/-- Signed M still rejects x+y+z<2k, including a nonempty T class. -/
theorem fixed_pair_card (k : ℕ) (hk : 1 ≤ k) (N M : Fin (2*k) → Bool) :
    Nat.card {p : PairingOn (Fin (2*k)) // FixedPairEvent N M p} =
      2 * Arithmetic.M k
        (Nat.card {v : Fin (2*k) // N v = true ∧ M v = false})
        (Nat.card {v : Fin (2*k) // N v = false ∧ M v = true})
        (Nat.card {v : Fin (2*k) // N v = true ∧ M v = true}) := by
  sorry

/-- Necessary degree conditions on the actual full vertex domain. -/
theorem triple_degrees {k : ℕ} (l c u : Fin (2*k) → Bool) (e : Coordinates k)
    (h : TriplePattern l c u e) :
    Nat.card {v : Fin (2*k) // c v = true} = 2*k-2 ∧
    (Nat.card {v : Fin (2*k) // l v = true} = k ∨
      Nat.card {v : Fin (2*k) // l v = true} = k+1) ∧
    (Nat.card {v : Fin (2*k) // u v = true} = k ∨
      Nat.card {v : Fin (2*k) // u v = true} = k+1) := by
  sorry

/-- Exact pairing probability for two distinct labelled vertices. -/
theorem prescribed_pair_probability (k : ℕ) (hk : 1 ≤ k) (a b : Fin (2*k)) (hab : a ≠ b) :
    (Nat.card {p : PairingOn (Fin (2*k)) // DirectedPair p a b ∨ DirectedPair p b a} : ℚ) /
      Arithmetic.Q k = 1 / (2*k-1 : ℚ) := by
  sorry

/-- All residual firstsets of the required size have the same exact fiber.
The direction a→b is fixed; reversing it has the same count. -/
theorem residual_fiber (k : ℕ) (a b : Fin (2*(k+1))) (hab : a ≠ b)
    (S : Finset (Fin (2*(k+1)))) (ha : a ∉ S) (hb : b ∉ S) (hS : S.card = k) :
    Nat.card {p : PairingOn (Fin (2*(k+1))) //
      DirectedPair p a b ∧ ResidualFirstSet p a b S} = k.factorial := by
  sorry

/-- Two possible outer orders give at most two residual firstsets. -/
theorem triple_residual_sets {k : ℕ} (l c u : Fin (2*k) → Bool)
    (p : PairingOn (Fin (2*k))) (h : TripleEvent l c u p)
    (a b : Fin (2*k)) (hab : a ≠ b) (hc : ∀ v, c v = false ↔ v = a ∨ v = b) :
    (DirectedPair p a b ∨ DirectedPair p b a) ∧
      ((∀ v, v ≠ a → v ≠ b → (v ∈ p.1 ↔ l v = true)) ∨
       (∀ v, v ≠ a → v ≠ b → (v ∈ p.1 ↔ u v = true))) := by
  sorry

/-- All three rows are arbitrary: incompatible central degrees make the
actual event empty. This stronger positive-k domain contains k>=4. -/
theorem triple_probability (k : ℕ) (hk : 1 ≤ k) (l c u : Fin (2*k) → Bool) :
    (Nat.card {p : PairingOn (Fin (2*k)) // TripleEvent l c u p} : ℚ) /
      Arithmetic.Q k ≤ Arithmetic.theta k := by
  sorry

theorem feasible_five (N : Fin 10 → Fin 10 → Bool) :
    ∃ e : Coordinates 5, Feasible (fun v => rankRow (N v) e) := by
  sorry

theorem feasible_six (N : Fin 12 → Fin 12 → Bool) :
    ∃ e : Coordinates 6, Feasible (fun v => rankRow (N v) e) := by
  sorry

theorem feasible_seven (N : Fin 14 → Fin 14 → Bool) :
    ∃ e : Coordinates 7, Feasible (fun v => rankRow (N v) e) := by
  sorry

end Crown.ProbabilitySpecification
