import Crown.OddGraphs

/-! The odd-part construction supplies a feasible pairing, before its word
representation is formed. This retains the stronger finite-family conclusion. -/

namespace Crown.OddGraphs

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem exists_feasible_pairing_three (k : ℕ) (hk : 3 ≤ k)
    (hA : Fintype.card A = 2*k-1) (hB : Fintype.card B ≤ Fintype.card A + 2)
    (M : A → B → Bool) :
    ∃ e : (Fin k × Bool) ≃ Option A, Ranks.Feasible (OddRanks.rows (pairedBits M e)) := by
  classical
  obtain ⟨a, ha⟩ := Crown.exists_safe_odd_vertex_three k hk hA hB (neighbourhood M)
  let z : Fin k := ⟨0, by omega⟩
  obtain ⟨e, hez, hed⟩ := exists_pairing hk hA a z
  have hsp : ∀ b, (pairedBits M e b z).2 = false := by
    intro b
    simp [pairedBits, hed, optBit]
  exact ⟨e, OddRanks.feasible_of_safe_three hk (pairedBits M e) z hsp
    (safe_pairedBits M e a z hez hed ha)⟩

theorem five_vertex_family (hB : Fintype.card B ≤ 7) (N : B → Finset (Fin 5)) :
    ∃ e : (Fin 3 × Bool) ≃ Option (Fin 5),
      Ranks.Feasible (OddRanks.rows (pairedBits (fun a b => decide (a ∈ N b)) e)) :=
  exists_feasible_pairing_three 3 (by decide) (by simp) (by simpa using hB) _

#print axioms exists_feasible_pairing_three
#print axioms five_vertex_family

end Crown.OddGraphs
