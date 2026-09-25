import Crown.GraphPadding

/-! Explicit part-size estimates used in Section6. These retain every vertex,
including isolated vertices and arbitrary neighbourhood multiplicities. -/
namespace Crown.PartSizeBounds
open Crown.BalancedLarge
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem baseline_halfceil (hA : 3 ≤ Fintype.card A) (M : A → B → Bool) :
    KRepresentable (matrixGraph M) (1 + halfCeil (Fintype.card A)) := by
  have hk : 2 ≤ halfCeil (Fintype.card A) := by unfold halfCeil; omega
  have hm : Fintype.card A ≤ 2 * halfCeil (Fintype.card A) := by unfold halfCeil; omega
  simpa only [Nat.add_comm] using GraphPadding.baseline _ hk hm M

theorem small_part (hA : Fintype.card A ≤ 4)
    (hN : 9 ≤ Fintype.card A + Fintype.card B) (M : A → B → Bool) :
    KRepresentable (matrixGraph M) 3 ∧
      3 ≤ quarterCeil (Fintype.card A + Fintype.card B) := by
  exact ⟨GraphPadding.at_most_four hA M,by unfold quarterCeil; omega⟩

theorem unbalanced_even (k : ℕ) (hk : 3 ≤ k) (hA : Fintype.card A = 2*k)
    (hB : Fintype.card A < Fintype.card B) (M : A → B → Bool) :
    KRepresentable (matrixGraph M) (k+1) ∧
      k+1 ≤ quarterCeil (Fintype.card A + Fintype.card B) := by
  exact ⟨GraphPadding.baseline k (by omega) (by omega) M,by unfold quarterCeil; omega⟩

theorem unbalanced_odd (k : ℕ) (hk : 3 ≤ k) (hA : Fintype.card A = 2*k-1)
    (hB : Fintype.card A + 3 ≤ Fintype.card B) (M : A → B → Bool) :
    KRepresentable (matrixGraph M) (k+1) ∧
      k+1 ≤ quarterCeil (Fintype.card A + Fintype.card B) := by
  exact ⟨GraphPadding.baseline k (by omega) (by omega) M,by unfold quarterCeil; omega⟩

theorem near_odd (k : ℕ) (hk : 3 ≤ k) (hA : Fintype.card A = 2*k-1)
    (hle : Fintype.card A ≤ Fintype.card B)
    (hB : Fintype.card B ≤ Fintype.card A + 2) (M : A → B → Bool) :
    KRepresentable (matrixGraph M) k ∧
      quarterCeil (Fintype.card A + Fintype.card B) = k := by
  exact ⟨OddGraphs.matrix_representable_three k hk hA hB M,by unfold quarterCeil; omega⟩

#print axioms baseline_halfceil
#print axioms small_part
#print axioms unbalanced_even
#print axioms unbalanced_odd
#print axioms near_odd
end Crown.PartSizeBounds
