import Specification.MatrixDefinitions

namespace Crown.PartSizeBounds
open Crown.BalancedLarge
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem baseline_halfceil (hA : 3 ≤ Fintype.card A) (M : A → B → Bool) :
    KRepresentable (matrixGraph M) (1 + halfCeil (Fintype.card A)) := by
  sorry

theorem small_part (hA : Fintype.card A ≤ 4)
    (hN : 9 ≤ Fintype.card A + Fintype.card B) (M : A → B → Bool) :
    KRepresentable (matrixGraph M) 3 ∧
      3 ≤ quarterCeil (Fintype.card A + Fintype.card B) := by
  sorry

theorem unbalanced_even (k : ℕ) (hk : 3 ≤ k) (hA : Fintype.card A = 2*k)
    (hB : Fintype.card A < Fintype.card B) (M : A → B → Bool) :
    KRepresentable (matrixGraph M) (k+1) ∧
      k+1 ≤ quarterCeil (Fintype.card A + Fintype.card B) := by
  sorry

theorem unbalanced_odd (k : ℕ) (hk : 3 ≤ k) (hA : Fintype.card A = 2*k-1)
    (hB : Fintype.card A + 3 ≤ Fintype.card B) (M : A → B → Bool) :
    KRepresentable (matrixGraph M) (k+1) ∧
      k+1 ≤ quarterCeil (Fintype.card A + Fintype.card B) := by
  sorry

theorem near_odd (k : ℕ) (hk : 3 ≤ k) (hA : Fintype.card A = 2*k-1)
    (hle : Fintype.card A ≤ Fintype.card B)
    (hB : Fintype.card B ≤ Fintype.card A + 2) (M : A → B → Bool) :
    KRepresentable (matrixGraph M) k ∧
      quarterCeil (Fintype.card A + Fintype.card B) = k := by
  sorry

end Crown.PartSizeBounds
namespace Crown

theorem exists_safe_odd_vertex_three {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (k : ℕ) (hk : 3 ≤ k)
    (hA : Fintype.card A = 2*k-1)
    (hB : Fintype.card B ≤ Fintype.card A + 2) (N : B → Finset A) :
    ∃ a : A, (¬ ∃ c : B, N c = Finset.univ.erase a) ∨
      ∀ l u : B, (N l).card = k → (N u).card = k →
        a ∈ N l → a ∈ N u → l = u := by
  sorry

end Crown
