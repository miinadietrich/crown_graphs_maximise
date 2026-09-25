import Crown.Baseline
import Crown.OddGraphs
import Mathlib.Logic.Function.Basic

/-! Padding and relabelling for arbitrary bipartite matrices. Empty parts,
isolated vertices and repeated neighbourhoods are all retained. -/

namespace Crown.GraphPadding
open Crown.BalancedLarge

variable {A B A' B' : Type*} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [DecidableEq A] [DecidableEq B] [DecidableEq A'] [DecidableEq B']

theorem of_embeddings (f : A ↪ A') (g : B ↪ B') (k : ℕ)
    (h : ∀ M' : A' → B' → Bool, KRepresentable (matrixGraph M') k)
    (M : A → B → Bool) : KRepresentable (matrixGraph M) k := by
  classical
  let expanded : A' → B' → Bool := Function.extend f
    (fun a => Function.extend g (M a) (fun _ => false)) (fun _ _ => false)
  have hexp (a : A) (b : B) : expanded (f a) (g b) = M a b := by
    dsimp [expanded]
    rw [f.injective.extend_apply, g.injective.extend_apply]
  apply kRepresentable_of_inducedEmbedding (f.sumMap g) ?_ (h expanded)
  intro a b
  cases a with
  | inl a =>
    cases b with
    | inl b => rfl
    | inr b =>
      change M a b = true ↔ expanded (f a) (g b) = true
      rw [hexp]
  | inr a =>
    cases b with
    | inl b =>
      change M b a = true ↔ expanded (f b) (g a) = true
      rw [hexp]
    | inr b => rfl

theorem of_card_le (hA : Fintype.card A ≤ Fintype.card A')
    (hB : Fintype.card B ≤ Fintype.card B') (k : ℕ)
    (h : ∀ M' : A' → B' → Bool, KRepresentable (matrixGraph M') k)
    (M : A → B → Bool) : KRepresentable (matrixGraph M) k := by
  classical
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hA
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hB
  exact of_embeddings f g k h M

theorem baseline (k : ℕ) (hk : 2 ≤ k) (hA : Fintype.card A ≤ 2*k)
    (M : A → B → Bool) : KRepresentable (matrixGraph M) (k+1) := by
  apply of_card_le (A' := Fin (2*k)) (B' := B) (by simpa using hA) le_rfl
  exact Crown.Baseline.matrix_representable k hk

theorem at_most_four (hA : Fintype.card A ≤ 4) (M : A → B → Bool) :
    KRepresentable (matrixGraph M) 3 := baseline 2 (by decide) hA M

theorem balanced_large (k : ℕ) (hk : 8 ≤ k)
    (hA : Fintype.card A ≤ 2*k) (hB : Fintype.card B ≤ 2*k)
    (M : A → B → Bool) : KRepresentable (matrixGraph M) k := by
  apply of_card_le (A' := Fin (2*k)) (B' := Fin (2*k))
    (by simpa using hA) (by simpa using hB)
  exact Crown.BalancedLarge.matrix_representable k hk

#print axioms of_embeddings
#print axioms of_card_le
#print axioms baseline
#print axioms balanced_large

end Crown.GraphPadding
