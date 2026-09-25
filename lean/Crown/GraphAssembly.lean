import Crown.GraphPadding
import Crown.Arithmetic

/-! The reduction of arbitrary part sizes to the balanced cases and the
five-by-seven case. The two outstanding inputs are explicit hypotheses of
these supporting lemmas. They are not assumptions of the final challenge. -/

namespace Crown.GraphAssembly
open Crown.BalancedLarge

def BalancedCases : Prop := ∀ k : ℕ, 3 ≤ k →
  ∀ M : Fin (2*k) → Fin (2*k) → Bool, KRepresentable (matrixGraph M) k

def FiveSevenCase : Prop :=
  ∀ M : Fin 5 → Fin 7 → Bool, KRepresentable (matrixGraph M) 3

theorem ordered_matrix_bound (hbalanced : BalancedCases) (hfive : FiveSevenCase)
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : A → B → Bool) (horder : Fintype.card A ≤ Fintype.card B)
    (hN : 9 ≤ Fintype.card A + Fintype.card B) :
    ∃ k, k ≤ quarterCeil (Fintype.card A + Fintype.card B) ∧
      KRepresentable (matrixGraph M) k := by
  by_cases hsmall : Fintype.card A ≤ 4
  · exact ⟨3, Arithmetic.small_parts_bound _ _ hN, GraphPadding.at_most_four hsmall M⟩
  by_cases heven : Fintype.card A % 2 = 0
  · let k := Fintype.card A / 2
    have hk : 3 ≤ k := by dsimp [k]; omega
    have hA : Fintype.card A = 2*k := by dsimp [k]; omega
    by_cases hB : Fintype.card B = 2*k
    · refine ⟨k, ?_, ?_⟩
      · simp [quarterCeil, hA, hB]; omega
      · apply GraphPadding.of_card_le (A' := Fin (2*k)) (B' := Fin (2*k))
          (by simp [hA]) (by simp [hB])
        exact hbalanced k hk
    · refine ⟨k+1, ?_, GraphPadding.baseline k (by omega) hA.le M⟩
      simpa [quarterCeil, hA] using Arithmetic.even_unbalanced_bound k
        (Fintype.card B) (by omega)
  · let k := (Fintype.card A + 1) / 2
    have hk : 3 ≤ k := by dsimp [k]; omega
    have hA : Fintype.card A = 2*k-1 := by dsimp [k]; omega
    by_cases hfar : 2*k+2 ≤ Fintype.card B
    · refine ⟨k+1, ?_, GraphPadding.baseline k (by omega) (by omega) M⟩
      simpa [quarterCeil, hA] using Arithmetic.odd_unbalanced_bound k
        (Fintype.card B) (by omega) hfar
    · have hceil : quarterCeil (Fintype.card A + Fintype.card B) = k := by
        simpa [quarterCeil, hA] using Arithmetic.odd_near_balanced_bound k
          (Fintype.card B) (by omega) (by omega) (by omega)
      refine ⟨k, hceil.ge, ?_⟩
      by_cases hk4 : 4 ≤ k
      · exact OddGraphs.matrix_representable k hk4 hA (by omega) M
      · have hk3 : k = 3 := by omega
        rw [hk3]
        apply GraphPadding.of_card_le (A' := Fin 5) (B' := Fin 7)
          (by simp only [Fintype.card_fin]; omega)
          (by simp only [Fintype.card_fin]; omega)
        exact hfive

theorem matrix_bound (hbalanced : BalancedCases) (hfive : FiveSevenCase)
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : A → B → Bool) (hN : 9 ≤ Fintype.card A + Fintype.card B) :
    ∃ k, k ≤ quarterCeil (Fintype.card A + Fintype.card B) ∧
      KRepresentable (matrixGraph M) k := by
  by_cases horder : Fintype.card A ≤ Fintype.card B
  · exact ordered_matrix_bound hbalanced hfive M horder hN
  · obtain ⟨k, hk, w, hw⟩ := ordered_matrix_bound hbalanced hfive
      (fun b a => M a b) (by omega) (by omega)
    refine ⟨k, by simpa [Nat.add_comm] using hk, w.map (Equiv.sumComm B A), ?_⟩
    apply represents_equiv (Equiv.sumComm B A) _ hw
    intro a b
    cases a <;> cases b <;> rfl

theorem graph_bound (hbalanced : BalancedCases) (hfive : FiveSevenCase)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hb : G.IsBipartite) (hN : 9 ≤ Fintype.card V) :
    ∃ k, k ≤ quarterCeil (Fintype.card V) ∧ KRepresentable G k := by
  classical
  obtain ⟨c, hc⟩ := hb
  let p : V → Prop := fun v => c v = 0
  let A := {v // p v}
  let B := {v // ¬p v}
  let e : A ⊕ B ≃ V := Equiv.sumCompl p
  let M : A → B → Bool := fun a b => decide (G.Adj a.val b.val)
  have hcard : Fintype.card A + Fintype.card B = Fintype.card V := by
    simpa using Fintype.card_congr e
  obtain ⟨k, hk, w, hw⟩ := matrix_bound hbalanced hfive M (by omega)
  refine ⟨k, by simpa [hcard] using hk, w.map e, represents_equiv e ?_ hw⟩
  intro a b
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change G.Adj a.val b.val ↔ False
      refine ⟨fun h => ?_, False.elim⟩
      have hne := hc h
      have ha := a.property
      have hb := b.property
      change c a.val = 0 at ha
      change c b.val = 0 at hb
      exact hne (ha.trans hb.symm)
    | inr b =>
      change G.Adj a.val b.val ↔ decide (G.Adj a.val b.val) = true
      simp
  | inr a =>
    cases b with
    | inl b =>
      change G.Adj a.val b.val ↔ decide (G.Adj b.val a.val) = true
      simpa using G.adj_comm a.val b.val
    | inr b =>
      change G.Adj a.val b.val ↔ False
      refine ⟨fun h => ?_, False.elim⟩
      have hne := hc h
      have ha := a.property
      have hb := b.property
      change c a.val ≠ 0 at ha
      change c b.val ≠ 0 at hb
      change c a.val ≠ c b.val at hne
      omega

#print axioms ordered_matrix_bound
#print axioms matrix_bound
#print axioms graph_bound

end Crown.GraphAssembly
