import Crown.GraphAssembly

namespace Crown.SmallEight
open Crown.BalancedLarge

theorem matrix {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : A → B → Bool) (hN : Fintype.card A + Fintype.card B ≤ 8) :
    KRepresentable (matrixGraph M) 3 := by
  by_cases hA : Fintype.card A ≤ 4
  · exact GraphPadding.at_most_four hA M
  · obtain ⟨w, hw⟩ := GraphPadding.at_most_four (by omega : Fintype.card B ≤ 4)
      (fun b a => M a b)
    refine ⟨w.map (Equiv.sumComm B A), represents_equiv (Equiv.sumComm B A) ?_ hw⟩
    intro a b
    cases a <;> cases b <;> rfl

theorem graph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hb : G.IsBipartite) (hN : Fintype.card V ≤ 8) :
    KRepresentable G 3 := by
  classical
  obtain ⟨c, hc⟩ := hb
  let p : V → Prop := fun v => c v = 0
  let A := {v // p v}
  let B := {v // ¬p v}
  let e : A ⊕ B ≃ V := Equiv.sumCompl p
  let M : A → B → Bool := fun a b => decide (G.Adj a.val b.val)
  have hcard : Fintype.card A + Fintype.card B = Fintype.card V := by
    simpa using Fintype.card_congr e
  obtain ⟨w, hw⟩ := matrix M (by omega)
  refine ⟨w.map e, represents_equiv e ?_ hw⟩
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

#print axioms matrix
#print axioms graph
end Crown.SmallEight
