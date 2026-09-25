import Crown.SmallBipartite
import Crown.Words
import Crown.GraphBasics
import Mathlib.Tactic.IntervalCases

/-! Transfer the finite six-vertex witnesses to arbitrary finite vertex types,
including empty parts, isolated vertices and disconnected graphs. -/

namespace Crown

open SmallBipartite

theorem six_cross_two_uniform (m : ℕ) (hm : m ≤ 3)
    (edge : Fin m → Fin (6-m) → Bool) : KRepresentable (crossGraph edge) 2 := by
  interval_cases m
  · exact ⟨_, all_zero_six edge⟩
  · exact ⟨_, all_one_five edge⟩
  · exact ⟨_, all_two_four edge⟩
  · exact ⟨_, all_three_three edge⟩

theorem small_cross_ordered {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (edge : A → B → Bool)
    (hA : Fintype.card A ≤ 3) (hN : Fintype.card A + Fintype.card B ≤ 6) :
    KRepresentable (crossGraph edge) 2 := by
  classical
  let m := Fintype.card A
  let n := Fintype.card B
  let eA : A ≃ Fin m := Fintype.equivFin A
  let eB : B ≃ Fin n := Fintype.equivFin B
  have hn : n ≤ 6-m := by dsimp [m,n]; omega
  let fB : B ↪ Fin (6-m) :=
    ⟨fun b => ⟨(eB b).val, Nat.lt_of_lt_of_le (eB b).isLt hn⟩,
      fun _ _ h => eB.injective (Fin.ext (congrArg (fun x : Fin (6-m) => x.val) h))⟩
  let f : A ⊕ B ↪ Fin m ⊕ Fin (6-m) := eA.toEmbedding.sumMap fB
  let expanded : Fin m → Fin (6-m) → Bool := fun a b =>
    if h : b.val < n then edge (eA.symm a) (eB.symm ⟨b.val,h⟩) else false
  have hexp (a : A) (b : B) : expanded (eA a) (fB b) = edge a b := by
    change (if h : (eB b).val < n then
      edge (eA.symm (eA a)) (eB.symm ⟨(eB b).val,h⟩) else false) = edge a b
    rw [dif_pos (eB b).isLt]
    simp
  apply kRepresentable_of_inducedEmbedding f ?_ (six_cross_two_uniform m hA expanded)
  intro a b
  cases a with
  | inl a =>
    cases b with
    | inl b => rfl
    | inr b =>
      change edge a b = true ↔ expanded (eA a) (fB b) = true
      rw [hexp]
  | inr a =>
    cases b with
    | inl b =>
      change edge b a = true ↔ expanded (eA b) (fB a) = true
      rw [hexp]
    | inr b => rfl

theorem small_cross_two_uniform {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (edge : A → B → Bool)
    (hN : Fintype.card A + Fintype.card B ≤ 6) :
    KRepresentable (crossGraph edge) 2 := by
  by_cases hA : Fintype.card A ≤ 3
  · exact small_cross_ordered edge hA hN
  · have hB : Fintype.card B ≤ 3 := by omega
    obtain ⟨w, hw⟩ := small_cross_ordered (fun b a => edge a b) hB (by omega)
    refine ⟨w.map (Equiv.sumComm B A), represents_equiv (Equiv.sumComm B A) ?_ hw⟩
    intro a b
    cases a <;> cases b <;> rfl

theorem small_bipartite_two_uniform_proof {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hb : G.IsBipartite) (hN : Fintype.card V ≤ 6) :
    KRepresentable G 2 := by
  classical
  obtain ⟨c, hc⟩ := hb
  let p : V → Prop := fun v => c v = 0
  let A := {v // p v}
  let B := {v // ¬p v}
  let e : A ⊕ B ≃ V := Equiv.sumCompl p
  let edge : A → B → Bool := fun a b => decide (G.Adj a.val b.val)
  have hcard : Fintype.card A + Fintype.card B ≤ 6 := by
    have he := Fintype.card_congr e
    simpa using he.le.trans hN
  obtain ⟨w, hw⟩ := small_cross_two_uniform edge hcard
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

#print axioms small_bipartite_two_uniform_proof

end Crown
