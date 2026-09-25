import Mathlib.Order.SuccPred.LinearLocallyFinite
import Mathlib.Data.Finset.Sort

namespace Crown.FiniteTraversal
open Order Function

theorem complete_of_successor {α : Type*} [Fintype α] [LinearOrder α]
    (next : α → α)
    (hs : ∀ {a}, ¬ IsMax a → ∀ b, a < b ↔ next a ≤ b)
    (hm : ∀ a, IsMax a → next a = a)
    (first : α) (hf : ∀ a, first ≤ a) :
    ∀ a, ∃ j : ℕ, next^[j] first = a := by
  letI : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  letI : SuccOrder α := SuccOrder.ofCore next hs hm
  intro a
  exact exists_succ_iterate_of_le (hf a)

#print axioms complete_of_successor

theorem complete_bounded {α : Type*} [Fintype α] [LinearOrder α]
    (next : α → α)
    (hs : ∀ a b, a < b → a < next a ∧ next a ≤ b)
    (first last : α) (hf : ∀ a, first ≤ a) (hl : ∀ a, a ≤ last) :
    (∀ a, ∃ j < Fintype.card α, next^[j] first = a) ∧
    next^[Fintype.card α-1] first = last ∧
    StrictMonoOn (fun j => next^[j] first) (Set.Iio (Fintype.card α)) := by
  classical
  let e := Fintype.orderIsoFinOfCardEq α rfl
  have hn : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨first⟩
  have hfirst : e ⟨0,hn⟩ = first := by
    apply le_antisymm
    · have h := e.monotone (show (⟨0,hn⟩ : Fin (Fintype.card α)) ≤ e.symm first from by exact Nat.zero_le _)
      simpa using h
    · exact hf _
  have hnext (i : ℕ) (hi : i+1 < Fintype.card α) :
      next (e ⟨i,by omega⟩) = e ⟨i+1,hi⟩ := by
    have hab : e ⟨i,by omega⟩ < e ⟨i+1,hi⟩ := e.strictMono (by exact Nat.lt_succ_self i)
    obtain ⟨hgt,hle⟩ := hs _ _ hab
    apply le_antisymm hle
    have hidx : i < (e.symm (next (e ⟨i,by omega⟩))).val := by
      have hfin : (⟨i,by omega⟩ : Fin (Fintype.card α)) <
          e.symm (next (e ⟨i,by omega⟩)) := by
        simpa only [OrderIso.symm_apply_apply] using e.symm.strictMono hgt
      exact Fin.lt_def.mp hfin
    have hh := e.monotone (show (⟨i+1,hi⟩ : Fin (Fintype.card α)) ≤
      e.symm (next (e ⟨i,by omega⟩)) from by exact Nat.succ_le_of_lt hidx)
    simpa using hh
  have hiter (i : ℕ) (hi : i < Fintype.card α) : next^[i] first = e ⟨i,hi⟩ := by
    induction i with
    | zero => simpa using hfirst.symm
    | succ i ih =>
      rw [Function.iterate_succ_apply',ih (by omega),hnext i hi]
  refine ⟨?_,?_,?_⟩
  · intro a
    refine ⟨(e.symm a).val,(e.symm a).isLt,?_⟩
    rw [hiter]
    exact e.apply_symm_apply a
  · rw [hiter _ (by omega)]
    apply le_antisymm (hl _)
    have h := e.monotone (show e.symm last ≤ (⟨Fintype.card α-1,by omega⟩ : Fin (Fintype.card α)) from by
      have := (e.symm last).isLt
      change (e.symm last).val ≤ Fintype.card α-1
      omega)
    simpa using h
  · intro i hi j hj hij
    change next^[i] first < next^[j] first
    rw [hiter i hi,hiter j hj]
    exact e.strictMono hij

#print axioms complete_bounded
end Crown.FiniteTraversal
