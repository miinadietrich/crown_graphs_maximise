import Crown.Ranks
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

/-! The direct three-pair check uses base-five completed ranks. This is a
different encoding from the base-four initial rows of the closure certificate:
zero here is an actual completed extreme, not the sentinel for a star. -/
namespace Crown.ThreeRankCoding
open Crown.Ranks
open scoped Classical

def encode (r : CompletedRow (Fin 3)) : Fin 125 :=
  ⟨(r 0).val + 5*(r 1).val + 25*(r 2).val,by
    have h0 := (r 0).isLt
    have h1 := (r 1).isLt
    have h2 := (r 2).isLt
    omega⟩

theorem encode_injective : Function.Injective encode := by
  intro r s h
  have he := congrArg Fin.val h
  change (r 0).val + 5*(r 1).val + 25*(r 2).val =
    (s 0).val + 5*(s 1).val + 25*(s 2).val at he
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  have h2 := (r 2).isLt
  have g0 := (s 0).isLt
  have g1 := (s 1).isLt
  have g2 := (s 2).isLt
  clear h
  have e0 : (r 0).val = (s 0).val := by omega
  have e1 : (r 1).val = (s 1).val := by omega
  have e2 : (r 2).val = (s 2).val := by omega
  funext i
  fin_cases i
  · exact Fin.ext e0
  · exact Fin.ext e1
  · exact Fin.ext e2

theorem encode_bijective : Function.Bijective encode := by
  apply (Fintype.bijective_iff_injective_and_card encode).mpr
  refine ⟨encode_injective,?_⟩
  simp only [CompletedRow,Fintype.card_pi_const,Fintype.card_fin]
  rfl

noncomputable def rowEquiv : CompletedRow (Fin 3) ≃ Fin 125 :=
  Equiv.ofBijective encode encode_bijective

noncomputable def comparison (a b : Fin 125) : Prop :=
  StrictBelow (rowEquiv.symm a) (rowEquiv.symm b)

theorem comparison_encode (r s : CompletedRow (Fin 3)) :
    comparison (encode r) (encode s) ↔ StrictBelow r s := by
  change StrictBelow (rowEquiv.symm (rowEquiv r)) (rowEquiv.symm (rowEquiv s)) ↔ _
  rw [rowEquiv.symm_apply_apply,rowEquiv.symm_apply_apply]

theorem completed_row_count : Fintype.card (CompletedRow (Fin 3)) = 125 := by
  simpa using Fintype.card_congr rowEquiv

theorem comparison_entry_count : Fintype.card (Fin 125 × Fin 125) = 15625 := by simp

theorem at_most_seven_choices {V : Type*} [Fintype V]
    (h : Fintype.card V ≤ 7) : Fintype.card (V → Bool) ≤ 128 := by
  rw [Fintype.card_fun,Fintype.card_bool]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) h).trans (by decide)

#print axioms encode_bijective
#print axioms comparison_encode
#print axioms completed_row_count
#print axioms comparison_entry_count
#print axioms at_most_seven_choices
end Crown.ThreeRankCoding
