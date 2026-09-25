import Crown.SmallGraphWheelFinite
import Mathlib.Tactic.FinCases

namespace Crown.SmallGraphs

local instance wheelBEqFin6 : BEq (Fin 6) := ⟨fun a b => decide (a = b)⟩
local instance wheelLawfulBEqFin6 : LawfulBEq (Fin 6) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

/-- Both lists are the actual gaps between the two hub occurrences. -/
theorem wheel_not_two : ¬Crown.KRepresentable wheel 2 := by
  rintro ⟨w,hw⟩
  obtain ⟨s,t,hr,hs,ht,ha⟩ := two_gaps hw 0
  have hall : ∀ a : Fin 6, a ≠ 0 → wheel.Adj 0 a := by decide +kernel
  have hsc : ∀ a : Fin 6, a ≠ 0 → s.count a = 1 :=
    fun a hn => (ha a hn).mp (hall a hn)
  have htc : ∀ a : Fin 6, a ≠ 0 → t.count a = 1 := by
    intro a hn
    have h := gap_counts hr hn
    have hh := hsc a hn
    omega
  have hc : ∀ a : Fin 6, ([(1:Fin 6),2,3,4,5].count a) = if a = 0 then 0 else 1 := by
    decide +kernel
  have hp : s.Perm [(1:Fin 6),2,3,4,5] := by
    apply List.perm_iff_count.mpr
    intro a
    rw [hc]
    by_cases hn : a = 0
    · subst a; simp [List.count_eq_zero.mpr hs]
    · simp [hn,hsc a hn]
  have hq : t.Perm [(1:Fin 6),2,3,4,5] := by
    apply List.perm_iff_count.mpr
    intro a
    rw [hc]
    by_cases hn : a = 0
    · subst a; simp [List.count_eq_zero.mpr ht]
    · simp [hn,htc a hn]
  exact wheel_permutations_fail s (List.mem_permutations'.mpr hp)
    t (List.mem_permutations'.mpr hq) hr.2.2

#print axioms wheel_not_two
end Crown.SmallGraphs
