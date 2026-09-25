import Crown.GosperSuccessor
import Crown.GosperStates
import Crown.FiniteTraversal

/-! Literal Gosper update on its full positive-weight fixed-width domain. -/
set_option Elab.async false

namespace Crown.GosperTraversal
open Crown.EnumeratorDefinitions Crown.GosperBits Crown.GosperWeight Crown.GosperSuccessor

theorem update_successor (n r x : ℕ) (hn : n ≤ 64) (hr : 0 < r) (hrn : r ≤ n)
    (hx : ValidMask n r x) (hlast : x ≠ lastMask n r) :
    0 < lowBit64 x ∧ x + lowBit64 x < 2^64 ∧
    ValidMask n r (gosperRaw x) ∧ x < gosperRaw x ∧
    ∀ y, ValidMask n r y → x < y → gosperRaw x ≤ y := by
  have hpos : 0<x := by
    by_contra h
    have he : x=0 := by omega
    have hw := hx.2
    rw [he,weight_zero] at hw
    omega
  obtain ⟨A,z,t,ht,rfl⟩ := exists_run x hpos
  have hwidth := run_width n A z t ht hx.1
  have hproper : z+t+1≤n := by
    by_contra h
    have he : z+t=n := by omega
    exact hlast (terminal_of_full_run n r A z t ht hx he)
  have h64 : runMask A z t < 2^64 :=
    lt_of_lt_of_le hx.1 (Nat.pow_le_pow_right (by decide) hn)
  obtain ⟨hnext,hweight,hgt⟩ := run_successor_valid n A z t ht hx.1 hproper
  rw [run_lowbit A z t ht h64,gosper_run A z t ht h64]
  refine ⟨Nat.two_pow_pos z,?_,⟨hnext,hweight.trans hx.2⟩,hgt,?_⟩
  · rw [run_add_lowbit]
    have hc : carryMask A z t ≤ nextMask A z t := Nat.le_add_right _ _
    exact lt_of_le_of_lt hc (lt_of_lt_of_le hnext (Nat.pow_le_pow_right (by decide) hn))
  · intro y hy hxy
    exact run_successor_minimal n A z t y ht hproper hxy (hy.2.trans hx.2.symm)

private theorem step_valid (n r : ℕ) (hn : n≤64) (hr : 0<r) (hrn : r≤n)
    (x : ℕ) (hx : ValidMask n r x) : ValidMask n r (gosperStep n r x) := by
  by_cases he : x=lastMask n r
  · simpa [gosperStep,he] using hx
  · simpa [gosperStep,he] using (update_successor n r x hn hr hrn hx he).2.2.1

/-- Every fixed-population mask occurs exactly once before the terminal mask. -/
theorem traversal_complete (n r : ℕ) (hn : n ≤ 64) (hr : 0 < r) (hrn : r ≤ n) :
    (∀ x, ValidMask n r x ↔ ∃ j < Nat.choose n r,
      (gosperStep n r)^[j] (firstMask r) = x) ∧
    (gosperStep n r)^[Nat.choose n r-1] (firstMask r) = lastMask n r ∧
    StrictMonoOn (fun j => (gosperStep n r)^[j] (firstMask r)) (Set.Iio (Nat.choose n r)) := by
  classical
  let lift : (x : ℕ) → ValidMask n r x → GosperStates.State n r :=
    fun x hx => ⟨⟨x,hx.1⟩,hx.2⟩
  let value : GosperStates.State n r → ℕ := fun x => x.val.val
  have valid (x : GosperStates.State n r) : ValidMask n r (value x) := ⟨x.val.isLt,x.property⟩
  let next : GosperStates.State n r → GosperStates.State n r := fun x =>
    lift (gosperStep n r (value x)) (step_valid n r hn hr hrn _ (valid x))
  let first := lift (firstMask r) (GosperStates.first_valid n r hrn)
  let last := lift (lastMask n r) (GosperStates.last_valid n r hrn)
  have hc := GosperStates.state_card n r
  have hf : ∀ a : GosperStates.State n r, first≤a := by
    intro a
    have h := least_mask n (value a) a.val.isLt
    change firstMask r≤value a
    simpa [firstMask,a.property,value] using h
  have hl : ∀ a : GosperStates.State n r, a≤last := by
    intro a
    have h := greatest_mask n (value a) a.val.isLt
    change value a≤lastMask n r
    simpa [lastMask,a.property,value] using h
  have hs (a b : GosperStates.State n r) (hab : a<b) : a<next a ∧ next a≤b := by
    have hlast : value a≠lastMask n r := by
      intro he
      have hmax := hl b
      change value b≤lastMask n r at hmax
      change value a<value b at hab
      omega
    have h := update_successor n r (value a) hn hr hrn (valid a) hlast
    constructor
    · change value a<gosperStep n r (value a)
      simpa [gosperStep,hlast] using h.2.2.2.1
    · change gosperStep n r (value a)≤value b
      simpa [gosperStep,hlast] using h.2.2.2.2 (value b) (valid b) hab
  have hiter (j : ℕ) : value (next^[j] first)=(gosperStep n r)^[j] (firstMask r) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      change gosperStep n r (value (next^[j] first))=_
      rw [ih]
  obtain ⟨hcover,hlast,hstrict⟩ := Crown.FiniteTraversal.complete_bounded next hs first last hf hl
  refine ⟨?_,?_,?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨j,hj,he⟩ := hcover (lift x hx)
      exact ⟨j,by simpa [hc] using hj,by simpa [hiter,lift,value] using congrArg value he⟩
    · rintro ⟨j,hj,rfl⟩
      rw [←hiter]
      exact valid _
  · simpa [hc,hiter,last,lift,value] using congrArg value hlast
  · intro i hi j hj hij
    have h := hstrict (by simpa [hc] using hi) (by simpa [hc] using hj) hij
    change value (next^[i] first)<value (next^[j] first) at h
    simpa [hiter] using h

#print axioms traversal_complete
#print axioms update_successor
end Crown.GosperTraversal
