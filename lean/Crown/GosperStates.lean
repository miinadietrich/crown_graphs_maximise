import Crown.GosperWeight
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fintype.Powerset

/-! Exact fixed-population state cardinality. Reuses the binary-expansion
bijection in Mathlib.Combinatorics.Colex (Bhavik Mehta, Alena Gusakov,
Yaël Dillies) and Nat.bitIndices (Peter Nelson), at the pinned revision.
The finite type below is used symbolically, never enumerated. -/
set_option Elab.async false

namespace Crown.GosperStates
open Crown.EnumeratorDefinitions Crown.GosperWeight
open scoped BigOperators

abbrev State (n r : ℕ) := {x : Fin (2^n) // weight n x.val = r}
abbrev Families (n r : ℕ) := {s : Finset ℕ // s ∈ (Finset.range n).powersetCard r}

theorem bits_eq_filter (n x : ℕ) (hx : x<2^n) :
    x.bitIndices.toFinset = (Finset.range n).filter (fun i => x.testBit i=true) := by
  ext i
  simp only [List.mem_toFinset,Nat.mem_bitIndices,Finset.mem_filter,Finset.mem_range]
  constructor
  · intro hi
    refine ⟨?_,hi⟩
    have hp := Nat.ge_two_pow_of_testBit hi
    by_contra h
    have hh : 2^n≤2^i := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · exact fun h => h.2

theorem bits_subset (n x : ℕ) (hx : x<2^n) :
    x.bitIndices.toFinset ⊆ Finset.range n := by
  rw [bits_eq_filter n x hx]
  exact Finset.filter_subset _ _

theorem encode_lt (n : ℕ) (s : Finset ℕ) (hs : s⊆Finset.range n) :
    (∑ i ∈ s,2^i) < 2^n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_cases hb : (∑ j ∈ s,2^j).testBit i=true
  · have hm : i ∈ (∑ j ∈ s,2^j).bitIndices.toFinset :=
      List.mem_toFinset.mpr (Nat.mem_bitIndices.mpr hb)
    rw [Finset.toFinset_bitIndices_sum_two_pow] at hm
    have hlt := Finset.mem_range.mp (hs hm)
    omega
  · cases he : (∑ j ∈ s,2^j).testBit i <;> simp_all

noncomputable def familyEquiv (n r : ℕ) : State n r ≃ Families n r where
  toFun x := ⟨x.val.val.bitIndices.toFinset,Finset.mem_powersetCard.mpr ⟨bits_subset n _ x.val.isLt,by
    rw [bits_eq_filter n _ x.val.isLt]
    exact x.property⟩⟩
  invFun s := ⟨⟨∑ i ∈ s.val,2^i,encode_lt n s.val (Finset.mem_powersetCard.mp s.property).1⟩,by
    change weight n (∑ i ∈ s.val,2^i)=r
    unfold weight
    rw [←bits_eq_filter n _ (encode_lt n s.val (Finset.mem_powersetCard.mp s.property).1),
      Finset.toFinset_bitIndices_sum_two_pow]
    exact (Finset.mem_powersetCard.mp s.property).2⟩
  left_inv x := by
    apply Subtype.ext
    apply Fin.ext
    exact Finset.sum_toFinset_bitIndices_two_pow x.val.val
  right_inv s := by
    apply Subtype.ext
    exact Finset.toFinset_bitIndices_sum_two_pow s.val

theorem state_card (n r : ℕ) : Fintype.card (State n r)=Nat.choose n r := by
  rw [Fintype.card_congr (familyEquiv n r),Fintype.card_coe,Finset.card_powersetCard,
    Finset.card_range]

theorem first_valid (n r : ℕ) (hrn : r≤n) : ValidMask n r (firstMask r) := by
  constructor
  · have hp := Nat.two_pow_pos r
    have hh : 2^r≤2^n := Nat.pow_le_pow_right (by decide) hrn
    unfold firstMask
    omega
  · simpa [firstMask,weight_ones,Nat.min_eq_right hrn]

theorem last_valid (n r : ℕ) (hrn : r≤n) : ValidMask n r (lastMask n r) := by
  have he : n=(n-r)+r := by omega
  have hp := Nat.two_pow_pos r
  have hp' := Nat.two_pow_pos (n-r)
  have hpow : 2^n=2^(n-r)*2^r := by
    conv_lhs => arg 2; rw [he]
    rw [pow_add]
  constructor
  · unfold lastMask
    rw [hpow]
    calc
      (2^r-1)*2^(n-r) < 2^r*2^(n-r) :=
        Nat.mul_lt_mul_of_pos_right (by omega) hp'
      _ = 2^(n-r)*2^r := Nat.mul_comm _ _
  · unfold lastMask
    have h := weight_concat (n-r) r (2^r-1) 0 hp'
    simpa [weight_zero,weight_ones,←he,Nat.mul_comm] using h
#print axioms state_card
#print axioms first_valid
#print axioms last_valid
end Crown.GosperStates
