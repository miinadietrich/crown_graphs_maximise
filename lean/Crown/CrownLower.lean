import Crown.CrownLowerEndpoints

/-! The general crown lower bound of Glen--Kitaev--Pyatkin, reconstructed
from actual uniform words. The only axioms used are Lean's standard logical
axioms; no lower-bound result is imported as an assumption. -/

namespace Crown.CrownLower

local instance {n : ℕ} : BEq (Bool × Fin n) := ⟨fun a b => decide (a = b)⟩
local instance {n : ℕ} : LawfulBEq (Bool × Fin n) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

theorem crown_size_le_twice_multiplicity {n k : ℕ} (hn : 5 ≤ n)
    (w : List (Bool × Fin n)) (hw : Crown.Represents (Crown.crownGraph n) k w) : n ≤ 2*k := by
  classical
  obtain ⟨w',hw',hsplit⟩ := exists_full_side_split hn w hw
  have hA : (leftSide n).Nonempty := ⟨(false,⟨0,by omega⟩),rfl⟩
  obtain ⟨D,hDrep,hDlen,hDgood⟩ := canonical_representation hw' (leftSide n) hA hsplit
  let E : List (Fin n) := (endpointLetters D).map Prod.snd
  have hcover : ∀ i : Fin n, i ∈ E := by
    intro i
    obtain ⟨d,hd,hi⟩ := endpoint_coverage (by omega) D hDrep hDlen hDgood i
    exact List.mem_map.mpr ⟨(false,i),endpointLetters_mem D d hd (false,i) hi,rfl⟩
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ E.toFinset := by
    intro i hi
    exact List.mem_toFinset.mpr (hcover i)
  calc
    n = (Finset.univ : Finset (Fin n)).card := by simp
    _ ≤ E.toFinset.card := Finset.card_le_card hsub
    _ ≤ E.length := List.toFinset_card_le E
    _ = (endpointLetters D).length := List.length_map Prod.snd
    _ ≤ 2 * D.length := endpointLetters_length D
    _ = 2*k := by rw [hDlen]

theorem halfCeil_le_of_kRepresentable {n k : ℕ} (hn : 5 ≤ n)
    (h : Crown.KRepresentable (Crown.crownGraph n) k) : Crown.halfCeil n ≤ k := by
  obtain ⟨w,hw⟩ := h
  have hh := crown_size_le_twice_multiplicity hn w hw
  unfold Crown.halfCeil
  omega

theorem halfCeil_le_representationNumber {n : ℕ} (hn : 5 ≤ n)
    (h : Crown.Representable (Crown.crownGraph n)) :
    Crown.halfCeil n ≤ Crown.representationNumber (Crown.crownGraph n) :=
  halfCeil_le_of_kRepresentable hn (Crown.representationNumber_spec h)

#print axioms crown_size_le_twice_multiplicity
#print axioms halfCeil_le_of_kRepresentable
#print axioms halfCeil_le_representationNumber

end Crown.CrownLower
