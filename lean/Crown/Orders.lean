import Crown.Ranks
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.ByContra

namespace Crown.Orders

open scoped BigOperators

variable {V : Type*} [Fintype V]

noncomputable def enumeration : List V := (Finset.univ : Finset V).toList

theorem mem_enumeration (b : V) : b ∈ enumeration (V := V) := by
  simp [enumeration]

theorem enumeration_nodup : (enumeration (V := V)).Nodup := Finset.nodup_toList _

noncomputable def sortByKey {K : Type*} [LinearOrder K] (key : V → K) : List V :=
  (enumeration (V := V)).mergeSort (fun b c => key b ≤ key c)

theorem sortByKey_perm {K : Type*} [LinearOrder K] (key : V → K) :
    (sortByKey key).Perm enumeration := List.mergeSort_perm _ _

theorem sortByKey_nodup {K : Type*} [LinearOrder K] (key : V → K) :
    (sortByKey key).Nodup := (sortByKey_perm key).nodup_iff.mpr enumeration_nodup

theorem mem_sortByKey {K : Type*} [LinearOrder K] (key : V → K) (b : V) :
    b ∈ sortByKey key := (sortByKey_perm key).mem_iff.mpr (mem_enumeration b)

theorem sortByKey_pairwise {K : Type*} [LinearOrder K] (key : V → K) :
    (sortByKey key).Pairwise (fun b c => key b ≤ key c) := by
  let rel : V → V → Prop := fun b c => key b ≤ key c
  let : IsTrans V rel := ⟨fun _ _ _ => le_trans⟩
  let : Std.Total rel := ⟨fun _ _ => le_total _ _⟩
  exact List.pairwise_mergeSort' rel enumeration

variable [DecidableEq V]

def Before (l : List V) (b c : V) : Prop := l.idxOf b < l.idxOf c

theorem key_le_of_before {K : Type*} [LinearOrder K] (key : V → K)
    (h : Before (sortByKey key) b c) : key b ≤ key c := by
  have hb := List.idxOf_lt_length_iff.mpr (mem_sortByKey key b)
  have hc := List.idxOf_lt_length_iff.mpr (mem_sortByKey key c)
  have hs := List.pairwise_iff_getElem.mp (sortByKey_pairwise key)
    _ _ hb hc h
  simpa using hs

omit [Fintype V] in
theorem before_or_before (l : List V) (hb : b ∈ l) (_hc : c ∈ l) (hbc : b ≠ c) :
    Before l b c ∨ Before l c b := by
  have hn : l.idxOf b ≠ l.idxOf c := fun h => hbc ((List.idxOf_inj hb).mp h)
  exact lt_or_gt_of_ne hn

variable {k : ℕ}

def rankSum (r : V → Ranks.CompletedRow (Fin k)) (b : V) : ℕ :=
  ∑ i, (r b i).val

noncomputable def firstKey (r : V → Ranks.CompletedRow (Fin k)) (z : Fin k) (b : V) :
    ℕ ×ₗ (ℕᵒᵈ ×ₗ ℕ) :=
  toLex ((r b z).val, toLex (OrderDual.toDual (rankSum r b), enumeration.idxOf b))

noncomputable def firstOrder (r : V → Ranks.CompletedRow (Fin k)) (z : Fin k) : List V :=
  sortByKey (firstKey r z)

noncomputable def laterKey (r : V → Ranks.CompletedRow (Fin k))
    (z i : Fin k) (b : V) : ℕ ×ₗ ℕᵒᵈ :=
  toLex ((r b i).val, OrderDual.toDual ((firstOrder r z).idxOf b))

noncomputable def orders (r : V → Ranks.CompletedRow (Fin k)) (z i : Fin k) : List V :=
  if i = z then firstOrder r z else sortByKey (laterKey r z i)

theorem orders_nodup (r : V → Ranks.CompletedRow (Fin k)) (z i : Fin k) :
    (orders r z i).Nodup := by
  unfold orders firstOrder
  split <;> apply sortByKey_nodup

theorem mem_orders (r : V → Ranks.CompletedRow (Fin k)) (z i : Fin k) (b : V) :
    b ∈ orders r z i := by
  unfold orders firstOrder
  split <;> apply mem_sortByKey

theorem first_key_consequences (r : V → Ranks.CompletedRow (Fin k)) (z : Fin k)
    (h : Before (firstOrder r z) b c) :
    (r b z).val ≤ (r c z).val ∧
      ((r b z).val = (r c z).val → rankSum r c ≤ rankSum r b) := by
  have hh := key_le_of_before (firstKey r z) h
  have hh' := Prod.Lex.toLex_le_toLex'.mp hh
  refine ⟨hh'.1, ?_⟩
  intro he
  have hh'' := Prod.Lex.toLex_le_toLex'.mp (hh'.2 he)
  exact hh''.1

theorem later_key_consequences (r : V → Ranks.CompletedRow (Fin k)) (z i : Fin k)
    (h : Before (sortByKey (laterKey r z i)) b c) :
    (r b i).val ≤ (r c i).val ∧
      ((r b i).val = (r c i).val →
        (firstOrder r z).idxOf c ≤ (firstOrder r z).idxOf b) := by
  exact Prod.Lex.toLex_le_toLex'.mp (key_le_of_before (laterKey r z i) h)

theorem coordinate_mono (r : V → Ranks.CompletedRow (Fin k)) (z i : Fin k)
    (h : Before (orders r z i) b c) : r b i ≤ r c i := by
  by_cases hi : i = z
  · subst i
    have h' : Before (firstOrder r z) b c := by simpa [orders] using h
    exact (first_key_consequences r z h').1
  · have h' : Before (sortByKey (laterKey r z i)) b c := by
      simpa [orders, hi] using h
    exact (later_key_consequences r z i h').1

/-- Constant relative order in all constructed permutations forces a strict
all-coordinate comparison. The strict sum argument needs a second coordinate. -/
theorem all_before_strict (hk : 2 ≤ k) (r : V → Ranks.CompletedRow (Fin k))
    (z : Fin k) (h : ∀ i, Before (orders r z i) b c) : Ranks.StrictBelow (r b) (r c) := by
  have hz : Before (firstOrder r z) b c := by simpa [orders] using h z
  have hle : ∀ i, (r b i).val ≤ (r c i).val := fun i => coordinate_mono r z i (h i)
  have hstrict : ∀ i, i ≠ z → (r b i).val < (r c i).val := by
    intro i hi
    have h' : Before (sortByKey (laterKey r z i)) b c := by
      simpa [orders, hi] using h i
    have he := (later_key_consequences r z i h').2
    change (firstOrder r z).idxOf b < (firstOrder r z).idxOf c at hz
    have hneq : (r b i).val ≠ (r c i).val := fun hh => (not_le_of_gt hz) (he hh)
    exact lt_of_le_of_ne (hle i) hneq
  have hzlt : (r b z).val < (r c z).val := by
    have hneq : (r b z).val ≠ (r c z).val := by
      intro he
      have hsumle := (first_key_consequences r z hz).2 he
      have hother : ∃ i : Fin k, i ≠ z := by
        by_cases hz0 : z = ⟨0, by omega⟩
        · exact ⟨⟨1, by omega⟩, by rw [hz0]; simp [Fin.ext_iff]⟩
        · exact ⟨⟨0, by omega⟩, Ne.symm hz0⟩
      obtain ⟨i, hi⟩ := hother
      have hsumlt : rankSum r b < rankSum r c :=
        Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hstrict i hi⟩
      exact (not_le_of_gt hsumlt) hsumle
    exact lt_of_le_of_ne (hle z) hneq
  intro i
  by_cases hi : i = z
  · simpa [hi] using hzlt
  · exact hstrict i hi

/-- L04: actual permutations, nondecreasing in their own coordinates, with both
relative orders for each distinct pair. -/
theorem coordinate_orders (hk : 2 ≤ k) (r : V → Ranks.CompletedRow (Fin k))
    (hn : ∀ b c, b ≠ c → ¬ Ranks.StrictBelow (r b) (r c)) :
    ∃ π : Fin k → List V,
      (∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i) ∧
      (∀ i b c, Before (π i) b c → r b i ≤ r c i) ∧
      ∀ b c, b ≠ c → (∃ i, Before (π i) b c) ∧ (∃ i, Before (π i) c b) := by
  classical
  let z : Fin k := ⟨0, by omega⟩
  refine ⟨orders r z, fun i => ⟨orders_nodup r z i, mem_orders r z i⟩,
    fun i b c h => coordinate_mono r z i h, ?_⟩
  have hex : ∀ b c, b ≠ c → ∃ i, Before (orders r z i) b c := by
    intro b c hbc
    by_contra! hnone
    have hall : ∀ i, Before (orders r z i) c b := by
      intro i
      exact (before_or_before _ (mem_orders r z i b) (mem_orders r z i c) hbc).resolve_left
        (hnone i)
    exact hn c b (Ne.symm hbc) (all_before_strict hk r z hall)
  intro b c hbc
  exact ⟨hex b c hbc, hex c b (Ne.symm hbc)⟩

/-- A feasible initial rank family supplies all rank and permutation data used
by the block construction, without an extra ordering hypothesis. -/
theorem feasible_coordinate_orders (hk : 2 ≤ k)
    (rows : V → Ranks.InitialRow (Fin k)) (hf : Ranks.Feasible rows) :
    ∃ (r : V → Ranks.CompletedRow (Fin k)) (π : Fin k → List V),
      (∀ b, Ranks.Completes (rows b) (r b)) ∧
      (∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i) ∧
      (∀ i b c, Before (π i) b c → r b i ≤ r c i) ∧
      ∀ b c, b ≠ c → (∃ i, Before (π i) b c) ∧ (∃ i, Before (π i) c b) := by
  obtain ⟨r, hr, hn⟩ := hf
  obtain ⟨π, hπ, hm, hb⟩ := coordinate_orders hk r (fun b c _ => hn b c)
  exact ⟨r, π, hr, hπ, hm, hb⟩

#print axioms coordinate_orders
#print axioms feasible_coordinate_orders

end Crown.Orders
