import Crown.CrownLowerCapacity
import Crown.CrownLowerAllocation

namespace Crown.CrownLower

local instance {n : ℕ} : BEq (Bool × Fin n) := ⟨fun a b => decide (a = b)⟩
local instance {n : ℕ} : LawfulBEq (Bool × Fin n) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

def leftSide (n : ℕ) : Set (Bool × Fin n) := {v | v.1 = false}
instance {n : ℕ} : DecidablePred (· ∈ leftSide n) :=
  fun v => inferInstanceAs (Decidable (v.1 = false))

def projectBlock {n : ℕ} (z : Fin n)
    (d : List (Bool × Fin n) × List (Bool × Fin n)) : List (Bool × Fin n) × ℕ :=
  (d.1.filter (fun v => v.1 = false),d.2.count (false,z))

theorem filter_left_except {n : ℕ} (z : Fin n) (l : List (Bool × Fin n)) :
    (l.filter (fun v => v.1 = false)).filter (fun v => v ≠ (false,z)) =
      l.filter (fun v => v ∈ leftExcept z) := by
  rw [List.filter_filter]
  apply List.filter_congr
  rintro ⟨b,i⟩ hi
  cases b <;> simp [leftExcept]

theorem filter_left_gap {n : ℕ} (z : Fin n) (l : List (Bool × Fin n))
    (hl : l.filter (fun v => v ∈ leftExcept z) = []) :
    l.filter (fun v => v.1 = false) = List.replicate (l.count (false,z)) (false,z) := by
  have hmem : ∀ v ∈ l.filter (fun v => v.1 = false), v = (false,z) := by
    intro v hv
    obtain ⟨hvl,hvf⟩ := List.mem_filter.mp hv
    have hvf' : v.1 = false := by simpa using hvf
    have hvz : v.2 = z := by
      by_contra hn
      have : v ∈ l.filter (fun v => v ∈ leftExcept z) := List.mem_filter.mpr ⟨hvl,decide_eq_true (show v ∈ leftExcept z from ⟨hvf',hn⟩)⟩
      simpa [hl] using this
    exact Prod.ext hvf' hvz
  have he := List.eq_replicate_of_mem hmem
  have hc := congrArg (List.count (false,z)) he
  simp only [List.count_replicate_self] at hc
  rw [List.count_filter (p := fun v : Bool × Fin n => decide (v.1 = false)) (by simp)] at hc
  exact he.trans (congrArg (fun t => List.replicate t (false,z)) hc.symm)

theorem allocationWord_project {n : ℕ} (z : Fin n)
    (D : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hD : ∀ d ∈ D, GoodBlock (leftExcept z) d) :
    allocationWord (false,z) (D.map (projectBlock z)) =
      (blockWord D).filter (fun v => v.1 = false) := by
  induction D with
  | nil => simp [blockWord]
  | cons d D ih =>
    have hd := hD d (by simp)
    have ht := ih (fun d hd => hD d (by simp [hd]))
    simp only [List.map_cons,allocationWord_cons,projectBlock,blockWord,List.flatMap_cons,
      List.filter_append] at ht ⊢
    rw [← ht,filter_left_gap z d.2 hd.2.1]

def blockWeight {V : Type*} [DecidableEq V] (z : V) (d : List V × List V) : ℤ :=
  ((d.1 ++ d.2).count z : ℤ) - 1

theorem weightSum_blockWeight {V : Type*} [DecidableEq V] (z : V)
    (D : List (List V × List V)) :
    weightSum (blockWeight z) D = ((blockWord D).count z : ℤ) - D.length := by
  induction D with
  | nil => simp [blockWord]
  | cons d D ih =>
    simp only [weightSum_cons,blockWeight,blockWord,List.flatMap_cons,List.count_append,
      List.length_cons,Nat.cast_add,Nat.cast_one] at ih ⊢
    rw [ih]
    omega

theorem closed_prefix_capacity {n k : ℕ} (hn : 5 ≤ n) (z : Fin n)
    (P : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (d : List (Bool × Fin n) × List (Bool × Fin n))
    (R : List (List (Bool × Fin n) × List (Bool × Fin n)))
    (hr : Crown.Represents (Crown.crownGraph n) k (blockWord (P++d::R)))
    (hD : ∀ e ∈ P++d::R, GoodBlock (leftExcept z) e) :
    (blockWord P ++ d.1).count (false,z) ≤ P.length + 1 := by
  cases P with
  | nil => simpa [blockWord] using core_missing_count_le_one (by omega) z d R hr hD
  | cons e T =>
    simpa only [List.length_cons,Nat.add_assoc] using
      prefix_span_missing_count_le hn z e d T R hr hD

#print axioms allocationWord_project
#print axioms closed_prefix_capacity

end Crown.CrownLower
