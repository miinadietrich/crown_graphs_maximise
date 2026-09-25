import Crown.Cyclic
import Mathlib.Data.List.Nodup
import Mathlib.Combinatorics.SimpleGraph.Sum

/-! Literal concatenation of two-uniform representations of disjoint graphs.
The disjoint sum is Mathlib's SimpleGraph.sum (Ivan Renison, Apache-2.0). -/
namespace Crown
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

local instance : BEq (V ⊕ W) := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq (V ⊕ W) where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

private theorem restriction_sum_left (u : List V) (v : List W) (a b : V) :
    restrictPair (u.map Sum.inl ++ v.map Sum.inr) (Sum.inl a) (Sum.inl b) =
      (restrictPair u a b).map Sum.inl := by
  rw [restrictPair_append,restrictPair_map Sum.inl Sum.inl_injective]
  simp [restrictPair,List.filter_map,Function.comp_def]

private theorem restriction_sum_right (u : List V) (v : List W) (a b : W) :
    restrictPair (u.map Sum.inl ++ v.map Sum.inr) (Sum.inr a) (Sum.inr b) =
      (restrictPair v a b).map Sum.inr := by
  rw [restrictPair_append,restrictPair_map Sum.inr Sum.inr_injective]
  simp [restrictPair,List.filter_map,Function.comp_def]

private theorem restriction_sum_cross (u : List V) (v : List W) (a : V) (b : W) :
    restrictPair (u.map Sum.inl ++ v.map Sum.inr) (Sum.inl a) (Sum.inr b) =
      List.replicate (u.count a) (Sum.inl a) ++ List.replicate (v.count b) (Sum.inr b) := by
  simp [restrictPair,List.filter_append,List.filter_map,Function.comp_def,List.filter_eq]

/-- Concatenation retains all within-component adjacencies and separates every
pair of vertices from different components. -/
theorem represents_sum_two {G : SimpleGraph V} {H : SimpleGraph W}
    {u : List V} {v : List W} (hu : Represents G 2 u) (hv : Represents H 2 v) :
    Represents (G.sum H) 2 (u.map Sum.inl ++ v.map Sum.inr) := by
  have count_left_zero (a : V) : (v.map (Sum.inr : W → V ⊕ W)).count (.inl a) = 0 := by
    simp [List.count_eq_zero]
  have count_right_zero (b : W) : (u.map (Sum.inl : V → V ⊕ W)).count (.inr b) = 0 := by
    simp [List.count_eq_zero]
  refine ⟨by decide,?_,?_⟩
  · intro x
    cases x with
    | inl a =>
      rw [List.count_append,List.count_map_of_injective _ _ Sum.inl_injective,
        count_left_zero,Nat.add_zero]
      exact hu.2.1 a
    | inr b =>
      rw [List.count_append,count_right_zero,Nat.zero_add,
        List.count_map_of_injective _ _ Sum.inr_injective]
      exact hv.2.1 b
  · intro x y hxy
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        rw [show (G.sum H).Adj (.inl a) (.inl b) ↔ G.Adj a b from Iff.rfl]
        rw [Alternates,restriction_sum_left,List.isChain_map]
        simpa only [ne_eq,Sum.inl.injEq,Alternates] using hu.2.2 a b (fun h => hxy (congrArg Sum.inl h))
      | inr b =>
        simp only [SimpleGraph.sum, Bool.false_eq_true]
        rw [Alternates,restriction_sum_cross,hu.2.1,hv.2.1]
        simp
    | inr a =>
      cases y with
      | inl b =>
        simp only [SimpleGraph.sum, Bool.false_eq_true]
        rw [alternates_comm,Alternates,restriction_sum_cross,hu.2.1,hv.2.1]
        simp
      | inr b =>
        rw [show (G.sum H).Adj (.inr a) (.inr b) ↔ H.Adj a b from Iff.rfl]
        rw [Alternates,restriction_sum_right,List.isChain_map]
        simpa only [ne_eq,Sum.inr.injEq,Alternates] using hv.2.2 a b (fun h => hxy (congrArg Sum.inr h))

#print axioms represents_sum_two
/-- Repeating any permutation represents the complete graph with multiplicity two. -/
theorem represents_complete_twice (l : List V) (hl : l.Nodup) (hall : ∀ a, a ∈ l) :
    Represents (⊤ : SimpleGraph V) 2 (l ++ l) := by
  have hc (a : V) : l.count a = 1 := List.count_eq_one_of_mem hl (hall a)
  refine ⟨by decide,?_,?_⟩
  · intro a
    simp [List.count_append,hc a]
  · intro a b hab
    have hh : (restrictPair l a b).IsChain (· ≠ ·) := (hl.filter _).isChain
    have he : (restrictPair l a b).count a = (restrictPair l a b).count b := by
      simp [restrictPair,List.count_filter,hc]
    have hend := balanced_chain_endpoints a b hab (restrictPair l a b)
      (fun x hx => by simpa [restrictPair] using (List.mem_filter.mp hx).2) he hh
    have ha : Alternates (l ++ l) a b := by
      rw [Alternates,restrictPair_append]
      exact hh.append hh (fun x hx y hy => Ne.symm (hend y hy x hx))
    exact ⟨fun _ => ha,fun _ => hab⟩

#print axioms represents_complete_twice
end Crown
