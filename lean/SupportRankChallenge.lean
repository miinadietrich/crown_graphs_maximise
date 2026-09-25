import Specification.BlockDefinitions
import Specification.MatrixDefinitions
import Specification.OddDefinitions
import Specification.SmallGraphDefinitions
import Specification.UnorderedDefinitions

namespace Crown.Ranks
universe u v w
variable {I : Type u} {V : Type v} {X : Type w}

-- Source statement: Crown/Ranks.lean:390
theorem feasible_iff_distinct [Nonempty I] (rows : V → InitialRow I) :
    Feasible rows ↔ ∃ r : V → CompletedRow I,
      (∀ b, Completes (rows b) (r b)) ∧
        ∀ b c, b ≠ c → ¬ StrictBelow (r b) (r c) := by
  sorry

-- Source statement: Crown/Ranks.lean:66
theorem completeEntry_lt_iff :
    ∀ (a b : Option (Fin 3)) (t u : Bool),
      completeEntry a t < completeEntry b u ↔
        PotentialEntry a b ∧ (a = none → t = false) ∧
          (b = none → u = true) := by
  sorry

-- Source statement: Crown/Ranks.lean:182
theorem multiStar_completion (ρ : InitialRow I) (h : MultiStar ρ) :
    ∃ r : CompletedRow I, Completes ρ r ∧
      ∀ s : CompletedRow I, ¬ StrictBelow r s ∧ ¬ StrictBelow s r := by
  sorry

-- Source statement: Crown/Ranks.lean:421
theorem feasible_iff_constraints (rows : V → InitialRow I) :
    Feasible rows ↔ NoFixedPair rows ∧
      ∃ t, ValidChoice (DirectOne rows) (DirectZero rows) (Implies rows) t := by
  sorry

-- Source statement: Crown/Ranks.lean:319
theorem choice_exists_iff (one zero : X → Prop) (edge : X → X → Prop) :
    (∃ t, ValidChoice one zero edge t) ↔
      ¬ ∃ x, Forced one edge x ∧ zero x := by
  sorry

-- Source statement: Crown/Ranks.lean:488
theorem feasible_iff_no_obstructions (hk : 4 ≤ k) (rows : V → InitialRow (Fin k)) :
    Feasible rows ↔ NoFixedPair rows ∧
      ¬ ∃ b, DirectOne rows b ∧ DirectZero rows b := by
  sorry

-- Source statement: Crown/Ranks.lean:495
theorem central_triple_values (l c u : InitialRow I) (j : I)
    (hl : Fixed l) (hc : OneStar c) (hu : Fixed u) (hj : c j = none)
    (hlc : PotentialBelow l c) (hcu : PotentialBelow c u) :
    ∀ i, i ≠ j → l i = some 0 ∧ c i = some 1 ∧ u i = some 2 := by
  sorry

-- Source statement: Crown/Ranks.lean:262
theorem no_fixed_three_star_chain (hk : 4 ≤ k)
    (a b c d : InitialRow (Fin k)) (ha : Fixed a)
    (hb : OneStar b) (hc : OneStar c) (hd : OneStar d)
    (hab : PotentialBelow a b) (hbc : PotentialBelow b c)
    (hcd : PotentialBelow c d) : False := by
  sorry

-- Source statement: Crown/Ranks.lean:276
theorem no_fixed_two_star_fixed_chain (hk : 4 ≤ k)
    (a b c d : InitialRow (Fin k)) (ha : Fixed a)
    (hb : OneStar b) (hc : OneStar c) (hd : Fixed d)
    (hab : PotentialBelow a b) (hbc : PotentialBelow b c)
    (hcd : PotentialBelow c d) : False := by
  sorry

end Crown.Ranks

namespace Crown.Orders
variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

-- Source statement: Crown/Orders.lean:163
theorem coordinate_orders (hk : 2 ≤ k) (r : V → Ranks.CompletedRow (Fin k))
    (hn : ∀ b c, b ≠ c → ¬ Ranks.StrictBelow (r b) (r c)) :
    ∃ π : Fin k → List V,
      (∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i) ∧
      (∀ i b c, Before (π i) b c → r b i ≤ r c i) ∧
      ∀ b c, b ≠ c → (∃ i, Before (π i) b c) ∧ (∃ i, Before (π i) c b) := by
  sorry

-- Source statement: Crown/Orders.lean:91
theorem orders_nodup (r : V → Ranks.CompletedRow (Fin k)) (z i : Fin k) :
    (orders r z i).Nodup := by
  sorry

-- Source statement: Crown/Orders.lean:96
theorem mem_orders (r : V → Ranks.CompletedRow (Fin k)) (z i : Fin k) (b : V) :
    b ∈ orders r z i := by
  sorry

-- Source statement: Crown/Orders.lean:119
theorem coordinate_mono (r : V → Ranks.CompletedRow (Fin k)) (z i : Fin k)
    (h : Before (orders r z i) b c) : r b i ≤ r c i := by
  sorry

-- Source statement: Crown/Orders.lean:131
theorem all_before_strict (hk : 2 ≤ k) (r : V → Ranks.CompletedRow (Fin k))
    (z : Fin k) (h : ∀ i, Before (orders r z i) b c) : Ranks.StrictBelow (r b) (r c) := by
  sorry

end Crown.Orders

namespace Crown.Blocks
variable {k : ℕ} {B : Type*} [DecidableEq B]
local instance : BEq (Alphabet k B) := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq (Alphabet k B) where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

-- Source statement: Crown/Blocks.lean:493
theorem restrict_block_cross (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (i j : Fin k) (side : Bool) (b : B) (hb : (π j).count b = 1) :
    Crown.restrictPair (block r π j) (Sum.inl (i, side)) (Sum.inr b) =
      if j = i then crossLocal (r b i) side (Sum.inl (i, side)) (Sum.inr b)
      else [Sum.inr b] := by
  sorry

-- Source statement: Crown/Blocks.lean:644
theorem word_represents_rankGraph (hk : 3 ≤ k)
    (r : B → Ranks.CompletedRow (Fin k)) (π : Fin k → List B)
    (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i)
    (hm : ∀ i b c, Orders.Before (π i) b c → r b i ≤ r c i)
    (ho : ∀ b c, b ≠ c → (∃ i, Orders.Before (π i) b c) ∧
      (∃ i, Orders.Before (π i) c b)) :
    Crown.Represents (rankGraph r) k (word r π) := by
  sorry

-- Source statement: Crown/Blocks.lean:709
theorem feasible_representable [Fintype B] (hk : 3 ≤ k)
    (rows : B → Ranks.InitialRow (Fin k)) (hf : Ranks.Feasible rows) :
    Crown.KRepresentable (initialRankGraph rows) k := by
  sorry

end Crown.Blocks

namespace Crown.Baseline
variable {B : Type*}

theorem matrix_representable [Fintype B] [DecidableEq B] (k : ℕ) (hk : 2 ≤ k)
    (M : Fin (2 * k) → B → Bool) :
    Crown.KRepresentable (BalancedLarge.matrixGraph M) (k + 1) := by
  sorry

end Crown.Baseline

namespace Crown.BaselineLiteral
open Crown.Blocks
variable {k : ℕ} {B : Type*} [DecidableEq B]
local instance : BEq (Alphabet k B) := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq (Alphabet k B) where
  eq_of_beq := of_decide_eq_true
  rfl := by simp

-- Source statement: Crown/BaselineLiteral.lean:365
theorem word_represents_initialRankGraph (hk : 2 ≤ k)
    (rows : B → Ranks.InitialRow (Fin k)) (π : Fin k → List B)
    (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i)
    (hm : ∀ i b c, Orders.Before (π i) b c →
      Ranks.complete (rows b) false i ≤ Ranks.complete (rows c) false i) :
    Crown.Represents (Blocks.initialRankGraph rows) (k+1)
      (word (fun b => Ranks.complete (rows b) false) π) := by
  sorry

end Crown.BaselineLiteral

namespace Crown.BalancedLarge

-- Source statement: Crown/BalancedLarge.lean:82
theorem matrix_representable (k : ℕ) (hk : 8 ≤ k)
    (M : Fin (2 * k) → Fin (2 * k) → Bool) :
    Crown.KRepresentable (matrixGraph M) k := by
  sorry

end Crown.BalancedLarge

namespace Crown.OddRanks
open Crown.Ranks
variable {k : ℕ} {B : Type*}

-- Source statement: Crown/OddRanks.lean:50
theorem no_fixed_pair (N : B → Orientations.NeighbourRow (Fin k)) (z : Fin k)
    (hsp : ∀ b, (N b z).2 = false) : NoFixedPair (rows N) := by
  sorry

-- Source statement: Crown/OddRanks.lean:67
theorem obstruction_shape (hk : 3 ≤ k) (N : B → Orientations.NeighbourRow (Fin k))
    (z : Fin k) (hsp : ∀ b, (N b z).2 = false)
    (c : B) (hone : DirectOne (rows N) c) (hzero : DirectZero (rows N) c) :
    ∃ l u, l ≠ u ∧ Centre (N c) z ∧ degree (N l) = k ∧ degree (N u) = k ∧
      (N l z).1 = true ∧ (N u z).1 = true := by
  sorry

-- Source statement: Crown/OddRanks.lean:125
theorem feasible_of_safe_three (hk : 3 ≤ k) (N : B → Orientations.NeighbourRow (Fin k))
    (z : Fin k) (hsp : ∀ b, (N b z).2 = false) (hsafe : Safe N z) : Feasible (rows N) := by
  sorry

end Crown.OddRanks

namespace Crown.OddGraphs
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

-- Source statement: Crown/OddGraphs.lean:118
theorem matrix_representable_three (k : ℕ) (hk : 3 ≤ k) (hA : Fintype.card A = 2*k-1)
    (hB : Fintype.card B ≤ Fintype.card A + 2) (M : A → B → Bool) :
    Crown.KRepresentable (BalancedLarge.matrixGraph M) k := by
  sorry

end Crown.OddGraphs

namespace Crown.CrownLower

-- Source statement: Crown/CrownLower.lean:14
theorem crown_size_le_twice_multiplicity {n k : ℕ} (hn : 5 ≤ n)
    (w : List (Bool × Fin n)) (hw : Crown.Represents (Crown.crownGraph n) k w) : n ≤ 2*k := by
  sorry

end Crown.CrownLower

namespace Crown.SmallGraphs
variable {V : Type*} [Fintype V] [DecidableEq V]

-- Source statement: Crown/SmallGraphs.lean:30
theorem at_most_six_iff (G : SimpleGraph V) (hc : Fintype.card V ≤ 6) :
    Crown.KRepresentable G 2 ↔ ¬Nonempty (prism ≃g G) ∧ ¬Nonempty (wheel ≃g G) := by
  sorry

-- Source statement: Crown/SmallGraphs.lean:43
theorem number_at_most_six_iff (G : SimpleGraph V) (hc : Fintype.card V ≤ 6)
    (hr : Crown.Representable G) :
    Crown.representationNumber G ≤ 2 ↔
      ¬Nonempty (prism ≃g G) ∧ ¬Nonempty (wheel ≃g G) := by
  sorry

-- Source statement: Crown/SmallGraphs.lean:61
theorem prism_not_bipartite : ¬prism.IsBipartite := by
  sorry

-- Source statement: Crown/SmallGraphs.lean:64
theorem wheel_not_bipartite : ¬wheel.IsBipartite := by
  sorry

end Crown.SmallGraphs

namespace Crown.UnorderedMatchings

-- Source statement: Crown/UnorderedMatchingCounts.lean:22
theorem perfect_pairings_six_card :
    Nat.card {P : Finset (Finset (Fin 6)) // IsPerfectPairing P} = 15 := by
  sorry

-- Source statement: Crown/UnorderedMatchingCounts.lean:28
theorem perfect_pairings_eight_card :
    Nat.card {P : Finset (Finset (Fin 8)) // IsPerfectPairing P} = 105 := by
  sorry

end Crown.UnorderedMatchings
