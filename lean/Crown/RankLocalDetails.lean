import Crown.Blocks
import Mathlib.Tactic.FinCases

/-! Literal local rank words (L03) and the necessary ordering condition (L05).
These supporting statements retain the actual alphabet and block construction. -/
namespace Crown.RankLocalDetails
open Crown.Blocks
variable {k : ℕ} {B : Type*} [DecidableEq B]
local instance : BEq (Alphabet k B) := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq (Alphabet k B) where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

def restrictTriple (w : List (Alphabet k B)) (i : Fin k) (b : B) : List (Alphabet k B) :=
  w.filter fun a => a = x i ∨ a = y i ∨ a = Sum.inr b

def localTriple (q : Fin 5) (i : Fin k) (b : B) : List (Alphabet k B) :=
  match q.val with
  | 0 => [Sum.inr b, x i, y i, x i, y i]
  | 1 => [x i, Sum.inr b, y i, x i, y i]
  | 2 => [x i, y i, Sum.inr b, x i, y i]
  | 3 => [x i, y i, x i, Sum.inr b, y i]
  | _ => [x i, y i, x i, y i, Sum.inr b]

private theorem restrictTriple_append (u v : List (Alphabet k B)) (i : Fin k) (b : B) :
    restrictTriple (u ++ v) i b = restrictTriple u i b ++ restrictTriple v i b := by
  simp [restrictTriple,List.filter_append]

private theorem gap_triple (rank : B → Fin 5) (π : List B) (q : Fin 5)
    (i : Fin k) (b : B) (hb : π.count b = 1) :
    restrictTriple (gap rank π q) i b = if rank b = q then [Sum.inr b] else [] := by
  have hf : restrictTriple (gap rank π q) i b =
      (gap rank π q).filter (fun a => a = Sum.inr b) := by
    apply List.filter_congr
    intro a ha
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
    simp [x,y]
  rw [hf,List.filter_eq,count_gap_right]
  by_cases he : rank b = q <;> simp [hb,he]

/-- The entire three-letter restriction, including both copies of x and y. -/
theorem restrict_block_three (r : B → Ranks.CompletedRow (Fin k))
    (π : Fin k → List B) (i : Fin k) (b : B) (hb : (π i).count b = 1) :
    restrictTriple (block r π i) i b = localTriple (r b i) i b := by
  have hg (q : Fin 5) := gap_triple (fun c => r c i) (π i) q i b hb
  rw [block]
  simp only [restrictTriple_append,hg]
  have hq : r b i = 0 ∨ r b i = 1 ∨ r b i = 2 ∨ r b i = 3 ∨ r b i = 4 :=
    rank_cases (r b i)
  rcases hq with hq | hq | hq | hq | hq <;>
    simp [hq,localTriple,restrictTriple,x,y]

/-- Any strict coordinate comparison forces one relative order in every
permutation nondecreasing in its own coordinate. -/
theorem strict_forces_order (r : B → Ranks.CompletedRow (Fin k))
    (π : Fin k → List B) (hπ : ∀ i b, b ∈ π i)
    (hm : ∀ i b c, Orders.Before (π i) b c → r b i ≤ r c i)
    (a b : B) (h : Ranks.StrictBelow (r a) (r b)) :
    ∀ i, Orders.Before (π i) a b := by
  intro i
  have hab : a ≠ b := by
    intro he
    subst b
    exact (Nat.lt_irrefl _) (h i)
  rcases Orders.before_or_before (π i) (hπ i a) (hπ i b) hab with hl | hr
  · exact hl
  · exact False.elim ((Nat.not_lt_of_ge (hm i b a hr)) (h i))

private theorem repeated_pair_chain (a b : B) (hab : a ≠ b) (is : List (Fin k)) :
    (is.flatMap (fun _ => [a,b])).IsChain (· ≠ ·) := by
  induction is with
  | nil => simp
  | cons i is ih =>
    cases is with
    | nil => simp [hab]
    | cons j js =>
      simpa [List.isChain_cons_cons,hab,Ne.symm hab] using ih

private theorem permutations_alternates_of_order (π : Fin k → List B)
    (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i) (a b : B) (hab : a ≠ b)
    (ho : ∀ i, Orders.Before (π i) a b) :
    Crown.Alternates ((List.finRange k).flatMap π) a b := by
  have hr : Crown.restrictPair ((List.finRange k).flatMap π) a b =
      (List.finRange k).flatMap (fun _ => [a,b]) := by
    simp only [Crown.restrictPair,List.filter_flatMap]
    apply List.flatMap_congr
    intro i _
    have hidx : (π i).idxOf a < (π i).idxOf b := ho i
    simpa only [Crown.restrictPair,if_pos hidx] using
      restrictPair_permutation (π i) (hπ i).1 a b ((hπ i).2 a) ((hπ i).2 b) hab
  unfold Crown.Alternates
  rw [hr]
  exact repeated_pair_chain a b hab _

/-- L07's full equivalence for the concatenation of arbitrary permutations. -/
theorem permutations_alternates_iff (π : Fin k → List B)
    (hπ : ∀ i, (π i).Nodup ∧ ∀ b, b ∈ π i) (a b : B) (hab : a ≠ b) :
    Crown.Alternates ((List.finRange k).flatMap π) a b ↔
      (∀ i, Orders.Before (π i) a b) ∨ (∀ i, Orders.Before (π i) b a) := by
  classical
  constructor
  · intro ha
    by_cases hf : ∀ i, Orders.Before (π i) a b
    · exact Or.inl hf
    · right
      obtain ⟨j,hj⟩ := not_forall.mp hf
      have hj' : Orders.Before (π j) b a :=
        (Orders.before_or_before (π j) ((hπ j).2 a) ((hπ j).2 b) hab).resolve_left hj
      intro i
      rcases Orders.before_or_before (π i) ((hπ i).2 a) ((hπ i).2 b) hab with hi | hi
      · exact False.elim (permutations_nonedge π hπ a b hab ⟨i,hi⟩ ⟨j,hj'⟩ ha)
      · exact hi
  · rintro (ho | ho)
    · exact permutations_alternates_of_order π hπ a b hab ho
    · rw [Crown.alternates_comm]
      exact permutations_alternates_of_order π hπ b a (Ne.symm hab) ho

#print axioms permutations_alternates_iff
#print axioms restrict_block_three
#print axioms strict_forces_order
end Crown.RankLocalDetails
