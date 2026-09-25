import Crown.Blocks
import Crown.Orientations

/-!
# Balanced bipartite graphs with at least sixteen vertices in each part

The raw adjacency bits remain unrestricted. The orientation supplied by
`Crown.Orientations` exchanges the two endpoints of selected pairs; the
explicit equivalence below transports the constructed word back to the
original graph. Thus no feasibility assumption occurs in the conclusion.
-/

namespace Crown.BalancedLarge

variable {k : ℕ} {B : Type*}

def bit (p : Bool × Bool) (side : Bool) : Bool := if side then p.2 else p.1

def rawGraph (N : B → Orientations.NeighbourRow (Fin k)) :
    SimpleGraph (Blocks.Alphabet k B) where
  Adj a b := match a, b with
    | Sum.inl p, Sum.inr b => bit (N b p.1) p.2 = true
    | Sum.inr b, Sum.inl p => bit (N b p.1) p.2 = true
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> exact id⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

def endpointSwap (o : Fin k → Bool) : (Fin k × Bool) ≃ (Fin k × Bool) where
  toFun p := (p.1, xor p.2 (o p.1))
  invFun p := (p.1, xor p.2 (o p.1))
  left_inv := by rintro ⟨i, s⟩; cases s <;> cases h : o i <;> simp [h]
  right_inv := by rintro ⟨i, s⟩; cases s <;> cases h : o i <;> simp [h]

def alphabetSwap (o : Fin k → Bool) : Blocks.Alphabet k B ≃ Blocks.Alphabet k B :=
  Equiv.sumCongr (endpointSwap o) (Equiv.refl B)

theorem entry_adjacent : ∀ p : Bool × Bool, ∀ o s : Bool,
    Blocks.RankAdjacent (Ranks.completeEntry (Orientations.entry p o) false) s ↔
      bit p (xor s o) = true := by
  rintro ⟨a, b⟩ o s
  cases a <;> cases b <;> cases o <;> cases s <;>
    simp [Blocks.RankAdjacent, Ranks.completeEntry, Ranks.prescribed, Orientations.entry, bit]

theorem swap_adj (N : B → Orientations.NeighbourRow (Fin k)) (o : Fin k → Bool)
    (a b : Blocks.Alphabet k B) :
    (rawGraph N).Adj (alphabetSwap o a) (alphabetSwap o b) ↔
      (Blocks.initialRankGraph (fun b => Orientations.row (N b) o)).Adj a b := by
  cases a with
  | inl a =>
    cases b with
    | inl b => rfl
    | inr b => exact (entry_adjacent (N b a.1) (o a.1) a.2).symm
  | inr a =>
    cases b with
    | inl b => exact (entry_adjacent (N a b.1) (o b.1) b.2).symm
    | inr b => rfl

/-- P03 followed by the full block construction: every unrestricted
2k-row adjacency table has a k-uniform representative for k≥8. -/
theorem raw_representable (k : ℕ) (hk : 8 ≤ k)
    (N : Fin (2 * k) → Orientations.NeighbourRow (Fin k)) :
    Crown.KRepresentable (rawGraph N) k := by
  obtain ⟨o, ho⟩ := Orientations.exists_feasible_orientation k hk N
  obtain ⟨w, hw⟩ := Blocks.feasible_representable (by omega : 3 ≤ k)
    (fun b => Orientations.row (N b) o) ho
  exact ⟨w.map (alphabetSwap o), Crown.represents_equiv (alphabetSwap o) (swap_adj N o) hw⟩

/-- A bipartite graph with arbitrary Boolean adjacency matrix. -/
def matrixGraph {A B : Type*} (M : A → B → Bool) : SimpleGraph (A ⊕ B) where
  Adj a b := match a, b with
    | Sum.inl a, Sum.inr b => M a b = true
    | Sum.inr b, Sum.inl a => M a b = true
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> exact id⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

noncomputable def pairEquiv (k : ℕ) : (Fin k × Bool) ≃ Fin (2 * k) :=
  Fintype.equivFinOfCardEq (by simp [Nat.mul_comm])

/-- Every bipartite graph with two labelled parts of size 2k is
k-representable when k≥8. No condition is imposed on its adjacency matrix. -/
theorem matrix_representable (k : ℕ) (hk : 8 ≤ k)
    (M : Fin (2 * k) → Fin (2 * k) → Bool) :
    Crown.KRepresentable (matrixGraph M) k := by
  let N : Fin (2 * k) → Orientations.NeighbourRow (Fin k) :=
    fun b i => (M (pairEquiv k (i, false)) b, M (pairEquiv k (i, true)) b)
  let e := Equiv.sumCongr (pairEquiv k) (Equiv.refl (Fin (2 * k)))
  obtain ⟨w, hw⟩ := raw_representable k hk N
  refine ⟨w.map e, Crown.represents_equiv e ?_ hw⟩
  intro a b
  cases a with
  | inl a =>
    cases b with
    | inl b => rfl
    | inr b => cases a with | mk i s => cases s <;> rfl
  | inr a =>
    cases b with
    | inl b => cases b with | mk i s => cases s <;> rfl
    | inr b => rfl

#print axioms raw_representable
#print axioms matrix_representable

end Crown.BalancedLarge
