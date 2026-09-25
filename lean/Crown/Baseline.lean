import Crown.BalancedLarge

namespace Crown.Baseline

variable {k : ℕ} {B : Type*}

def reverseRank (r : Fin 5) : Fin 5 := ⟨4 - r.val, by omega⟩

def extendedRanks (z : Fin k) (r : B → Ranks.CompletedRow (Fin k)) :
    B → Ranks.CompletedRow (Fin (k + 1)) :=
  fun b => Fin.lastCases (reverseRank (r b z)) (r b)

theorem extendedRanks_incomparable (z : Fin k) (r : B → Ranks.CompletedRow (Fin k))
    (b c : B) : ¬ Ranks.StrictBelow (extendedRanks z r b) (extendedRanks z r c) := by
  intro h
  have hfirst := h z.castSucc
  have hlast := h (Fin.last k)
  simp only [extendedRanks, Fin.lastCases_castSucc, Fin.lastCases_last] at hfirst hlast
  change (r b z).val < (r c z).val at hfirst
  change 4 - (r b z).val < 4 - (r c z).val at hlast
  have hb := (r b z).isLt
  have hc := (r c z).isLt
  omega

def alphabetEmbedding : Blocks.Alphabet k B ↪ Blocks.Alphabet (k + 1) B where
  toFun := Sum.map (fun p => (p.1.castSucc, p.2)) id
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        simp only [Sum.map_inl, Sum.inl.injEq, Prod.mk.injEq] at h
        have hi := Fin.castSucc_injective k h.1
        exact congrArg Sum.inl (Prod.ext hi h.2)
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (Sum.inr.inj h)

/-- R01 for any completed rank table, with no comparability restriction. -/
theorem rankGraph_representable [Fintype B] [DecidableEq B] (hk : 2 ≤ k)
    (r : B → Ranks.CompletedRow (Fin k)) :
    Crown.KRepresentable (Blocks.rankGraph r) (k + 1) := by
  let z : Fin k := ⟨0, by omega⟩
  obtain ⟨π, hπ, hm, ho⟩ := Orders.coordinate_orders (by omega : 2 ≤ k + 1)
    (extendedRanks z r) (fun b c _ => extendedRanks_incomparable z r b c)
  have hrep : Crown.KRepresentable (Blocks.rankGraph (extendedRanks z r)) (k + 1) :=
    ⟨_, Blocks.word_represents_rankGraph (by omega) _ π hπ hm ho⟩
  apply Crown.kRepresentable_of_inducedEmbedding alphabetEmbedding _ hrep
  intro a b
  cases a with
  | inl a =>
    cases b with
    | inl b => rfl
    | inr b =>
      change Blocks.RankAdjacent (r b a.1) a.2 ↔
        Blocks.RankAdjacent (Fin.lastCases (reverseRank (r b z)) (r b) a.1.castSucc) a.2
      rw [Fin.lastCases_castSucc]
  | inr a =>
    cases b with
    | inl b =>
      change Blocks.RankAdjacent (r a b.1) b.2 ↔
        Blocks.RankAdjacent (Fin.lastCases (reverseRank (r a z)) (r a) b.1.castSucc) b.2
      rw [Fin.lastCases_castSucc]
    | inr b => rfl

theorem raw_representable [Fintype B] [DecidableEq B] (hk : 2 ≤ k)
    (N : B → Orientations.NeighbourRow (Fin k)) :
    Crown.KRepresentable (BalancedLarge.rawGraph N) (k + 1) := by
  let rows := fun b => Orientations.row (N b) (fun _ => false)
  obtain ⟨w, hw⟩ := rankGraph_representable hk (fun b => Ranks.complete (rows b) false)
  exact ⟨w.map (BalancedLarge.alphabetSwap (fun _ => false)),
    Crown.represents_equiv (BalancedLarge.alphabetSwap (fun _ => false))
      (BalancedLarge.swap_adj N (fun _ => false)) hw⟩

/-- Every bipartite graph with one part of size 2k and an arbitrary finite
other part is (k+1)-representable for k≥2. -/
theorem matrix_representable [Fintype B] [DecidableEq B] (k : ℕ) (hk : 2 ≤ k)
    (M : Fin (2 * k) → B → Bool) :
    Crown.KRepresentable (BalancedLarge.matrixGraph M) (k + 1) := by
  let N : B → Orientations.NeighbourRow (Fin k) :=
    fun b i => (M (BalancedLarge.pairEquiv k (i, false)) b,
      M (BalancedLarge.pairEquiv k (i, true)) b)
  let e := Equiv.sumCongr (BalancedLarge.pairEquiv k) (Equiv.refl B)
  obtain ⟨w, hw⟩ := raw_representable hk N
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

#print axioms extendedRanks_incomparable
#print axioms rankGraph_representable
#print axioms raw_representable
#print axioms matrix_representable

end Crown.Baseline
