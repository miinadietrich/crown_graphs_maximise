import Crown.Counting
import Crown.Ranks

/-!
# Independently orienting a fixed pairing

An input row gives the two adjacency bits at each pair. An orientation either
retains or exchanges the endpoints. This module establishes the at-most-two
bad-orientation bound of P01/P02 directly from these neighbourhood bits.
The values `some 0`, `some 1`, `some 2` use the rank encoding of `Crown.Ranks`
and therefore represent the manuscript's prescribed ranks 1, 2, 3.
-/

namespace Crown.Orientations

open Crown.Ranks

abbrev NeighbourRow (I : Type*) := I → Bool × Bool

def entry : Bool × Bool → Bool → Option (Fin 3)
  | (false, false), _ => none
  | (true, true), _ => some 1
  | (true, false), o => if o then some 2 else some 0
  | (false, true), o => if o then some 0 else some 2

def row {I : Type*} (N : NeighbourRow I) (o : I → Bool) : InitialRow I :=
  fun i => entry (N i) (o i)

def zeroRow {I : Type*} (N : NeighbourRow I) (o : I → Bool) : CompletedRow I :=
  complete (row N o) false

def DoubleStar {I : Type*} (N : NeighbourRow I) : Prop :=
  ∃ i j, i ≠ j ∧ N i = (false, false) ∧ N j = (false, false)

/-- Multi-star rows are completed with both extremes, so only the other
rows contribute bad events. The remaining stars receive zero. -/
def PairBad {I : Type*} (N M : NeighbourRow I) (o : I → Bool) : Prop :=
  ¬ DoubleStar N ∧ ¬ DoubleStar M ∧
    (StrictBelow (zeroRow N o) (zeroRow M o) ∨ StrictBelow (zeroRow M o) (zeroRow N o))

noncomputable def badOrientations {k : ℕ} (N M : NeighbourRow (Fin k)) :
    Finset (Counting.Orientations k) := by
  classical
  exact Finset.univ.filter (PairBad N M)

noncomputable def directedBad {k : ℕ} (N M : NeighbourRow (Fin k)) :
    Finset (Counting.Orientations k) := by
  classical
  exact Finset.univ.filter (fun o => StrictBelow (zeroRow N o) (zeroRow M o))

theorem entry_none_iff : ∀ p : Bool × Bool, ∀ o : Bool,
    entry p o = none ↔ p = (false, false) := by decide

/-- A strict comparison of two prescribed ranks can hold for at most one
of the two orientations of the same pair. -/
theorem prescribed_comparison_orientation_unique :
    ∀ p q : Bool × Bool, ∀ a b : Bool,
      p ≠ (false, false) → q ≠ (false, false) →
      completeEntry (entry p a) false < completeEntry (entry q a) false →
      completeEntry (entry p b) false < completeEntry (entry q b) false → a = b := by decide

theorem doubleStar_iff {I : Type*} (N : NeighbourRow I) (o : I → Bool) :
    DoubleStar N ↔ MultiStar (row N o) := by
  simp only [DoubleStar, MultiStar, row, entry_none_iff]

theorem fixed_iff {I : Type*} (N : NeighbourRow I) (o : I → Bool) :
    Fixed (row N o) ↔ ∀ i, N i ≠ (false, false) := by
  constructor
  · intro h i hi
    exact h i ((entry_none_iff (N i) (o i)).mpr hi)
  · intro h i hi
    exact h i ((entry_none_iff (N i) (o i)).mp hi)

theorem pairBad_swap {I : Type*} (N M : NeighbourRow I) (o : I → Bool) :
    PairBad N M o ↔ PairBad M N o := by
  constructor <;> rintro ⟨hN, hM, h⟩ <;> exact ⟨hM, hN, h.symm⟩

theorem mem_badOrientations {k : ℕ} (N M : NeighbourRow (Fin k)) (o : Counting.Orientations k) :
    o ∈ badOrientations N M ↔ PairBad N M o := by
  classical
  simp [badOrientations]

theorem strict_zero_upper_fixed {I : Type*} (N M : NeighbourRow I) (o : I → Bool)
    (h : StrictBelow (zeroRow N o) (zeroRow M o)) : ∀ i, M i ≠ (false, false) := by
  intro i hi
  have hz : zeroRow M o i = 0 := by
    simp [zeroRow, complete, row, entry, hi, completeEntry]
  have hlt := h i
  rw [hz] at hlt
  exact Nat.not_lt_zero _ hlt

theorem bad_card_le_two_of_star {k : ℕ} (N M : NeighbourRow (Fin k))
    (j : Fin k) (hj : N j = (false, false)) : (badOrientations N M).card ≤ 2 := by
  classical
  have hinj : Set.InjOn (fun o : Counting.Orientations k => o j) (badOrientations N M) := by
    intro a ha b hb hab
    have ha' := (mem_badOrientations N M a).mp ha
    have hb' := (mem_badOrientations N M b).mp hb
    have hforwardA : StrictBelow (zeroRow N a) (zeroRow M a) :=
      ha'.2.2.resolve_right (fun h => strict_zero_upper_fixed M N a h j hj)
    have hforwardB : StrictBelow (zeroRow N b) (zeroRow M b) :=
      hb'.2.2.resolve_right (fun h => strict_zero_upper_fixed M N b h j hj)
    funext i
    by_cases hij : i = j
    · simpa [hij] using hab
    · have hNi : N i ≠ (false, false) := fun hi => ha'.1 ⟨i, j, hij, hi, hj⟩
      exact prescribed_comparison_orientation_unique (N i) (M i) (a i) (b i)
        hNi (strict_zero_upper_fixed N M a hforwardA i) (hforwardA i) (hforwardB i)
  have hcard := Finset.card_le_card_of_injOn (fun o : Counting.Orientations k => o j)
    (t := (Finset.univ : Finset Bool)) (fun _ _ => Finset.mem_univ _) hinj
  simpa using hcard

theorem directed_bad_card_le_one {k : ℕ} (N M : NeighbourRow (Fin k))
    (hN : ∀ i, N i ≠ (false, false)) (hM : ∀ i, M i ≠ (false, false)) :
    (directedBad N M).card ≤ 1 := by
  classical
  unfold directedBad
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  funext i
  exact prescribed_comparison_orientation_unique (N i) (M i) (a i) (b i)
    (hN i) (hM i) (ha' i) (hb' i)

/-- P01/P02: every unordered pair of rows excludes at most two orientations,
with no restriction on repeated or empty neighbourhoods. -/
theorem bad_card_le_two {k : ℕ} (N M : NeighbourRow (Fin k)) :
    (badOrientations N M).card ≤ 2 := by
  classical
  by_cases hN : ∃ j, N j = (false, false)
  · obtain ⟨j, hj⟩ := hN
    exact bad_card_le_two_of_star N M j hj
  by_cases hM : ∃ j, M j = (false, false)
  · obtain ⟨j, hj⟩ := hM
    have heq : badOrientations N M = badOrientations M N := by
      ext o
      simp only [mem_badOrientations, pairBad_swap N M o]
    rw [heq]
    exact bad_card_le_two_of_star M N j hj
  have hN' : ∀ i, N i ≠ (false, false) := by simpa using hN
  have hM' : ∀ i, M i ≠ (false, false) := by simpa using hM
  let left := directedBad N M
  let right := directedBad M N
  have hsub : badOrientations N M ⊆ left ∪ right := by
    intro o ho
    have h := ((mem_badOrientations N M o).mp ho).2.2
    simpa [left, right, directedBad] using h
  have hleft : left.card ≤ 1 := directed_bad_card_le_one N M hN' hM'
  have hright : right.card ≤ 1 := directed_bad_card_le_one M N hM' hN'
  calc
    _ ≤ (left ∪ right).card := Finset.card_le_card hsub
    _ ≤ left.card + right.card := Finset.card_union_le ..
    _ ≤ 2 := by omega

theorem not_doubleStar_of_fixed {I : Type*} (N : NeighbourRow I) (o : I → Bool)
    (h : Fixed (row N o)) : ¬ DoubleStar N := by
  intro hd
  obtain ⟨i, j, hij, hi, hj⟩ := (doubleStar_iff N o).mp hd
  exact h i hi

theorem not_doubleStar_of_oneStar {I : Type*} (N : NeighbourRow I) (o : I → Bool)
    (h : OneStar (row N o)) : ¬ DoubleStar N := by
  obtain ⟨j, hj, huniq⟩ := h
  intro hd
  obtain ⟨a, b, hab, ha, hb⟩ := (doubleStar_iff N o).mp hd
  exact hab ((huniq a ha).trans (huniq b hb).symm)

/-- Excluding the bad events really gives the manuscript's feasibility
predicate. Multi-star rows are restored by the already proved rank lemma. -/
theorem feasible_of_no_pairBad {I V : Type*} [Nonempty I]
    (N : V → NeighbourRow I) (o : I → Bool)
    (hgood : ∀ b c, b ≠ c → ¬ PairBad (N b) (N c) o) :
    Feasible (fun b => row (N b) o) := by
  classical
  have hnone : ∀ b, ¬ DirectOne (fun b => row (N b) o) b := by
    rintro b ⟨hb, c, hc, hpot⟩
    have hbc : b ≠ c := by
      intro heq
      subst c
      exact fixed_not_hasStar hc (oneStar_hasStar hb)
    apply hgood b c hbc
    refine ⟨not_doubleStar_of_oneStar (N b) o hb,
      not_doubleStar_of_fixed (N c) o hc, Or.inl ?_⟩
    exact (strictBelow_complete_iff (row (N b) o) (row (N c) o) false false).mpr
      ⟨hpot, fun _ => rfl, fun hs => False.elim (fixed_not_hasStar hc hs)⟩
  apply (feasible_iff_constraints _).mpr
  constructor
  · intro b c hb hc hpot
    have hs := (fixed_fixed_comparison hb hc false false).mpr hpot
    by_cases hbc : b = c
    · subst c
      exact Nat.lt_irrefl _ (hs (Classical.arbitrary I))
    · exact hgood b c hbc ⟨not_doubleStar_of_fixed (N b) o hb,
        not_doubleStar_of_fixed (N c) o hc, Or.inl hs⟩
  · refine ⟨fun _ => false, ?_, ?_, ?_⟩
    · intro b hb
      exact False.elim (hnone b hb)
    · intro b hb
      rfl
    · intro b c hedge hb
      exact hb

noncomputable def badPairFamily {k : ℕ} (N : Fin (2 * k) → NeighbourRow (Fin k))
    (pair : Finset (Fin (2 * k))) : Finset (Counting.Orientations k) := by
  classical
  exact Finset.univ.filter (fun o =>
    ∃ b ∈ pair, ∃ c ∈ pair, b ≠ c ∧ PairBad (N b) (N c) o)

theorem badPairFamily_pair {k : ℕ} (N : Fin (2 * k) → NeighbourRow (Fin k))
    (b c : Fin (2 * k)) (hbc : b ≠ c) :
    badPairFamily N {b, c} = badOrientations (N b) (N c) := by
  classical
  ext o
  simp only [badPairFamily, Finset.mem_filter, Finset.mem_univ, true_and, mem_badOrientations]
  constructor
  · rintro ⟨u, hu, v, hv, huv, hbad⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact False.elim (huv rfl)
    · exact hbad
    · exact (pairBad_swap _ _ _).mp hbad
    · exact False.elim (huv rfl)
  · intro hbad
    exact ⟨b, by simp, c, by simp, hbc, hbad⟩

/-- P01--P03: every set of 2k neighbourhood rows on a fixed k-pair
partition has a feasible orientation when k≥8. All row values are allowed,
including duplicate, empty and complete neighbourhoods. -/
theorem exists_feasible_orientation (k : ℕ) (hk : 8 ≤ k)
    (N : Fin (2 * k) → NeighbourRow (Fin k)) :
    ∃ o : Counting.Orientations k, Feasible (fun b => row (N b) o) := by
  classical
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hbound : ∀ pair ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard 2,
      (badPairFamily N pair).card ≤ 2 := by
    intro pair hp
    obtain ⟨b, c, hbc, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hp).2
    rw [badPairFamily_pair N b c hbc]
    exact bad_card_le_two (N b) (N c)
  obtain ⟨o, ho⟩ := Counting.exists_good_orientation k hk (badPairFamily N) hbound
  refine ⟨o, feasible_of_no_pairBad N o ?_⟩
  intro b c hbc hbad
  have hp : ({b, c} : Finset (Fin (2 * k))) ∈
      (Finset.univ : Finset (Fin (2 * k))).powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _, by simp [hbc]⟩
  apply ho {b, c} hp
  rw [badPairFamily_pair N b c hbc]
  exact (mem_badOrientations (N b) (N c) o).mpr hbad

#print axioms bad_card_le_two
#print axioms feasible_of_no_pairBad
#print axioms exists_feasible_orientation

end Crown.Orientations
