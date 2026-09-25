import Crown.Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace Crown.Counting

/-- The exact finite union bound. The bad sets need not be disjoint. -/
theorem exists_avoiding_of_sum_card_lt {ι Ω : Type*} [DecidableEq Ω]
    (indices : Finset ι) (samples : Finset Ω) (bad : ι → Finset Ω)
    (hsmall : (∑ i ∈ indices, (bad i).card) < samples.card) :
    ∃ ω ∈ samples, ∀ i ∈ indices, ω ∉ bad i := by
  have hunion : (indices.biUnion bad).card < samples.card :=
    Finset.card_biUnion_le.trans_lt hsmall
  obtain ⟨ω, hω, hgood⟩ := Finset.exists_mem_notMem_of_card_lt_card hunion
  refine ⟨ω, hω, ?_⟩
  intro i hi hbad
  exact hgood (Finset.mem_biUnion.mpr ⟨i, hi, hbad⟩)

/-- A finite union bound with a separately proved bound for each event. -/
theorem exists_avoiding_of_bounds {ι Ω : Type*} [DecidableEq Ω]
    (indices : Finset ι) (samples : Finset Ω) (bad : ι → Finset Ω) (bound : ι → ℕ)
    (hbound : ∀ i ∈ indices, (bad i).card ≤ bound i)
    (hsmall : (∑ i ∈ indices, bound i) < samples.card) :
    ∃ ω ∈ samples, ∀ i ∈ indices, ω ∉ bad i := by
  apply exists_avoiding_of_sum_card_lt
  exact (Finset.sum_le_sum hbound).trans_lt hsmall

/-- The equal-event-bound form used for independently oriented pairs. -/
theorem exists_avoiding_of_uniform_bound {ι Ω : Type*} [DecidableEq Ω]
    (indices : Finset ι) (samples : Finset Ω) (bad : ι → Finset Ω) (bound : ℕ)
    (hbound : ∀ i ∈ indices, (bad i).card ≤ bound)
    (hsmall : indices.card * bound < samples.card) :
    ∃ ω ∈ samples, ∀ i ∈ indices, ω ∉ bad i := by
  apply exists_avoiding_of_bounds indices samples bad (fun _ => bound) hbound
  simpa using hsmall

/-- The pair/triple form of the union bound, with potentially different
index types and overlapping bad events. -/
theorem exists_avoiding_two_families {ι κ Ω : Type*} [DecidableEq Ω]
    (left : Finset ι) (right : Finset κ) (samples : Finset Ω)
    (badLeft : ι → Finset Ω) (badRight : κ → Finset Ω)
    (hsmall : (∑ i ∈ left, (badLeft i).card) +
      (∑ j ∈ right, (badRight j).card) < samples.card) :
    ∃ ω ∈ samples,
      (∀ i ∈ left, ω ∉ badLeft i) ∧ (∀ j ∈ right, ω ∉ badRight j) := by
  have hcard : (left.biUnion badLeft ∪ right.biUnion badRight).card < samples.card :=
    calc
      _ ≤ (left.biUnion badLeft).card + (right.biUnion badRight).card := Finset.card_union_le ..
      _ ≤ (∑ i ∈ left, (badLeft i).card) + (∑ j ∈ right, (badRight j).card) :=
        Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
      _ < samples.card := hsmall
  obtain ⟨ω, hω, hgood⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨ω, hω, ?_, ?_⟩
  · intro i hi hbad
    exact hgood (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hi, hbad⟩))
  · intro j hj hbad
    exact hgood (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, hbad⟩))

theorem card_orientations (k : ℕ) : Fintype.card (Orientations k) = 2 ^ k := by
  simp [Orientations]

theorem card_vertex_pairs (k : ℕ) :
    ((Finset.univ : Finset (Fin (2 * k))).powersetCard 2).card = Nat.choose (2 * k) 2 := by
  simp

/-- P03 as an existence argument once the P01/P02 per-pair bounds have
been established. Its hypotheses explicitly retain those semantic duties. -/
theorem exists_good_orientation (k : ℕ) (hk : 8 ≤ k)
    (bad : Finset (Fin (2 * k)) → Finset (Orientations k))
    (hbound : ∀ pair ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard 2,
      (bad pair).card ≤ 2) :
    ∃ ω : Orientations k,
      ∀ pair ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard 2, ω ∉ bad pair := by
  have hsmall : ((Finset.univ : Finset (Fin (2 * k))).powersetCard 2).card * 2 <
      (Finset.univ : Finset (Orientations k)).card := by
    rw [card_vertex_pairs, Finset.card_univ, card_orientations]
    simpa [Nat.mul_comm] using Arithmetic.orientation_count_lt k hk
  obtain ⟨ω, _, hgood⟩ := exists_avoiding_of_uniform_bound
    ((Finset.univ : Finset (Fin (2 * k))).powersetCard 2)
    (Finset.univ : Finset (Orientations k)) bad 2 hbound hsmall
  exact ⟨ω, hgood⟩

end Crown.Counting
