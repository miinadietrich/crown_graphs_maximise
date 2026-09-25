import Crown.GraphAssembly
import Crown.MatchingFive
import Crown.MatchingExistence
import Crown.CrownValues
import Crown.SmallEight
import Crown.SmallGraph

/-! These supporting reductions retain their remaining inputs explicitly.
Only the later closed main theorems will discharge the three- and four-pair
certificate cases. -/
namespace Crown.FinalReductions
open Crown.BalancedLarge

theorem balanced_cases
    (h3 : ∀ M : Fin 6 → Fin 6 → Bool, KRepresentable (matrixGraph M) 3)
    (h4 : ∀ M : Fin 8 → Fin 8 → Bool, KRepresentable (matrixGraph M) 4) :
    GraphAssembly.BalancedCases := by
  intro k hk M
  by_cases hlarge : 8 ≤ k
  · exact BalancedLarge.matrix_representable k hlarge M
  · interval_cases k
    · exact h3 M
    · exact h4 M
    · exact MatchingFive.matrix_representable M
    · exact MatchingExistence.matrix_representable6 M
    · exact MatchingExistence.matrix_representable7 M

theorem graph_bound
    (h3 : ∀ M : Fin 6 → Fin 6 → Bool, KRepresentable (matrixGraph M) 3)
    (h4 : ∀ M : Fin 8 → Fin 8 → Bool, KRepresentable (matrixGraph M) 4)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hb : G.IsBipartite) (hN : 9 ≤ Fintype.card V) :
    ∃ k, k ≤ quarterCeil (Fintype.card V) ∧ KRepresentable G k :=
  GraphAssembly.graph_bound (balanced_cases h3 h4) OddGraphs.five_seven G hb hN

theorem extremal_of_large_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n) (hcard : Fintype.card V = 2*n)
    (hb : G.IsBipartite)
    (hlarge : 9 ≤ Fintype.card V →
      ∃ k, k ≤ quarterCeil (Fintype.card V) ∧ KRepresentable G k) :
    Representable G ∧ representationNumber G ≤ representationNumber (crownGraph n) := by
  rw [(crown_representation_number n hn).2]
  by_cases hsmall : n ≤ 3
  · have hg := small_bipartite_two_uniform_proof G hb (by omega)
    exact ⟨⟨2,hg⟩, by simpa [crownValue,hsmall] using representationNumber_le hg⟩
  by_cases hfour : n = 4
  · have hg := SmallEight.graph G hb (by omega)
    exact ⟨⟨3,hg⟩, by simpa [crownValue,hsmall,hfour] using representationNumber_le hg⟩
  · obtain ⟨k,hk,hg⟩ := hlarge (by omega)
    refine ⟨⟨k,hg⟩, (representationNumber_le hg).trans ?_⟩
    have hceil : quarterCeil (2*n) = halfCeil n := by
      dsimp [quarterCeil,halfCeil]
      omega
    simpa [crownValue,hsmall,hfour,hcard,hceil] using hk

theorem length_of_bounds (n : ℕ) (hn : 5 ≤ n)
    (hbound : ∀ G : SimpleGraph (Fin (2*n)), G.IsBipartite →
      ∃ k, k ≤ quarterCeil (2*n) ∧ KRepresentable G k) :
    (∃ w, Represents (crownGraph n) (halfCeil n) w ∧
      w.length = (2*n)*halfCeil n ∧
      ∀ k u, Represents (crownGraph n) k u → w.length ≤ u.length) ∧
    (∀ G : SimpleGraph (Fin (2*n)), G.IsBipartite →
      ∃ k w, Represents G k w ∧ w.length ≤ (2*n)*halfCeil n) := by
  refine ⟨crown_minimum_uniform_length n hn, ?_⟩
  intro G hb
  obtain ⟨k,hk,w,hw⟩ := hbound G hb
  refine ⟨k,w,hw,?_⟩
  rw [uniform_length hw.2.1]
  simp only [Fintype.card_fin]
  apply Nat.mul_le_mul_left
  dsimp [quarterCeil,halfCeil] at *
  omega

#print axioms balanced_cases
#print axioms graph_bound
#print axioms extremal_of_large_bound
#print axioms length_of_bounds
end Crown.FinalReductions
