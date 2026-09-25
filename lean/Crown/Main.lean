import Crown.CertificateGraph
import Crown.CertificateSixGraph
import Crown.FinalReductions

/-! # The bipartite bound and crown extremality

The two finite certificate cases close the remaining premises of the part-size
reductions. The resulting bounds cover every finite bipartite graph in the
stated range, without a feasibility or certificate-success assumption. Exact
crown values then give extremality at every positive even order and the asserted
minimum uniform word length for orders at least ten.
-/

namespace Crown

theorem balanced_matrix_representation_bound (k : ℕ) (hk : 3 ≤ k)
    (M : Fin (2*k) → Fin (2*k) → Bool) :
    KRepresentable (BalancedLarge.matrixGraph M) k :=
  FinalReductions.balanced_cases
    (fun M => CertificateSixGraph.matrix_representable (by simp) M)
    (fun M => CertificateGraph.matrix_representable (by simp) M) k hk M

/-- Every finite bipartite graph on at least nine vertices has a uniform
representant with multiplicity at most the ceiling of one quarter its order. -/
theorem bipartite_representation_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hb : G.IsBipartite) (hN : 9 ≤ Fintype.card V) :
    ∃ k, k ≤ quarterCeil (Fintype.card V) ∧ KRepresentable G k :=
  FinalReductions.graph_bound
    (fun M => CertificateSixGraph.matrix_representable (by simp) M)
    (fun M => CertificateGraph.matrix_representable (by simp) M) G hb hN

theorem bipartite_representation_number_bound {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hb : G.IsBipartite) (hN : 9 ≤ Fintype.card V) :
    Representable G ∧ representationNumber G ≤ quarterCeil (Fintype.card V) := by
  obtain ⟨k,hk,hg⟩ := bipartite_representation_bound G hb hN
  exact ⟨⟨k,hg⟩,(representationNumber_le hg).trans hk⟩

/-- Crowns attain the greatest representation number among all bipartite
graphs of the same positive even order. -/
theorem crown_extremal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n) (hcard : Fintype.card V = 2*n)
    (hb : G.IsBipartite) :
    Representable G ∧ representationNumber G ≤ representationNumber (crownGraph n) :=
  FinalReductions.extremal_of_large_bound G n hn hcard hb
    (bipartite_representation_bound G hb)

/-- The maximum minimum uniform word length, with the crown as an explicit
attaining graph, at every even order at least ten. -/
theorem crown_extremal_uniform_length (n : ℕ) (hn : 5 ≤ n) :
    (∃ w, Represents (crownGraph n) (halfCeil n) w ∧
      w.length = (2*n)*halfCeil n ∧
      ∀ k u, Represents (crownGraph n) k u → w.length ≤ u.length) ∧
    (∀ G : SimpleGraph (Fin (2*n)), G.IsBipartite →
      ∃ k w, Represents G k w ∧ w.length ≤ (2*n)*halfCeil n) :=
  FinalReductions.length_of_bounds n hn
    (fun G hb => by simpa using bipartite_representation_bound G hb (by simp; omega))

#print axioms balanced_matrix_representation_bound
#print axioms bipartite_representation_bound
#print axioms bipartite_representation_number_bound
#print axioms crown_representation_number
#print axioms crown_extremal
#print axioms crown_extremal_uniform_length
end Crown
