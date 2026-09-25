import SupportAnalyticalChallenge
import SupportFormulaChallenge
import SupportPairingChallenge
import Crown.Definitions
import Specification.MatrixDefinitions
import NumericalChallenge
import SupportCatalogueChallenge
import SupportCertificateChallenge
import SupportCNFChallenge
import SupportProbabilityChallenge
import SupportProbabilityDirectChallenge
import SupportRankChallenge
import SupportRankDetailChallenge
import SupportReductionChallenge
import SupportSymmetryChallenge
import SupportTraversalChallenge
import SupportWordChallenge

namespace Crown

theorem balanced_matrix_representation_bound (k : ℕ) (hk : 3 ≤ k)
    (M : Fin (2*k) → Fin (2*k) → Bool) :
    KRepresentable (BalancedLarge.matrixGraph M) k := by
  sorry

/-- H01: every bipartite graph of order at least nine has the asserted word. -/
theorem bipartite_representation_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hb : G.IsBipartite) (hN : 9 ≤ Fintype.card V) :
    ∃ k, k ≤ quarterCeil (Fintype.card V) ∧ KRepresentable G k := by
  sorry

/-- H01 in terms of the least multiplicity, with existence retained explicitly. -/
theorem bipartite_representation_number_bound {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hb : G.IsBipartite) (hN : 9 ≤ Fintype.card V) :
    Representable G ∧ representationNumber G ≤ quarterCeil (Fintype.card V) := by
  sorry

/-- H03, H05 and H06: the exact crown values at every positive part size. -/
theorem crown_representation_number (n : ℕ) (hn : 1 ≤ n) :
    Representable (crownGraph n) ∧ representationNumber (crownGraph n) = crownValue n := by
  sorry

/-- H02: crowns attain the largest representation number at each even order. -/
theorem crown_extremal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (n : ℕ) (hn : 1 ≤ n) (hcard : Fintype.card V = 2 * n)
    (hb : G.IsBipartite) :
    Representable G ∧ representationNumber G ≤ representationNumber (crownGraph n) := by
  sorry

/-- H07: the required small bipartite graphs admit two-uniform representations. -/
theorem small_bipartite_two_uniform {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hb : G.IsBipartite) (hcard : Fintype.card V ≤ 6) :
    KRepresentable G 2 := by
  sorry

/-- H04: the maximum minimum uniform length at each even order at least ten. -/
theorem crown_extremal_uniform_length (n : ℕ) (hn : 5 ≤ n) :
    (∃ w, Represents (crownGraph n) (halfCeil n) w ∧
      w.length = (2 * n) * halfCeil n ∧
      ∀ k u, Represents (crownGraph n) k u → w.length ≤ u.length) ∧
    (∀ (G : SimpleGraph (Fin (2 * n))), G.IsBipartite →
      ∃ k w, Represents G k w ∧ w.length ≤ (2 * n) * halfCeil n) := by
  sorry

end Crown
