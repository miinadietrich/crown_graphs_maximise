import Crown.SmallGraphsSixData
import Crown.SmallGraphExceptions

namespace Crown.SmallGraphs

def candidateRecord (m : Nat) := sixCandidates.getD m (0,0,0)
def permutationAt (i : Nat) (a : Fin 6) : Fin 6 :=
  (vertexPermutations.getD i []).getD a.val 0
def candidatePermutation (m : Nat) := permutationAt (candidateRecord m).2.2

def candidateSource (m : Nat) : Nat :=
  if (candidateRecord m).1 = 0 then representativeMasks.getD (candidateRecord m).2.1 0
  else if (candidateRecord m).1 = 1 then 30887 else 21311

def ValidCandidate (m : Nat) : Prop :=
  (candidateRecord m).1 ≤ 2 ∧
  ((candidateRecord m).1 = 0 → (candidateRecord m).2.1 < 154) ∧
  (candidateRecord m).2.2 < 720 ∧
  ∀ a b : Fin 6, a < b → ((graph 6 m).Adj (candidatePermutation m a) (candidatePermutation m b) ↔
    (graph 6 (candidateSource m)).Adj a b)

theorem relation_of_upper {G H : SimpleGraph (Fin 6)} (f : Fin 6 → Fin 6)
    (h : ∀ a b, a < b → (H.Adj (f a) (f b) ↔ G.Adj a b)) :
    ∀ a b, H.Adj (f a) (f b) ↔ G.Adj a b := by
  intro a b
  rcases lt_trichotomy a b with hab | hab | hba
  · exact h a b hab
  · subst b; simp
  · rw [H.adj_comm,G.adj_comm]
    exact h b a hba
instance (m : Nat) : Decidable (ValidCandidate m) := by
  unfold ValidCandidate
  infer_instance

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem all_vertex_permutations : ∀ i : Fin 720, Function.Bijective (permutationAt i.val) := by
  unfold Function.Bijective Function.Injective Function.Surjective
  decide +kernel

theorem six_representatives : ∀ i : Fin 154,
    Crown.Represents (graph 6 (representativeMasks.getD i.val 0)) 2
      (representativeWords.getD i.val []) := by
  unfold Crown.Represents Crown.Uniform Crown.Alternates Crown.restrictPair
  decide +kernel

#print axioms all_vertex_permutations
#print axioms six_representatives
end Crown.SmallGraphs
