import Crown.SmallGraphsCodec
import Crown.SmallGraphGaps

/-! The two exceptional six-vertex graphs, with explicit labelled edge sets.
The wheel has a five-vertex rim; its hub is vertex zero. -/

namespace Crown.SmallGraphs

def prism : SimpleGraph (Fin 6) := graph 6 30887
def wheel : SimpleGraph (Fin 6) := graph 6 21311

instance : DecidableRel prism.Adj := inferInstanceAs (DecidableRel (graph 6 30887).Adj)
instance : DecidableRel wheel.Adj := inferInstanceAs (DecidableRel (graph 6 21311).Adj)

theorem prism_edges : ∀ a b : Fin 6, prism.Adj a b ↔
    (min a b,max a b) ∈ ([(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),
      (3,4),(3,5),(4,5)] : List (Fin 6 × Fin 6)) := by decide +kernel

theorem wheel_edges : ∀ a b : Fin 6, wheel.Adj a b ↔
    (min a b,max a b) ∈ ([(0,1),(0,2),(0,3),(0,4),(0,5),
      (1,2),(1,5),(2,3),(3,4),(4,5)] : List (Fin 6 × Fin 6)) := by decide +kernel

def Matches (G : SimpleGraph (Fin 6)) (w : List (Fin 6)) : Prop :=
  ∀ a b, a ≠ b → (G.Adj a b ↔ Crown.Alternates w a b)

def gapWord (s t : List (Fin 6)) := (0::s) ++ 0::t

#print axioms prism_edges
#print axioms wheel_edges

end Crown.SmallGraphs
