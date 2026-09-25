import Specification.CatalogueTemplates
import Mathlib.Data.Finset.Union

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

def maskFeasible (rows : Fin 256 → RankRow) (M : Finset (Fin 256)) : Prop :=
  Feasible (fun m : {m // m ∈ M} => rows m.val)

def MinimalMaskFamily (rows : Fin 256 → RankRow) (M : Finset (Fin 256)) : Prop :=
  ¬ maskFeasible rows M ∧ ∀ T, T ⊂ M → maskFeasible rows T

def pairingRows (p : Pairing8) : Fin 256 → RankRow :=
  fun m => rowOfMask (pairsOfEquiv p) (maskBits m)

noncomputable def catalogueUnion : Finset (Finset (Fin 256)) :=
  Finset.univ.biUnion fun t : Fin 840 =>
    (templates t).toFinset.image (fun c => (cores c).toFinset)

end Crown.CertificateData
