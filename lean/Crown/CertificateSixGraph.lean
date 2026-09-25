import Crown.CertificateSix
import generated.CertificateSixFormula
import Crown.SixCatalogue
import Crown.MaskGraphTransport

/-! # From the three-pair certificate to graph representations

A universally obstructing family of at most six neighbourhood masks would give
a satisfying assignment of the exact reduced CNF. Its checked refutation rules
this out. The catalogue uses the general implication-closure criterion at three
coordinates. Matrix transport then restores arbitrary labels and repeated
neighbourhoods and supplies the three-uniform representing word.
-/

namespace Crown.CertificateSixGraph
open Crown.Ranks Crown.CertificateSemantics Crown.CertificateSixSemantics
open Crown.CertificateSixValuation

/-- The three-pair certificate supplies a feasible pairing for every family
of at most six distinct neighbourhoods. -/
theorem exists_feasible (s : Fin 64 → Bool)
    (hs : Fintype.card {m // s m = true} ≤ 6) :
    ∃ p : Pairing6, Feasible (fun m : {m // s m = true} =>
      rowOfMask (pairsOfEquiv p) (maskBits m.val)) := by
  classical
  by_contra h
  have hb : AllPairingsBad (fun m : {m // s m = true} => m.val) := by
    intro p hp
    exact h ⟨p,hp⟩
  obtain ⟨t,ht,htb,htmax⟩ := canonical_bad_selection s hs hb
  exact Crown.CertificateSix.pairing6_unsatisfiable
    (valuation (Crown.CertificateSixData.assignment t))
    (Crown.CertificateSixData.reduced_formula_satisfied t ht htmax
      (Crown.CertificateSixData.all_templates_selected t ht htb))

theorem matrix_representable {B : Type*} [Fintype B] [DecidableEq B]
    (hB : Fintype.card B ≤ 6) (M : Fin 6 → B → Bool) :
    KRepresentable (BalancedLarge.matrixGraph M) 3 :=
  MaskGraphTransport.matrix_of_masks (k := 3) (by decide) maskBits maskBits_surjective
    exists_feasible hB M

#print axioms exists_feasible
#print axioms matrix_representable
end Crown.CertificateSixGraph
