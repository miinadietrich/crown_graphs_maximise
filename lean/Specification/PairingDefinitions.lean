import Specification.CertificateDefinitions
import Specification.ProbabilityDefinitions

namespace Crown.PairingCoordinates
abbrev Coordinates (k : ℕ) := (Fin k × Bool) ≃ Fin (2*k)
def flipEquiv (k : ℕ) : (Fin k × Bool) ≃ (Fin k × Bool) where
  toFun x := (x.1,!x.2)
  invFun x := (x.1,!x.2)
  left_inv x := by simp
  right_inv x := by simp
def reverseCoordinates {k : ℕ} (p : Coordinates k) : Coordinates k := (flipEquiv k).trans p
end Crown.PairingCoordinates
namespace Crown.PairingCoverage
open Crown.PairingCoordinates Crown.Ranks
def rankRows {k : ℕ} {V : Type*} (p : Coordinates k) (N : V → Fin (2*k) → Bool) :
    V → InitialRow (Fin k) := fun v i =>
      Crown.Orientations.entry (N v (p (i,false)),N v (p (i,true))) false
end Crown.PairingCoverage
namespace Crown.MatchingRepresentatives
open Crown.Matchings
abbrev AnchoredPairing (k : ℕ) (v : Fin (2*k)) := {p : OrientedPairing k // v ∈ p.1.val}
end Crown.MatchingRepresentatives
