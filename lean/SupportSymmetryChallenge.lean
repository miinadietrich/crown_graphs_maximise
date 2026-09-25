import Specification.CertificateDefinitions
import Mathlib.Order.PiLex

namespace Crown.CertificateSymmetry
open Crown.CertificateSemantics

def MaskImage (e : Fin 8 ≃ Fin 8) (f : Fin 256 ≃ Fin 256) : Prop :=
  ∀ m i, maskBits (f m) (e i) = maskBits m i

theorem mask_image_exists (e : Fin 8 ≃ Fin 8) :
    ∃ f : Fin 256 ≃ Fin 256, MaskImage e f := by
  sorry

theorem orbit_maximum (s : Fin 256 → Bool) :
    ∃ (e : Fin 8 ≃ Fin 8) (f : Fin 256 ≃ Fin 256), MaskImage e f ∧
      ∀ (d : Fin 8 ≃ Fin 8) (g : Fin 256 ≃ Fin 256), MaskImage d g →
        toColex (fun m => s (f (g m))) ≤ toColex (fun m => s (f m)) := by
  sorry

theorem obstruction_invariant {V : Type} (masks : V → Fin 256)
    (h : AllPairingsBad masks) (e : Fin 8 ≃ Fin 8) (f : Fin 256 ≃ Fin 256)
    (hf : MaskImage e f) : AllPairingsBad (fun v => f (masks v)) := by
  sorry

theorem canonical_bad_selection_explicit (s : Fin 256 → Bool)
    (hcard : Fintype.card {m // s m = true} ≤ 8)
    (hbad : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ t : Fin 256 → Bool,
      Fintype.card {m // t m = true} ≤ 8 ∧
      AllPairingsBad (fun m : {m // t m = true} => m.val) ∧
      (∀ (e : Fin 8 ≃ Fin 8) (f : Fin 256 ≃ Fin 256), MaskImage e f →
        toColex (fun m => t (f m)) ≤ toColex t) := by
  sorry

end Crown.CertificateSymmetry
