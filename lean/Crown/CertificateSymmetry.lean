import Crown.CertificateSemantics

namespace Crown.CertificateSymmetry
open Crown.CertificateSemantics

def MaskImage (e : Fin 8 ≃ Fin 8) (f : Fin 256 ≃ Fin 256) : Prop :=
  ∀ m i, maskBits (f m) (e i) = maskBits m i

theorem image_unique (e : Fin 8 ≃ Fin 8) (f : Fin 256 ≃ Fin 256)
    (h : MaskImage e f) : ∀ m, f m = permuteMask e m := by
  intro m
  apply maskBits_injective
  funext i
  have hi := h m (e.symm i)
  simpa only [Equiv.apply_symm_apply,permuteMask_bits] using hi

theorem maskPermutation_image (e : Fin 8 ≃ Fin 8) :
    MaskImage e (maskPermutation e) := by
  intro m i
  change maskBits (permuteMask e m) (e i) = _
  simp only [permuteMask_bits,Equiv.symm_apply_apply]

theorem mask_image_exists (e : Fin 8 ≃ Fin 8) :
    ∃ f : Fin 256 ≃ Fin 256, MaskImage e f :=
  ⟨maskPermutation e, maskPermutation_image e⟩

theorem orbit_maximum (s : Fin 256 → Bool) :
    ∃ (e : Fin 8 ≃ Fin 8) (f : Fin 256 ≃ Fin 256), MaskImage e f ∧
      ∀ (d : Fin 8 ≃ Fin 8) (g : Fin 256 ≃ Fin 256), MaskImage d g →
        toColex (fun m => s (f (g m))) ≤ toColex (fun m => s (f m)) := by
  obtain ⟨e, he⟩ := exists_lex_max_relabeling s
  refine ⟨e, maskPermutation e, maskPermutation_image e, ?_⟩
  intro d g hg
  change toColex (fun m => s (permuteMask e (g m))) ≤
    toColex (fun m => s (permuteMask e m))
  have hh := he d
  change toColex (fun m => s (permuteMask e (permuteMask d m))) ≤
    toColex (fun m => s (permuteMask e m)) at hh
  simpa only [image_unique d g hg] using hh

theorem obstruction_invariant {V : Type} (masks : V → Fin 256)
    (h : AllPairingsBad masks) (e : Fin 8 ≃ Fin 8) (f : Fin 256 ≃ Fin 256)
    (hf : MaskImage e f) : AllPairingsBad (fun v => f (masks v)) := by
  have he := image_unique e f hf
  simpa only [he] using allPairingsBad_permute masks h e

theorem canonical_bad_selection_explicit (s : Fin 256 → Bool)
    (hcard : Fintype.card {m // s m = true} ≤ 8)
    (hbad : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ t : Fin 256 → Bool,
      Fintype.card {m // t m = true} ≤ 8 ∧
      AllPairingsBad (fun m : {m // t m = true} => m.val) ∧
      (∀ (e : Fin 8 ≃ Fin 8) (f : Fin 256 ≃ Fin 256), MaskImage e f →
        toColex (fun m => t (f m)) ≤ toColex t) := by
  obtain ⟨t,ht,hb,hm⟩ := canonical_bad_selection s hcard hbad
  refine ⟨t,ht,hb,fun e f hf => ?_⟩
  have hh := hm e
  change toColex (fun m => t (permuteMask e m)) ≤ toColex t at hh
  simpa only [image_unique e f hf] using hh

#print axioms mask_image_exists
#print axioms orbit_maximum
#print axioms obstruction_invariant
#print axioms canonical_bad_selection_explicit
end Crown.CertificateSymmetry
