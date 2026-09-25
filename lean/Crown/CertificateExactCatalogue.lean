import Crown.CertificatePatterns
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Nodup

/-! From one-sided containment to the exact minimal-obstruction catalogue.
The extra finite checks concern only core lengths and absence of repetitions.
No second enumeration of rank coordinates is needed. -/

namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

variable (rows : Fin 256 → RankRow) (cores : Fin 4935 → List (Fin 256))
  (template : List (Fin 4935)) (witness : Pattern → Fin 4935)

def ExactCoverage : Prop :=
  ∀ q, List.Perm ((cores (witness q)).map rows) (patternRows q)

theorem exactCoverage_of_sizes
    (hinj : Function.Injective rows) (hcov : Coverage rows cores template witness)
    (hnodup : ∀ c, (cores c).Nodup)
    (hsize : ∀ q, (cores (witness q)).length = (patternRows q).length) :
    ExactCoverage rows cores witness := by
  intro q
  have hsub : (cores (witness q)).map rows ⊆ patternRows q := by
    intro r hr
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hr
    exact (hcov q).2 m hm
  apply (List.Nodup.subperm (List.Nodup.map hinj (hnodup (witness q))) hsub).perm_of_length_le
  simp only [List.length_map, hsize q, le_refl]

theorem exactCoverage_witness_injective (hex : ExactCoverage rows cores witness) :
    Function.Injective witness := by
  intro p q hpq
  apply patternSet_injective
  ext r
  constructor
  · intro hr
    apply (hex q).mem_iff.mp
    simpa only [hpq] using (hex p).mem_iff.mpr hr
  · intro hr
    apply (hex p).mem_iff.mp
    simpa only [hpq] using (hex q).mem_iff.mpr hr

theorem exactCoverage_template (hcov : Coverage rows cores template witness)
    (hex : ExactCoverage rows cores witness) (hlen : template.length = 105) :
    ∀ c ∈ template, ∃ q, List.Perm ((cores c).map rows) (patternRows q) := by
  classical
  let image : Finset (Fin 4935) := Finset.univ.image witness
  have himage : image.card = 105 := by
    change (Finset.univ.image witness).card = 105
    rw [Finset.card_image_of_injective _ (exactCoverage_witness_injective rows cores witness hex)]
    exact pattern_count
  have hsub : image ⊆ template.toFinset := by
    intro c hc
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hc
    exact List.mem_toFinset.mpr (hcov q).1
  have heq : image = template.toFinset := Finset.eq_of_subset_of_card_le hsub (by
    calc
      template.toFinset.card ≤ template.length := List.toFinset_card_le _
      _ = 105 := hlen
      _ = image.card := himage.symm)
  intro c hc
  have hc' : c ∈ image := heq.symm ▸ List.mem_toFinset.mpr hc
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hc'
  exact ⟨q, hex q⟩

theorem template_core_minimal (hcov : Coverage rows cores template witness)
    (hex : ExactCoverage rows cores witness) (hlen : template.length = 105)
    (c : Fin 4935) (hc : c ∈ template) :
    MinimalInfeasible {r | r ∈ (cores c).map rows} := by
  obtain ⟨q, hq⟩ := exactCoverage_template rows cores template witness hcov hex hlen c hc
  have he : {r | r ∈ (cores c).map rows} = patternSet q := by
    ext r
    exact hq.mem_iff
  rw [he]
  exact pattern_minimal q

#print axioms exactCoverage_of_sizes
#print axioms exactCoverage_template
#print axioms template_core_minimal
end Crown.CertificateData
