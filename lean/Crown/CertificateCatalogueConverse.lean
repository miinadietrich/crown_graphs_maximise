import Crown.CertificateExactCatalogue

/-! Both directions of catalogue exactness, first for actual rank-row sets and
then for neighbourhood-mask sets. This file adds no finite data assumptions. -/
namespace Crown.CertificateData
open Crown.Ranks Crown.CertificateSemantics

theorem minimal_rowSet_in_template (rows : Fin 256 → RankRow)
    (cores : Fin 4935 → List (Fin 256)) (template : List (Fin 4935))
    (witness : Pattern → Fin 4935)
    (hcov : Coverage rows cores template witness)
    (hex : ExactCoverage rows cores witness)
    (S : Set RankRow) (hS : MinimalInfeasible S) :
    ∃ c ∈ template, S = {r | r ∈ (cores c).map rows} := by
  obtain ⟨q,hq⟩ := (minimal_infeasible_iff S).mp hS
  refine ⟨witness q,(hcov q).1,?_⟩
  rw [hq]
  ext r
  exact (hex q).mem_iff.symm

def rowImage (rows : Fin 256 → RankRow) (M : Finset (Fin 256)) : Set RankRow :=
  {r | ∃ m ∈ M, rows m = r}

theorem rowImage_list (rows : Fin 256 → RankRow) (L : List (Fin 256)) :
    rowImage rows L.toFinset = {r | r ∈ L.map rows} := by
  ext r
  simp [rowImage,List.mem_map]

theorem rowImage_injective (rows : Fin 256 → RankRow)
    (hinj : Function.Injective rows) : Function.Injective (rowImage rows) := by
  intro M N h
  apply Finset.Subset.antisymm
  · intro m hm
    have hr : rows m ∈ rowImage rows M := ⟨m,hm,rfl⟩
    rw [h] at hr
    obtain ⟨n,hn,he⟩ := hr
    simpa only [hinj he] using hn
  · intro m hm
    have hr : rows m ∈ rowImage rows N := ⟨m,hm,rfl⟩
    rw [←h] at hr
    obtain ⟨n,hn,he⟩ := hr
    simpa only [hinj he] using hn

def maskFeasible (rows : Fin 256 → RankRow) (M : Finset (Fin 256)) : Prop :=
  Feasible (fun m : {m // m ∈ M} => rows m.val)

def MinimalMaskFamily (rows : Fin 256 → RankRow) (M : Finset (Fin 256)) : Prop :=
  ¬ maskFeasible rows M ∧ ∀ T, T ⊂ M → maskFeasible rows T

theorem maskFeasible_iff_rowImage (rows : Fin 256 → RankRow)
    (M : Finset (Fin 256)) : maskFeasible rows M ↔ rowSetFeasible (rowImage rows M) := by
  let f : {m // m ∈ M} → rowImage rows M := fun m => ⟨rows m.val,m.val,m.property,rfl⟩
  have hf : Function.Surjective f := by
    intro r
    obtain ⟨m,hm,he⟩ := r.property
    exact ⟨⟨m,hm⟩,Subtype.ext he⟩
  exact feasible_surjective (fun r : rowImage rows M => r.val) f hf

theorem minimalMask_iff_rowImage (rows : Fin 256 → RankRow)
    (hinj : Function.Injective rows) (M : Finset (Fin 256)) :
    MinimalMaskFamily rows M ↔ MinimalInfeasible (rowImage rows M) := by
  classical
  constructor
  · rintro ⟨hn,hmin⟩
    refine ⟨fun h => hn ((maskFeasible_iff_rowImage rows M).mpr h),?_⟩
    intro S hS
    let T := M.filter (fun m => rows m ∈ S)
    have he : rowImage rows T = S := by
      ext r
      constructor
      · rintro ⟨m,hm,rfl⟩
        exact (Finset.mem_filter.mp hm).2
      · intro hr
        obtain ⟨m,hm,he⟩ := hS.subset hr
        exact ⟨m,Finset.mem_filter.mpr ⟨hm,he.symm ▸ hr⟩,he⟩
    have ht : T ⊂ M := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _,by
      intro h
      apply hS.ne
      rw [←he,h]⟩
    rw [←he]
    exact (maskFeasible_iff_rowImage rows T).mp (hmin T ht)
  · rintro ⟨hn,hmin⟩
    refine ⟨fun h => hn ((maskFeasible_iff_rowImage rows M).mp h),?_⟩
    intro T hT
    have ht : rowImage rows T ⊂ rowImage rows M := Set.ssubset_iff_subset_ne.mpr ⟨by
      rintro r ⟨m,hm,he⟩
      exact ⟨m,hT.subset hm,he⟩,by
      intro h
      exact hT.ne (rowImage_injective rows hinj h)⟩
    exact (maskFeasible_iff_rowImage rows T).mpr (hmin _ ht)

theorem minimal_maskSet_iff_template (rows : Fin 256 → RankRow)
    (hinj : Function.Injective rows) (cores : Fin 4935 → List (Fin 256))
    (template : List (Fin 4935)) (witness : Pattern → Fin 4935)
    (hcov : Coverage rows cores template witness)
    (hex : ExactCoverage rows cores witness) (hlen : template.length = 105)
    (M : Finset (Fin 256)) :
    MinimalMaskFamily rows M ↔ ∃ c ∈ template, (cores c).toFinset = M := by
  rw [minimalMask_iff_rowImage rows hinj]
  constructor
  · intro hM
    obtain ⟨c,hc,he⟩ := minimal_rowSet_in_template rows cores template witness hcov hex _ hM
    refine ⟨c,hc,rowImage_injective rows hinj ?_⟩
    rw [rowImage_list]
    exact he.symm
  · rintro ⟨c,hc,rfl⟩
    rw [rowImage_list]
    exact template_core_minimal rows cores template witness hcov hex hlen c hc

#print axioms minimal_rowSet_in_template
#print axioms minimalMask_iff_rowImage
#print axioms minimal_maskSet_iff_template
end Crown.CertificateData
