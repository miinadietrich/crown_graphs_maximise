import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! The vertex-selection argument of Section 6.2. Neighbourhoods may repeat:
the indexing type B retains the multiplicity of every vertex. -/

namespace Crown

theorem exists_safe_odd_vertex_three {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (k : ℕ) (hk : 3 ≤ k)
    (hA : Fintype.card A = 2*k-1)
    (hB : Fintype.card B ≤ Fintype.card A + 2) (N : B → Finset A) :
    ∃ a : A, (¬ ∃ c : B, N c = Finset.univ.erase a) ∨
      ∀ l u : B, (N l).card = k → (N u).card = k →
        a ∈ N l → a ∈ N u → l = u := by
  classical
  by_cases hall : ∀ a : A, ∃ c : B, N c = Finset.univ.erase a
  · choose f hf using hall
    have hfi : Function.Injective f := by
      intro a b hab
      have he : Finset.univ.erase a = Finset.univ.erase b := by
        rw [← hf a, ← hf b, hab]
      exact (Finset.erase_inj _ (Finset.mem_univ a)).mp he
    let C : Finset B := Finset.univ.image f
    let F : Finset B := Finset.univ.filter (fun b => (N b).card = k)
    have hC : C.card = Fintype.card A := by simp [C, Finset.card_image_of_injective, hfi]
    have hFC : F ⊆ Finset.univ \ C := by
      intro b hb
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, ?_⟩
      intro hbc
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hbc
      have hdeg : (N (f a)).card = k := (Finset.mem_filter.mp hb).2
      rw [hf a, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, hA] at hdeg
      omega
    have hF : F.card ≤ 2 := by
      have hle := Finset.card_le_card hFC
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ C), Finset.card_univ, hC] at hle
      omega
    by_cases hnonempty : F.Nonempty
    · obtain ⟨b, hb⟩ := hnonempty
      have hdeg : (N b).card = k := (Finset.mem_filter.mp hb).2
      have hsmall : (N b).card < (Finset.univ : Finset A).card := by
        rw [hdeg, Finset.card_univ, hA]
        omega
      obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
      refine ⟨a, Or.inr ?_⟩
      intro l u hl hu hal hau
      have herase : (F.erase b).card ≤ 1 := by
        rw [Finset.card_erase_of_mem hb]
        omega
      apply Finset.card_le_one.mp herase
      · apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩⟩
        intro h; subst l; exact ha hal
      · apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩⟩
        intro h; subst u; exact ha hau
    · have hpos : 0 < (Finset.univ : Finset A).card := by
        rw [Finset.card_univ, hA]; omega
      obtain ⟨a, _⟩ := Finset.card_pos.mp hpos
      refine ⟨a, Or.inr ?_⟩
      intro l u hl _ _ _
      exact False.elim (hnonempty ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩⟩)
  · push_neg at hall
    obtain ⟨a, ha⟩ := hall
    exact ⟨a, Or.inl (by simpa using ha)⟩

theorem exists_safe_odd_vertex {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (k : ℕ) (hk : 4 ≤ k)
    (hA : Fintype.card A = 2*k-1)
    (hB : Fintype.card B ≤ Fintype.card A + 2) (N : B → Finset A) :
    ∃ a : A, (¬ ∃ c : B, N c = Finset.univ.erase a) ∨
      ∀ l u : B, (N l).card = k → (N u).card = k →
        a ∈ N l → a ∈ N u → l = u :=
  exists_safe_odd_vertex_three k (by omega) hA hB N

#print axioms exists_safe_odd_vertex_three
#print axioms exists_safe_odd_vertex

end Crown
