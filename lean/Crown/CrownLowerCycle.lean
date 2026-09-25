import Crown.CrownLowerCounts

namespace Crown.CrownLower

variable {V : Type*}

def weightSum (f : V → ℤ) (L : List V) : ℤ := (L.map f).sum

@[simp] theorem weightSum_nil (f : V → ℤ) : weightSum f [] = 0 := rfl
@[simp] theorem weightSum_cons (f : V → ℤ) (a : V) (L : List V) :
    weightSum f (a::L) = f a + weightSum f L := by simp [weightSum]
@[simp] theorem weightSum_append (f : V → ℤ) (L M : List V) :
    weightSum f (L++M) = weightSum f L + weightSum f M := by simp [weightSum]

theorem exists_minimum_prefix (f : V → ℤ) (L : List V) :
    ∃ u v, L = u ++ v ∧ ∀ p, p <+: L → weightSum f u ≤ weightSum f p := by
  induction L with
  | nil =>
    refine ⟨[],[],rfl,?_⟩
    intro p hp
    have : p = [] := List.prefix_nil.mp hp
    simp [this]
  | cons a L ih =>
    obtain ⟨u,v,hL,hmin⟩ := ih
    by_cases hnonneg : 0 ≤ f a + weightSum f u
    · refine ⟨[],a::L,rfl,?_⟩
      intro p hp
      rcases List.prefix_cons_iff.mp hp with rfl | ⟨t,rfl,ht⟩
      · simp
      · have := hmin t ht
        simp only [weightSum_nil,weightSum_cons]
        omega
    · refine ⟨a::u,v,by simp [hL],?_⟩
      intro p hp
      rcases List.prefix_cons_iff.mp hp with rfl | ⟨t,rfl,ht⟩
      · simp only [weightSum_nil,weightSum_cons]
        omega
      · have := hmin t ht
        simp only [weightSum_cons]
        omega

theorem exists_nonnegative_rotation (f : V → ℤ) (L : List V)
    (hzero : weightSum f L = 0) :
    ∃ u v, L = u ++ v ∧ ∀ p, p <+: v ++ u → 0 ≤ weightSum f p := by
  obtain ⟨u,v,hL,hmin⟩ := exists_minimum_prefix f L
  refine ⟨u,v,hL,?_⟩
  have htotal : weightSum f u + weightSum f v = 0 := by simpa [hL] using hzero
  intro p hp
  rcases List.prefix_or_prefix_of_prefix hp (List.prefix_append v u) with h | h
  · have hp' : u ++ p <+: L := by
      rw [hL]
      exact List.prefix_append_right_inj u |>.mpr h
    have hh := hmin (u++p) hp'
    simp only [weightSum_append] at hh
    omega
  · obtain ⟨r,hr⟩ := h
    have hp' : r <+: u := by
      rw [← hr] at hp
      exact (List.prefix_append_right_inj v).mp hp
    have hh := hmin r (by rw [hL]; exact List.prefix_append_of_prefix hp')
    rw [← hr,weightSum_append]
    omega

#print axioms exists_nonnegative_rotation

end Crown.CrownLower
