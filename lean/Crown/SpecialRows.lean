import Crown.Ranks

/-! With one distinguished coordinate restricted to star or rank one, the
short-obstruction classification also holds for three coordinates. -/

namespace Crown.SpecialRows
open Crown.Ranks

universe u
variable {k : Nat} {V : Type u} (rows : V → InitialRow (Fin k)) (z : Fin k)

theorem comparison_star (hsp : ∀ b, rows b z = none ∨ rows b z = some 0)
    {a b : V} (h : PotentialBelow (rows a) (rows b)) :
    rows a z = none ∨ rows b z = none := by
  rcases hsp a with ha | ha
  · exact Or.inl ha
  rcases hsp b with hb | hb
  · exact Or.inr hb
  exact False.elim ((Nat.lt_irrefl 0) (h z 0 0 ha hb))

theorem avoiding_two (hk : 3 ≤ k) (a b : Fin k) :
    ∃ i : Fin k, i ≠ a ∧ i ≠ b := by
  apply Classical.byContradiction
  intro hn
  have h : ∀ i : Fin k, i = a ∨ i = b := by
    intro i
    by_cases hi : i = a
    · exact Or.inl hi
    · exact Or.inr (Classical.byContradiction (fun hb => hn ⟨i, hi, hb⟩))
  have h0 := h ⟨0, by omega⟩
  have h1 := h ⟨1, by omega⟩
  have h2 := h ⟨2, by omega⟩
  simp only [Fin.ext_iff] at h0 h1 h2
  omega

theorem no_three_star_fixed (hsp : ∀ b, rows b z = none ∨ rows b z = some 0)
    (hk : 3 ≤ k) (a b c u : V)
    (ha : OneStar (rows a)) (hb : OneStar (rows b)) (hc : OneStar (rows c))
    (hu : Fixed (rows u)) (hab : PotentialBelow (rows a) (rows b))
    (hbc : PotentialBelow (rows b) (rows c)) (hcu : PotentialBelow (rows c) (rows u)) : False := by
  have hcz : rows c z = none := (comparison_star rows z hsp hcu).resolve_right (hu z)
  obtain ⟨ic, hic, huc⟩ := hc
  have hicz : ic = z := (huc z hcz).symm
  subst ic
  obtain ⟨ia, hia, hua⟩ := ha
  obtain ⟨ib, hib, hub⟩ := hb
  rcases comparison_star rows z hsp hab with haz | hbz
  · have hiaz : ia = z := (hua z haz).symm
    subst ia
    obtain ⟨i, hiz, hib'⟩ := avoiding_two hk z ib
    exact no_four_nonstar (rows a) (rows b) (rows c) (rows u) i
      (fun h => hiz (hua i h)) (fun h => hib' (hub i h))
      (fun h => hiz (huc i h)) (hu i) hab hbc hcu
  · have hibz : ib = z := (hub z hbz).symm
    subst ib
    obtain ⟨i, hiz, hia'⟩ := avoiding_two hk z ia
    exact no_four_nonstar (rows a) (rows b) (rows c) (rows u) i
      (fun h => hia' (hua i h)) (fun h => hiz (hub i h))
      (fun h => hiz (huc i h)) (hu i) hab hbc hcu

theorem no_fixed_two_star_fixed (hk : 3 ≤ k) (a b c d : InitialRow (Fin k))
    (ha : Fixed a) (hb : OneStar b) (hc : OneStar c) (hd : Fixed d)
    (hab : PotentialBelow a b) (hbc : PotentialBelow b c) (hcd : PotentialBelow c d) : False := by
  obtain ⟨ib, _, hub⟩ := hb
  obtain ⟨ic, _, huc⟩ := hc
  obtain ⟨i, hib, hic⟩ := avoiding_two hk ib ic
  exact no_four_nonstar a b c d i (ha i)
    (fun h => hib (hub i h)) (fun h => hic (huc i h)) (hd i) hab hbc hcd

theorem forced_short (hsp : ∀ b, rows b z = none ∨ rows b z = some 0)
    (hk : 3 ≤ k) {b : V}
    (hf : Forced (DirectOne rows) (Implies rows) b) :
    DirectOne rows b ∨ (OneStar (rows b) ∧ ∃ c u, OneStar (rows c) ∧ Fixed (rows u) ∧
      PotentialBelow (rows b) (rows c) ∧ PotentialBelow (rows c) (rows u)) := by
  induction hf with
  | seed h => exact Or.inl h
  | @step x y _ he ih =>
    rcases ih with hd | ⟨_, c, u, hc, hu, hxc, hcu⟩
    · obtain ⟨hx, u, hu, hxu⟩ := hd
      exact Or.inr ⟨he.2.1, x, u, hx, hu, he.2.2, hxu⟩
    · exact False.elim (no_three_star_fixed rows z hsp hk y x c u
        he.2.1 he.1 hc hu he.2.2 hxc hcu)

theorem forced_zero_iff_direct (hsp : ∀ b, rows b z = none ∨ rows b z = some 0)
    (hk : 3 ≤ k) :
    (∃ b, Forced (DirectOne rows) (Implies rows) b ∧ DirectZero rows b) ↔
      ∃ b, DirectOne rows b ∧ DirectZero rows b := by
  constructor
  · rintro ⟨b, hf, hz⟩
    rcases forced_short rows z hsp hk hf with hd | ⟨hb, c, u, hc, hu, hbc, hcu⟩
    · exact ⟨b, hd, hz⟩
    · obtain ⟨_, l, hl, hlb⟩ := hz
      exact False.elim (no_fixed_two_star_fixed hk (rows l) (rows b) (rows c) (rows u)
        hl hb hc hu hlb hbc hcu)
  · rintro ⟨b, ho, hz⟩
    exact ⟨b, Forced.seed ho, hz⟩

theorem feasible_iff (hsp : ∀ b, rows b z = none ∨ rows b z = some 0)
    (hk : 3 ≤ k) :
    Feasible rows ↔ NoFixedPair rows ∧ ¬ ∃ b, DirectOne rows b ∧ DirectZero rows b := by
  rw [feasible_iff_constraints, choice_exists_iff, forced_zero_iff_direct rows z hsp hk]

#print axioms feasible_iff

end Crown.SpecialRows
