import Lean

namespace Crown.Ranks

universe u v w
variable {I : Type u} {V : Type v} {X : Type w}

abbrev InitialRow (I : Type u) := I → Option (Fin 3)
abbrev CompletedRow (I : Type u) := I → Fin 5

variable {ρ σ : InitialRow I} {r : CompletedRow I}

def prescribed (u : Fin 3) : Fin 5 := ⟨u.val + 1, by omega⟩

def completeEntry (a : Option (Fin 3)) (t : Bool) : Fin 5 :=
  match a with
  | none => if t then 4 else 0
  | some u => prescribed u

def complete (ρ : InitialRow I) (t : Bool) : CompletedRow I :=
  fun i => completeEntry (ρ i) t

def Completes (ρ : InitialRow I) (r : CompletedRow I) : Prop :=
  ∀ i, match ρ i with
  | none => r i = 0 ∨ r i = 4
  | some u => r i = prescribed u

def StrictBelow (r s : CompletedRow I) : Prop := ∀ i, r i < s i

def PotentialEntry (a b : Option (Fin 3)) : Prop :=
  ∀ u v : Fin 3, a = some u → b = some v → u < v

def PotentialBelow (ρ σ : InitialRow I) : Prop :=
  ∀ i, PotentialEntry (ρ i) (σ i)

def Fixed (ρ : InitialRow I) : Prop := ∀ i, ρ i ≠ none

def HasStar (ρ : InitialRow I) : Prop := ∃ i, ρ i = none

def OneStar (ρ : InitialRow I) : Prop :=
  ∃ j, ρ j = none ∧ ∀ i, ρ i = none → i = j

def MultiStar (ρ : InitialRow I) : Prop :=
  ∃ i j, i ≠ j ∧ ρ i = none ∧ ρ j = none

theorem complete_completes (ρ : InitialRow I) (t : Bool) :
    Completes ρ (complete ρ t) := by
  intro i
  cases h : ρ i with
  | none => cases t <;> simp [complete, completeEntry, h]
  | some u => simp [complete, completeEntry, h]

/-- The coordinate truth table, including the case of two coincident stars. -/
theorem completeEntry_lt_iff :
    ∀ (a b : Option (Fin 3)) (t u : Bool),
      completeEntry a t < completeEntry b u ↔
        PotentialEntry a b ∧ (a = none → t = false) ∧
          (b = none → u = true) := by
  intro a b t u
  cases a <;> cases b <;> cases t <;> cases u <;>
    simp [completeEntry, PotentialEntry, prescribed, Fin.lt_def] <;> omega

/-- Strict comparison between uniformly completed rows. -/
theorem strictBelow_complete_iff (ρ σ : InitialRow I) (t u : Bool) :
    StrictBelow (complete ρ t) (complete σ u) ↔
      PotentialBelow ρ σ ∧ (HasStar ρ → t = false) ∧
        (HasStar σ → u = true) := by
  constructor
  · intro h
    refine ⟨fun i => ((completeEntry_lt_iff _ _ _ _).mp (h i)).1, ?_, ?_⟩
    · rintro ⟨i, hi⟩
      exact ((completeEntry_lt_iff _ _ _ _).mp (h i)).2.1 hi
    · rintro ⟨i, hi⟩
      exact ((completeEntry_lt_iff _ _ _ _).mp (h i)).2.2 hi
  · rintro ⟨h, ht, hu⟩ i
    exact (completeEntry_lt_iff _ _ _ _).mpr
      ⟨h i, fun hi => ht ⟨i, hi⟩, fun hi => hu ⟨i, hi⟩⟩

theorem fixed_not_hasStar (h : Fixed ρ) : ¬ HasStar ρ := by
  rintro ⟨i, hi⟩
  exact h i hi

theorem oneStar_hasStar (h : OneStar ρ) : HasStar ρ := by
  obtain ⟨i, hi, _⟩ := h
  exact ⟨i, hi⟩

/-- A fixed row has a unique completion. -/
theorem fixed_completion_unique (hρ : Fixed ρ) (hr : Completes ρ r) (t : Bool) :
    r = complete ρ t := by
  funext i
  cases hi : ρ i with
  | none => exact False.elim (hρ i hi)
  | some u => simpa [complete, completeEntry, hi] using hr i

/-- Every completion of a one-star row is represented by its Boolean variable. -/
theorem oneStar_completion_coverage (hρ : OneStar ρ) (hr : Completes ρ r) :
    ∃ t : Bool, r = complete ρ t := by
  obtain ⟨j, hj, hu⟩ := hρ
  have hstar : r j = 0 ∨ r j = 4 := by simpa [hj] using hr j
  rcases hstar with hz | hf
  · refine ⟨false, ?_⟩
    funext i
    cases hi : ρ i with
    | none =>
      have hij := hu i hi
      subst i
      simpa [complete, completeEntry, hj] using hz
    | some u => simpa [complete, completeEntry, hi] using hr i
  · refine ⟨true, ?_⟩
    funext i
    cases hi : ρ i with
    | none =>
      have hij := hu i hi
      subst i
      simpa [complete, completeEntry, hj] using hf
    | some u => simpa [complete, completeEntry, hi] using hr i

/-- The first line of the manuscript's Boolean constraint table. -/
theorem fixed_fixed_comparison (hρ : Fixed ρ) (hσ : Fixed σ) (t u : Bool) :
    StrictBelow (complete ρ t) (complete σ u) ↔ PotentialBelow ρ σ := by
  simp [strictBelow_complete_iff, fixed_not_hasStar hρ, fixed_not_hasStar hσ]

/-- The second line of the table: the lower row's star must receive 4. -/
theorem oneStar_fixed_constraint (hρ : OneStar ρ) (hσ : Fixed σ)
    (hp : PotentialBelow ρ σ) (t u : Bool) :
    ¬ StrictBelow (complete ρ t) (complete σ u) ↔ t = true := by
  have hs := oneStar_hasStar hρ
  simp only [strictBelow_complete_iff, hp, hs, true_implies,
    fixed_not_hasStar hσ, false_implies, and_true, true_and]
  cases t <;> decide

/-- The third line of the table: the upper row's star must receive 0. -/
theorem fixed_oneStar_constraint (hρ : Fixed ρ) (hσ : OneStar σ)
    (hp : PotentialBelow ρ σ) (t u : Bool) :
    ¬ StrictBelow (complete ρ t) (complete σ u) ↔ u = false := by
  have hs := oneStar_hasStar hσ
  simp only [strictBelow_complete_iff, hp, hs, true_implies,
    fixed_not_hasStar hρ, false_implies, true_and]
  cases u <;> decide

/-- The fourth line of the table, without a distinct-star-coordinate assumption. -/
theorem oneStar_oneStar_constraint (hρ : OneStar ρ) (hσ : OneStar σ)
    (hp : PotentialBelow ρ σ) (t u : Bool) :
    ¬ StrictBelow (complete ρ t) (complete σ u) ↔ (u = true → t = true) := by
  have hsρ := oneStar_hasStar hρ
  have hsσ := oneStar_hasStar hσ
  simp only [strictBelow_complete_iff, hp, hsρ, hsσ, true_implies, true_and]
  cases t <;> cases u <;> decide

/-- A completed row containing both extremes cannot compare with any row. -/
theorem extremes_incomparable (r : CompletedRow I)
    (hz : ∃ i, r i = 0) (hf : ∃ i, r i = 4) (s : CompletedRow I) :
    ¬ StrictBelow r s ∧ ¬ StrictBelow s r := by
  obtain ⟨i, hi⟩ := hz
  obtain ⟨j, hj⟩ := hf
  constructor
  · intro h
    have hlt := h j
    rw [hj] at hlt
    have hb := (s j).isLt
    change 4 < (s j).val at hlt
    omega
  · intro h
    have hlt := h i
    rw [hi] at hlt
    change (s i).val < 0 at hlt
    omega

/-- L09: a row with at least two stars admits a universally incomparable completion. -/
theorem multiStar_completion (ρ : InitialRow I) (h : MultiStar ρ) :
    ∃ r : CompletedRow I, Completes ρ r ∧
      ∀ s : CompletedRow I, ¬ StrictBelow r s ∧ ¬ StrictBelow s r := by
  classical
  obtain ⟨i, j, hij, hi, hj⟩ := h
  let r : CompletedRow I := fun a =>
    if a = j then 4 else completeEntry (ρ a) false
  refine ⟨r, ?_, ?_⟩
  · intro a
    by_cases ha : a = j
    · subst a
      simp [r, hj]
    · cases he : ρ a with
      | none => simp [r, ha, he, completeEntry]
      | some u => simp [r, ha, he, completeEntry]
  · intro s
    apply extremes_incomparable r
    · exact ⟨i, by simp [r, hij, hi, completeEntry]⟩
    · exact ⟨j, by simp [r]⟩

/-- Four prescribed ranks cannot increase strictly within one coordinate. -/
theorem no_four_prescribed (a b c d : Fin 3) :
    ¬ (a < b ∧ b < c ∧ c < d) := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  simp only [Fin.lt_def]
  omega

/-- Three strictly increasing prescribed ranks are exactly 1,2,3 in manuscript notation. -/
theorem three_prescribed_values (a b c : Fin 3) (hab : a < b) (hbc : b < c) :
    a.val = 0 ∧ b.val = 1 ∧ c.val = 2 := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [Fin.lt_def] at hab hbc
  omega

theorem no_four_nonstar (a b c d : InitialRow I) (i : I)
    (ha : a i ≠ none) (hb : b i ≠ none) (hc : c i ≠ none) (hd : d i ≠ none)
    (hab : PotentialBelow a b) (hbc : PotentialBelow b c)
    (hcd : PotentialBelow c d) : False := by
  cases ea : a i with
  | none => exact ha ea
  | some av =>
    cases eb : b i with
    | none => exact hb eb
    | some bv =>
      cases ec : c i with
      | none => exact hc ec
      | some cv =>
        cases ed : d i with
        | none => exact hd ed
        | some dv =>
          exact no_four_prescribed av bv cv dv
            ⟨hab i av bv ea eb, hbc i bv cv eb ec, hcd i cv dv ec ed⟩

/-- At least four coordinates leave one outside any three specified coordinates. -/
theorem coordinate_avoiding_three (hk : 4 ≤ k) (a b c : Fin k) :
    ∃ i : Fin k, i ≠ a ∧ i ≠ b ∧ i ≠ c := by
  classical
  apply Classical.byContradiction
  intro hn
  have h : ∀ i : Fin k, i = a ∨ i = b ∨ i = c := by
    intro i
    by_cases ha : i = a
    · exact Or.inl ha
    by_cases hb : i = b
    · exact Or.inr (Or.inl hb)
    exact Or.inr (Or.inr (Classical.byContradiction (fun hc => hn ⟨i, ha, hb, hc⟩)))
  have h0 := h ⟨0, by omega⟩
  have h1 := h ⟨1, by omega⟩
  have h2 := h ⟨2, by omega⟩
  have h3 := h ⟨3, by omega⟩
  simp only [Fin.ext_iff] at h0 h1 h2 h3
  omega

/-- The long-path impossibility used in L13: a fixed row cannot be followed
by three one-star rows in an increasing potential chain when k ≥ 4. -/
theorem no_fixed_three_star_chain (hk : 4 ≤ k)
    (a b c d : InitialRow (Fin k)) (ha : Fixed a)
    (hb : OneStar b) (hc : OneStar c) (hd : OneStar d)
    (hab : PotentialBelow a b) (hbc : PotentialBelow b c)
    (hcd : PotentialBelow c d) : False := by
  obtain ⟨ib, _, hub⟩ := hb
  obtain ⟨ic, _, huc⟩ := hc
  obtain ⟨id, _, hud⟩ := hd
  obtain ⟨i, hib, hic, hid⟩ := coordinate_avoiding_three hk ib ic id
  exact no_four_nonstar a b c d i (ha i)
    (fun h => hib (hub i h)) (fun h => hic (huc i h))
    (fun h => hid (hud i h)) hab hbc hcd

/-- The two-intermediate-row impossibility used in L13. -/
theorem no_fixed_two_star_fixed_chain (hk : 4 ≤ k)
    (a b c d : InitialRow (Fin k)) (ha : Fixed a)
    (hb : OneStar b) (hc : OneStar c) (hd : Fixed d)
    (hab : PotentialBelow a b) (hbc : PotentialBelow b c)
    (hcd : PotentialBelow c d) : False := by
  obtain ⟨ib, _, hub⟩ := hb
  obtain ⟨ic, _, huc⟩ := hc
  obtain ⟨i, hib, hic, _⟩ := coordinate_avoiding_three hk ib ic ic
  exact no_four_nonstar a b c d i (ha i)
    (fun h => hib (hub i h)) (fun h => hic (huc i h)) (hd i) hab hbc hcd

theorem no_three_star_fixed_chain (hk : 4 ≤ k)
    (a b c d : InitialRow (Fin k)) (ha : OneStar a)
    (hb : OneStar b) (hc : OneStar c) (hd : Fixed d)
    (hab : PotentialBelow a b) (hbc : PotentialBelow b c)
    (hcd : PotentialBelow c d) : False := by
  obtain ⟨ia, _, hua⟩ := ha
  obtain ⟨ib, _, hub⟩ := hb
  obtain ⟨ic, _, huc⟩ := hc
  obtain ⟨i, hia, hib, hic⟩ := coordinate_avoiding_three hk ia ib ic
  exact no_four_nonstar a b c d i
    (fun h => hia (hua i h)) (fun h => hib (hub i h))
    (fun h => hic (huc i h)) (hd i) hab hbc hcd

/-! The abstract implication-closure argument used by the finite test. -/

/-- Closure of the directly forced-1 variables under directed implications. -/
inductive Forced (one : X → Prop) (edge : X → X → Prop) : X → Prop
  | seed {x} : one x → Forced one edge x
  | step {x y} : Forced one edge x → edge x y → Forced one edge y

def ValidChoice (one zero : X → Prop) (edge : X → X → Prop) (t : X → Bool) : Prop :=
  (∀ x, one x → t x = true) ∧ (∀ x, zero x → t x = false) ∧
    (∀ x y, edge x y → t x = true → t y = true)

theorem forced_true (h : ValidChoice one zero edge t) (hf : Forced one edge x) :
    t x = true := by
  induction hf with
  | seed ho => exact h.1 _ ho
  | step _ he ih => exact h.2.2 _ _ he ih

/-- L11's implication-closure criterion; it holds without a finiteness restriction.
The separate obstruction from a fixed/fixed pair is handled by the rank table. -/
theorem choice_exists_iff (one zero : X → Prop) (edge : X → X → Prop) :
    (∃ t, ValidChoice one zero edge t) ↔
      ¬ ∃ x, Forced one edge x ∧ zero x := by
  classical
  constructor
  · rintro ⟨t, ht⟩ ⟨x, hf, hz⟩
    have htrue := forced_true ht hf
    have hfalse := ht.2.1 x hz
    simp [htrue] at hfalse
  · intro hn
    let t : X → Bool := fun x => decide (Forced one edge x)
    refine ⟨t, ?_, ?_, ?_⟩
    · intro x hx
      exact decide_eq_true (Forced.seed hx)
    · intro x hx
      apply decide_eq_false
      intro hf
      exact hn ⟨x, hf, hx⟩
    · intro x y he hx
      have hf : Forced one edge x := of_decide_eq_true hx
      exact decide_eq_true (Forced.step hf he)

def DirectOne (rows : V → InitialRow I) (b : V) : Prop :=
  OneStar (rows b) ∧ ∃ u, Fixed (rows u) ∧ PotentialBelow (rows b) (rows u)

def DirectZero (rows : V → InitialRow I) (b : V) : Prop :=
  OneStar (rows b) ∧ ∃ l, Fixed (rows l) ∧ PotentialBelow (rows l) (rows b)

def Implies (rows : V → InitialRow I) (b c : V) : Prop :=
  OneStar (rows b) ∧ OneStar (rows c) ∧ PotentialBelow (rows c) (rows b)

/-- With k ≥ 4, every forced variable is direct or one implication from direct. -/
theorem forced_short (hk : 4 ≤ k) (rows : V → InitialRow (Fin k))
    (hf : Forced (DirectOne rows) (Implies rows) b) :
    DirectOne rows b ∨
      (OneStar (rows b) ∧ ∃ c u, OneStar (rows c) ∧ Fixed (rows u) ∧
        PotentialBelow (rows b) (rows c) ∧ PotentialBelow (rows c) (rows u)) := by
  induction hf with
  | seed h => exact Or.inl h
  | @step x y _ he ih =>
    rcases ih with hd | ⟨_, c, u, hc, hu, hxc, hcu⟩
    · obtain ⟨hx, u, hu, hxu⟩ := hd
      exact Or.inr ⟨he.2.1, x, u, hx, hu, he.2.2, hxu⟩
    · exact False.elim (no_three_star_fixed_chain hk (rows y) (rows x)
        (rows c) (rows u) he.2.1 he.1 hc hu he.2.2 hxc hcu)

/-- L12's implication part: a contradictory closure contains a direct conflict. -/
theorem forced_zero_iff_direct (hk : 4 ≤ k) (rows : V → InitialRow (Fin k)) :
    (∃ b, Forced (DirectOne rows) (Implies rows) b ∧ DirectZero rows b) ↔
      ∃ b, DirectOne rows b ∧ DirectZero rows b := by
  constructor
  · rintro ⟨b, hf, hz⟩
    rcases forced_short hk rows hf with hd | ⟨hb, c, u, hc, hu, hbc, hcu⟩
    · exact ⟨b, hd, hz⟩
    · obtain ⟨_, l, hl, hlb⟩ := hz
      exact False.elim (no_fixed_two_star_fixed_chain hk (rows l) (rows b)
        (rows c) (rows u) hl hb hc hu hlb hbc hcu)
  · rintro ⟨b, ho, hz⟩
    exact ⟨b, Forced.seed ho, hz⟩

theorem rank_choice_exists_iff (hk : 4 ≤ k) (rows : V → InitialRow (Fin k)) :
    (∃ t, ValidChoice (DirectOne rows) (DirectZero rows) (Implies rows) t) ↔
      ¬ ∃ b, DirectOne rows b ∧ DirectZero rows b := by
  rw [choice_exists_iff, forced_zero_iff_direct hk rows]

def Feasible (rows : V → InitialRow I) : Prop :=
  ∃ r : V → CompletedRow I, (∀ b, Completes (rows b) (r b)) ∧
    ∀ b c, ¬ StrictBelow (r b) (r c)

/-- With a nonempty coordinate type, including equal row indices in `Feasible`
is equivalent to the manuscript's restriction to distinct vertices. -/
theorem feasible_iff_distinct [Nonempty I] (rows : V → InitialRow I) :
    Feasible rows ↔ ∃ r : V → CompletedRow I,
      (∀ b, Completes (rows b) (r b)) ∧
        ∀ b c, b ≠ c → ¬ StrictBelow (r b) (r c) := by
  constructor
  · rintro ⟨r, hr, hn⟩
    exact ⟨r, hr, fun b c _ => hn b c⟩
  · rintro ⟨r, hr, hn⟩
    refine ⟨r, hr, ?_⟩
    intro b c hlt
    by_cases hbc : b = c
    · subst c
      obtain ⟨i⟩ := ‹Nonempty I›
      exact Nat.lt_irrefl _ (hlt i)
    · exact hn b c hbc hlt

def NoFixedPair (rows : V → InitialRow I) : Prop :=
  ∀ b c, Fixed (rows b) → Fixed (rows c) → ¬ PotentialBelow (rows b) (rows c)

theorem fixed_or_oneStar_of_not_multiStar (ρ : InitialRow I) (h : ¬ MultiStar ρ) :
    Fixed ρ ∨ OneStar ρ := by
  classical
  by_cases hs : HasStar ρ
  · obtain ⟨j, hj⟩ := hs
    refine Or.inr ⟨j, hj, ?_⟩
    intro i hi
    exact Classical.byContradiction (fun hij => h ⟨i, j, hij, hi, hj⟩)
  · exact Or.inl (fun i hi => hs ⟨i, hi⟩)

/-- L09--L11 combined: the rank completion problem is exactly its Boolean system
together with the absence of fixed-pair obstructions. -/
theorem feasible_iff_constraints (rows : V → InitialRow I) :
    Feasible rows ↔ NoFixedPair rows ∧
      ∃ t, ValidChoice (DirectOne rows) (DirectZero rows) (Implies rows) t := by
  classical
  constructor
  · rintro ⟨r, hr, hn⟩
    have hp : NoFixedPair rows := by
      intro b c hb hc hbc
      apply hn b c
      rw [fixed_completion_unique hb (hr b) false,
        fixed_completion_unique hc (hr c) false]
      exact (fixed_fixed_comparison hb hc false false).mpr hbc
    let t : V → Bool := fun b =>
      if h : OneStar (rows b) then
        Classical.choose (oneStar_completion_coverage h (hr b)) else false
    have ht : ∀ b, OneStar (rows b) → r b = complete (rows b) (t b) := by
      intro b hb
      simp only [t, dif_pos hb]
      exact Classical.choose_spec (oneStar_completion_coverage hb (hr b))
    refine ⟨hp, t, ?_, ?_, ?_⟩
    · rintro b ⟨hb, u, hu, hbu⟩
      apply (oneStar_fixed_constraint hb hu hbu (t b) false).mp
      rw [← ht b hb, ← fixed_completion_unique hu (hr u) false]
      exact hn b u
    · rintro b ⟨hb, l, hl, hlb⟩
      apply (fixed_oneStar_constraint hl hb hlb false (t b)).mp
      rw [← fixed_completion_unique hl (hr l) false, ← ht b hb]
      exact hn l b
    · rintro b c ⟨hb, hc, hcb⟩ hbt
      apply (oneStar_oneStar_constraint hc hb hcb (t c) (t b)).mp _ hbt
      rw [← ht c hc, ← ht b hb]
      exact hn c b
  · rintro ⟨hp, t, ht⟩
    let r : V → CompletedRow I := fun b =>
      if h : MultiStar (rows b) then Classical.choose (multiStar_completion (rows b) h)
      else complete (rows b) (t b)
    have hr : ∀ b, Completes (rows b) (r b) := by
      intro b
      by_cases hb : MultiStar (rows b)
      · simpa only [r, dif_pos hb] using
          (Classical.choose_spec (multiStar_completion (rows b) hb)).1
      · simpa only [r, dif_neg hb] using complete_completes (rows b) (t b)
    refine ⟨r, hr, ?_⟩
    intro b c hlt
    by_cases hb : MultiStar (rows b)
    · have hi := (Classical.choose_spec (multiStar_completion (rows b) hb)).2 (r c)
      exact hi.1 (by simpa only [r, dif_pos hb] using hlt)
    by_cases hc : MultiStar (rows c)
    · have hi := (Classical.choose_spec (multiStar_completion (rows c) hc)).2 (r b)
      exact hi.2 (by simpa only [r, dif_pos hc] using hlt)
    have hcomp : StrictBelow (complete (rows b) (t b)) (complete (rows c) (t c)) := by
      simpa only [r, dif_neg hb, dif_neg hc] using hlt
    obtain ⟨hpot, htb, htc⟩ := (strictBelow_complete_iff _ _ _ _).mp hcomp
    rcases fixed_or_oneStar_of_not_multiStar (rows b) hb with hbf | hbs
    · rcases fixed_or_oneStar_of_not_multiStar (rows c) hc with hcf | hcs
      · exact hp b c hbf hcf hpot
      · have hzero := ht.2.1 c ⟨hcs, b, hbf, hpot⟩
        have hone := htc (oneStar_hasStar hcs)
        simp [hzero] at hone
    · have hzero := htb (oneStar_hasStar hbs)
      rcases fixed_or_oneStar_of_not_multiStar (rows c) hc with hcf | hcs
      · have hone := ht.1 b ⟨hbs, c, hcf, hpot⟩
        simp [hzero] at hone
      · have hone := ht.2.2 c b ⟨hcs, hbs, hpot⟩ (htc (oneStar_hasStar hcs))
        simp [hzero] at hone

/-- L12: complete obstruction classification for arbitrary rank families, k ≥ 4. -/
theorem feasible_iff_no_obstructions (hk : 4 ≤ k) (rows : V → InitialRow (Fin k)) :
    Feasible rows ↔ NoFixedPair rows ∧
      ¬ ∃ b, DirectOne rows b ∧ DirectZero rows b := by
  rw [feasible_iff_constraints, rank_choice_exists_iff hk rows]

/-- The rank pattern in the central row obstruction is forced: off its star,
the lower, central and upper prescribed ranks are exactly 1,2,3. -/
theorem central_triple_values (l c u : InitialRow I) (j : I)
    (hl : Fixed l) (hc : OneStar c) (hu : Fixed u) (hj : c j = none)
    (hlc : PotentialBelow l c) (hcu : PotentialBelow c u) :
    ∀ i, i ≠ j → l i = some 0 ∧ c i = some 1 ∧ u i = some 2 := by
  obtain ⟨j', _, huniq⟩ := hc
  intro i hij
  have hc' : c i ≠ none := fun he => hij ((huniq i he).trans (huniq j hj).symm)
  cases el : l i with
  | none => exact False.elim (hl i el)
  | some lv =>
    cases ec : c i with
    | none => exact False.elim (hc' ec)
    | some cv =>
      cases eu : u i with
      | none => exact False.elim (hu i eu)
      | some uv =>
        obtain ⟨h0, h1, h2⟩ := three_prescribed_values lv cv uv
          (hlc i lv cv el ec) (hcu i cv uv ec eu)
        exact ⟨congrArg some (Fin.ext h0),
          congrArg some (Fin.ext h1), congrArg some (Fin.ext h2)⟩

#print axioms completeEntry_lt_iff
#print axioms strictBelow_complete_iff
#print axioms oneStar_oneStar_constraint
#print axioms oneStar_completion_coverage
#print axioms multiStar_completion
#print axioms no_four_prescribed
#print axioms three_prescribed_values
#print axioms no_fixed_three_star_chain
#print axioms no_fixed_two_star_fixed_chain
#print axioms choice_exists_iff
#print axioms forced_zero_iff_direct
#print axioms rank_choice_exists_iff
#print axioms feasible_iff_constraints
#print axioms feasible_iff_no_obstructions
#print axioms central_triple_values

end Crown.Ranks
