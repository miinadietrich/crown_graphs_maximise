import Crown.Orientations
import Crown.SpecialRows
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Crown.OddRanks

open Crown.Ranks

variable {k : ℕ} {B : Type*}

def degree (N : Orientations.NeighbourRow (Fin k)) : ℕ :=
  ∑ i, ((if (N i).1 then 1 else 0) + (if (N i).2 then 1 else 0))

def Centre (N : Orientations.NeighbourRow (Fin k)) (z : Fin k) : Prop :=
  ∀ i, N i = if i = z then (false, false) else (true, true)

def Safe (N : B → Orientations.NeighbourRow (Fin k)) (z : Fin k) : Prop :=
  (¬ ∃ c, Centre (N c) z) ∨
    ∀ l u, degree (N l) = k → degree (N u) = k →
      (N l z).1 = true → (N u z).1 = true → l = u

abbrev rows (N : B → Orientations.NeighbourRow (Fin k)) : B → InitialRow (Fin k) :=
  fun b => Orientations.row (N b) (fun _ => false)

theorem entry_zero_iff (p : Bool × Bool) :
    Orientations.entry p false = some 0 ↔ p = (true, false) := by
  rcases p with ⟨a,b⟩; cases a <;> cases b <;> decide

theorem entry_one_iff (p : Bool × Bool) :
    Orientations.entry p false = some 1 ↔ p = (true, true) := by
  rcases p with ⟨a,b⟩; cases a <;> cases b <;> decide

theorem entry_two_iff (p : Bool × Bool) :
    Orientations.entry p false = some 2 ↔ p = (false, true) := by
  rcases p with ⟨a,b⟩; cases a <;> cases b <;> decide

theorem fixed_special (N : B → Orientations.NeighbourRow (Fin k)) (z : Fin k)
    (hsp : ∀ b, (N b z).2 = false) (b : B) (hb : Fixed (rows N b)) :
    N b z = (true, false) := by
  have hn := hb z
  rcases he : N b z with ⟨a,s⟩
  have hs := hsp b
  rw [he] at hs
  cases s <;> cases a <;> simp_all [rows, Orientations.row, Orientations.entry]

theorem no_fixed_pair (N : B → Orientations.NeighbourRow (Fin k)) (z : Fin k)
    (hsp : ∀ b, (N b z).2 = false) : NoFixedPair (rows N) := by
  intro b c hb hc hbc
  have hbz := fixed_special N z hsp b hb
  have hcz := fixed_special N z hsp c hc
  have hlt := hbc z 0 0 ((entry_zero_iff _).mpr hbz) ((entry_zero_iff _).mpr hcz)
  exact (Nat.lt_irrefl 0) hlt

theorem degree_of_single (N : Orientations.NeighbourRow (Fin k))
    (h : ∀ i, N i = (true, false) ∨ N i = (false, true)) : degree N = k := by
  unfold degree
  have he : ∀ i, (if (N i).1 then 1 else 0) + (if (N i).2 then 1 else 0) = (1 : ℕ) := by
    intro i; rcases h i with hi | hi <;> simp [hi]
  simp [he]

/-- R07: a direct central obstruction has precisely the missing-a central
neighbourhood and two distinct degree-k outer rows adjacent to a. -/
theorem obstruction_shape (hk : 3 ≤ k) (N : B → Orientations.NeighbourRow (Fin k))
    (z : Fin k) (hsp : ∀ b, (N b z).2 = false)
    (c : B) (hone : DirectOne (rows N) c) (hzero : DirectZero (rows N) c) :
    ∃ l u, l ≠ u ∧ Centre (N c) z ∧ degree (N l) = k ∧ degree (N u) = k ∧
      (N l z).1 = true ∧ (N u z).1 = true := by
  obtain ⟨hc, u, hu, hcu⟩ := hone
  obtain ⟨_, l, hl, hlc⟩ := hzero
  have hcone := hc
  obtain ⟨j, hj, _⟩ := hcone
  have hvals := central_triple_values (rows N l) (rows N c) (rows N u) j hl hc hu hj hlc hcu
  have hjz : j = z := by
    by_contra hne
    have hc1 := (hvals z (Ne.symm hne)).2.1
    have he := (entry_one_iff (N c z)).mp hc1
    have hs := hsp c
    simp [he] at hs
  subst j
  have hcz : N c z = (false, false) := (Orientations.entry_none_iff _ _).mp hj
  have hlz := fixed_special N z hsp l hl
  have huz := fixed_special N z hsp u hu
  have hlall : ∀ i, N l i = (true, false) := by
    intro i; by_cases hi : i = z
    · simpa [hi] using hlz
    · exact (entry_zero_iff _).mp (hvals i hi).1
  have huall : ∀ i, N u i = (true, false) ∨ N u i = (false, true) := by
    intro i; by_cases hi : i = z
    · exact Or.inl (by simpa [hi] using huz)
    · exact Or.inr ((entry_two_iff _).mp (hvals i hi).2.2)
  have hlu : l ≠ u := by
    intro he
    have hex : ∃ i : Fin k, i ≠ z := by
      by_cases hz : z = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by rw [hz]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, by omega⟩, Ne.symm hz⟩
    obtain ⟨i, hi⟩ := hex
    have hli := hlall i
    have hui := (entry_two_iff _).mp (hvals i hi).2.2
    rw [he, hui] at hli
    cases hli
  refine ⟨l, u, hlu, ?_, degree_of_single _ (fun i => Or.inl (hlall i)),
    degree_of_single _ huall, ?_, ?_⟩
  · intro i; by_cases hi : i = z
    · simpa [hi] using hcz
    · simpa [hi] using (entry_one_iff _).mp (hvals i hi).2.1
  · simp [hlz]
  · simp [huz]

theorem feasible_of_safe (hk : 4 ≤ k) (N : B → Orientations.NeighbourRow (Fin k))
    (z : Fin k) (hsp : ∀ b, (N b z).2 = false) (hsafe : Safe N z) : Feasible (rows N) := by
  apply (feasible_iff_no_obstructions hk _).mpr
  refine ⟨no_fixed_pair N z hsp, ?_⟩
  rintro ⟨c, hone, hzero⟩
  obtain ⟨l,u,hlu,hc,hl,hu,hlz,huz⟩ := obstruction_shape (by omega) N z hsp c hone hzero
  rcases hsafe with hnone | hone
  · exact hnone ⟨c,hc⟩
  · exact hlu (hone l u hl hu hlz huz)

/-- The distinguished isolated endpoint also permits the three-pair case. -/
theorem feasible_of_safe_three (hk : 3 ≤ k) (N : B → Orientations.NeighbourRow (Fin k))
    (z : Fin k) (hsp : ∀ b, (N b z).2 = false) (hsafe : Safe N z) : Feasible (rows N) := by
  have hrows : ∀ b, rows N b z = none ∨ rows N b z = some 0 := by
    intro b
    rcases he : N b z with ⟨a,s⟩
    have hs := hsp b
    rw [he] at hs
    cases s <;> cases a <;> simp_all [rows, Orientations.row, Orientations.entry]
  apply (Crown.SpecialRows.feasible_iff (rows N) z hrows hk).mpr
  refine ⟨no_fixed_pair N z hsp, ?_⟩
  rintro ⟨c, hone, hzero⟩
  obtain ⟨l,u,hlu,hc,hl,hu,hlz,huz⟩ := obstruction_shape hk N z hsp c hone hzero
  rcases hsafe with hnone | hone
  · exact hnone ⟨c,hc⟩
  · exact hlu (hone l u hl hu hlz huz)

#print axioms obstruction_shape
#print axioms feasible_of_safe
#print axioms feasible_of_safe_three

end Crown.OddRanks
