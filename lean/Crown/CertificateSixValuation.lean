import Crown.CertificateSixSemantics

-- Lean 4.35 needs a deeper reduction when elaborating the 64-mask decision procedure.
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Crown.CertificateSixValuation
open Crown.CertificateSemantics Crown.CertificateSixSemantics

inductive Variable where
  | select (mask : Fin 64)
  | falsum
  | count (prefixLength threshold : Nat)
  | lex (permutation : Fin 6 ≃ Fin 6) (index : Fin 64)
  | core (masks : List (Fin 64))

noncomputable def lexBefore (s : Fin 64 → Bool) (d : Fin 6 ≃ Fin 6)
    (i : Fin 64) : Bool :=
  decide (∀ j > i, s j = s (permuteMask d j))

noncomputable def lexAfter (s : Fin 64 → Bool) (d : Fin 6 ≃ Fin 6)
    (i : Fin 64) : Bool :=
  decide (∀ j ≥ i, s j = s (permuteMask d j))

noncomputable def value (s : Fin 64 → Bool) : Variable → Bool
  | .select m => s m
  | .falsum => false
  | .count i j => counterValue (selectorNat s) i j
  | .lex d i => lexAfter s d i
  | .core masks => masks.all s

theorem lexBefore_iff (s : Fin 64 → Bool) (d : Fin 6 ≃ Fin 6) (i : Fin 64) :
    lexBefore s d i = true ↔ ∀ j > i, s j = s (permuteMask d j) := by
  unfold lexBefore
  rw [decide_eq_true_eq]

theorem lexAfter_iff (s : Fin 64 → Bool) (d : Fin 6 ≃ Fin 6) (i : Fin 64) :
    lexAfter s d i = true ↔ ∀ j ≥ i, s j = s (permuteMask d j) := by
  unfold lexAfter
  rw [decide_eq_true_eq]

theorem lex_step (s : Fin 64 → Bool) (d : Fin 6 ≃ Fin 6) (i : Fin 64) :
    lexAfter s d i = (lexBefore s d i && (s i == s (permuteMask d i))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [lexAfter_iff, Bool.and_eq_true, lexBefore_iff, beq_iff_eq]
  constructor
  · intro h
    exact ⟨fun j hj => h j hj.le, h i le_rfl⟩
  · rintro ⟨h, hi⟩ j hj
    rcases eq_or_lt_of_le hj with rfl | hj
    · exact hi
    · exact h j hj

/-- Above the first moved mask all comparisons are tautological. -/
theorem lex_first (s : Fin 64 → Bool) (d : Fin 6 ≃ Fin 6) (i : Fin 64)
    (h : ∀ j > i, permuteMask d j = j) : lexBefore s d i = true := by
  apply (lexBefore_iff s d i).mpr
  intro j hj
  rw [h j hj]

theorem lex_skipped (s : Fin 64 → Bool) (d : Fin 6 ≃ Fin 6)
    (i previous : Fin 64) (hip : i < previous)
    (hfixed : ∀ j, i < j → j < previous → permuteMask d j = j) :
    lexBefore s d i = lexAfter s d previous := by
  apply Bool.eq_iff_iff.mpr
  rw [lexBefore_iff, lexAfter_iff]
  constructor
  · intro h j hj
    exact h j (lt_of_lt_of_le hip hj)
  · intro h j hj
    by_cases hp : previous ≤ j
    · exact h j hp
    · rw [hfixed j hj (lt_of_not_ge hp)]

theorem lex_comparison (s : Fin 64 → Bool) (d : Fin 6 ≃ Fin 6) (i : Fin 64)
    (hmax : toColex (relabelSelector s d) ≤ toColex s) :
    lexBefore s d i = true → s (permuteMask d i) = true → s i = true := by
  intro hp
  exact lex_max_prefix s d hmax i ((lexBefore_iff s d i).mp hp)

theorem count_zero (s : Fin 64 → Bool) (i : Nat) :
    value s (.count i 0) = true := counter_zero (selectorNat s) i

theorem count_above (s : Fin 64 → Bool) (i j : Nat) (h : i < j) :
    value s (.count i j) = false := counter_above (selectorNat s) i j h

theorem count_step (s : Fin 64 → Bool) (i : Fin 64) (j : Nat) :
    value s (.count (i.val + 1) (j + 1)) =
      (value s (.count i.val (j+1)) ||
        (value s (.select i) && value s (.count i.val j))) := by
  simpa [value, Crown.CertificateSixSemantics.selectorNat, i.isLt] using counter_step (selectorNat s) i.val j

theorem count_final (s : Fin 64 → Bool) :
    value s (.count 64 7) = false ↔ Fintype.card {m // s m = true} ≤ 6 := by
  exact (counter_six_iff (selectorNat s)).trans (by rw [Crown.CertificateSixSemantics.prefixCount_selector])

theorem core_true_iff (s : Fin 64 → Bool) (masks : List (Fin 64)) :
    value s (.core masks) = true ↔ ∀ m ∈ masks, s m = true := by
  simp [value, List.all_eq_true]

theorem core_implies_select (s : Fin 64 → Bool) (masks : List (Fin 64))
    (m : Fin 64) (hm : m ∈ masks) :
    value s (.core masks) = true → value s (.select m) = true := by
  intro h
  exact (core_true_iff s masks).mp h m hm

/-- The counter gate under any concrete assignment of its four literals. -/
theorem counter_gate (s : Fin 64 → Bool) (i : Fin 64) (j : Nat)
    (a : Nat → Bool) (z u x w : Sat.Literal)
    (hz : literalValue a z = value s (.count (i.val+1) (j+1)))
    (hu : literalValue a u = value s (.count i.val (j+1)))
    (hx : literalValue a x = value s (.select i))
    (hw : literalValue a w = value s (.count i.val j)) :
    (valuation a).satisfies_fmla (counterCNF z u x w) := by
  apply (counter_cnf_iff a z u x w).mpr
  rw [hz, hu, hx, hw]
  exact count_step s i j

/-- The five prefix-equality clauses at a moved index. -/
theorem equality_gate (s : Fin 64 → Bool) (d : Fin 6 ≃ Fin 6) (i : Fin 64)
    (a : Nat → Bool) (z e x y : Sat.Literal)
    (hz : literalValue a z = value s (.lex d i))
    (he : literalValue a e = lexBefore s d i)
    (hx : literalValue a x = s i)
    (hy : literalValue a y = s (permuteMask d i)) :
    (valuation a).satisfies_fmla (equalityCNF z e x y) := by
  apply (equality_cnf_iff a z e x y).mpr
  rw [hz, he, hx, hy]
  exact lex_step s d i

theorem comparison_gate (s : Fin 64 → Bool) (d : Fin 6 ≃ Fin 6) (i : Fin 64)
    (hmax : toColex (relabelSelector s d) ≤ toColex s)
    (a : Nat → Bool) (e x y : Sat.Literal)
    (he : literalValue a e = lexBefore s d i)
    (hx : literalValue a x = s i)
    (hy : literalValue a y = s (permuteMask d i)) :
    (valuation a).satisfies [e.negate, x, y.negate] := by
  apply (lex_clause_iff a e x y).mpr
  rw [he, hx, hy]
  exact lex_comparison s d i hmax

theorem core_gate (s : Fin 64 → Bool) (masks : List (Fin 64))
    (m : Fin 64) (hm : m ∈ masks) (a : Nat → Bool) (z x : Sat.Literal)
    (hz : literalValue a z = value s (.core masks))
    (hx : literalValue a x = value s (.select m)) :
    (valuation a).satisfies [z.negate, x] := by
  apply (implication_clause_iff a z x).mpr
  rw [hz, hx]
  exact core_implies_select s masks m hm

#print axioms lex_step
#print axioms lex_first
#print axioms lex_skipped
#print axioms lex_comparison
#print axioms count_step
#print axioms count_final
#print axioms core_implies_select
#print axioms counter_gate
#print axioms equality_gate
#print axioms comparison_gate
#print axioms core_gate
end Crown.CertificateSixValuation
