import Mathlib.Tactic.Sat.FromLRAT
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Max
import Mathlib.Order.PiLex
import Mathlib.Data.Bool.Basic
import Init.Data.Nat.Bitwise.Lemmas
import Crown.Ranks

namespace Crown.CertificateSemantics

def literalValue (a : Nat → Bool) : Sat.Literal → Bool
  | .pos n => a n
  | .neg n => !(a n)

def valuation (a : Nat → Bool) : Sat.Valuation := fun n => a n = true

theorem literalValue_negate (a : Nat → Bool) (l : Sat.Literal) :
    literalValue a l.negate = !(literalValue a l) := by
  cases l <;> simp [literalValue, Sat.Literal.negate]

theorem neg_iff_false (a : Nat → Bool) (l : Sat.Literal) :
    (valuation a).neg l ↔ literalValue a l = false := by
  cases l with
  | pos n => cases h : a n <;> simp [valuation, Sat.Valuation.neg, literalValue, h]
  | neg n => cases h : a n <;> simp [valuation, Sat.Valuation.neg, literalValue, h]

/-- Mathlib's negative-implication clause semantics equals Boolean disjunction. -/
theorem clause_satisfied_iff (a : Nat → Bool) (c : Sat.Clause) :
    (valuation a).satisfies c ↔ (c.map (literalValue a)).any id = true := by
  induction c with
  | nil => simp [Sat.Valuation.satisfies]
  | cons l c ih =>
    change ((valuation a).neg l → (valuation a).satisfies c) ↔ _
    rw [neg_iff_false, ih]
    cases h : literalValue a l <;> simp [h]

theorem formula_satisfied_iff (a : Nat → Bool) (f : Sat.Fmla) :
    (valuation a).satisfies_fmla f ↔
      ∀ c ∈ f, (c.map (literalValue a)).any id = true := by
  constructor
  · intro h c hc
    exact (clause_satisfied_iff a c).mp (h.prop c hc)
  · intro h
    exact ⟨fun c hc => (clause_satisfied_iff a c).mpr (h c hc)⟩

theorem formula_nil_iff (v : Sat.Valuation) : v.satisfies_fmla [] ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨fun _ h => nomatch h⟩

theorem formula_cons_iff (v : Sat.Valuation) (c : Sat.Clause) (f : Sat.Fmla) :
    v.satisfies_fmla (c :: f) ↔ v.satisfies c ∧ v.satisfies_fmla f := by
  constructor
  · intro h
    exact ⟨h.prop c (List.Mem.head _), ⟨fun d hd => h.prop d (List.Mem.tail c hd)⟩⟩
  · rintro ⟨hc, hf⟩
    refine ⟨fun d hd => ?_⟩
    cases hd with
    | head => exact hc
    | tail _ hd => exact hf.prop d hd

/-- The four clauses emitted for `z ↔ u ∨ (x ∧ w)`. -/
def counterCNF (z u x w : Sat.Literal) : Sat.Fmla :=
  [[u.negate, z], [x.negate, w.negate, z], [z.negate, u, x], [z.negate, u, w]]

theorem counter_cnf_iff (a : Nat → Bool) (z u x w : Sat.Literal) :
    (valuation a).satisfies_fmla (counterCNF z u x w) ↔
      literalValue a z = (literalValue a u || (literalValue a x && literalValue a w)) := by
  unfold counterCNF
  erw [formula_cons_iff, formula_cons_iff, formula_cons_iff, formula_cons_iff, formula_nil_iff]
  erw [clause_satisfied_iff, clause_satisfied_iff, clause_satisfied_iff, clause_satisfied_iff]
  cases hz : literalValue a z <;> cases hu : literalValue a u <;>
    cases hx : literalValue a x <;> cases hw : literalValue a w <;>
    simp [literalValue_negate, hz, hu, hx, hw]

/-- The five clauses emitted for the lexicographic prefix-equality flag. -/
def equalityCNF (z e x y : Sat.Literal) : Sat.Fmla :=
  [[z.negate, e], [z.negate, x.negate, y], [z.negate, x, y.negate],
    [e.negate, x.negate, y.negate, z], [e.negate, x, y, z]]

theorem equality_cnf_iff (a : Nat → Bool) (z e x y : Sat.Literal) :
    (valuation a).satisfies_fmla (equalityCNF z e x y) ↔
      literalValue a z = (literalValue a e && (literalValue a x == literalValue a y)) := by
  unfold equalityCNF
  erw [formula_cons_iff, formula_cons_iff, formula_cons_iff, formula_cons_iff, formula_cons_iff, formula_nil_iff]
  erw [clause_satisfied_iff, clause_satisfied_iff, clause_satisfied_iff, clause_satisfied_iff, clause_satisfied_iff]
  cases hz : literalValue a z <;> cases he : literalValue a e <;>
    cases hx : literalValue a x <;> cases hy : literalValue a y <;>
    simp [literalValue_negate, hz, he, hx, hy]

theorem implication_clause_iff (a : Nat → Bool) (z x : Sat.Literal) :
    (valuation a).satisfies [z.negate, x] ↔
      (literalValue a z = true → literalValue a x = true) := by
  erw [clause_satisfied_iff]
  cases hz : literalValue a z <;> cases hx : literalValue a x <;>
    simp [literalValue_negate, hz, hx]

/-- A lexicographic comparison is imposed precisely while the prefix agrees. -/
theorem lex_clause_iff (a : Nat → Bool) (e x y : Sat.Literal) :
    (valuation a).satisfies [e.negate, x, y.negate] ↔
      (literalValue a e = true → literalValue a y = true → literalValue a x = true) := by
  erw [clause_satisfied_iff]
  cases he : literalValue a e <;> cases hx : literalValue a x <;>
    cases hy : literalValue a y <;> simp [literalValue_negate, he, hx, hy]

def prefixCount (s : Nat → Bool) : Nat → Nat
  | 0 => 0
  | i + 1 => prefixCount s i + if s i then 1 else 0

theorem prefixCount_le (s : Nat → Bool) (i : Nat) : prefixCount s i ≤ i := by
  induction i with
  | zero => simp [prefixCount]
  | succ i ih => cases h : s i <;> simp [prefixCount, h] <;> omega

/-- The recursive counter counts exactly the selected indices in its prefix. -/
theorem prefixCount_eq_card (s : Nat → Bool) (i : Nat) :
    prefixCount s i = ((Finset.range i).filter (fun j => s j = true)).card := by
  induction i with
  | zero => simp [prefixCount]
  | succ i ih =>
    cases h : s i <;>
      simp [prefixCount, Finset.range_add_one, Finset.filter_insert, h, ih]

theorem count_threshold_step (s : Nat → Bool) (i j : Nat) :
    j + 1 ≤ prefixCount s (i + 1) ↔
      j + 1 ≤ prefixCount s i ∨ (s i = true ∧ j ≤ prefixCount s i) := by
  cases h : s i <;> simp [prefixCount, h] <;> omega

def counterValue (s : Nat → Bool) (i j : Nat) : Bool := decide (j ≤ prefixCount s i)

theorem counter_zero (s : Nat → Bool) (i : Nat) : counterValue s i 0 = true := by
  simp [counterValue]

theorem counter_above (s : Nat → Bool) (i j : Nat) (h : i < j) :
    counterValue s i j = false := by
  have hb := prefixCount_le s i
  have hn : ¬ j ≤ prefixCount s i := by omega
  simp [counterValue, hn]

theorem counter_step (s : Nat → Bool) (i j : Nat) :
    counterValue s (i+1) (j+1) =
      (counterValue s i (j+1) || (s i && counterValue s i j)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [counterValue, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact count_threshold_step s i j

/-- The final counter clause expresses exactly the bound of eight selected masks. -/
theorem counter_eight_iff (s : Nat → Bool) :
    counterValue s 256 9 = false ↔ prefixCount s 256 ≤ 8 := by
  simp only [counterValue, decide_eq_false_iff_not]
  omega

open Crown.Ranks

/-- A pair of incidence bits gives the manuscript's four initial rank cases. -/
def rankOfBits : Bool → Bool → Option (Fin 3)
  | false, false => none
  | true, false => some 0
  | true, true => some 1
  | false, true => some 2

def bitsOfRank : Option (Fin 3) → Bool × Bool
  | none => (false, false)
  | some u => if u = 0 then (true, false) else if u = 1 then (true, true) else (false, true)

theorem bits_rank_inverse : ∀ a b : Bool, bitsOfRank (rankOfBits a b) = (a,b) := by
  decide +kernel

theorem rank_bits_inverse : ∀ u : Option (Fin 3),
    rankOfBits (bitsOfRank u).1 (bitsOfRank u).2 = u := by
  have h : ∀ u : Fin 3,
      rankOfBits (bitsOfRank (some u)).1 (bitsOfRank (some u)).2 = some u := by
    decide +kernel
  intro u
  cases u with
  | none => rfl
  | some u => exact h u

def rowOfMask {I A : Type} (pairs : I → A × A) (mask : A → Bool) : InitialRow I :=
  fun i => rankOfBits (mask (pairs i).1) (mask (pairs i).2)

def maskBits (m : Fin 256) : Fin 8 → Bool := fun i => m.val.testBit i.val

/-- All eight incidence bits determine a mask; higher bits vanish by the bound. -/
theorem maskBits_injective : Function.Injective maskBits := by
  intro m n h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · exact congrFun h ⟨i, hi⟩
  · have hpow : 256 ≤ 2^i := by
      exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega : 8 ≤ i)
    have hm : m.val < 2^i := Nat.lt_of_lt_of_le m.isLt hpow
    have hn : n.val < 2^i := Nat.lt_of_lt_of_le n.isLt hpow
    rw [Nat.testBit_lt_two_pow hm, Nat.testBit_lt_two_pow hn]

/-- Cardinality and injectivity give coverage of all eight-bit neighbourhoods,
without checking all 256 squared pairs of bit vectors. -/
theorem maskBits_surjective : Function.Surjective maskBits := by
  have hcard : Fintype.card (Fin 256) = Fintype.card (Fin 8 → Bool) := by
    simp only [Fintype.card_fin, Fintype.card_pi_const, Fintype.card_bool]
    rfl
  exact ((Fintype.bijective_iff_injective_and_card maskBits).mpr
    ⟨maskBits_injective, hcard⟩).2

noncomputable def permuteMask (e : Fin 8 ≃ Fin 8) (m : Fin 256) : Fin 256 :=
  Classical.choose (maskBits_surjective (fun i => maskBits m (e.symm i)))

theorem permuteMask_bits (e : Fin 8 ≃ Fin 8) (m : Fin 256) :
    maskBits (permuteMask e m) = fun i => maskBits m (e.symm i) :=
  Classical.choose_spec (maskBits_surjective (fun i => maskBits m (e.symm i)))

theorem permuteMask_injective (e : Fin 8 ≃ Fin 8) : Function.Injective (permuteMask e) := by
  intro m n h
  apply maskBits_injective
  funext i
  have hb := congrFun (congrArg maskBits h) (e i)
  simpa only [permuteMask_bits, Equiv.symm_apply_apply] using hb

noncomputable def maskPermutation (e : Fin 8 ≃ Fin 8) : Fin 256 ≃ Fin 256 :=
  Equiv.ofBijective (permuteMask e)
    ⟨permuteMask_injective e, Finite.surjective_of_injective (permuteMask_injective e)⟩

theorem permuteMask_trans (e d : Fin 8 ≃ Fin 8) (m : Fin 256) :
    permuteMask (e.trans d) m = permuteMask d (permuteMask e m) := by
  apply maskBits_injective
  funext i
  simp [permuteMask_bits, Equiv.trans_apply]

/-- Relabel the selector vector by pullback along a coordinate permutation. -/
noncomputable def relabelSelector (s : Fin 256 → Bool) (e : Fin 8 ≃ Fin 8) : Fin 256 → Bool :=
  fun m => s (permuteMask e m)

theorem relabelSelector_trans (s : Fin 256 → Bool) (e d : Fin 8 ≃ Fin 8) :
    relabelSelector (relabelSelector s e) d = relabelSelector s (d.trans e) := by
  funext m
  simp [relabelSelector, permuteMask_trans]

/-- The maximum of the finite coordinate-permutation orbit satisfies all the
lexicographic comparisons. The order is descending in the mask index, exactly
as in `add_lex_geq`; no enumeration of the 40,320 permutations is evaluated. -/
theorem exists_lex_max_relabeling (s : Fin 256 → Bool) :
    ∃ e : Fin 8 ≃ Fin 8, ∀ d : Fin 8 ≃ Fin 8,
      toColex (relabelSelector (relabelSelector s e) d) ≤
        toColex (relabelSelector s e) := by
  classical
  obtain ⟨e, _, he⟩ := Finset.exists_max_image Finset.univ
    (fun e : Fin 8 ≃ Fin 8 => toColex (relabelSelector s e))
    (show (Finset.univ : Finset (Fin 8 ≃ Fin 8)).Nonempty from
      ⟨Equiv.refl _, Finset.mem_univ _⟩)
  refine ⟨e, fun d => ?_⟩
  rw [relabelSelector_trans]
  exact he (d.trans e) (Finset.mem_univ _)

/-- The prefix equality flag at an index enforces the source lex clause. -/
theorem lex_max_prefix (s : Fin 256 → Bool) (d : Fin 8 ≃ Fin 8)
    (hmax : toColex (relabelSelector s d) ≤ toColex s) (i : Fin 256)
    (hprefix : ∀ j > i, s j = s (permuteMask d j)) :
    s (permuteMask d i) = true → s i = true := by
  have hle := Pi.apply_le_of_toColex hmax (fun j hj => (hprefix j hj).symm)
  cases hx : s (permuteMask d i) <;> cases hy : s i <;>
    simp_all [relabelSelector, Bool.le_iff_imp]

/-- An oriented pairing is a bijective labelling of the eight endpoints. -/
abbrev Pairing8 := (Fin 4 × Bool) ≃ Fin 8

def pairsOfEquiv (p : Pairing8) : Fin 4 → Fin 8 × Fin 8 :=
  fun i => (p (i, false), p (i, true))

theorem pairing_rank_coverage (p : Pairing8) (ρ : InitialRow (Fin 4)) :
    ∃ m : Fin 256, rowOfMask (pairsOfEquiv p) (maskBits m) = ρ := by
  let bits : Fin 8 → Bool := fun a =>
    if (p.symm a).2 then (bitsOfRank (ρ (p.symm a).1)).2
    else (bitsOfRank (ρ (p.symm a).1)).1
  obtain ⟨m, hm⟩ := maskBits_surjective bits
  refine ⟨m, ?_⟩
  rw [hm]
  funext i
  simpa [rowOfMask, pairsOfEquiv, bits] using rank_bits_inverse (ρ i)

def AllPairingsBad {V : Type} (masks : V → Fin 256) : Prop :=
  ∀ p : Pairing8, ¬ Feasible (fun v => rowOfMask (pairsOfEquiv p) (maskBits (masks v)))

/-- Universal infeasibility is invariant under vertex relabelling. No assumption
that the stored list of 840 pairings exhausts all pairings is needed here. -/
theorem allPairingsBad_permute {V : Type} (masks : V → Fin 256)
    (h : AllPairingsBad masks) (e : Fin 8 ≃ Fin 8) :
    AllPairingsBad (fun v => permuteMask e (masks v)) := by
  intro p hp
  apply h (p.trans e.symm)
  convert hp using 1
  funext v i
  simp [rowOfMask, pairsOfEquiv, permuteMask_bits, Equiv.trans_apply]

def Covers {I A : Type} (pairs : I → A × A) : Prop :=
  ∀ a, ∃ i, a = (pairs i).1 ∨ a = (pairs i).2

theorem rowOfMask_injective {I A : Type} (pairs : I → A × A) (h : Covers pairs) :
    Function.Injective (rowOfMask pairs) := by
  intro m n he
  funext a
  obtain ⟨i, hi⟩ := h a
  have hbits := congrArg bitsOfRank (congrFun he i)
  change bitsOfRank (rankOfBits (m (pairs i).1) (m (pairs i).2)) =
    bitsOfRank (rankOfBits (n (pairs i).1) (n (pairs i).2)) at hbits
  rw [bits_rank_inverse, bits_rank_inverse] at hbits
  rcases hi with hi | hi
  · rw [hi]
    exact congrArg Prod.fst hbits
  · rw [hi]
    exact congrArg Prod.snd hbits

theorem mask_rank_injective (pairs : Fin 4 → Fin 8 × Fin 8) (h : Covers pairs) :
    Function.Injective (fun m : Fin 256 => rowOfMask pairs (maskBits m)) := by
  intro m n he
  exact maskBits_injective (rowOfMask_injective pairs h he)

/-- Passing to distinct neighbourhood masks preserves the entire completion problem. -/
theorem feasible_surjective {I V M : Type} (rows : M → InitialRow I)
    (f : V → M) (hf : Function.Surjective f) :
    Feasible (fun v => rows (f v)) ↔ Feasible rows := by
  classical
  constructor
  · rintro ⟨r, hr, hn⟩
    let g : M → V := fun m => Classical.choose (hf m)
    have hg : ∀ m, f (g m) = m := fun m => Classical.choose_spec (hf m)
    refine ⟨fun m => r (g m), ?_, fun m n => hn (g m) (g n)⟩
    intro m
    simpa only [hg m] using hr (g m)
  · rintro ⟨r, hr, hn⟩
    exact ⟨fun v => r (f v), fun v => hr (f v), fun v w => hn (f v) (f w)⟩

/-- Extend the selector vector to the natural-number indexing of the counter. -/
def selectorNat (s : Fin 256 → Bool) (n : Nat) : Bool :=
  if h : n < 256 then s ⟨n, h⟩ else false

theorem prefixCount_selector (s : Fin 256 → Bool) :
    prefixCount (selectorNat s) 256 = Fintype.card {m // s m = true} := by
  rw [prefixCount_eq_card, Fintype.card_subtype]
  apply Finset.card_bij (fun n hn => ⟨n, Finset.mem_range.mp (Finset.mem_filter.mp hn).1⟩)
  · intro n hn
    obtain ⟨hn, hs⟩ := Finset.mem_filter.mp hn
    have hb := Finset.mem_range.mp hn
    simpa [selectorNat, hb] using hs
  · intro a ha b hb he
    exact congrArg Fin.val he
  · intro m hm
    have hs : s m = true := (Finset.mem_filter.mp hm).2
    refine ⟨m.val, ?_, rfl⟩
    simp [selectorNat, m.isLt, hs]

/-- The selected masks before and after relabelling are in bijection. -/
noncomputable def selectedEquiv (s : Fin 256 → Bool) (e : Fin 8 ≃ Fin 8) :
    {m // relabelSelector s e m = true} ≃ {m // s m = true} :=
  (maskPermutation e).subtypeEquiv (fun _ => Iff.rfl)

theorem selected_card_relabel (s : Fin 256 → Bool) (e : Fin 8 ≃ Fin 8) :
    Fintype.card {m // relabelSelector s e m = true} = Fintype.card {m // s m = true} :=
  Fintype.card_congr (selectedEquiv s e)

theorem selected_bad_relabel (s : Fin 256 → Bool) (e : Fin 8 ≃ Fin 8)
    (h : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    AllPairingsBad (fun m : {m // relabelSelector s e m = true} => m.val) := by
  intro p hp
  apply h (p.trans e)
  apply (feasible_surjective
    (fun m : {m // s m = true} => rowOfMask (pairsOfEquiv (p.trans e)) (maskBits m.val))
    (selectedEquiv s e) (selectedEquiv s e).surjective).mp
  convert hp using 1
  funext m i
  change rankOfBits (maskBits (permuteMask e m.val) (e (p (i, false))))
    (maskBits (permuteMask e m.val) (e (p (i, true)))) =
      rankOfBits (maskBits m.val (p (i, false))) (maskBits m.val (p (i, true)))
  simp only [permuteMask_bits, Equiv.symm_apply_apply]

/-- Any universally bad family has an equally large universally bad relabelling
satisfying every coordinate-permutation lex constraint. -/
theorem canonical_bad_selection (s : Fin 256 → Bool)
    (hcard : Fintype.card {m // s m = true} ≤ 8)
    (hbad : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ t : Fin 256 → Bool,
      Fintype.card {m // t m = true} ≤ 8 ∧
      AllPairingsBad (fun m : {m // t m = true} => m.val) ∧
      (∀ d : Fin 8 ≃ Fin 8, toColex (relabelSelector t d) ≤ toColex t) := by
  obtain ⟨e, he⟩ := exists_lex_max_relabeling s
  refine ⟨relabelSelector s e, ?_, selected_bad_relabel s e hbad, he⟩
  rw [selected_card_relabel]
  exact hcard

/-- The three possible strictly increasing prescribed-rank pairs. -/
def increasingRanks (t : Fin 3) : Fin 3 × Fin 3 :=
  if t = 0 then (0,1) else if t = 1 then (0,2) else (1,2)

theorem increasingRanks_complete : ∀ a b : Fin 3,
    a < b ↔ ∃ t : Fin 3, increasingRanks t = (a,b) := by
  decide +kernel

/-- The six possibilities retained at the star coordinate of a triple. -/
def decreasingRanks (t : Fin 6) : Fin 3 × Fin 3 :=
  if t = 0 then (0,0) else if t = 1 then (1,0) else if t = 2 then (1,1)
  else if t = 3 then (2,0) else if t = 4 then (2,1) else (2,2)

theorem decreasingRanks_complete : ∀ a b : Fin 3,
    b ≤ a ↔ ∃ t : Fin 6, decreasingRanks t = (a,b) := by
  decide +kernel

def pairLower {I : Type} (t : I → Fin 3) : InitialRow I :=
  fun i => some (increasingRanks (t i)).1

def pairUpper {I : Type} (t : I → Fin 3) : InitialRow I :=
  fun i => some (increasingRanks (t i)).2

/-- Coordinatewise coverage of the three choices used by each pair template. -/
theorem pair_pattern_iff {I : Type} (l u : InitialRow I) :
    (∃ t : I → Fin 3, l = pairLower t ∧ u = pairUpper t) ↔
      Fixed l ∧ Fixed u ∧ PotentialBelow l u := by
  classical
  constructor
  · rintro ⟨t, rfl, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simp [pairLower]
    · intro i
      simp [pairUpper]
    · intro i a b ha hb
      simp only [pairLower, Option.some.injEq] at ha
      simp only [pairUpper, Option.some.injEq] at hb
      subst a
      subst b
      exact (increasingRanks_complete _ _).mpr ⟨t i, rfl⟩
  · rintro ⟨hl, hu, hlt⟩
    have h : ∀ i, ∃ t : Fin 3,
        l i = some (increasingRanks t).1 ∧ u i = some (increasingRanks t).2 := by
      intro i
      cases el : l i with
      | none => exact False.elim (hl i el)
      | some a =>
        cases eu : u i with
        | none => exact False.elim (hu i eu)
        | some b =>
          obtain ⟨t, ht⟩ := (increasingRanks_complete a b).mp (hlt i a b el eu)
          exact ⟨t, by simp [ht], by simp [ht]⟩
    let t : I → Fin 3 := fun i => Classical.choose (h i)
    exact ⟨t, funext (fun i => (Classical.choose_spec (h i)).1),
      funext (fun i => (Classical.choose_spec (h i)).2)⟩

def tripleLower {I : Type} [DecidableEq I] (j : I) (a : Fin 3) : InitialRow I :=
  fun i => some (if i = j then a else 0)

def tripleCenter {I : Type} [DecidableEq I] (j : I) : InitialRow I :=
  fun i => if i = j then none else some 1

def tripleUpper {I : Type} [DecidableEq I] (j : I) (b : Fin 3) : InitialRow I :=
  fun i => some (if i = j then b else 2)

theorem triple_lower_fixed {I : Type} [DecidableEq I] (j : I) (a : Fin 3) :
    Fixed (tripleLower j a) := fun i => by simp [tripleLower]

theorem triple_upper_fixed {I : Type} [DecidableEq I] (j : I) (b : Fin 3) :
    Fixed (tripleUpper j b) := fun i => by simp [tripleUpper]

theorem triple_center_oneStar {I : Type} [DecidableEq I] (j : I) :
    OneStar (tripleCenter j) := by
  refine ⟨j, by simp [tripleCenter], ?_⟩
  intro i hi
  by_cases hij : i = j
  · exact hij
  · simp [tripleCenter, hij] at hi

theorem triple_lower_center {I : Type} [DecidableEq I] (j : I) (a : Fin 3) :
    PotentialBelow (tripleLower j a) (tripleCenter j) := by
  intro i x y hx hy
  by_cases hij : i = j
  · simp [tripleCenter, hij] at hy
  · simp only [tripleLower, if_neg hij, Option.some.injEq] at hx
    simp only [tripleCenter, if_neg hij, Option.some.injEq] at hy
    subst x
    subst y
    decide

theorem triple_center_upper {I : Type} [DecidableEq I] (j : I) (b : Fin 3) :
    PotentialBelow (tripleCenter j) (tripleUpper j b) := by
  intro i x y hx hy
  by_cases hij : i = j
  · simp [tripleCenter, hij] at hx
  · simp only [tripleCenter, if_neg hij, Option.some.injEq] at hx
    simp only [tripleUpper, if_neg hij, Option.some.injEq] at hy
    subst x
    subst y
    decide

theorem triple_lower_upper_iff {I : Type} [DecidableEq I] (j : I) (a b : Fin 3) :
    PotentialBelow (tripleLower j a) (tripleUpper j b) ↔ a < b := by
  constructor
  · intro h
    exact h j a b (by simp [tripleLower]) (by simp [tripleUpper])
  · intro hab i x y hx hy
    by_cases hij : i = j
    · simp only [tripleLower, if_pos hij, Option.some.injEq] at hx
      simp only [tripleUpper, if_pos hij, Option.some.injEq] at hy
      subst x
      subst y
      exact hab
    · simp only [tripleLower, if_neg hij, Option.some.injEq] at hx
      simp only [tripleUpper, if_neg hij, Option.some.injEq] at hy
      subst x
      subst y
      decide

/-- Every directly forced central row has the explicit template shape. -/
theorem central_pattern_coverage {I : Type} [DecidableEq I]
    (l c u : InitialRow I) (j : I) (hl : Fixed l) (hc : OneStar c)
    (hu : Fixed u) (hj : c j = none)
    (hlc : PotentialBelow l c) (hcu : PotentialBelow c u) :
    ∃ a b : Fin 3, l = tripleLower j a ∧ c = tripleCenter j ∧ u = tripleUpper j b := by
  have values := central_triple_values l c u j hl hc hu hj hlc hcu
  cases el : l j with
  | none => exact False.elim (hl j el)
  | some a =>
    cases eu : u j with
    | none => exact False.elim (hu j eu)
    | some b =>
      refine ⟨a, b, ?_, ?_, ?_⟩
      · funext i
        by_cases hij : i = j
        · subst i
          simpa [tripleLower] using el
        · simpa [tripleLower, hij] using (values i hij).1
      · funext i
        by_cases hij : i = j
        · subst i
          simpa [tripleCenter] using hj
        · simpa [tripleCenter, hij] using (values i hij).2.1
      · funext i
        by_cases hij : i = j
        · subst i
          simpa [tripleUpper] using eu
        · simpa [tripleUpper, hij] using (values i hij).2.2

def PairPattern (l u : InitialRow (Fin 4)) : Prop :=
  ∃ t : Fin 4 → Fin 3, l = pairLower t ∧ u = pairUpper t

def TriplePattern (l c u : InitialRow (Fin 4)) : Prop :=
  ∃ j : Fin 4, ∃ t : Fin 6,
    l = tripleLower j (decreasingRanks t).1 ∧ c = tripleCenter j ∧
      u = tripleUpper j (decreasingRanks t).2

/-- The omitted increasing star-coordinate cases already contain a pair obstruction. -/
theorem direct_conflict_covered {V : Type} (rows : V → InitialRow (Fin 4)) (c : V)
    (ho : DirectOne rows c) (hz : DirectZero rows c) :
    (∃ l u, PairPattern (rows l) (rows u)) ∨
      ∃ l u, TriplePattern (rows l) (rows c) (rows u) := by
  obtain ⟨hc, u, hu, hcu⟩ := ho
  obtain ⟨_, l, hl, hlc⟩ := hz
  obtain ⟨j, hj, _⟩ := (show OneStar (rows c) from hc)
  obtain ⟨a, b, el, ec, eu⟩ := central_pattern_coverage
    (rows l) (rows c) (rows u) j hl hc hu hj hlc hcu
  by_cases hab : a < b
  · left
    refine ⟨l, u, (pair_pattern_iff _ _).mpr ⟨hl, hu, ?_⟩⟩
    rw [el, eu]
    exact (triple_lower_upper_iff j a b).mpr hab
  · right
    have hba : b ≤ a := Nat.le_of_not_gt hab
    obtain ⟨t, ht⟩ := (decreasingRanks_complete a b).mp hba
    exact ⟨l, u, j, t, by simpa [ht] using el, ec, by simpa [ht] using eu⟩

theorem triple_pattern_conflict (l c u : InitialRow (Fin 4))
    (h : TriplePattern l c u) :
    Fixed l ∧ OneStar c ∧ Fixed u ∧ PotentialBelow l c ∧ PotentialBelow c u := by
  obtain ⟨j, t, rfl, rfl, rfl⟩ := h
  exact ⟨triple_lower_fixed j _, triple_center_oneStar j, triple_upper_fixed j _,
    triple_lower_center j _, triple_center_upper j _⟩

/-- Complete symbolic 81-pair / 24-triple catalogue, before mask enumeration. -/
theorem infeasible_iff_patterns {V : Type} (rows : V → InitialRow (Fin 4)) :
    ¬ Feasible rows ↔ (∃ l u, PairPattern (rows l) (rows u)) ∨
      ∃ l c u, TriplePattern (rows l) (rows c) (rows u) := by
  classical
  constructor
  · intro hn
    by_cases hp : NoFixedPair rows
    · have hc : ∃ c, DirectOne rows c ∧ DirectZero rows c := by
        apply Classical.byContradiction
        intro hc
        exact hn ((feasible_iff_no_obstructions (by decide : 4 ≤ 4) rows).mpr ⟨hp, hc⟩)
      obtain ⟨c, ho, hz⟩ := hc
      rcases direct_conflict_covered rows c ho hz with h | ⟨l, u, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨l, c, u, h⟩
    · left
      apply Classical.byContradiction
      intro hnone
      apply hp
      intro l u hl hu hlu
      exact hnone ⟨l, u, (pair_pattern_iff _ _).mpr ⟨hl, hu, hlu⟩⟩
  · intro h hf
    obtain ⟨hp, hc⟩ := (feasible_iff_no_obstructions (by decide : 4 ≤ 4) rows).mp hf
    rcases h with ⟨l, u, h⟩ | ⟨l, c, u, h⟩
    · obtain ⟨hl, hu, hlu⟩ := (pair_pattern_iff _ _).mp h
      exact hp l u hl hu hlu
    · obtain ⟨hl, hcs, hu, hlc, hcu⟩ := triple_pattern_conflict _ _ _ h
      exact hc ⟨c, ⟨hcs, u, hu, hcu⟩, ⟨hcs, l, hl, hlc⟩⟩

/-- The selected-mask form of the obstruction statement used by the CNF. -/
theorem selected_infeasible_iff (rows : Fin 256 → InitialRow (Fin 4))
    (s : Fin 256 → Bool) :
    ¬ Feasible (fun m : {m : Fin 256 // s m = true} => rows m.val) ↔
      (∃ l u, s l = true ∧ s u = true ∧ PairPattern (rows l) (rows u)) ∨
      ∃ l c u, s l = true ∧ s c = true ∧ s u = true ∧
        TriplePattern (rows l) (rows c) (rows u) := by
  rw [infeasible_iff_patterns]
  constructor
  · rintro (⟨l, u, h⟩ | ⟨l, c, u, h⟩)
    · exact Or.inl ⟨l.val, u.val, l.property, u.property, h⟩
    · exact Or.inr ⟨l.val, c.val, u.val, l.property, c.property, u.property, h⟩
  · rintro (⟨l, u, hl, hu, h⟩ | ⟨l, c, u, hl, hc, hu, h⟩)
    · exact Or.inl ⟨⟨l, hl⟩, ⟨u, hu⟩, h⟩
    · exact Or.inr ⟨⟨l, hl⟩, ⟨c, hc⟩, ⟨u, hu⟩, h⟩

#print axioms clause_satisfied_iff
#print axioms counter_cnf_iff
#print axioms equality_cnf_iff
#print axioms implication_clause_iff
#print axioms lex_clause_iff
#print axioms prefixCount_eq_card
#print axioms counter_step
#print axioms counter_eight_iff
#print axioms bits_rank_inverse
#print axioms rank_bits_inverse
#print axioms increasingRanks_complete
#print axioms decreasingRanks_complete
#print axioms maskBits_injective
#print axioms maskBits_surjective
#print axioms permuteMask_injective
#print axioms exists_lex_max_relabeling
#print axioms lex_max_prefix
#print axioms pairing_rank_coverage
#print axioms allPairingsBad_permute
#print axioms mask_rank_injective
#print axioms prefixCount_selector
#print axioms selected_card_relabel
#print axioms selected_bad_relabel
#print axioms canonical_bad_selection
#print axioms feasible_surjective
#print axioms pair_pattern_iff
#print axioms central_pattern_coverage
#print axioms direct_conflict_covered
#print axioms infeasible_iff_patterns
#print axioms selected_infeasible_iff

end Crown.CertificateSemantics
