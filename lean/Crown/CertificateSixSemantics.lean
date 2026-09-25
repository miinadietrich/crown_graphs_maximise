import Crown.CertificateSemantics

/-! Six-endpoint specialization of the verified four-pair mask transport.
The generic incidence-rank, implication, gate and surjection lemmas are reused
from CertificateSemantics. All finite domains below have exactly six bits.
-/
namespace Crown.CertificateSixSemantics
open Crown.Ranks Crown.CertificateSemantics

def maskBits (m : Fin 64) : Fin 6 → Bool := fun i => m.val.testBit i.val

/-- All six incidence bits determine a mask; higher bits vanish by the bound. -/
theorem maskBits_injective : Function.Injective maskBits := by
  intro m n h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · exact congrFun h ⟨i, hi⟩
  · have hpow : 64 ≤ 2^i := by
      exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega : 6 ≤ i)
    have hm : m.val < 2^i := Nat.lt_of_lt_of_le m.isLt hpow
    have hn : n.val < 2^i := Nat.lt_of_lt_of_le n.isLt hpow
    rw [Nat.testBit_lt_two_pow hm, Nat.testBit_lt_two_pow hn]

/-- Cardinality and injectivity give coverage of all six-bit neighbourhoods,
without checking all 64 squared pairs of bit vectors. -/
theorem maskBits_surjective : Function.Surjective maskBits := by
  have hcard : Fintype.card (Fin 64) = Fintype.card (Fin 6 → Bool) := by
    simp only [Fintype.card_fin, Fintype.card_pi_const, Fintype.card_bool]
    rfl
  exact ((Fintype.bijective_iff_injective_and_card maskBits).mpr
    ⟨maskBits_injective, hcard⟩).2

noncomputable def permuteMask (e : Fin 6 ≃ Fin 6) (m : Fin 64) : Fin 64 :=
  Classical.choose (maskBits_surjective (fun i => maskBits m (e.symm i)))

theorem permuteMask_bits (e : Fin 6 ≃ Fin 6) (m : Fin 64) :
    maskBits (permuteMask e m) = fun i => maskBits m (e.symm i) :=
  Classical.choose_spec (maskBits_surjective (fun i => maskBits m (e.symm i)))

theorem permuteMask_injective (e : Fin 6 ≃ Fin 6) : Function.Injective (permuteMask e) := by
  intro m n h
  apply maskBits_injective
  funext i
  have hb := congrFun (congrArg maskBits h) (e i)
  simpa only [permuteMask_bits, Equiv.symm_apply_apply] using hb

noncomputable def maskPermutation (e : Fin 6 ≃ Fin 6) : Fin 64 ≃ Fin 64 :=
  Equiv.ofBijective (permuteMask e)
    ⟨permuteMask_injective e, Finite.surjective_of_injective (permuteMask_injective e)⟩

theorem permuteMask_trans (e d : Fin 6 ≃ Fin 6) (m : Fin 64) :
    permuteMask (e.trans d) m = permuteMask d (permuteMask e m) := by
  apply maskBits_injective
  funext i
  simp [permuteMask_bits, Equiv.trans_apply]

/-- Relabel the selector vector by pullback along a coordinate permutation. -/
noncomputable def relabelSelector (s : Fin 64 → Bool) (e : Fin 6 ≃ Fin 6) : Fin 64 → Bool :=
  fun m => s (permuteMask e m)

theorem relabelSelector_trans (s : Fin 64 → Bool) (e d : Fin 6 ≃ Fin 6) :
    relabelSelector (relabelSelector s e) d = relabelSelector s (d.trans e) := by
  funext m
  simp [relabelSelector, permuteMask_trans]

/-- The maximum of the finite coordinate-permutation orbit satisfies all the
lexicographic comparisons. The order is descending in the mask index, exactly
as in `add_lex_geq`; no enumeration of the 720 permutations is evaluated. -/
theorem exists_lex_max_relabeling (s : Fin 64 → Bool) :
    ∃ e : Fin 6 ≃ Fin 6, ∀ d : Fin 6 ≃ Fin 6,
      toColex (relabelSelector (relabelSelector s e) d) ≤
        toColex (relabelSelector s e) := by
  classical
  obtain ⟨e, _, he⟩ := Finset.exists_max_image Finset.univ
    (fun e : Fin 6 ≃ Fin 6 => toColex (relabelSelector s e))
    (show (Finset.univ : Finset (Fin 6 ≃ Fin 6)).Nonempty from
      ⟨Equiv.refl _, Finset.mem_univ _⟩)
  refine ⟨e, fun d => ?_⟩
  rw [relabelSelector_trans]
  exact he (d.trans e) (Finset.mem_univ _)

/-- The prefix equality flag at an index enforces the source lex clause. -/
theorem lex_max_prefix (s : Fin 64 → Bool) (d : Fin 6 ≃ Fin 6)
    (hmax : toColex (relabelSelector s d) ≤ toColex s) (i : Fin 64)
    (hprefix : ∀ j > i, s j = s (permuteMask d j)) :
    s (permuteMask d i) = true → s i = true := by
  have hle := Pi.apply_le_of_toColex hmax (fun j hj => (hprefix j hj).symm)
  cases hx : s (permuteMask d i) <;> cases hy : s i <;>
    simp_all [relabelSelector, Bool.le_iff_imp]

/-- An oriented pairing is a bijective labelling of the six endpoints. -/
abbrev Pairing6 := (Fin 3 × Bool) ≃ Fin 6

def pairsOfEquiv (p : Pairing6) : Fin 3 → Fin 6 × Fin 6 :=
  fun i => (p (i, false), p (i, true))

theorem pairing_rank_coverage (p : Pairing6) (ρ : InitialRow (Fin 3)) :
    ∃ m : Fin 64, rowOfMask (pairsOfEquiv p) (maskBits m) = ρ := by
  let bits : Fin 6 → Bool := fun a =>
    if (p.symm a).2 then (bitsOfRank (ρ (p.symm a).1)).2
    else (bitsOfRank (ρ (p.symm a).1)).1
  obtain ⟨m, hm⟩ := maskBits_surjective bits
  refine ⟨m, ?_⟩
  rw [hm]
  funext i
  simpa [rowOfMask, pairsOfEquiv, bits] using rank_bits_inverse (ρ i)

def AllPairingsBad {V : Type} (masks : V → Fin 64) : Prop :=
  ∀ p : Pairing6, ¬ Feasible (fun v => rowOfMask (pairsOfEquiv p) (maskBits (masks v)))

/-- Universal infeasibility is invariant under vertex relabelling. No assumption
that the stored list of 60 pairings exhausts all pairings is needed here. -/
theorem allPairingsBad_permute {V : Type} (masks : V → Fin 64)
    (h : AllPairingsBad masks) (e : Fin 6 ≃ Fin 6) :
    AllPairingsBad (fun v => permuteMask e (masks v)) := by
  intro p hp
  apply h (p.trans e.symm)
  convert hp using 1
  funext v i
  simp [rowOfMask, pairsOfEquiv, permuteMask_bits, Equiv.trans_apply]

theorem mask_rank_injective (pairs : Fin 3 → Fin 6 × Fin 6) (h : Covers pairs) :
    Function.Injective (fun m : Fin 64 => rowOfMask pairs (maskBits m)) := by
  intro m n he
  exact maskBits_injective (rowOfMask_injective pairs h he)

/-- Extend the selector vector to the natural-number indexing of the counter. -/
def selectorNat (s : Fin 64 → Bool) (n : Nat) : Bool :=
  if h : n < 64 then s ⟨n, h⟩ else false

theorem prefixCount_selector (s : Fin 64 → Bool) :
    prefixCount (selectorNat s) 64 = Fintype.card {m // s m = true} := by
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
noncomputable def selectedEquiv (s : Fin 64 → Bool) (e : Fin 6 ≃ Fin 6) :
    {m // relabelSelector s e m = true} ≃ {m // s m = true} :=
  (maskPermutation e).subtypeEquiv (fun _ => Iff.rfl)

theorem selected_card_relabel (s : Fin 64 → Bool) (e : Fin 6 ≃ Fin 6) :
    Fintype.card {m // relabelSelector s e m = true} = Fintype.card {m // s m = true} :=
  Fintype.card_congr (selectedEquiv s e)

theorem selected_bad_relabel (s : Fin 64 → Bool) (e : Fin 6 ≃ Fin 6)
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
theorem canonical_bad_selection (s : Fin 64 → Bool)
    (hcard : Fintype.card {m // s m = true} ≤ 6)
    (hbad : AllPairingsBad (fun m : {m // s m = true} => m.val)) :
    ∃ t : Fin 64 → Bool,
      Fintype.card {m // t m = true} ≤ 6 ∧
      AllPairingsBad (fun m : {m // t m = true} => m.val) ∧
      (∀ d : Fin 6 ≃ Fin 6, toColex (relabelSelector t d) ≤ toColex t) := by
  obtain ⟨e, he⟩ := exists_lex_max_relabeling s
  refine ⟨relabelSelector s e, ?_, selected_bad_relabel s e hbad, he⟩
  rw [selected_card_relabel]
  exact hcard

theorem counter_six_iff (s : Nat → Bool) :
    counterValue s 64 7 = false ↔ prefixCount s 64 ≤ 6 := by
  simp only [counterValue, decide_eq_false_iff_not]
  omega

#print axioms maskBits_surjective
#print axioms canonical_bad_selection
end Crown.CertificateSixSemantics
