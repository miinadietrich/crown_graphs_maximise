import Crown.Arithmetic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Bool
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Crown.Matchings

abbrev FirstSets (k : ℕ) := {s : Finset (Fin (2 * k)) // s.card = k}
abbrev First {k : ℕ} (s : FirstSets k) := {v : Fin (2 * k) // v ∈ s.val}
abbrev Second {k : ℕ} (s : FirstSets k) := {v : Fin (2 * k) // v ∉ s.val}
abbrev OrientedPairing (k : ℕ) := Σ s : FirstSets k, First s ≃ Second s

/-- The same oriented pairing model on any finite vertex type. The
bijection itself forces the two endpoint sets to have equal cardinality. -/
abbrev PairingOn (V : Type*) [DecidableEq V] :=
  Σ s : Finset V, {v : V // v ∈ s} ≃ {v : V // v ∉ s}

def relabel {V W : Type*} [DecidableEq V] [DecidableEq W] (e : V ≃ W) :
    PairingOn V ≃ PairingOn W :=
  Equiv.sigmaCongr e.finsetCongr (fun s => Equiv.equivCongr
    (Equiv.subtypeEquiv e (by intro v; simp))
    (Equiv.subtypeEquiv e (by intro v; simp)))

theorem pairingOn_half_card (k : ℕ) (p : PairingOn (Fin (2 * k))) : p.1.card = k := by
  have h := Fintype.card_congr p.2
  simp only [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe] at h
  omega

def constrainedEquiv (k : ℕ) : OrientedPairing k ≃ PairingOn (Fin (2 * k)) where
  toFun p := ⟨p.1.val, p.2⟩
  invFun p := ⟨⟨p.1, pairingOn_half_card k p⟩, p.2⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

theorem card_firstSets (k : ℕ) : Fintype.card (FirstSets k) = Nat.choose (2 * k) k := by
  simp [FirstSets]

theorem card_first {k : ℕ} (s : FirstSets k) : Fintype.card (First s) = k := by
  simpa using s.property

theorem card_second {k : ℕ} (s : FirstSets k) : Fintype.card (Second s) = k := by
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin, card_first]
  omega

noncomputable def firstCoordinates {k : ℕ} (s : FirstSets k) : Fin k ≃ First s :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin, card_first])

/-- An explicit coordinate presentation of the unordered pairs. -/
noncomputable def coordinates {k : ℕ} (p : OrientedPairing k) : Fin k × Bool ≃ Fin (2 * k) :=
  ((Equiv.prodComm (Fin k) Bool).trans (Equiv.boolProdEquivSum (Fin k))).trans
    ((Equiv.sumCongr (firstCoordinates p.1) ((firstCoordinates p.1).trans p.2)).trans
      (Equiv.sumCompl (fun v : Fin (2 * k) => v ∈ p.1.val)))

theorem coordinates_first {k : ℕ} (p : OrientedPairing k) (i : Fin k) :
    coordinates p (i, false) = (firstCoordinates p.1 i).val := rfl

theorem coordinates_second {k : ℕ} (p : OrientedPairing k) (i : Fin k) :
    coordinates p (i, true) = (p.2 (firstCoordinates p.1 i)).val := rfl

theorem coordinates_first_mem {k : ℕ} (p : OrientedPairing k) (i : Fin k) :
    coordinates p (i, false) ∈ p.1.val := (firstCoordinates p.1 i).property

theorem coordinates_second_not_mem {k : ℕ} (p : OrientedPairing k) (i : Fin k) :
    coordinates p (i, true) ∉ p.1.val := (p.2 (firstCoordinates p.1 i)).property

theorem coordinates_pair_distinct {k : ℕ} (p : OrientedPairing k) (i : Fin k) :
    coordinates p (i, false) ≠ coordinates p (i, true) := by
  intro heq
  have h := (coordinates p).injective heq
  cases Prod.mk.inj h |>.2

/-- The pairs cover the entire vertex set, with unique pair and endpoint
coordinates. This includes k=0, when both sides of the equivalence are empty. -/
theorem coordinates_coverage {k : ℕ} (p : OrientedPairing k) (v : Fin (2 * k)) :
    ∃! q : Fin k × Bool, coordinates p q = v :=
  (coordinates p).bijective.existsUnique v

theorem card_pairing_fiber {k : ℕ} (s : FirstSets k) :
    Fintype.card (First s ≃ Second s) = k.factorial := by
  let e : First s ≃ Second s := Fintype.equivOfCardEq (by rw [card_first, card_second])
  rw [Fintype.card_equiv e, card_first]

theorem choose_mul_factorial_eq_Q (k : ℕ) :
    Nat.choose (2 * k) k * k.factorial = Arithmetic.Q k := by
  have h := Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ 2 * k)
  have he : 2 * k - k = k := by omega
  rw [he] at h
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos k)
  exact h.trans (Arithmetic.Q_mul_factorial k).symm

/-- P04: exact cardinality of the oriented, unordered pairing sample space. -/
theorem card_orientedPairing (k : ℕ) : Fintype.card (OrientedPairing k) = Arithmetic.Q k := by
  calc
    Fintype.card (OrientedPairing k) = ∑ s : FirstSets k, k.factorial := by
      rw [Fintype.card_sigma]
      exact Finset.sum_congr rfl (fun s _ => card_pairing_fiber s)
    _ = Nat.choose (2 * k) k * k.factorial := by simp
    _ = Arithmetic.Q k := choose_mul_factorial_eq_Q k

theorem card_pairingOn {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ)
    (hV : Fintype.card V = 2 * k) : Fintype.card (PairingOn V) = Arithmetic.Q k := by
  let e : V ≃ Fin (2 * k) := Fintype.equivOfCardEq (by simpa using hV)
  calc
    Fintype.card (PairingOn V) = Fintype.card (PairingOn (Fin (2 * k))) :=
      Fintype.card_congr (relabel e)
    _ = Fintype.card (OrientedPairing k) := Fintype.card_congr (constrainedEquiv k).symm
    _ = Arithmetic.Q k := card_orientedPairing k

/-- Fixing the first-endpoint set leaves exactly the bijection as free data. -/
def firstSetFiberEquiv {k : ℕ} (s : FirstSets k) :
    {p : OrientedPairing k // p.1 = s} ≃ (First s ≃ Second s) where
  toFun p := by
    rcases p with ⟨⟨t, e⟩, h⟩
    cases h
    exact e
  invFun e := ⟨⟨s, e⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨t, e⟩, h⟩
    cases h
    rfl
  right_inv := by intro e; rfl

theorem card_firstSetFiber {k : ℕ} (s : FirstSets k) :
    Fintype.card {p : OrientedPairing k // p.1 = s} = k.factorial := by
  rw [Fintype.card_congr (firstSetFiberEquiv s), card_pairing_fiber]

/-- Rearranging the data of an event determined only by its first endpoints. -/
def selectedFirstSetsEquiv {k : ℕ} (T : Finset (FirstSets k)) :
    {p : OrientedPairing k // p.1 ∈ T} ≃
      (Σ s : {s : FirstSets k // s ∈ T}, First s.val ≃ Second s.val) where
  toFun p := ⟨⟨p.val.1, p.property⟩, p.val.2⟩
  invFun q := ⟨⟨q.1.val, q.2⟩, q.1.property⟩
  left_inv := by intro p; rfl
  right_inv := by intro q; rfl

/-- Exact uniformity of the first-endpoint sets in the pairing sample space.
This supplies the conditional uniformity calculation needed in P15 after
the specified central pair has been deleted. -/
theorem card_selectedFirstSets {k : ℕ} (T : Finset (FirstSets k)) :
    Fintype.card {p : OrientedPairing k // p.1 ∈ T} = T.card * k.factorial := by
  rw [Fintype.card_congr (selectedFirstSetsEquiv T), Fintype.card_sigma]
  simp_rw [card_pairing_fiber]
  simp

theorem card_selectedFirstSets_le_two {k : ℕ} (T : Finset (FirstSets k)) (hT : T.card ≤ 2) :
    Fintype.card {p : OrientedPairing k // p.1 ∈ T} ≤ 2 * k.factorial := by
  rw [card_selectedFirstSets]
  exact Nat.mul_le_mul_right _ hT

/-- Removing a prescribed image from a bijection. -/
def deleteImage {A B : Type*} (a : A) (b : B) (e : A ≃ B) (he : e a = b) :
    {x : A // x ≠ a} ≃ {y : B // y ≠ b} :=
  Equiv.subtypeEquiv e (by intro x; rw [← he, e.injective.ne_iff])

/-- Reinserting the prescribed image gives a bijection on the full types. -/
def insertImage {A B : Type*} [DecidableEq A] [DecidableEq B] (a : A) (b : B)
    (e : {x : A // x ≠ a} ≃ {y : B // y ≠ b}) : A ≃ B where
  toFun x := if h : x = a then b else (e ⟨x, h⟩).val
  invFun y := if h : y = b then a else (e.symm ⟨y, h⟩).val
  left_inv x := by
    by_cases h : x = a
    · simp [h]
    · simp [h, (e ⟨x, h⟩).property]
  right_inv y := by
    by_cases h : y = b
    · simp [h]
    · simp [h, (e.symm ⟨y, h⟩).property]

def prescribedImageEquiv {A B : Type*} [DecidableEq A] [DecidableEq B] (a : A) (b : B) :
    {e : A ≃ B // e a = b} ≃ ({x : A // x ≠ a} ≃ {y : B // y ≠ b}) where
  toFun e := deleteImage a b e.val e.property
  invFun e := ⟨insertImage a b e, by simp [insertImage]⟩
  left_inv e := by
    apply Subtype.ext
    ext x
    by_cases hx : x = a
    · simp [insertImage, hx, e.property]
    · simp [insertImage, deleteImage, hx]
  right_inv e := by
    ext x
    simp [deleteImage, insertImage, x.property]

theorem card_prescribedImage {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (a : A) (b : B)
    (hcard : Fintype.card A = Fintype.card B) :
    Fintype.card {e : A ≃ B // e a = b} = (Fintype.card A - 1).factorial := by
  rw [Fintype.card_congr (prescribedImageEquiv a b)]
  have hc : Fintype.card {x : A // x ≠ a} = Fintype.card {y : B // y ≠ b} := by
    simp only [Fintype.card_subtype_compl, Fintype.card_unique, hcard]
  let e : {x : A // x ≠ a} ≃ {y : B // y ≠ b} := Fintype.equivOfCardEq hc
  rw [Fintype.card_equiv e]
  simp only [Fintype.card_subtype_compl, Fintype.card_unique]

/-- For a fixed first-endpoint set, prescribing a pair leaves (k-1)!
bijections. This counts actual pairs in the full unordered matching model. -/
theorem card_fixedFirstSet_prescribedPair {k : ℕ} (s : FirstSets k)
    (a : First s) (b : Second s) :
    Fintype.card {e : First s ≃ Second s // e a = b} = (k - 1).factorial := by
  rw [card_prescribedImage a b (by rw [card_first, card_second]), card_first]

section PrescribedPair

variable (V : Type*) [Fintype V] [DecidableEq V]

abbrev PrescribedFirstSets := {s : Finset (Bool ⊕ V) //
  Sum.inl false ∈ s ∧ Sum.inl true ∉ s}

def residualFirstSet (s : PrescribedFirstSets V) : Finset V :=
  Finset.univ.filter (fun v => Sum.inr v ∈ s.val)

def prescribedFirstSetsEquiv : PrescribedFirstSets V ≃ Finset V where
  toFun := residualFirstSet V
  invFun t := ⟨insert (Sum.inl false) (t.map ⟨Sum.inr, Sum.inr_injective⟩), by simp⟩
  left_inv s := by
    apply Subtype.ext
    ext v
    cases v with
    | inl b => cases b <;> simp [residualFirstSet, s.property.1, s.property.2]
    | inr v => simp [residualFirstSet]
  right_inv t := by
    ext v
    simp [residualFirstSet]

abbrev PairFirst (s : PrescribedFirstSets V) := {v : Bool ⊕ V // v ∈ s.val}
abbrev PairSecond (s : PrescribedFirstSets V) := {v : Bool ⊕ V // v ∉ s.val}

def removedFirstEquiv (s : PrescribedFirstSets V) :
    {x : PairFirst V s // x ≠ ⟨Sum.inl false, s.property.1⟩} ≃
      {v : V // v ∈ residualFirstSet V s} where
  toFun x := by
    rcases x with ⟨⟨x, hx⟩, hne⟩
    cases x with
    | inl b =>
      cases b with
      | false => exact False.elim (hne (Subtype.ext rfl))
      | true => exact False.elim (s.property.2 hx)
    | inr v => exact ⟨v, by simpa [residualFirstSet] using hx⟩
  invFun v := ⟨⟨Sum.inr v.val, by simpa [residualFirstSet] using v.property⟩,
    by intro h; cases congrArg Subtype.val h⟩
  left_inv x := by
    rcases x with ⟨⟨x, hx⟩, hne⟩
    cases x with
    | inl b =>
      cases b with
      | false => exact False.elim (hne (Subtype.ext rfl))
      | true => exact False.elim (s.property.2 hx)
    | inr v => rfl
  right_inv v := rfl

def removedSecondEquiv (s : PrescribedFirstSets V) :
    {x : PairSecond V s // x ≠ ⟨Sum.inl true, s.property.2⟩} ≃
      {v : V // v ∉ residualFirstSet V s} where
  toFun x := by
    rcases x with ⟨⟨x, hx⟩, hne⟩
    cases x with
    | inl b =>
      cases b with
      | false => exact False.elim (hx s.property.1)
      | true => exact False.elim (hne (Subtype.ext rfl))
    | inr v => exact ⟨v, by simpa [residualFirstSet] using hx⟩
  invFun v := ⟨⟨Sum.inr v.val, by simpa [residualFirstSet] using v.property⟩,
    by intro h; cases congrArg Subtype.val h⟩
  left_inv x := by
    rcases x with ⟨⟨x, hx⟩, hne⟩
    cases x with
    | inl b =>
      cases b with
      | false => exact False.elim (hx s.property.1)
      | true => exact False.elim (hne (Subtype.ext rfl))
    | inr v => rfl
  right_inv v := rfl

/-- Actual oriented pairings containing the prescribed pair false → true.
The remaining vertices are arbitrary; there is no ordering of the other pairs. -/
abbrev PrescribedPair := Σ s : PrescribedFirstSets V,
  {e : PairFirst V s ≃ PairSecond V s //
    e ⟨Sum.inl false, s.property.1⟩ = ⟨Sum.inl true, s.property.2⟩}

def DirectedPair {W : Type*} [DecidableEq W] (p : PairingOn W) (a b : W) : Prop :=
  a ∈ p.1 ∧ b ∉ p.1 ∧ ∀ ha hb, p.2 ⟨a, ha⟩ = ⟨b, hb⟩

theorem directedPair_relabel {A B : Type*} [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (p : PairingOn A) (a b : A) :
    DirectedPair (relabel e p) (e a) (e b) ↔ DirectedPair p a b := by
  let e₁ : {v : A // v ∈ p.1} ≃ {v : B // v ∈ e.finsetCongr p.1} := Equiv.subtypeEquiv e (by intro v; simp : ∀ v, v ∈ p.1 ↔ e v ∈ e.finsetCongr p.1)
  let e₂ : {v : A // v ∉ p.1} ≃ {v : B // v ∉ e.finsetCongr p.1} := Equiv.subtypeEquiv e (by intro v; simp : ∀ v, v ∉ p.1 ↔ e v ∉ e.finsetCongr p.1)
  change DirectedPair ⟨e.finsetCongr p.1, e₁.symm.trans (p.2.trans e₂)⟩ (e a) (e b) ↔ _
  constructor
  · rintro ⟨ha, hb, he⟩
    refine ⟨by simpa using ha, by simpa using hb, ?_⟩
    intro h1 h2
    have hx : e₁.symm ⟨e a, ha⟩ = ⟨a, h1⟩ := by
      apply Subtype.ext
      exact e.symm_apply_apply a
    have h := congrArg Subtype.val (he ha hb)
    change e ((p.2 (e₁.symm ⟨e a, ha⟩)).val) = e b at h
    rw [hx] at h
    exact Subtype.ext (e.injective h)
  · rintro ⟨ha, hb, he⟩
    refine ⟨by simpa using ha, by simpa using hb, ?_⟩
    intro h1 h2
    apply Subtype.ext
    change e ((p.2 (e₁.symm ⟨e a, h1⟩)).val) = e b
    have hx : e₁.symm ⟨e a, h1⟩ = ⟨a, ha⟩ := by
      apply Subtype.ext
      exact e.symm_apply_apply a
    rw [hx, he ha hb]
def prescribedPairEventEquiv : PrescribedPair V ≃
    {p : PairingOn (Bool ⊕ V) // DirectedPair p (Sum.inl false) (Sum.inl true)} where
  toFun p := ⟨⟨p.1.val, p.2.val⟩, p.1.property.1, p.1.property.2,
    fun _ _ => p.2.property⟩
  invFun p := ⟨⟨p.val.1, p.property.1, p.property.2.1⟩,
    p.val.2, p.property.2.2 _ _⟩
  left_inv _ := rfl
  right_inv _ := rfl

def deletePrescribedPair : PrescribedPair V ≃ PairingOn V :=
  Equiv.sigmaCongr (prescribedFirstSetsEquiv V) (fun s =>
    (prescribedImageEquiv (⟨Sum.inl false, s.property.1⟩ : PairFirst V s) (⟨Sum.inl true, s.property.2⟩ : PairSecond V s)).trans
      (Equiv.equivCongr (removedFirstEquiv V s) (removedSecondEquiv V s)))

theorem card_prescribedPair (k : ℕ) (hV : Fintype.card V = 2 * k) :
    Fintype.card (PrescribedPair V) = Arithmetic.Q k := by
  rw [Fintype.card_congr (deletePrescribedPair V), card_pairingOn k hV]

open scoped Classical in
theorem card_directedPair_event (k : ℕ) (hV : Fintype.card V = 2 * k) :
    Fintype.card {p : PairingOn (Bool ⊕ V) //
      DirectedPair p (Sum.inl false) (Sum.inl true)} = Arithmetic.Q k := by
  classical
  rw [← Fintype.card_congr (prescribedPairEventEquiv V), card_prescribedPair V k hV]

open scoped Classical in
theorem card_reversePair_event (k : ℕ) (hV : Fintype.card V = 2 * k) :
    Fintype.card {p : PairingOn (Bool ⊕ V) //
      DirectedPair p (Sum.inl true) (Sum.inl false)} = Arithmetic.Q k := by
  let swap := Equiv.sumCongr Equiv.boolNot (Equiv.refl V)
  let e : {p : PairingOn (Bool ⊕ V) // DirectedPair p (Sum.inl true) (Sum.inl false)} ≃
      {p : PairingOn (Bool ⊕ V) // DirectedPair p (Sum.inl false) (Sum.inl true)} :=
    Equiv.subtypeEquiv (relabel swap) (fun p =>
      (directedPair_relabel swap p (Sum.inl true) (Sum.inl false)).symm)
  rw [Fintype.card_congr e]
  exact card_directedPair_event V k hV

open scoped Classical in
theorem card_unorientedPair_event (k : ℕ) (hV : Fintype.card V = 2 * k) :
    Fintype.card {p : PairingOn (Bool ⊕ V) //
      DirectedPair p (Sum.inl false) (Sum.inl true) ∨
      DirectedPair p (Sum.inl true) (Sum.inl false)} = 2 * Arithmetic.Q k := by
  rw [Fintype.card_subtype_or_disjoint]
  · rw [card_directedPair_event V k hV, card_reversePair_event V k hV]
    omega
  · exact fun _ hf hg p hp => (hg p hp).2.1 (hf p hp).1

end PrescribedPair

abbrev ResidualVertices {V : Type*} (a b : V) := {v : V // v ≠ a ∧ v ≠ b}

def twoVertexEquiv {V : Type*} [DecidableEq V] (a b : V) (hab : a ≠ b) :
    Bool ⊕ ResidualVertices a b ≃ V where
  toFun x := match x with
    | Sum.inl false => a
    | Sum.inl true => b
    | Sum.inr v => v.val
  invFun v := if ha : v = a then Sum.inl false
    else if hb : v = b then Sum.inl true else Sum.inr ⟨v, ha, hb⟩
  left_inv x := by
    cases x with
    | inl s => cases s <;> simp [Ne.symm hab]
    | inr v => simp [v.property.1, v.property.2]
  right_inv v := by
    by_cases ha : v = a
    · simp [ha]
    · by_cases hb : v = b <;> simp [ha, hb, Ne.symm hab]

def deletePairEvent {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V) (hab : a ≠ b) :
    {p : PairingOn V // DirectedPair p a b} ≃ PairingOn (ResidualVertices a b) := by
  let e := twoVertexEquiv a b hab
  let er : {p : PairingOn (Bool ⊕ ResidualVertices a b) //
      DirectedPair p (Sum.inl false) (Sum.inl true)} ≃
      {p : PairingOn V // DirectedPair p a b} :=
    Equiv.subtypeEquiv (relabel e) (fun p =>
      (directedPair_relabel e p (Sum.inl false) (Sum.inl true)).symm)
  exact er.symm.trans ((prescribedPairEventEquiv (ResidualVertices a b)).symm.trans
    (deletePrescribedPair (ResidualVertices a b)))

theorem card_residualVertices {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V) (hab : a ≠ b) :
    Fintype.card (ResidualVertices a b) + 2 = Fintype.card V := by
  have h := Fintype.card_congr (twoVertexEquiv a b hab)
  simpa [Nat.add_comm] using h

open scoped Classical in
theorem card_directedPair_any {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (hV : Fintype.card V = 2 * (k + 1)) (a b : V) (hab : a ≠ b) :
    Fintype.card {p : PairingOn V // DirectedPair p a b} = Arithmetic.Q k := by
  have hc := card_residualVertices a b hab
  rw [hV] at hc
  rw [Fintype.card_congr (deletePairEvent a b hab), card_pairingOn k (by omega)]

open scoped Classical in
theorem card_unorientedPair_any {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (hV : Fintype.card V = 2 * (k + 1)) (a b : V) (hab : a ≠ b) :
    Fintype.card {p : PairingOn V // DirectedPair p a b ∨ DirectedPair p b a} =
      2 * Arithmetic.Q k := by
  rw [Fintype.card_subtype_or_disjoint]
  · rw [card_directedPair_any k hV a b hab, card_directedPair_any k hV b a (Ne.symm hab)]
    omega
  · exact fun _ hf hg p hp => (hg p hp).2.1 (hf p hp).1

noncomputable def residualPairing (k : ℕ) :
    PrescribedPair (Fin (2 * k)) ≃ OrientedPairing k :=
  (deletePrescribedPair (Fin (2 * k))).trans (constrainedEquiv k).symm

/-- After deleting a specified oriented pair, the first endpoint sets of
the residual unordered pairs are exactly uniform. -/
theorem card_prescribedPair_residualSets (k : ℕ) (T : Finset (FirstSets k)) :
    Fintype.card {p : PrescribedPair (Fin (2 * k)) // (residualPairing k p).1 ∈ T} =
      T.card * k.factorial := by
  classical
  let e : {p : PrescribedPair (Fin (2 * k)) // (residualPairing k p).1 ∈ T} ≃
      {p : OrientedPairing k // p.1 ∈ T} :=
    Equiv.subtypeEquiv (residualPairing k) (fun _ => Iff.rfl)
  rw [Fintype.card_congr e, card_selectedFirstSets]

theorem Q_succ (k : ℕ) : Arithmetic.Q (k + 1) =
    2 * (2 * k + 1) * Arithmetic.Q k := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (k + 1))
  rw [Arithmetic.Q_mul_factorial]
  have he : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
  rw [he, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  rw [← Arithmetic.Q_mul_factorial k]
  ring

theorem prescribedPair_probability (k : ℕ) :
    (2 * Arithmetic.Q k : ℚ) / Arithmetic.Q (k + 1) = 1 / (2 * k + 1) := by
  rw [Q_succ]
  have hQ : (Arithmetic.Q k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Arithmetic.Q_pos k))
  push_cast
  field_simp

theorem residual_at_most_two (k : ℕ) (T : Finset (FirstSets k)) (hT : T.card ≤ 2) :
    Fintype.card {p : PrescribedPair (Fin (2 * k)) // (residualPairing k p).1 ∈ T} ≤
      2 * k.factorial := by
  rw [card_prescribedPair_residualSets]
  exact Nat.mul_le_mul_right _ hT

theorem directedPair_delete_prescribed {V : Type*} [Fintype V] [DecidableEq V]
    (p : PrescribedPair V) (x y : V) :
    DirectedPair (deletePrescribedPair V p) x y ↔
      DirectedPair (prescribedPairEventEquiv V p).val (Sum.inr x) (Sum.inr y) := by
  let s := p.1
  let ea := removedFirstEquiv V s
  let eb := removedSecondEquiv V s
  let ed := deleteImage (⟨Sum.inl false,s.property.1⟩ : PairFirst V s)
    (⟨Sum.inl true,s.property.2⟩ : PairSecond V s) p.2.val p.2.property
  change DirectedPair ⟨residualFirstSet V s,ea.symm.trans (ed.trans eb)⟩ x y ↔
    DirectedPair ⟨s.val,p.2.val⟩ (Sum.inr x) (Sum.inr y)
  constructor
  · rintro ⟨hx,hy,he⟩
    have hx' : Sum.inr x ∈ s.val := (Finset.mem_filter.mp hx).2
    have hy' : Sum.inr y ∉ s.val := fun h => hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    refine ⟨hx',hy',?_⟩
    intro h1 h2
    have hh := he hx hy
    change eb (ed (ea.symm ⟨x,hx⟩)) = ⟨y,hy⟩ at hh
    have hd := eb.injective (hh.trans (eb.apply_symm_apply ⟨y,hy⟩).symm)
    have hv := congrArg (fun z => z.val.val) hd
    exact Subtype.ext hv
  · rintro ⟨hx,hy,he⟩
    have hx' : x ∈ residualFirstSet V s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩
    have hy' : y ∉ residualFirstSet V s := fun h => hy (Finset.mem_filter.mp h).2
    refine ⟨hx',hy',?_⟩
    intro h1 h2
    change eb (ed (ea.symm ⟨x,h1⟩)) = ⟨y,h2⟩
    apply eb.symm.injective
    rw [Equiv.symm_apply_apply]
    apply Subtype.ext
    exact he hx hy

theorem directedPair_delete_any {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V) (hab : a ≠ b) (p : {p : PairingOn V // DirectedPair p a b})
    (x y : ResidualVertices a b) :
    DirectedPair (deletePairEvent a b hab p) x y ↔ DirectedPair p.val x.val y.val := by
  let e := twoVertexEquiv a b hab
  let er : {p : PairingOn (Bool ⊕ ResidualVertices a b) //
      DirectedPair p (Sum.inl false) (Sum.inl true)} ≃
      {p : PairingOn V // DirectedPair p a b} :=
    Equiv.subtypeEquiv (relabel e) (fun p =>
      (directedPair_relabel e p (Sum.inl false) (Sum.inl true)).symm)
  let q := er.symm p
  have hp : relabel e q.val = p.val := congrArg Subtype.val (er.apply_symm_apply p)
  change DirectedPair (deletePrescribedPair (ResidualVertices a b)
    ((prescribedPairEventEquiv (ResidualVertices a b)).symm q)) x y ↔ _
  rw [directedPair_delete_prescribed]
  change DirectedPair q.val (Sum.inr x) (Sum.inr y) ↔ _
  have hh := directedPair_relabel e q.val (Sum.inr x) (Sum.inr y)
  rw [hp] at hh
  exact hh.symm

def Respects {V : Type*} [DecidableEq V] (p : PairingOn V) (R : V → V → Prop) : Prop :=
  ∀ a b, DirectedPair p a b → R a b

theorem respects_relabel {V W : Type*} [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (p : PairingOn V) (R : W → W → Prop) :
    Respects (relabel e p) R ↔ Respects p (fun a b => R (e a) (e b)) := by
  constructor
  · intro h a b hab
    exact h (e a) (e b) ((directedPair_relabel e p a b).mpr hab)
  · intro h a b hab
    obtain ⟨a,rfl⟩ := e.surjective a
    obtain ⟨b,rfl⟩ := e.surjective b
    exact h a b ((directedPair_relabel e p a b).mp hab)

theorem directedPair_same_second {V : Type*} [DecidableEq V] (p : PairingOn V)
    (a b c : V) (ha : DirectedPair p a c) (hb : DirectedPair p b c) : a = b := by
  have h := p.2.injective ((ha.2.2 ha.1 ha.2.1).trans (hb.2.2 hb.1 hb.2.1).symm)
  exact congrArg Subtype.val h

/-- Deleting a specified pair preserves every other oriented edge.
Consequently any restriction on the other edges is exactly a restriction
on the residual pairing, not merely an upper bound. -/
theorem respects_deletePair {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V) (hab : a ≠ b) (p : {p : PairingOn V // DirectedPair p a b})
    (R : V → V → Prop) :
    Respects (deletePairEvent a b hab p) (fun x y => R x.val y.val) ↔
      ∀ x y, DirectedPair p.val x y → x = a ∨ R x y := by
  constructor
  · intro h x y hxy
    by_cases hxa : x = a
    · exact Or.inl hxa
    · right
      have hxb : x ≠ b := fun he => p.property.2.1 (he ▸ hxy.1)
      have hya : y ≠ a := fun he => hxy.2.1 (he.symm ▸ p.property.1)
      have hyb : y ≠ b := by
        intro he
        subst y
        exact hxa (directedPair_same_second p.val x a b hxy p.property)
      exact h ⟨x,hxa,hxb⟩ ⟨y,hya,hyb⟩
        ((directedPair_delete_any a b hab p _ _).mpr hxy)
  · intro h x y hxy
    have hh := h x.val y.val ((directedPair_delete_any a b hab p x y).mp hxy)
    exact hh.resolve_left x.property.1

def ExceptPairEvent {V : Type*} [DecidableEq V] (p : PairingOn V)
    (a b : V) (R : V → V → Prop) : Prop :=
  DirectedPair p a b ∧ ∀ x y, DirectedPair p x y → x = a ∨ R x y

noncomputable def exceptPairEventEquiv {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V) (hab : a ≠ b) (R : V → V → Prop) :
    {p : PairingOn V // ExceptPairEvent p a b R} ≃
      {q : PairingOn (ResidualVertices a b) // Respects q (fun x y => R x.val y.val)} := by
  let e₁ : {p : PairingOn V // ExceptPairEvent p a b R} ≃
      {p : {p : PairingOn V // DirectedPair p a b} //
        ∀ x y, DirectedPair p.val x y → x = a ∨ R x y} :=
    { toFun := fun p => ⟨⟨p.val,p.property.1⟩,p.property.2⟩
      invFun := fun p => ⟨p.val.val,p.val.property,p.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ : {p : {p : PairingOn V // DirectedPair p a b} //
        ∀ x y, DirectedPair p.val x y → x = a ∨ R x y} ≃
      {q : PairingOn (ResidualVertices a b) // Respects q (fun x y => R x.val y.val)} :=
    Equiv.subtypeEquiv (deletePairEvent a b hab)
      (fun p => (respects_deletePair a b hab p R).symm)
  exact e₁.trans e₂

open scoped Classical in
theorem card_exceptPairEvent {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V) (hab : a ≠ b) (R : V → V → Prop) :
    Fintype.card {p : PairingOn V // ExceptPairEvent p a b R} =
      Fintype.card {q : PairingOn (ResidualVertices a b) // Respects q (fun x y => R x.val y.val)} :=
  Fintype.card_congr (exceptPairEventEquiv a b hab R)

theorem directedPair_same_first {V : Type*} [DecidableEq V] (p : PairingOn V)
    (a b c : V) (ha : DirectedPair p a b) (hb : DirectedPair p a c) : b = c := by
  have h := (ha.2.2 ha.1 ha.2.1).symm.trans (hb.2.2 hb.1 hb.2.1)
  exact congrArg Subtype.val h

def OneExceptional {V : Type*} [DecidableEq V] (p : PairingOn V)
    (R : V → V → Prop) (E : Finset (V × V)) : Prop :=
  ∃ e : {e : V × V // e ∈ E}, ExceptPairEvent p e.val.1 e.val.2 R

noncomputable def oneExceptionEquiv {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (E : Finset (V × V)) (hbad : ∀ e ∈ E, ¬ R e.1 e.2) :
    (Σ e : {e : V × V // e ∈ E}, {p : PairingOn V // ExceptPairEvent p e.val.1 e.val.2 R}) ≃
      {p : PairingOn V // OneExceptional p R E} :=
  Equiv.ofBijective (fun r => ⟨r.2.val,⟨r.1,r.2.property⟩⟩) ⟨by
    rintro ⟨e,p⟩ ⟨f,q⟩ h
    have hpq : p.val = q.val := congrArg Subtype.val h
    have hq : DirectedPair p.val f.val.1 f.val.2 := hpq.symm ▸ q.property.1
    have hfirst : e.val.1 = f.val.1 := by
      rcases p.property.2 f.val.1 f.val.2 hq with he | hr
      · exact he.symm
      · exact False.elim (hbad f.val f.property hr)
    have hq' : DirectedPair p.val e.val.1 f.val.2 :=
      Eq.mp (congrArg (fun v => DirectedPair p.val v f.val.2) hfirst.symm) hq
    have hsecond := directedPair_same_first p.val e.val.1 e.val.2 f.val.2 p.property.1 hq'
    have hef : e = f := Subtype.ext (Prod.ext hfirst hsecond)
    cases hef
    exact congrArg (Sigma.mk e) (Subtype.ext hpq), by
    rintro ⟨p,⟨e,he⟩⟩
    exact ⟨⟨e,⟨p,he⟩⟩,rfl⟩⟩

open scoped Classical in
theorem card_oneExceptional {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (E : Finset (V × V)) (hbad : ∀ e ∈ E, ¬ R e.1 e.2) :
    Fintype.card {p : PairingOn V // OneExceptional p R E} =
      ∑ e : {e : V × V // e ∈ E},
        Fintype.card {p : PairingOn V // ExceptPairEvent p e.val.1 e.val.2 R} := by
  rw [← Fintype.card_congr (oneExceptionEquiv R E hbad), Fintype.card_sigma]

open scoped Classical in
theorem card_ordinary_or_oneExceptional {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (E : Finset (V × V)) (hbad : ∀ e ∈ E, ¬ R e.1 e.2) :
    Fintype.card {p : PairingOn V // Respects p R ∨ OneExceptional p R E} =
      Fintype.card {p : PairingOn V // Respects p R} +
        ∑ e : {e : V × V // e ∈ E},
          Fintype.card {p : PairingOn V // ExceptPairEvent p e.val.1 e.val.2 R} := by
  rw [Fintype.card_subtype_or_disjoint]
  · rw [card_oneExceptional R E hbad]
  · intro q hR hE p hp
    obtain ⟨e,he⟩ := hE p hp
    exact hbad e.val e.property (hR p hp e.val.1 e.val.2 he.1)

def residualSwap {V : Type*} (a b : V) : ResidualVertices a b ≃ ResidualVertices b a :=
  Equiv.subtypeEquivProp (by funext v; exact propext and_comm)

noncomputable def reverseExceptPairEquiv {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V) (hab : a ≠ b) (R : V → V → Prop) :
    {p : PairingOn V // ExceptPairEvent p a b R} ≃
      {p : PairingOn V // ExceptPairEvent p b a R} := by
  let e : {q : PairingOn (ResidualVertices a b) // Respects q (fun x y => R x.val y.val)} ≃
      {q : PairingOn (ResidualVertices b a) // Respects q (fun x y => R x.val y.val)} :=
    Equiv.subtypeEquiv (relabel (residualSwap a b)) (fun q =>
      (respects_relabel (residualSwap a b) q (fun x y => R x.val y.val)).symm)
  exact (exceptPairEventEquiv a b hab R).trans
    (e.trans (exceptPairEventEquiv b a (Ne.symm hab) R).symm)

open scoped Classical in
theorem card_exceptPair_reverse {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V) (hab : a ≠ b) (R : V → V → Prop) :
    Fintype.card {p : PairingOn V // ExceptPairEvent p a b R} =
      Fintype.card {p : PairingOn V // ExceptPairEvent p b a R} :=
  Fintype.card_congr (reverseExceptPairEquiv a b hab R)

theorem natCard_exceptPairEvent {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V) (hab : a ≠ b) (R : V → V → Prop) :
    Nat.card {p : PairingOn V // ExceptPairEvent p a b R} =
      Nat.card {q : PairingOn (ResidualVertices a b) // Respects q (fun x y => R x.val y.val)} :=
  Nat.card_congr (exceptPairEventEquiv a b hab R)

open scoped Classical in
theorem natCard_oneExceptional {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) (E : Finset (V × V)) (hbad : ∀ e ∈ E, ¬ R e.1 e.2) :
    Nat.card {p : PairingOn V // OneExceptional p R E} =
      ∑ e : {e : V × V // e ∈ E}, Nat.card {p : PairingOn V // ExceptPairEvent p e.val.1 e.val.2 R} := by
  rw [← Nat.card_congr (oneExceptionEquiv R E hbad), Nat.card_sigma]

theorem natCard_exceptPair_reverse {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V) (hab : a ≠ b) (R : V → V → Prop) :
    Nat.card {p : PairingOn V // ExceptPairEvent p a b R} =
      Nat.card {p : PairingOn V // ExceptPairEvent p b a R} :=
  Nat.card_congr (reverseExceptPairEquiv a b hab R)
#print axioms card_exceptPair_reverse#print axioms card_ordinary_or_oneExceptional#print axioms respects_deletePair#print axioms directedPair_delete_prescribed#print axioms card_prescribedPair_residualSets

#print axioms card_prescribedPair
#print axioms card_prescribedImage
#print axioms coordinates_coverage
#print axioms card_orientedPairing
#print axioms card_selectedFirstSets

end Crown.Matchings
