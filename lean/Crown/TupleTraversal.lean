import Crown.EnumeratorDefinitions
import Crown.FiniteTraversal
import Mathlib.Order.PiLex
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.Finite

/-! The exact rightmost-increment/reset recurrence for increasing tuples.
The lexicographic order is reused from Mathlib (Chris Hughes), and sorted
finite-set enumeration and subset cardinalities from Mathlib (Mario Carneiro),
all Apache-2.0 at the pinned dependency revision. All parameters remain
arbitrary, including the empty tuple. -/
namespace Crown.TupleTraversal
open Crown.EnumeratorDefinitions

private theorem gap {r : ℕ} {a : TupleState r} (ha : StrictMono a)
    (i : Fin r) (d : ℕ) (hd : i.val+d < r) : a i+d ≤ a ⟨i.val+d,hd⟩ := by
  induction d with
  | zero => simpa using le_refl (a i)
  | succ d ih =>
    have hp := ih (by omega)
    have hs := ha (show (⟨i.val+d,by omega⟩ : Fin r) < ⟨i.val+(d+1),hd⟩ from by simp)
    omega

private theorem lower {n r : ℕ} {a : TupleState r} (ha : ValidTuple n r a)
    (i : Fin r) : i.val ≤ a i := by
  have hi := i.isLt
  have h := gap ha.1 ⟨0,by omega⟩ i.val (by simpa using i.isLt)
  simpa using (Nat.le_trans (Nat.le_add_left _ _) h)

private theorem upper {n r : ℕ} (hrn : r ≤ n) {a : TupleState r}
    (ha : ValidTuple n r a) (i : Fin r) : a i ≤ n-r+i.val := by
  have hd : i.val+(r-1-i.val) < r := by omega
  have h := gap ha.1 i (r-1-i.val) hd
  have hh := ha.2 ⟨i.val+(r-1-i.val),hd⟩
  omega

private theorem lex_iff {r : ℕ} (a b : TupleState r) :
    LexLess a b ↔ toLex a < toLex b := by
  change (∃ j, a j < b j ∧ ∀ i, i < j → a i = b i) ↔
    ∃ j, (∀ i, i < j → a i = b i) ∧ a j < b j
  exact exists_congr (fun _ => and_comm)

private theorem pointwise_lex {r : ℕ} (a b : TupleState r) (h : ∀ i, a i ≤ b i) :
    a = b ∨ LexLess a b := by
  have hh := Pi.toLex_monotone h
  rcases hh.eq_or_lt with he | hl
  · exact Or.inl (congrArg ofLex he)
  · exact Or.inr ((lex_iff a b).mpr hl)

private theorem move_none {n r : ℕ} (hrn : r ≤ n) {a : TupleState r}
    (ha : ValidTuple n r a) : ¬ (movable n r a).Nonempty ↔ a = lastTuple n r := by
  constructor
  · intro h
    funext i
    have hu := upper hrn ha i
    have hn : ¬ a i < n-r+i.val := fun hi => h ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    exact Nat.le_antisymm hu (Nat.le_of_not_gt hn)
  · intro he h
    obtain ⟨i,hi⟩ := h
    have hh := (Finset.mem_filter.mp hi).2
    simp [he,lastTuple] at hh

private theorem reset_valid {n r : ℕ} {a : TupleState r} (ha : ValidTuple n r a)
    (j : Fin r) (hj : a j < n-r+j.val) (hrn : r ≤ n) :
    ValidTuple n r (fun i => if i < j then a i else a j+1+(i.val-j.val)) := by
  constructor
  · intro i l hil
    dsimp
    split_ifs with hi hl hl
    · exact ha.1 hil
    · have h := ha.1 hi
      omega
    · have hiv : j.val ≤ i.val := Fin.le_iff_val_le_val.mp (le_of_not_gt hi)
      have hlv : l.val < j.val := hl
      have hilv : i.val < l.val := hil
      omega
    · have hiv : j.val ≤ i.val := Fin.le_iff_val_le_val.mp (le_of_not_gt hi)
      have hlv : j.val ≤ l.val := Fin.le_iff_val_le_val.mp (le_of_not_gt hl)
      have hilv : i.val < l.val := hil
      omega
  · intro i
    dsimp
    split_ifs with hi
    · exact ha.2 i
    · have hiv : j.val ≤ i.val := Fin.le_iff_val_le_val.mp (le_of_not_gt hi)
      have := i.isLt
      omega

/-- The source update is the immediate lexicographic successor, and stops
exactly at the final increasing tuple. -/
theorem update_successor (n r : ℕ) (hrn : r ≤ n) (a : TupleState r)
    (ha : ValidTuple n r a) :
    (tupleNext n r a = none ↔ a = lastTuple n r) ∧
    ∀ b, tupleNext n r a = some b → ValidTuple n r b ∧ LexLess a b ∧
      ∀ c, ValidTuple n r c → LexLess a c → b = c ∨ LexLess b c := by
  classical
  by_cases hh : (movable n r a).Nonempty
  · let j := (movable n r a).max' hh
    have hjm : j ∈ movable n r a := Finset.max'_mem _ hh
    have hj : a j < n-r+j.val := (Finset.mem_filter.mp hjm).2
    have hn : a ≠ lastTuple n r := by
      intro he
      simp [he,lastTuple] at hj
    refine ⟨by simp [tupleNext,hh,hn],?_⟩
    intro b hb
    have he : b = (fun i => if i < j then a i else a j+1+(i.val-j.val)) := by
      simpa [tupleNext,hh,j] using hb.symm
    subst b
    refine ⟨reset_valid ha j hj hrn,⟨j,by simp,fun i hi => by simp [hi]⟩,?_⟩
    intro c hc hac
    obtain ⟨p,hp,hprefix⟩ := hac
    have hpj : p ≤ j := by
      by_contra h
      have hjp : j < p := lt_of_not_ge h
      have hpm : p ∈ movable n r a := Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_lt_of_le hp (upper hrn hc p)⟩
      exact (not_lt_of_ge (Finset.le_max' _ p hpm)) hjp
    rcases hpj.eq_or_lt with heq | hlt
    · subst p
      by_cases hjc : a j+1 < c j
      · right
        refine ⟨j,by simpa using hjc,?_⟩
        intro i hi
        simpa [hi] using hprefix i hi
      · have hjce : c j = a j+1 := by omega
        apply pointwise_lex
        intro i
        split_ifs with hi
        · exact le_of_eq (hprefix i hi)
        · have hiv : j.val ≤ i.val := Fin.le_iff_val_le_val.mp (le_of_not_gt hi)
          have hd : j.val+(i.val-j.val) < r := by omega
          have hg := gap hc.1 j (i.val-j.val) hd
          have he : (⟨j.val+(i.val-j.val),hd⟩ : Fin r) = i := by
            apply Fin.ext
            change j.val+(i.val-j.val) = i.val
            omega
          rw [he,hjce] at hg
          exact hg
    · right
      refine ⟨p,by simpa [hlt] using hp,?_⟩
      intro i hi
      simpa [lt_trans hi hlt] using hprefix i hi
  · refine ⟨by simpa [tupleNext,hh] using move_none hrn ha,?_⟩
    intro b hb
    simp [tupleNext,hh] at hb

private abbrev State (n r : ℕ) :=
  {a : Lex (Fin r → Fin n) // StrictMono (ofLex a)}

private def asTuple {n r : ℕ} (a : State n r) : TupleState r := fun i => (ofLex a.val i).val

private theorem state_valid {n r : ℕ} (a : State n r) : ValidTuple n r (asTuple a) :=
  ⟨fun _ _ h => a.property h,fun i => (ofLex a.val i).isLt⟩

private def asState {n r : ℕ} (a : TupleState r) (ha : ValidTuple n r a) : State n r :=
  ⟨toLex (fun i => ⟨a i,ha.2 i⟩),fun _ _ h => ha.1 h⟩

private theorem tuple_state {n r : ℕ} (a : TupleState r) (ha : ValidTuple n r a) :
    asTuple (asState a ha) = a := rfl

private theorem state_tuple {n r : ℕ} (a : State n r) :
    asState (asTuple a) (state_valid a) = a := rfl

private theorem state_lt {n r : ℕ} (a b : State n r) : a < b ↔ LexLess (asTuple a) (asTuple b) := by
  change (∃ j, (∀ i, i < j → ofLex a.val i = ofLex b.val i) ∧ ofLex a.val j < ofLex b.val j) ↔ _
  simp only [LexLess,asTuple,Fin.ext_iff,Fin.lt_def]
  exact exists_congr (fun _ => and_comm)

private noncomputable def subsetEquiv (n r : ℕ) : State n r ≃
    {s : Finset (Fin n) // s.card = r} where
  toFun a := ⟨Finset.univ.image (ofLex a.val),by
    rw [Finset.card_image_of_injective _ a.property.injective]
    simp⟩
  invFun s := ⟨toLex (s.val.orderEmbOfFin s.property), (s.val.orderEmbOfFin s.property).strictMono⟩
  left_inv a := by
    apply Subtype.ext
    apply congrArg toLex
    exact (Finset.orderEmbOfFin_unique _ (fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) a.property).symm
  right_inv s := by
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ s.val s.property

private theorem state_card (n r : ℕ) : Nat.card (State n r) = Nat.choose n r := by
  classical
  rw [Nat.card_congr (subsetEquiv n r),Nat.card_eq_fintype_card,Fintype.card_finset_len,Fintype.card_fin]

private theorem first_valid (n r : ℕ) (hrn : r ≤ n) : ValidTuple n r (firstTuple r) :=
  ⟨fun _ _ h => h,fun i => lt_of_lt_of_le i.isLt hrn⟩

private theorem last_valid (n r : ℕ) (hrn : r ≤ n) : ValidTuple n r (lastTuple n r) := by
  constructor
  · intro i j hij
    change n-r+i.val < n-r+j.val
    exact Nat.add_lt_add_left hij _
  · intro i
    change n-r+i.val < n
    have := i.isLt
    omega

private theorem step_valid {n r : ℕ} (hrn : r ≤ n) (a : TupleState r)
    (ha : ValidTuple n r a) : ValidTuple n r (tupleStep n r a) := by
  unfold tupleStep
  cases he : tupleNext n r a with
  | none => simpa using ha
  | some b => exact (update_successor n r hrn a ha).2 b he |>.1

/-- Every increasing tuple occurs once in the finite traversal prefix. -/
theorem traversal_complete (n r : ℕ) (hrn : r ≤ n) :
    (∀ a, ValidTuple n r a ↔ ∃ j < Nat.choose n r,
      (tupleStep n r)^[j] (firstTuple r) = a) ∧
    (tupleStep n r)^[Nat.choose n r-1] (firstTuple r) = lastTuple n r ∧
    (∀ i j, i < j → j < Nat.choose n r →
      LexLess ((tupleStep n r)^[i] (firstTuple r)) ((tupleStep n r)^[j] (firstTuple r))) := by
  classical
  letI : Fintype (State n r) := Fintype.ofFinite _
  let next : State n r → State n r := fun a => asState (tupleStep n r (asTuple a)) (step_valid hrn _ (state_valid a))
  let first : State n r := asState (firstTuple r) (first_valid n r hrn)
  let last : State n r := asState (lastTuple n r) (last_valid n r hrn)
  have hc : Fintype.card (State n r) = Nat.choose n r := by
    rw [← Nat.card_eq_fintype_card]
    exact state_card n r
  have hf : ∀ a : State n r, first ≤ a := by
    intro a
    rcases pointwise_lex (firstTuple r) (asTuple a) (lower (state_valid a)) with he | hl
    · have heq : first = a := by
        apply Subtype.ext
        apply funext
        intro i
        apply Fin.ext
        exact congrFun he i
      exact le_of_eq heq
    · exact le_of_lt ((state_lt first a).mpr hl)
  have hl : ∀ a : State n r, a ≤ last := by
    intro a
    rcases pointwise_lex (asTuple a) (lastTuple n r) (upper hrn (state_valid a)) with he | hh
    · have heq : a = last := by
        apply Subtype.ext
        apply funext
        intro i
        apply Fin.ext
        exact congrFun he i
      exact le_of_eq heq
    · exact le_of_lt ((state_lt a last).mpr hh)
  have hs (a b : State n r) (hab : a < b) : a < next a ∧ next a ≤ b := by
    have hlex := (state_lt a b).mp hab
    have hn : tupleNext n r (asTuple a) ≠ none := by
      intro he
      have hlast := (update_successor n r hrn _ (state_valid a)).1.mp he
      obtain ⟨j,hj,_⟩ := hlex
      have hu := upper hrn (state_valid b) j
      change asTuple a j < asTuple b j at hj
      rw [hlast] at hj
      exact (not_lt_of_ge hu) hj
    obtain ⟨c,he⟩ := Option.ne_none_iff_exists'.mp hn
    obtain ⟨hcv,hac,hmin⟩ := (update_successor n r hrn _ (state_valid a)).2 c he
    have heq : asTuple (next a) = c := by
      change (tupleNext n r (asTuple a)).getD (asTuple a) = c
      rw [he]
      rfl
    refine ⟨(state_lt a (next a)).mpr (by simpa [heq] using hac),?_⟩
    rcases hmin (asTuple b) (state_valid b) hlex with hec | hbc
    · apply le_of_eq
      apply Subtype.ext
      apply funext
      intro i
      apply Fin.ext
      exact congrFun (heq.trans hec) i
    · exact le_of_lt ((state_lt (next a) b).mpr (by simpa [heq] using hbc))
  have hiter (j : ℕ) : asTuple (next^[j] first) = (tupleStep n r)^[j] (firstTuple r) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      change tupleStep n r (asTuple (next^[j] first)) = _
      rw [ih]
  obtain ⟨hcover,hlast,hstrict⟩ := Crown.FiniteTraversal.complete_bounded next hs first last hf hl
  refine ⟨?_,?_,?_⟩
  · intro a
    constructor
    · intro ha
      obtain ⟨j,hj,he⟩ := hcover (asState a ha)
      refine ⟨j,by simpa [hc] using hj,?_⟩
      simpa only [hiter,tuple_state] using congrArg asTuple he
    · rintro ⟨j,hj,rfl⟩
      rw [← hiter]
      exact state_valid _
  · simpa only [hiter,hc,last,tuple_state] using congrArg asTuple hlast
  · intro i j hij hj
    have hh := (state_lt (next^[i] first) (next^[j] first)).mp
      (hstrict (by simpa [hc] using lt_trans hij hj) (by simpa [hc] using hj) hij)
    simpa [hiter] using hh

#print axioms update_successor
#print axioms traversal_complete
end Crown.TupleTraversal
