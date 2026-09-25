import Crown.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Elementary properties of uniform representations

These lemmas connect positive multiplicity, least multiplicity and word length.
In particular the default zero value for a nonrepresentable graph never supplies
a representation or a spurious positive representation-number conclusion.
-/

namespace Crown

variable {V : Type*} [DecidableEq V]

theorem restrictPair_comm (w : List V) (a b : V) :
    restrictPair w a b = restrictPair w b a := by
  simp [restrictPair, or_comm]

theorem alternates_comm (w : List V) (a b : V) :
    Alternates w a b ↔ Alternates w b a := by
  rw [Alternates, Alternates, restrictPair_comm]

theorem kRepresentable_pos {G : SimpleGraph V} {k : ℕ}
    (h : KRepresentable G k) : 0 < k := by
  obtain ⟨w, hw⟩ := h
  exact hw.1

theorem representationNumber_spec {G : SimpleGraph V} (h : Representable G) :
    KRepresentable G (representationNumber G) := by
  classical
  simpa [representationNumber, h] using Nat.find_spec h

theorem representationNumber_pos {G : SimpleGraph V} (h : Representable G) :
    0 < representationNumber G :=
  kRepresentable_pos (representationNumber_spec h)

theorem representationNumber_le {G : SimpleGraph V} {k : ℕ}
    (h : KRepresentable G k) : representationNumber G ≤ k := by
  classical
  have hex : Representable G := ⟨k, h⟩
  simpa [representationNumber, hex] using Nat.find_min' hex h

theorem representationNumber_eq_zero_iff {G : SimpleGraph V} :
    representationNumber G = 0 ↔ ¬Representable G := by
  classical
  constructor
  · intro hz hr
    have := representationNumber_pos hr
    omega
  · intro hr
    simp [representationNumber, hr]

theorem sum_counts [Fintype V] (w : List V) :
    (∑ v : V, w.count v) = w.length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp [List.count_cons, Finset.sum_add_distrib, ih]

theorem uniform_length [Fintype V] {k : ℕ} {w : List V}
    (h : Uniform k w) : w.length = Fintype.card V * k := by
  calc
    w.length = ∑ v : V, w.count v := (sum_counts w).symm
    _ = ∑ _v : V, k := Finset.sum_congr rfl (fun v _ => h v)
    _ = Fintype.card V * k := by simp

theorem restrictPair_append (u w : List V) (a b : V) :
    restrictPair (u ++ w) a b = restrictPair u a b ++ restrictPair w a b := by
  simp [restrictPair]

theorem restrictPair_map {W : Type*} [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (w : List V) (a b : V) :
    restrictPair (w.map f) (f a) (f b) = (restrictPair w a b).map f := by
  unfold restrictPair
  induction w with
  | nil => rfl
  | cons x w ih =>
    by_cases hx : x = a ∨ x = b <;> simp [hf.eq_iff, hx] <;>
      simpa only [Bool.decide_or] using ih

theorem alternates_map {W : Type*} [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (w : List V) (a b : V) :
    Alternates (w.map f) (f a) (f b) ↔ Alternates w a b := by
  simp only [Alternates, restrictPair_map f hf, List.isChain_map, hf.ne_iff]

/-- A repeated letter inside a restricted word prevents alternation. -/
theorem not_alternates_of_repeat {w : List V} {a b x : V}
    (h : [x, x] <:+: restrictPair w a b) : ¬Alternates w a b := by
  intro hc
  have hx := List.IsChain.infix hc h
  simp at hx

/-- A representing word transports along an equivalence of labelled graphs. -/
theorem represents_equiv {W : Type*} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : V ≃ W)
    (he : ∀ a b, H.Adj (e a) (e b) ↔ G.Adj a b)
    {k : ℕ} {w : List V} (h : Represents G k w) :
    Represents H k (w.map e) := by
  refine ⟨h.1, ?_, ?_⟩
  · intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    simpa only [List.count_map_of_injective w e e.injective] using h.2.1 u
  · intro a b hab
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    rw [he, alternates_map e e.injective]
    exact h.2.2 a b (fun hh => hab (congrArg e hh))

#print axioms uniform_length
#print axioms represents_equiv
#print axioms representationNumber_spec

/-- Deletion of all letters outside a vertex predicate, with the retained
letters regarded as vertices of the induced graph. -/
def restrictVertices (p : V → Prop) [DecidablePred p] (w : List V) : List {v // p v} :=
  w.filterMap fun v => if h : p v then some ⟨v, h⟩ else none

omit [DecidableEq V] in
theorem map_restrictVertices (p : V → Prop) [DecidablePred p] (w : List V) :
    (restrictVertices p w).map Subtype.val = w.filter (fun v => decide (p v)) := by
  unfold restrictVertices
  induction w with
  | nil => rfl
  | cons x w ih =>
    by_cases hx : p x <;> simpa [hx] using ih

theorem restrictPair_filter (p : V → Prop) [DecidablePred p]
    (w : List V) (a b : V) (ha : p a) (hb : p b) :
    restrictPair (w.filter fun v => decide (p v)) a b = restrictPair w a b := by
  unfold restrictPair
  rw [List.filter_filter]
  congr 1
  funext x
  by_cases hx : x = a ∨ x = b
  · have hp : p x := hx.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
    simp [hx, hp]
  · simp [hx]

theorem alternates_restrictVertices (p : V → Prop) [DecidablePred p]
    (w : List V) (a b : {v // p v}) :
    Alternates (restrictVertices p w) a b ↔ Alternates w a.val b.val := by
  rw [← alternates_map Subtype.val Subtype.val_injective, map_restrictVertices]
  simp only [Alternates, restrictPair_filter p w a.val b.val a.property b.property]

theorem count_restrictVertices (p : V → Prop) [DecidablePred p]
    (w : List V) (a : {v // p v}) : (restrictVertices p w).count a = w.count a.val := by
  rw [← List.count_map_of_injective (restrictVertices p w) Subtype.val
    Subtype.val_injective, map_restrictVertices]
  exact List.count_filter (by simp [a.property])

/-- Induced-subgraph deletion preserves the same positive multiplicity. -/
theorem represents_induce {G : SimpleGraph V} {k : ℕ} {w : List V}
    (h : Represents G k w) (p : V → Prop) [DecidablePred p] :
    Represents (G.induce {v | p v}) k (restrictVertices p w) := by
  refine ⟨h.1, fun a => ?_, fun a b hab => ?_⟩
  · have ha := (count_restrictVertices p w a).trans (h.2.1 a.val)
    have hcount : @List.count _ instBEqOfDecidableEq a (restrictVertices p w) =
        @List.count _ Subtype.instBEq a (restrictVertices p w) := by
      apply List.countP_congr
      intro x _
      simp only [beq_iff_eq]
    exact hcount.trans ha
  · rw [alternates_restrictVertices]
    exact h.2.2 a.val b.val (fun he => hab (Subtype.ext he))

theorem kRepresentable_induce {G : SimpleGraph V} {k : ℕ}
    (h : KRepresentable G k) (p : V → Prop) [DecidablePred p] :
    KRepresentable (G.induce {v | p v}) k := by
  obtain ⟨w, hw⟩ := h
  exact ⟨restrictVertices p w, represents_induce hw p⟩

#print axioms represents_induce

/-- Multiplicity one forces every distinct pair to be adjacent. -/
theorem one_uniform_complete {G : SimpleGraph V} (h : KRepresentable G 1) :
    ∀ a b, a ≠ b → G.Adj a b := by
  obtain ⟨w, hw⟩ := h
  have hnd : w.Nodup := List.nodup_iff_count.mpr (fun a => by rw [hw.2.1 a])
  intro a b hab
  apply (hw.2.2 a b hab).mpr
  exact (hnd.filter _).isChain

theorem two_le_representationNumber_of_nonedge {G : SimpleGraph V}
    (hr : Representable G) {a b : V} (hab : a ≠ b) (hn : ¬G.Adj a b) :
    2 ≤ representationNumber G := by
  have hp := representationNumber_pos hr
  have hs := representationNumber_spec hr
  by_contra h
  have he : representationNumber G = 1 := by omega
  rw [he] at hs
  exact hn (one_uniform_complete hs a b hab)

#print axioms two_le_representationNumber_of_nonedge

/-- A representation of a larger graph restricts along any induced embedding. -/
theorem kRepresentable_of_inducedEmbedding {W : Type*} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
    (he : ∀ a b, G.Adj a b ↔ H.Adj (f a) (f b)) {k : ℕ}
    (h : KRepresentable H k) : KRepresentable G k := by
  classical
  obtain ⟨w, hw⟩ := kRepresentable_induce h (fun v => v ∈ Set.range f)
  let e : V ≃ Set.range f := Equiv.ofInjective f f.injective
  refine ⟨w.map e.symm, represents_equiv e.symm ?_ hw⟩
  intro a b
  have ha : f (e.symm a) = a.val := congrArg Subtype.val (e.apply_symm_apply a)
  have hb : f (e.symm b) = b.val := congrArg Subtype.val (e.apply_symm_apply b)
  simpa only [SimpleGraph.induce_adj, ha, hb] using he (e.symm a) (e.symm b)

#print axioms kRepresentable_of_inducedEmbedding

/-- The least multiplicity gives the least length among all positive uniform
representations, with an attaining word. -/
theorem minimum_uniform_length [Fintype V] {G : SimpleGraph V}
    (hr : Representable G) :
    ∃ w, Represents G (representationNumber G) w ∧
      w.length = Fintype.card V * representationNumber G ∧
      ∀ k u, Represents G k u → w.length ≤ u.length := by
  obtain ⟨w, hw⟩ := representationNumber_spec hr
  refine ⟨w, hw, uniform_length hw.2.1, ?_⟩
  intro k u hu
  rw [uniform_length hw.2.1, uniform_length hu.2.1]
  exact Nat.mul_le_mul_left _ (representationNumber_le ⟨u, hu⟩)

#print axioms minimum_uniform_length

end Crown
