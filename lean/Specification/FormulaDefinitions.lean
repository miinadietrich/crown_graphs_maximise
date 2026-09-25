import Specification.CertificateDefinitions

import Mathlib.Data.Fintype.EquivFin

import Mathlib.Order.PiLex

import Init.Data.Nat.Bitwise.Lemmas

open scoped Classical

namespace Crown.CertificateSemantics

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

theorem maskBits_surjective : Function.Surjective maskBits := by
  have hcard : Fintype.card (Fin 256) = Fintype.card (Fin 8 → Bool) := by
    simp only [Fintype.card_fin, Fintype.card_pi_const, Fintype.card_bool]
    rfl
  exact ((Fintype.bijective_iff_injective_and_card maskBits).mpr
    ⟨maskBits_injective, hcard⟩).2

noncomputable def permuteMask (e : Fin 8 ≃ Fin 8) (m : Fin 256) : Fin 256 :=
  Classical.choose (maskBits_surjective (fun i => maskBits m (e.symm i)))

noncomputable def relabelSelector (s : Fin 256 → Bool) (e : Fin 8 ≃ Fin 8) : Fin 256 → Bool :=
  fun m => s (permuteMask e m)

end Crown.CertificateSemantics

namespace Crown.CertificateSixSemantics

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

theorem maskBits_surjective : Function.Surjective maskBits := by
  have hcard : Fintype.card (Fin 64) = Fintype.card (Fin 6 → Bool) := by
    simp only [Fintype.card_fin, Fintype.card_pi_const, Fintype.card_bool]
    rfl
  exact ((Fintype.bijective_iff_injective_and_card maskBits).mpr
    ⟨maskBits_injective, hcard⟩).2

noncomputable def permuteMask (e : Fin 6 ≃ Fin 6) (m : Fin 64) : Fin 64 :=
  Classical.choose (maskBits_surjective (fun i => maskBits m (e.symm i)))

noncomputable def relabelSelector (s : Fin 64 → Bool) (e : Fin 6 ≃ Fin 6) : Fin 64 → Bool :=
  fun m => s (permuteMask e m)

def selectorNat (s : Fin 64 → Bool) (n : Nat) : Bool :=
  if h : n < 64 then s ⟨n, h⟩ else false

end Crown.CertificateSixSemantics

namespace Crown.CertificateValuation

open Crown.CertificateSemantics

inductive Variable where
  | select (mask : Fin 256)
  | falsum
  | count (prefixLength threshold : Nat)
  | lex (permutation : Fin 8 ≃ Fin 8) (index : Fin 256)
  | core (masks : List (Fin 256))

noncomputable def lexBefore (s : Fin 256 → Bool) (d : Fin 8 ≃ Fin 8)
    (i : Fin 256) : Bool :=
  decide (∀ j > i, s j = s (permuteMask d j))

noncomputable def lexAfter (s : Fin 256 → Bool) (d : Fin 8 ≃ Fin 8)
    (i : Fin 256) : Bool :=
  decide (∀ j ≥ i, s j = s (permuteMask d j))

noncomputable def value (s : Fin 256 → Bool) : Variable → Bool
  | .select m => s m
  | .falsum => false
  | .count i j => counterValue (selectorNat s) i j
  | .lex d i => lexAfter s d i
  | .core masks => masks.all s

end Crown.CertificateValuation

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

end Crown.CertificateSixValuation
