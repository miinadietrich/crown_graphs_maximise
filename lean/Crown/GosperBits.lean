import Crown.EnumeratorDefinitions
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

set_option Elab.async false

namespace Crown.GosperBits
open Crown.EnumeratorDefinitions

/-- A block of t low one-bits, preceded by z zero-bits and followed by a zero. -/
def runMask (A z t : ℕ) : ℕ := 2^(z+t+1)*A + (2^t-1)*2^z

def carryMask (A z t : ℕ) : ℕ := 2^(z+t+1)*A + 2^(z+t)

def nextMask (A z t : ℕ) : ℕ := carryMask A z t + (2^(t-1)-1)

theorem run_low_lt (z t : ℕ) : (2^t-1)*2^z < 2^(z+t+1) := by
  have hp : 0 < 2^t := Nat.two_pow_pos t
  have hz : 0 < 2^z := Nat.two_pow_pos z
  have hm : (2^t-1)*2^z < 2^t*2^z := Nat.mul_lt_mul_of_pos_right (by omega) hz
  rw [pow_add,pow_add]
  nlinarith

theorem run_bits (A z t i : ℕ) :
    (runMask A z t).testBit i =
      if i < z+t+1 then decide (z ≤ i ∧ i < z+t) else A.testBit (i-(z+t+1)) := by
  rw [runMask,Nat.testBit_two_pow_mul_add A (run_low_lt z t)]
  split_ifs with hi
  · rw [Nat.testBit_mul_two_pow,Nat.testBit_two_pow_sub_one]
    by_cases hz : z ≤ i <;> by_cases ht : i < z+t <;> simp_all <;> omega
  · rfl

theorem carry_bits (A z t i : ℕ) :
    (carryMask A z t).testBit i =
      if i < z+t+1 then decide (i = z+t) else A.testBit (i-(z+t+1)) := by
  have hp : 2^(z+t) < 2^(z+t+1) := by
    rw [pow_succ]
    have := Nat.two_pow_pos (z+t)
    omega
  rw [carryMask,Nat.testBit_two_pow_mul_add A hp]
  split_ifs
  · rw [Nat.testBit_two_pow]
    simp [eq_comm]
  · rfl

theorem carry_xor_run (A z t : ℕ) :
    carryMask A z t ^^^ runMask A z t = (2^(t+1)-1)*2^z := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor,carry_bits,run_bits,Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : i < z+t+1
  · by_cases hlo : i < z
    · have hz : ¬z ≤ i := by omega
      have he : i ≠ z+t := by omega
      simp [hi,hz,he]
    · have hz : z ≤ i := by omega
      have hm : i-z < t+1 := by omega
      by_cases he : i = z+t
      · have hn : ¬i < z+t := by omega
        simp [hi,hz,hm,he,hn]
      · have hn : i < z+t := by omega
        simp [hi,hz,hm,he,hn]
  · have hz : z ≤ i := by omega
    have hm : ¬i-z < t+1 := by omega
    cases h : A.testBit (i-(z+t+1)) <;> simp [hi,hz,hm,h]

/-- At the least selected bit, subtraction by one changes the bit to zero;
all more significant bits are unchanged. This isolates x & (-x) exactly. -/
theorem lowbit_odd_part (w z q : ℕ)
    (hx : 2^(z+1)*q+2^z < 2^w) :
    (2^(z+1)*q+2^z) &&& (2^w-(2^(z+1)*q+2^z)) = 2^z := by
  let x := 2^(z+1)*q+2^z
  have hz : 0 < 2^z := Nat.two_pow_pos z
  have hxp : 0 < x := by dsimp [x]; omega
  have hxpred : x-1+1=x := Nat.sub_add_cancel hxp
  have hp : 2^z < 2^(z+1) := by rw [pow_succ]; omega
  have hp' : 2^z-1 < 2^(z+1) := by omega
  have hxsub : x-1 = 2^(z+1)*q+(2^z-1) := by dsimp [x]; omega
  have hzw : z < w := by
    by_contra hn
    have hh : 2^w ≤ 2^z := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  change x &&& (2^w-x) = 2^z
  apply Nat.eq_of_testBit_eq
  intro i
  have hc : (2^w-x).testBit i = (decide (i<w) && !(x-1).testBit i) := by
    conv_lhs => arg 1; rw [←hxpred]
    exact Nat.testBit_two_pow_sub_succ (by omega) i
  rw [Nat.testBit_and,hc,hxsub]
  dsimp [x]
  rw [Nat.testBit_two_pow_mul_add q hp, Nat.testBit_two_pow_mul_add q hp',
    Nat.testBit_two_pow_sub_one,Nat.testBit_two_pow]
  by_cases hi : i < z+1
  · by_cases he : i = z
    · subst i
      simp [hzw]
    · have hi' : i < z := by omega
      have hw : i < w := by omega
      simp [hi,he,Ne.symm he,hi',hw]
  · have he : i ≠ z := by omega
    by_cases hw : i < w
    · cases hq : q.testBit (i-(z+1)) <;> simp [hi,he,Ne.symm he,hw,hq]
    · simp [hi,he,Ne.symm he,hw]

/-- Every positive integer has a trailing-zero/one-run decomposition. -/
theorem exists_run (x : ℕ) (hx : 0 < x) :
    ∃ A z t, 0 < t ∧ x = runMask A z t := by
  obtain ⟨z,m,hm,hx'⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : x ≠ 0)
  obtain ⟨t,u,hu,htu⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : m+1 ≠ 0)
  obtain ⟨q,hq⟩ := hm
  obtain ⟨A,hA⟩ := hu
  have ht : 0 < t := by
    by_contra ht
    have : t=0 := by omega
    simp [this] at htu
    omega
  have hpow : 0 < 2^t := Nat.two_pow_pos t
  refine ⟨A,z,t,ht,?_⟩
  dsimp [runMask]
  rw [hx']
  have hm' : m = 2^(t+1)*A+(2^t-1) := by
    rw [pow_succ]
    rw [hA] at htu
    have hpred : 2^t-1+1=2^t := Nat.sub_add_cancel hpow
    nlinarith
  rw [hm']
  simp only [pow_add,pow_one]
  ring

theorem run_as_odd_part (A z t : ℕ) (ht : 0 < t) :
    runMask A z t = 2^(z+1)*(2^t*A+(2^(t-1)-1))+2^z := by
  have hp : 0 < 2^(t-1) := Nat.two_pow_pos _
  have he : 2^t=2*2^(t-1) := by
    conv_lhs => arg 2; rw [←Nat.sub_add_cancel ht]
    rw [pow_add]
    ring
  have he' : 2^t-1=2*(2^(t-1)-1)+1 := by omega
  unfold runMask
  rw [he']
  simp only [pow_add,pow_one]
  ring

theorem run_lowbit (A z t : ℕ) (ht : 0 < t) (hx : runMask A z t < 2^64) :
    lowBit64 (runMask A z t) = 2^z := by
  unfold lowBit64
  rw [run_as_odd_part A z t ht] at hx ⊢
  exact lowbit_odd_part 64 z _ hx

theorem run_add_lowbit (A z t : ℕ) :
    runMask A z t + 2^z = carryMask A z t := by
  have hp := Nat.two_pow_pos t
  have he : 2^t-1+1=2^t := Nat.sub_add_cancel hp
  unfold runMask carryMask
  calc
    2^(z+t+1)*A+(2^t-1)*2^z+2^z =
        2^(z+t+1)*A+((2^t-1)+1)*2^z := by ring
    _ = 2^(z+t+1)*A+2^(z+t) := by rw [he,pow_add]; ring

theorem xor_shift_quotient (z t : ℕ) (ht : 0 < t) :
    (((2^(t+1)-1)*2^z) >>> 2) / 2^z = 2^(t-1)-1 := by
  rw [Nat.shiftRight_eq_div_pow,Nat.div_div_eq_div_mul]
  norm_num only [show (2:ℕ)^2=4 from rfl]
  rw [Nat.mul_div_mul_right _ _ (Nat.two_pow_pos z)]
  have hp := Nat.two_pow_pos (t-1)
  have he : 2^(t+1)=4*2^(t-1) := by
    have ht' : t+1=(t-1)+2 := by omega
    rw [ht',pow_add]
    ring
  omega

/-- Exact source arithmetic, reduced to moving the low run and packing its tail. -/
theorem gosper_run (A z t : ℕ) (ht : 0 < t) (hx : runMask A z t < 2^64) :
    gosperRaw (runMask A z t) = nextMask A z t := by
  simp only [gosperRaw,run_lowbit A z t ht hx,run_add_lowbit,carry_xor_run,
    xor_shift_quotient z t ht]
  have hbound : 2^(t-1)-1 < 2^(z+t) := by
    have hp := Nat.two_pow_pos (t-1)
    have he : 2^(t-1) ≤ 2^(z+t) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hc : carryMask A z t = 2^(z+t)*(2*A+1) := by
    unfold carryMask
    rw [pow_succ]
    ring
  rw [hc,Nat.or_comm,←Nat.two_pow_add_eq_or_of_lt hbound]
  simp only [nextMask,hc]
#print axioms run_bits
#print axioms carry_xor_run
#print axioms lowbit_odd_part
#print axioms exists_run
end Crown.GosperBits
