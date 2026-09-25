import Crown.GosperWeight

/-! The immediate fixed-population successor, obtained by moving a low run.
These lemmas retain every width-n mask and use positional-block population
identities; there is no sampling or interval reduction. -/
set_option Elab.async false

namespace Crown.GosperSuccessor
open Crown.EnumeratorDefinitions Crown.GosperBits Crown.GosperWeight

private theorem low_weight (z t : ℕ) :
    weight (z+t+1) ((2^t-1)*2^z) = t := by
  have he : z+t+1=z+(t+1) := by omega
  rw [he,Nat.mul_comm]
  simpa [weight_zero,weight_ones] using
    weight_concat z (t+1) (2^t-1) 0 (Nat.two_pow_pos z)

private theorem next_low_lt (z t : ℕ) (ht : 0<t) :
    2^(z+t)+(2^(t-1)-1) < 2^(z+t+1) := by
  have hpow : 2^(t-1) ≤ 2^(z+t) := Nat.pow_le_pow_right (by decide) (by omega)
  have hp := Nat.two_pow_pos (t-1)
  rw [pow_succ]
  omega

private theorem next_low_weight (z t : ℕ) (ht : 0<t) :
    weight (z+t+1) (2^(z+t)+(2^(t-1)-1)) = t := by
  have hbound : 2^(t-1)-1 < 2^(z+t) := by
    have hpow : 2^(t-1) ≤ 2^(z+t) := Nat.pow_le_pow_right (by decide) (by omega)
    have hp := Nat.two_pow_pos (t-1)
    omega
  have h := weight_concat (z+t) 1 1 (2^(t-1)-1) hbound
  simpa [weight_ones,weight_one_bit 1 (by decide),Nat.min_eq_right (show t-1≤z+t by omega),Nat.sub_add_cancel ht] using h

theorem run_width (n A z t : ℕ) (ht : 0<t)
    (hx : runMask A z t < 2^n) : z+t ≤ n := by
  have hb : (runMask A z t).testBit (z+t-1) = true := by
    rw [run_bits]
    simp [show z+t-1<z+t+1 by omega,show z≤z+t-1 by omega,show z+t-1<z+t by omega]
  have hp := Nat.ge_two_pow_of_testBit hb
  by_contra hn
  have hh : 2^n ≤ 2^(z+t-1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem terminal_of_full_run (n r A z t : ℕ) (ht : 0<t)
    (hx : ValidMask n r (runMask A z t)) (hn : z+t=n) :
    runMask A z t = lastMask n r := by
  have hp := Nat.two_pow_pos n
  have hA : A=0 := by
    have h := hx.1
    dsimp [runMask] at h
    rw [hn,pow_succ] at h
    by_contra hne
    have ha : 1 ≤ A := Nat.pos_of_ne_zero hne
    have hm : 2^n*2 ≤ 2^n*2*A := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2^n*2) ha
    omega
  have hw : weight n (runMask A z t)=t := by
    rw [hA]
    simp only [runMask,Nat.mul_zero,Nat.zero_add]
    rw [←hn,Nat.mul_comm]
    simpa [weight_zero,weight_ones] using weight_concat z t (2^t-1) 0 (Nat.two_pow_pos z)
  have hr : r=t := hx.2.symm.trans hw
  subst r
  simp [runMask,hA,lastMask,←hn]

/-- Moving the low run stays inside the width and preserves the population. -/
theorem run_successor_valid (n A z t : ℕ) (ht : 0<t)
    (hx : runMask A z t < 2^n) (hn : z+t+1≤n) :
    nextMask A z t < 2^n ∧
    weight n (nextMask A z t) = weight n (runMask A z t) ∧
    runMask A z t < nextMask A z t := by
  let d := n-(z+t+1)
  have hnd : n=(z+t+1)+d := by dsimp [d]; omega
  have hpow : 2^n=2^(z+t+1)*2^d := by rw [hnd,pow_add]
  have hA : A < 2^d := by
    have hp := Nat.two_pow_pos (z+t+1)
    dsimp [runMask] at hx
    rw [hpow] at hx
    exact Nat.lt_of_mul_lt_mul_left ((Nat.le_add_right _ _).trans_lt hx)
  have hl := next_low_lt z t ht
  have hp := Nat.two_pow_pos (z+t+1)
  have hnext : nextMask A z t < 2^n := by
    unfold nextMask carryMask
    rw [hpow]
    nlinarith
  refine ⟨hnext,?_,?_⟩
  · rw [hnd]
    have h₁ := weight_concat (z+t+1) d A ((2^t-1)*2^z) (run_low_lt z t)
    have h₂ := weight_concat (z+t+1) d A (2^(z+t)+(2^(t-1)-1)) hl
    rw [low_weight] at h₁
    rw [next_low_weight z t ht] at h₂
    simpa [runMask,nextMask,carryMask,Nat.add_assoc] using h₂.trans h₁.symm
  · have hc := run_add_lowbit A z t
    have hp := Nat.two_pow_pos z
    unfold nextMask
    omega

/-- No same-population integer lies strictly between the old and new masks. -/
theorem run_successor_minimal (n A z t y : ℕ) (ht : 0<t)
    (hn : z+t+1≤n) (hxy : runMask A z t < y)
    (hpop : weight n y = weight n (runMask A z t)) :
    nextMask A z t ≤ y := by
  by_contra hny
  have hyn : y < nextMask A z t := by omega
  let m := z+t
  let H := 2^(m+1)*A
  let b := y-H
  have hm : m=z+t := rfl
  have hH : H≤y := by dsimp [H,m] at *; unfold runMask at hxy; omega
  have hy : y=H+b := by dsimp [b]; omega
  have hb : b<2^(m+1) := by
    have hl := next_low_lt z t ht
    dsimp [nextMask,carryMask] at hyn
    dsimp [H,m,b]
    omega
  let d := n-(m+1)
  have hnd : n=m+1+d := by dsimp [d,m]; omega
  have hweight : weight (m+1) b=t := by
    have h₁ := weight_concat (m+1) d A b hb
    have h₂ := weight_concat (m+1) d A ((2^t-1)*2^z) (run_low_lt z t)
    rw [show m+1=z+t+1 from rfl,low_weight] at h₂
    rw [hnd] at hpop
    have hbform : y=2^(m+1)*A+b := hy
    rw [hbform,h₁] at hpop
    change weight (m+1) b+weight d A = _ at hpop
    have h₂' : weight (m+1+d) (runMask A z t) = t+weight d A := h₂
    rw [h₂'] at hpop
    omega
  by_cases hlow : b<2^m
  · have hwb : weight m b=t := by
      have h := weight_concat m 1 0 b hlow
      simpa [weight_zero,hweight] using h.symm
    have hbmax := greatest_mask m b hlow
    rw [hwb,show m-t=z by dsimp [m]; omega] at hbmax
    dsimp [H,m] at hy
    unfold runMask at hxy
    omega
  · let c := b-2^m
    have hc : c < 2^(t-1)-1 := by
      dsimp [c,m]
      dsimp [nextMask,carryMask] at hyn
      dsimp [H,m] at hy
      have hlow' : 2^(z+t) ≤ b := by simpa only [m] using Nat.le_of_not_gt hlow
      omega
    have hcm : c < 2^m := by
      have hp : 2^(t-1)≤2^m := Nat.pow_le_pow_right (by decide) (by dsimp [m]; omega)
      omega
    have hbform : b=2^m+c := by dsimp [c]; omega
    have hcw : weight m c=t-1 := by
      have h := weight_concat m 1 1 c hcm
      simp only [Nat.mul_one] at h
      rw [←hbform,hweight,weight_one_bit 1 (by decide)] at h
      omega
    have hmin := least_mask m c hcm
    rw [hcw] at hmin
    omega
#print axioms run_width
#print axioms terminal_of_full_run
#print axioms run_successor_valid
#print axioms run_successor_minimal
end Crown.GosperSuccessor
