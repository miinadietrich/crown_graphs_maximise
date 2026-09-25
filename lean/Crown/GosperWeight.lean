import Crown.GosperBits

/-! Fixed-width population counts and positional block decompositions.
All statements concern the complete width-n bit domain. -/
set_option Elab.async false

namespace Crown.GosperWeight
open Crown.EnumeratorDefinitions
open scoped BigOperators

theorem weight_le_width (n x : ℕ) : weight n x ≤ n := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem weight_zero (n : ℕ) : weight n 0 = 0 := by simp [weight]

theorem weight_ones (n t : ℕ) : weight n (2^t-1) = min n t := by
  unfold weight
  have he : (Finset.range n).filter (fun i => (2^t-1).testBit i = true) =
      Finset.range (min n t) := by
    ext i
    simp [Nat.testBit_two_pow_sub_one,lt_min_iff]
  rw [he,Finset.card_range]

theorem weight_eq_sum (n x : ℕ) :
    weight n x = ∑ i ∈ Finset.range n, (x.testBit i).toNat := by
  rw [weight,Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  cases x.testBit i <;> simp

/-- Concatenating two positional blocks adds their populations. -/
theorem weight_concat (m d A b : ℕ) (hb : b < 2^m) :
    weight (m+d) (2^m*A+b) = weight m b + weight d A := by
  simp only [weight_eq_sum]
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.testBit_two_pow_mul_add A hb]
    simp [Finset.mem_range.mp hi]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.testBit_two_pow_mul_add A hb]
    simp [Nat.not_lt.mpr (Nat.le_add_right m i)]

theorem weight_one_bit (x : ℕ) (hx : x < 2) : weight 1 x = x := by
  interval_cases x <;> decide

theorem weight_top_decomposition (n x : ℕ) (hx : x < 2^(n+1)) :
    weight (n+1) x = weight n (x % 2^n) + x / 2^n := by
  have hp : 0 < 2^n := Nat.two_pow_pos n
  have hq : x / 2^n < 2 := by
    apply (Nat.div_lt_iff_lt_mul hp).2
    simpa [pow_succ,Nat.mul_comm] using hx
  have he : 2^n*(x/2^n)+x%2^n=x := Nat.div_add_mod x (2^n)
  calc
    weight (n+1) x = weight (n+1) (2^n*(x/2^n)+x%2^n) := congrArg (weight (n+1)) he.symm
    _ = weight n (x%2^n)+weight 1 (x/2^n) := weight_concat n 1 _ _ (Nat.mod_lt _ hp)
    _ = weight n (x%2^n)+x/2^n := by rw [weight_one_bit _ hq]

/-- The least integer with population r consists of r low one-bits. -/
theorem least_mask (n x : ℕ) (hx : x < 2^n) : 2^(weight n x)-1 ≤ x := by
  induction n generalizing x with
  | zero =>
    have hx0 : x=0 := by simpa using hx
    subst x
    simp [weight]
  | succ n ih =>
    let b := x % 2^n
    let q := x / 2^n
    have hp : 0 < 2^n := Nat.two_pow_pos n
    have hb : b < 2^n := Nat.mod_lt _ hp
    have hq : q < 2 := by
      apply (Nat.div_lt_iff_lt_mul hp).2
      simpa [pow_succ,Nat.mul_comm] using hx
    have he : x = 2^n*q+b := (Nat.div_add_mod x (2^n)).symm
    have hw : weight (n+1) x = weight n b+q := weight_top_decomposition n x hx
    have hmin := ih b hb
    have hcard := weight_le_width n b
    have hpow : 2^(weight n b) ≤ 2^n := Nat.pow_le_pow_right (by decide) hcard
    have hpos : 0 < 2^(weight n b) := Nat.two_pow_pos _
    rw [hw]
    interval_cases q
    · simpa [he] using hmin
    · rw [pow_succ]
      simp only [Nat.mul_one] at he
      omega

/-- Complementation exchanges selected and unselected positions in the full width. -/
theorem weight_complement (n x : ℕ) (hx : x < 2^n) :
    weight n (2^n-(x+1)) + weight n x = n := by
  have he : (Finset.range n).filter (fun i => (2^n-(x+1)).testBit i = true) =
      (Finset.range n).filter (fun i => ¬x.testBit i = true) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range,Nat.testBit_two_pow_sub_succ hx]
    by_cases hi : i<n <;> cases x.testBit i <;> simp_all
  unfold weight
  rw [he,add_comm,Finset.card_filter_add_card_filter_not,Finset.card_range]

/-- The greatest width-n integer with population r consists of r high one-bits. -/
theorem greatest_mask (n x : ℕ) (hx : x < 2^n) :
    x ≤ (2^(weight n x)-1)*2^(n-weight n x) := by
  let y := 2^n-(x+1)
  have hy : y < 2^n := by dsimp [y]; omega
  have hc := weight_complement n x hx
  have hl := least_mask n y hy
  have hw := weight_le_width n x
  have he : weight n y = n-weight n x := by dsimp [y]; omega
  rw [he] at hl
  have hp : 2^n = 2^(weight n x)*2^(n-weight n x) := by
    rw [←pow_add,Nat.add_sub_of_le hw]
  have hpos := Nat.two_pow_pos (weight n x)
  have hpos' := Nat.two_pow_pos (n-weight n x)
  dsimp [y] at hl
  have hprod : (2^(weight n x)-1)*2^(n-weight n x)+2^(n-weight n x)=2^n := by
    calc
      (2^(weight n x)-1)*2^(n-weight n x)+2^(n-weight n x) =
          (2^(weight n x)-1+1)*2^(n-weight n x) := by ring
      _ = 2^(weight n x)*2^(n-weight n x) := by rw [Nat.sub_add_cancel hpos]
      _ = 2^n := hp.symm
  omega
#print axioms weight_concat
#print axioms weight_top_decomposition
#print axioms least_mask
end Crown.GosperWeight
