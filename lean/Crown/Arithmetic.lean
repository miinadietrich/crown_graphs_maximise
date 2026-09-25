import Crown.ArithmeticDefinitions
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Crown.Arithmetic

theorem Q_mul_factorial (k : ℕ) : Q k * k.factorial = (2 * k).factorial := by
  exact Nat.div_mul_cancel (Nat.factorial_dvd_factorial (by omega : k ≤ 2 * k))

theorem Q_pos (k : ℕ) : 0 < Q k := by
  apply Nat.pos_of_ne_zero
  intro hzero
  exact Nat.factorial_ne_zero (2 * k) (by simpa [hzero] using (Q_mul_factorial k).symm)

theorem M_denominator_pos (k x y z : ℤ) :
    0 < (k - x).toNat.factorial * (k - y).toNat.factorial * (k - z).toNat.factorial :=
  Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) (Nat.factorial_pos _)

theorem M_eq_zero_of_negative {k x y z : ℤ}
    (h : k < 0 ∨ x < 0 ∨ y < 0 ∨ z < 0) : M k x y z = 0 := by
  unfold M
  split_ifs with hc
  · omega
  · rfl

theorem M_eq_zero_of_large_z {k x y z : ℤ} (h : k < z) : M k x y z = 0 := by
  unfold M
  split_ifs with hc
  · omega
  · rfl

theorem P_eq_zero_of_two_le_t {k x y z t : ℕ} (h : 2 ≤ t) : P k x y z t = 0 := by
  simp [P, show t ≠ 0 by omega, show t ≠ 1 by omega]

theorem P_eq_zero_of_large_z {k x y z t : ℕ} (h : k < z) : P k x y z t = 0 := by
  have h₀ : (k : ℤ) < z := by omega
  have h₁ : (k : ℤ) - 1 < z := by omega
  simp [P, M_eq_zero_of_large_z h₀, M_eq_zero_of_large_z h₁]

theorem finiteSliceMaximum_iff (k z t a : ℕ) :
    FiniteSliceMaximum k z t a ↔ IsSliceMaximum k z t a := by
  constructor
  · rintro ⟨hbound, x, hx, heq⟩
    constructor
    · intro u v huv
      have hu : u < 2 * k + 1 := by omega
      have hv : v = 2 * k - (u + z + t) := by omega
      subst v
      exact hbound ⟨u, hu⟩ (by change u + z + t ≤ 2 * k; omega)
    · exact ⟨x.val, 2 * k - (x.val + z + t), by omega, heq⟩
  · rintro ⟨hbound, x, y, hxy, heq⟩
    constructor
    · intro u hu
      exact hbound u.val (2 * k - (u.val + z + t)) (by omega)
    · have hx : x < 2 * k + 1 := by omega
      have hy : y = 2 * k - (x + z + t) := by omega
      subst y
      exact ⟨⟨x, hx⟩, by change x + z + t ≤ 2 * k; omega, heq⟩

private theorem finite_table60 : ∀ z : Fin 7, FiniteSliceMaximum 6 z.val 0 (table60 z) := by
  decide

private theorem finite_table61 : ∀ z : Fin 7, FiniteSliceMaximum 6 z.val 1 (table61 z) := by
  decide

private theorem finite_table70 : ∀ z : Fin 8, FiniteSliceMaximum 7 z.val 0 (table70 z) := by
  decide

private theorem finite_table71 : ∀ z : Fin 8, FiniteSliceMaximum 7 z.val 1 (table71 z) := by
  decide

/-- P09, all seven entries in the first row, with full-domain upper bounds
and witnesses of equality. -/
theorem table60_exact (z : Fin 7) : IsSliceMaximum 6 z.val 0 (table60 z) :=
  (finiteSliceMaximum_iff ..).mp (finite_table60 z)

theorem table61_exact (z : Fin 7) : IsSliceMaximum 6 z.val 1 (table61 z) :=
  (finiteSliceMaximum_iff ..).mp (finite_table61 z)

theorem table70_exact (z : Fin 8) : IsSliceMaximum 7 z.val 0 (table70 z) :=
  (finiteSliceMaximum_iff ..).mp (finite_table70 z)

theorem table71_exact (z : Fin 8) : IsSliceMaximum 7 z.val 1 (table71 z) :=
  (finiteSliceMaximum_iff ..).mp (finite_table71 z)

theorem P6_le (x y z t : ℕ) (h : x + y + z + t = 12) : P 6 x y z t ≤ 8640 := by
  by_cases hz : z ≤ 6
  · have hz' : z < 7 := by omega
    rcases Nat.lt_or_ge t 2 with ht | ht
    · have ht' : t = 0 ∨ t = 1 := by omega
      rcases ht' with rfl | rfl
      · exact (table60_exact ⟨z, hz'⟩).1 x y h |>.trans
          ((by decide : ∀ j : Fin 7, table60 j ≤ 8640) ⟨z, hz'⟩)
      · exact (table61_exact ⟨z, hz'⟩).1 x y h |>.trans
          ((by decide : ∀ j : Fin 7, table61 j ≤ 8640) ⟨z, hz'⟩)
    · simp [P_eq_zero_of_two_le_t ht]
  · simp [P_eq_zero_of_large_z (by omega : 6 < z)]

theorem P7_le (x y z t : ℕ) (h : x + y + z + t = 14) : P 7 x y z t ≤ 86400 := by
  by_cases hz : z ≤ 7
  · have hz' : z < 8 := by omega
    rcases Nat.lt_or_ge t 2 with ht | ht
    · have ht' : t = 0 ∨ t = 1 := by omega
      rcases ht' with rfl | rfl
      · exact (table70_exact ⟨z, hz'⟩).1 x y h |>.trans
          ((by decide : ∀ j : Fin 8, table70 j ≤ 86400) ⟨z, hz'⟩)
      · exact (table71_exact ⟨z, hz'⟩).1 x y h |>.trans
          ((by decide : ∀ j : Fin 8, table71 j ≤ 86400) ⟨z, hz'⟩)
    · simp [P_eq_zero_of_two_le_t ht]
  · simp [P_eq_zero_of_large_z (by omega : 7 < z)]

theorem Q6 : Q 6 = 665280 := by decide
theorem Q7 : Q 7 = 17297280 := by decide
theorem P6_maximum_attained : ∃ x y z t, x + y + z + t = 12 ∧ P 6 x y z t = 8640 := by
  obtain ⟨x, y, hxy, heq⟩ := (table60_exact 3).2
  exact ⟨x, y, 3, 0, hxy, heq⟩
theorem P7_maximum_attained : ∃ x y z t, x + y + z + t = 14 ∧ P 7 x y z t = 86400 := by
  obtain ⟨x, y, hxy, heq⟩ := (table70_exact 4).2
  exact ⟨x, y, 4, 0, hxy, heq⟩

theorem P6_ratio : (8640 : ℚ) / Q 6 = 1 / 77 := by norm_num [Q6]
theorem P7_ratio : (86400 : ℚ) / Q 7 = 5 / 1001 := by norm_num [Q7]
theorem union6 : ((Nat.choose 12 2 : ℕ) : ℚ) / 77 = 6 / 7 ∧ (6 / 7 : ℚ) < 1 := by
  norm_num [Nat.choose]
theorem union7 : ((Nat.choose 14 2 : ℕ) : ℚ) * (5 / 1001) = 5 / 11 ∧ (5 / 11 : ℚ) < 1 := by
  norm_num [Nat.choose]

/-- P03 after cancellation: C(2k,2)·2^(1-k)<1 is equivalent,
for k≥1, to k(2k−1)<2^(k−1). This is the exact all-k inequality. -/
theorem orientation_tail (k : ℕ) (hk : 8 ≤ k) : k * (2 * k - 1) < 2 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : (k + 1) * (2 * (k + 1) - 1) < 2 * (k * (2 * k - 1)) := by
      have hsub : 2 * k - 1 + 1 = 2 * k := by omega
      have hsub' : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
      rw [hsub']
      have hmul : 8 * k ≤ k * k := Nat.mul_le_mul_right k hk
      have hprod := congrArg (fun t : ℕ => k * t) hsub
      nlinarith
    have he : k + 1 - 1 = k - 1 + 1 := by omega
    rw [he, pow_succ]
    omega

theorem orientation_base : (120 : ℚ) / 128 = 15 / 16 ∧ (15 / 16 : ℚ) < 1 := by
  norm_num

theorem orientation_ratio_lt (k : ℕ) (hk : 8 ≤ k) :
    ((k + 1) * (2 * k + 1) : ℕ) < 2 * k * (2 * k - 1) := by
  have hsub : 2 * k - 1 + 1 = 2 * k := by omega
  have hmul : 8 * k ≤ k * k := Nat.mul_le_mul_right k hk
  have hprod := congrArg (fun t : ℕ => k * t) hsub
  nlinarith

theorem choose_even_two (k : ℕ) : Nat.choose (2 * k) 2 = k * (2 * k - 1) := by
  rw [Nat.choose_two_right]
  have heq : 2 * k * (2 * k - 1) = k * (2 * k - 1) * 2 := by ac_rfl
  rw [heq]
  omega

/-- P03 in the direct finite-count form: the union of at most two forbidden
orientations per unordered vertex pair has cardinality smaller than 2^k. -/
theorem orientation_count_lt (k : ℕ) (hk : 8 ≤ k) :
    2 * Nat.choose (2 * k) 2 < 2 ^ k := by
  rw [choose_even_two]
  have ht := orientation_tail k hk
  have he : k - 1 + 1 = k := by omega
  have hp : 2 ^ k = 2 ^ (k - 1) * 2 := by rw [← pow_succ, he]
  rw [hp]
  omega

/-! ## The five-pair constants -/

theorem Q5 : Q 5 = 30240 := by decide

theorem M_swap_xy (k x y z : ℤ) : M k x y z = M k y x z := by
  unfold M
  have hc :
      (0 ≤ k ∧ 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x ≤ k ∧ y ≤ k ∧ z ≤ k ∧ x + y + z = 2 * k) ↔
      (0 ≤ k ∧ 0 ≤ y ∧ 0 ≤ x ∧ 0 ≤ z ∧ y ≤ k ∧ x ≤ k ∧ z ≤ k ∧ y + x + z = 2 * k) := by omega
  simp only [hc]
  split_ifs <;> simp [mul_comm, mul_assoc]

theorem M_swap_yz (k x y z : ℤ) : M k x y z = M k x z y := by
  unfold M
  have hc :
      (0 ≤ k ∧ 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x ≤ k ∧ y ≤ k ∧ z ≤ k ∧ x + y + z = 2 * k) ↔
      (0 ≤ k ∧ 0 ≤ x ∧ 0 ≤ z ∧ 0 ≤ y ∧ x ≤ k ∧ z ≤ k ∧ y ≤ k ∧ x + z + y = 2 * k) := by omega
  simp only [hc]
  split_ifs <;> simp [mul_comm, mul_left_comm, mul_assoc]

/-- Full permutation symmetry, including invalid signed inputs. -/
theorem M_permutation (k x y z a b c : ℤ) (h : [x, y, z].Perm [a, b, c]) :
    M k x y z = M k a b c := by
  have hs : x + y + z = a + b + c := by
    simpa only [List.sum_cons, List.sum_nil, add_zero, add_assoc] using h.sum_eq
  have hd :
      (0 ≤ k ∧ 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x ≤ k ∧ y ≤ k ∧ z ≤ k ∧ x + y + z = 2 * k) ↔
      (0 ≤ k ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a ≤ k ∧ b ≤ k ∧ c ≤ k ∧ a + b + c = 2 * k) := by
    have hm : (∀ v ∈ [x, y, z], 0 ≤ v ∧ v ≤ k) ↔
        (∀ v ∈ [a, b, c], 0 ≤ v ∧ v ≤ k) := by
      constructor
      · intro hv v hmem
        exact hv v (h.mem_iff.mpr hmem)
      · intro hv v hmem
        exact hv v (h.mem_iff.mp hmem)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, and_assoc] at hm
    omega
  have hn := (h.map (fun v : ℤ => v.toNat.factorial)).prod_eq
  have he := (h.map (fun v : ℤ => (k - v).toNat.factorial)).prod_eq
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hn he
  unfold M
  simp only [hd]
  split_ifs
  · simpa only [mul_assoc] using congrArg₂ (fun u v : ℕ => u / v) hn he
  · rfl

/-- P13: all sorted nonnegative triples of pair counts are precisely these
five possibilities. Permuting the three classes uses `M_swap_xy/y z`. -/
theorem pair_counts_five_coverage (α β γ : ℕ) (hab : α ≤ β) (hbc : β ≤ γ)
    (hsum : α + β + γ = 5) :
    (α = 0 ∧ β = 0 ∧ γ = 5) ∨ (α = 0 ∧ β = 1 ∧ γ = 4) ∨
    (α = 0 ∧ β = 2 ∧ γ = 3) ∨ (α = 1 ∧ β = 1 ∧ γ = 3) ∨
    (α = 1 ∧ β = 2 ∧ γ = 2) := by omega

theorem pair_counts_five_values :
    M 5 0 5 5 = 120 ∧ M 5 1 4 5 = 120 ∧ M 5 2 3 5 = 120 ∧
    M 5 2 4 4 = 192 ∧ M 5 3 3 4 = 216 := by decide

/-- P13 exhaustiveness up to an actual list permutation. Unlike an informal
sorting convention, this assertion retains every order of the three inputs. -/
theorem pair_counts_five_permutations (α β γ : ℕ) (hsum : α + β + γ = 5) :
    [α, β, γ].Perm [0, 0, 5] ∨ [α, β, γ].Perm [0, 1, 4] ∨
    [α, β, γ].Perm [0, 2, 3] ∨ [α, β, γ].Perm [1, 1, 3] ∨
    [α, β, γ].Perm [1, 2, 2] := by
  have hfinite : ∀ a b : Fin 6, a.val + b.val ≤ 5 →
      [a.val, b.val, 5 - (a.val + b.val)].Perm [0, 0, 5] ∨
      [a.val, b.val, 5 - (a.val + b.val)].Perm [0, 1, 4] ∨
      [a.val, b.val, 5 - (a.val + b.val)].Perm [0, 2, 3] ∨
      [a.val, b.val, 5 - (a.val + b.val)].Perm [1, 1, 3] ∨
      [a.val, b.val, 5 - (a.val + b.val)].Perm [1, 2, 2] := by decide
  have hγ : γ = 5 - (α + β) := by omega
  subst γ
  exact hfinite ⟨α, by omega⟩ ⟨β, by omega⟩ (by change α + β ≤ 5; omega)

/-- Only the five unordered pair-count triples require numerical evaluation.
Permutation symmetry covers every ordering of the input classes. -/
theorem M5_complement_le (α β γ : ℕ) (hsum : α + β + γ = 5) :
    M 5 ((5 : ℤ) - α) ((5 : ℤ) - β) ((5 : ℤ) - γ) ≤ 216 := by
  rcases pair_counts_five_permutations α β γ hsum with h | h | h | h | h
  all_goals
    have hm := h.map (fun v : ℕ => (5 : ℤ) - v)
    simp only [List.map_cons, List.map_nil] at hm
    have heq := M_permutation 5 _ _ _ _ _ _ hm
    rw [heq]
    decide

/-- P12: the bound includes every signed input, not only a finite box. -/
theorem M5_le (x y z : ℤ) : M 5 x y z ≤ 216 := by
  by_cases hc : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x ≤ 5 ∧ y ≤ 5 ∧ z ≤ 5 ∧ x + y + z = 10
  · have hsum : (5 - x).toNat + (5 - y).toNat + (5 - z).toNat = 5 := by omega
    have heq : M 5 x y z =
        M 5 (5 - ((5 - x).toNat : ℤ)) (5 - ((5 - y).toNat : ℤ)) (5 - ((5 - z).toNat : ℤ)) := by
      congr 1 <;> omega
    rw [heq]
    exact M5_complement_le _ _ _ hsum
  · have hzero : M 5 x y z = 0 := by
      unfold M
      split_ifs with h
      · omega
      · rfl
    simp [hzero]

theorem M5_maximum_attained : M 5 3 3 4 = 216 := by decide
theorem pair5_ratio : (432 : ℚ) / Q 5 = 1 / 70 := by norm_num [Q5]

/-- P14: the complete closed domain, including d=9,10. -/
theorem triple_candidates_five (d : ℕ) (hd : d ≤ 10) :
    d * Nat.choose (10 - d) 2 ≤ 63 := by
  interval_cases d <;> norm_num [Nat.choose]

theorem triple_candidates_five_attained : 3 * Nat.choose (10 - 3) 2 = 63 := by decide

theorem theta5 : theta 5 = 1 / 315 := by norm_num [theta, Nat.choose]
theorem union5 : ((Nat.choose 10 2 : ℕ) : ℚ) / 70 + 63 / 315 = 59 / 70 ∧
    (59 / 70 : ℚ) < 1 := by norm_num [Nat.choose]

/-! ## Natural ceiling arithmetic for §6

`(N + 3) / 4` is the natural-number ceiling of N/4. These statements expose
that expression directly; they do not use a rounded real approximation.
-/

theorem small_parts_bound (m n : ℕ) (hN : 9 ≤ m + n) : 3 ≤ (m + n + 3) / 4 := by omega

theorem even_unbalanced_bound (k n : ℕ) (hn : 2 * k < n) :
    k + 1 ≤ (2 * k + n + 3) / 4 := by omega

theorem odd_unbalanced_bound (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k + 2 ≤ n) :
    k + 1 ≤ (2 * k - 1 + n + 3) / 4 := by omega

theorem odd_near_balanced_bound (k n : ℕ) (hk : 1 ≤ k)
    (hlo : 2 * k - 1 ≤ n) (hhi : n ≤ 2 * k + 1) :
    (2 * k - 1 + n + 3) / 4 = k := by omega

theorem odd_near_balanced_parameter (k : ℕ) (hm : 7 ≤ 2 * k - 1) : 4 ≤ k := by omega

end Crown.Arithmetic
