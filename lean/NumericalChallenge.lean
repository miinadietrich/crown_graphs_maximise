import Crown.ArithmeticDefinitions
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators

namespace Crown.Numerical.Arithmetic
open Crown.Arithmetic

theorem Q_mul_factorial : ∀ (k : ℕ),
    Q k * k.factorial = (2 * k).factorial :=
  by sorry

theorem Q_pos : ∀ (k : ℕ),
    0 < Q k :=
  by sorry

theorem M_denominator_pos : ∀ (k x y z : ℤ),
    0 < (k - x).toNat.factorial * (k - y).toNat.factorial * (k - z).toNat.factorial :=
  by sorry

theorem M_eq_zero_of_negative : ∀ {k x y z : ℤ}
    (h : k < 0 ∨ x < 0 ∨ y < 0 ∨ z < 0),
    M k x y z = 0 :=
  by sorry

theorem M_eq_zero_of_large_z : ∀ {k x y z : ℤ} (h : k < z),
    M k x y z = 0 :=
  by sorry

theorem P_eq_zero_of_two_le_t : ∀ {k x y z t : ℕ} (h : 2 ≤ t),
    P k x y z t = 0 :=
  by sorry

theorem P_eq_zero_of_large_z : ∀ {k x y z t : ℕ} (h : k < z),
    P k x y z t = 0 :=
  by sorry

theorem finiteSliceMaximum_iff : ∀ (k z t a : ℕ),
    FiniteSliceMaximum k z t a ↔ IsSliceMaximum k z t a :=
  by sorry

theorem table60_exact : ∀ (z : Fin 7),
    IsSliceMaximum 6 z.val 0 (table60 z) :=
  by sorry

theorem table61_exact : ∀ (z : Fin 7),
    IsSliceMaximum 6 z.val 1 (table61 z) :=
  by sorry

theorem table70_exact : ∀ (z : Fin 8),
    IsSliceMaximum 7 z.val 0 (table70 z) :=
  by sorry

theorem table71_exact : ∀ (z : Fin 8),
    IsSliceMaximum 7 z.val 1 (table71 z) :=
  by sorry

theorem P6_le : ∀ (x y z t : ℕ) (h : x + y + z + t = 12),
    P 6 x y z t ≤ 8640 :=
  by sorry

theorem P7_le : ∀ (x y z t : ℕ) (h : x + y + z + t = 14),
    P 7 x y z t ≤ 86400 :=
  by sorry

theorem Q6 : Q 6 = 665280 :=
  by sorry

theorem Q7 : Q 7 = 17297280 :=
  by sorry

theorem P6_maximum_attained : ∃ x y z t, x + y + z + t = 12 ∧ P 6 x y z t = 8640 :=
  by sorry

theorem P7_maximum_attained : ∃ x y z t, x + y + z + t = 14 ∧ P 7 x y z t = 86400 :=
  by sorry

theorem P6_ratio : (8640 : ℚ) / Q 6 = 1 / 77 :=
  by sorry

theorem P7_ratio : (86400 : ℚ) / Q 7 = 5 / 1001 :=
  by sorry

theorem union6 : ((Nat.choose 12 2 : ℕ) : ℚ) / 77 = 6 / 7 ∧ (6 / 7 : ℚ) < 1 :=
  by sorry

theorem union7 : ((Nat.choose 14 2 : ℕ) : ℚ) * (5 / 1001) = 5 / 11 ∧ (5 / 11 : ℚ) < 1 :=
  by sorry

theorem orientation_tail : ∀ (k : ℕ) (hk : 8 ≤ k),
    k * (2 * k - 1) < 2 ^ (k - 1) :=
  by sorry

theorem orientation_base : (120 : ℚ) / 128 = 15 / 16 ∧ (15 / 16 : ℚ) < 1 :=
  by sorry

theorem orientation_ratio_lt : ∀ (k : ℕ) (hk : 8 ≤ k),
    ((k + 1) * (2 * k + 1) : ℕ) < 2 * k * (2 * k - 1) :=
  by sorry

theorem choose_even_two : ∀ (k : ℕ),
    Nat.choose (2 * k) 2 = k * (2 * k - 1) :=
  by sorry

theorem orientation_count_lt : ∀ (k : ℕ) (hk : 8 ≤ k),
    2 * Nat.choose (2 * k) 2 < 2 ^ k :=
  by sorry

theorem Q5 : Q 5 = 30240 :=
  by sorry

theorem M_swap_xy : ∀ (k x y z : ℤ),
    M k x y z = M k y x z :=
  by sorry

theorem M_swap_yz : ∀ (k x y z : ℤ),
    M k x y z = M k x z y :=
  by sorry

theorem M_permutation : ∀ (k x y z a b c : ℤ) (h : [x, y, z].Perm [a, b, c]),
    M k x y z = M k a b c :=
  by sorry

theorem pair_counts_five_coverage : ∀ (α β γ : ℕ) (hab : α ≤ β) (hbc : β ≤ γ)
    (hsum : α + β + γ = 5),
    (α = 0 ∧ β = 0 ∧ γ = 5) ∨ (α = 0 ∧ β = 1 ∧ γ = 4) ∨
    (α = 0 ∧ β = 2 ∧ γ = 3) ∨ (α = 1 ∧ β = 1 ∧ γ = 3) ∨
    (α = 1 ∧ β = 2 ∧ γ = 2) :=
  by sorry

theorem pair_counts_five_values : M 5 0 5 5 = 120 ∧ M 5 1 4 5 = 120 ∧ M 5 2 3 5 = 120 ∧
    M 5 2 4 4 = 192 ∧ M 5 3 3 4 = 216 :=
  by sorry

theorem pair_counts_five_permutations : ∀ (α β γ : ℕ) (hsum : α + β + γ = 5),
    [α, β, γ].Perm [0, 0, 5] ∨ [α, β, γ].Perm [0, 1, 4] ∨
    [α, β, γ].Perm [0, 2, 3] ∨ [α, β, γ].Perm [1, 1, 3] ∨
    [α, β, γ].Perm [1, 2, 2] :=
  by sorry

theorem M5_complement_le : ∀ (α β γ : ℕ) (hsum : α + β + γ = 5),
    M 5 ((5 : ℤ) - α) ((5 : ℤ) - β) ((5 : ℤ) - γ) ≤ 216 :=
  by sorry

theorem M5_le : ∀ (x y z : ℤ),
    M 5 x y z ≤ 216 :=
  by sorry

theorem M5_maximum_attained : M 5 3 3 4 = 216 :=
  by sorry

theorem pair5_ratio : (432 : ℚ) / Q 5 = 1 / 70 :=
  by sorry

theorem triple_candidates_five : ∀ (d : ℕ) (hd : d ≤ 10),
    d * Nat.choose (10 - d) 2 ≤ 63 :=
  by sorry

theorem triple_candidates_five_attained : 3 * Nat.choose (10 - 3) 2 = 63 :=
  by sorry

theorem theta5 : theta 5 = 1 / 315 :=
  by sorry

theorem union5 : ((Nat.choose 10 2 : ℕ) : ℚ) / 70 + 63 / 315 = 59 / 70 ∧
    (59 / 70 : ℚ) < 1 :=
  by sorry

theorem small_parts_bound : ∀ (m n : ℕ) (hN : 9 ≤ m + n),
    3 ≤ (m + n + 3) / 4 :=
  by sorry

theorem even_unbalanced_bound : ∀ (k n : ℕ) (hn : 2 * k < n),
    k + 1 ≤ (2 * k + n + 3) / 4 :=
  by sorry

theorem odd_unbalanced_bound : ∀ (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k + 2 ≤ n),
    k + 1 ≤ (2 * k - 1 + n + 3) / 4 :=
  by sorry

theorem odd_near_balanced_bound : ∀ (k n : ℕ) (hk : 1 ≤ k)
    (hlo : 2 * k - 1 ≤ n) (hhi : n ≤ 2 * k + 1),
    (2 * k - 1 + n + 3) / 4 = k :=
  by sorry

theorem odd_near_balanced_parameter : ∀ (k : ℕ) (hm : 7 ≤ 2 * k - 1),
    4 ≤ k :=
  by sorry

end Crown.Numerical.Arithmetic

namespace Crown.Numerical.Counting
open Crown.Counting

theorem exists_avoiding_of_sum_card_lt : ∀ {ι Ω : Type*} [DecidableEq Ω]
    (indices : Finset ι) (samples : Finset Ω) (bad : ι → Finset Ω)
    (hsmall : (∑ i ∈ indices, (bad i).card) < samples.card),
    ∃ ω ∈ samples, ∀ i ∈ indices, ω ∉ bad i :=
  by sorry

theorem exists_avoiding_of_bounds : ∀ {ι Ω : Type*} [DecidableEq Ω]
    (indices : Finset ι) (samples : Finset Ω) (bad : ι → Finset Ω) (bound : ι → ℕ)
    (hbound : ∀ i ∈ indices, (bad i).card ≤ bound i)
    (hsmall : (∑ i ∈ indices, bound i) < samples.card),
    ∃ ω ∈ samples, ∀ i ∈ indices, ω ∉ bad i :=
  by sorry

theorem exists_avoiding_of_uniform_bound : ∀ {ι Ω : Type*} [DecidableEq Ω]
    (indices : Finset ι) (samples : Finset Ω) (bad : ι → Finset Ω) (bound : ℕ)
    (hbound : ∀ i ∈ indices, (bad i).card ≤ bound)
    (hsmall : indices.card * bound < samples.card),
    ∃ ω ∈ samples, ∀ i ∈ indices, ω ∉ bad i :=
  by sorry

theorem exists_avoiding_two_families : ∀ {ι κ Ω : Type*} [DecidableEq Ω]
    (left : Finset ι) (right : Finset κ) (samples : Finset Ω)
    (badLeft : ι → Finset Ω) (badRight : κ → Finset Ω)
    (hsmall : (∑ i ∈ left, (badLeft i).card) +
      (∑ j ∈ right, (badRight j).card) < samples.card),
    ∃ ω ∈ samples,
      (∀ i ∈ left, ω ∉ badLeft i) ∧ (∀ j ∈ right, ω ∉ badRight j) :=
  by sorry

theorem card_orientations : ∀ (k : ℕ),
    Fintype.card (Orientations k) = 2 ^ k :=
  by sorry

theorem card_vertex_pairs : ∀ (k : ℕ),
    ((Finset.univ : Finset (Fin (2 * k))).powersetCard 2).card = Nat.choose (2 * k) 2 :=
  by sorry

theorem exists_good_orientation : ∀ (k : ℕ) (hk : 8 ≤ k)
    (bad : Finset (Fin (2 * k)) → Finset (Orientations k))
    (hbound : ∀ pair ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard 2,
      (bad pair).card ≤ 2),
    ∃ ω : Orientations k,
      ∀ pair ∈ (Finset.univ : Finset (Fin (2 * k))).powersetCard 2, ω ∉ bad pair :=
  by sorry

end Crown.Numerical.Counting
