import Mathlib.Tactic

/-! Amortizing nested dyadic transportation bounds on finitely many cutoffs.
All weights and movement budgets below are real. -/
namespace Shellsort.DyadicCutBudget

open Finset

private noncomputable def remainder (x : ℝ) (j : ℕ) : ℝ :=
  min 1 (x / 2 ^ j)

private theorem term_le_drop (x : ℝ) (hx : 0 ≤ x) (j : ℕ) :
    (if x ≤ (2 : ℝ)^j then x / 2^j else 0) ≤
      2 * (remainder x j - remainder x (j+1)) := by
  have hd : 0 < (2 : ℝ)^j := by positivity
  have hs : x / (2 : ℝ)^(j+1) = (x / 2^j)/2 := by
    rw [pow_succ, div_mul_eq_div_div]
  have hn : 0 ≤ x/(2:ℝ)^j := div_nonneg hx hd.le
  unfold remainder
  rw [hs]
  split_ifs with h
  · have hu : x/(2:ℝ)^j ≤ 1 := (div_le_one hd).mpr h
    rw [min_eq_right hu, min_eq_right (by linarith : (x / (2:ℝ)^j)/2 ≤ 1)]
    linarith
  · have hmono : min 1 ((x / (2:ℝ)^j)/2) ≤ min 1 (x/(2:ℝ)^j) :=
      min_le_min le_rfl (by linarith)
    linarith

private theorem sum_range_le_drop (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (∑ j ∈ range N, if x ≤ (2:ℝ)^j then x / 2^j else 0) ≤
      2 * (remainder x 0 - remainder x N) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    linarith [term_le_drop x hx n]

/-- A fixed stride contributes at most twice its movement budget across any
set of cutoffs. The set is finite and need not contain consecutive scales. -/
theorem one_stride (x : ℝ) (hx : 0 ≤ x) (J : Finset ℕ) :
    (∑ j ∈ J, if x ≤ (2:ℝ)^j then x / 2^j else 0) ≤ 2 := by
  let N := J.sup id + 1
  have hsub : J ⊆ range N := by
    intro j hj
    exact mem_range.mpr (Nat.lt_succ_of_le (le_sup (f := id) hj))
  have h0 : remainder x 0 ≤ 1 := min_le_left _ _
  have hN : 0 ≤ remainder x N := le_min (by norm_num) (by positivity)
  have hh : (∑ j ∈ J, if x ≤ (2:ℝ)^j then x / 2^j else 0) ≤
      ∑ j ∈ range N, if x ≤ (2:ℝ)^j then x / 2^j else 0 := by
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro j _ _
    split_ifs <;> positivity
  linarith [sum_range_le_drop x hx N]

/-- If each state is bounded by twice the stride-weighted remaining shifts,
the sum of its normalized deviations costs at most four times all shifts. -/
theorem total_cut_charge (J strides : Finset ℕ) (moves state : ℕ → ℝ)
    (hm : ∀ h ∈ strides, 0 ≤ moves h)
    (cut : ∀ j ∈ J, state j ≤
      2 * ∑ h ∈ strides, if (h:ℝ) ≤ (2:ℝ)^j then (h:ℝ) * moves h else 0) :
    (∑ j ∈ J, state j / (2:ℝ)^j) ≤ 4 * ∑ h ∈ strides, moves h := by
  let weight (h j : ℕ) : ℝ := if (h:ℝ) ≤ (2:ℝ)^j then (h:ℝ) / 2^j else 0
  have localBound (j : ℕ) (hj : j ∈ J) :
      state j / (2:ℝ)^j ≤ ∑ h ∈ strides, (2 * moves h) * weight h j := by
    apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^j)).mpr
    refine (cut j hj).trans ?_
    rw [mul_sum, sum_mul]
    apply sum_le_sum
    intro h _
    unfold weight
    split_ifs <;> field_simp
    <;> ring_nf
    <;> exact le_rfl
  calc
    _ ≤ ∑ j ∈ J, ∑ h ∈ strides, (2 * moves h) * weight h j := sum_le_sum localBound
    _ = ∑ h ∈ strides, ∑ j ∈ J, (2 * moves h) * weight h j := sum_comm
    _ ≤ ∑ h ∈ strides, 4 * moves h := by
      apply sum_le_sum
      intro h hh
      rw [← mul_sum]
      have bound : (∑ j ∈ J, weight h j) ≤ 2 := one_stride (h:ℝ) (Nat.cast_nonneg _) J
      have nonnegative : 0 ≤ 2 * moves h := by linarith [hm h hh]
      linarith [mul_le_mul_of_nonneg_left bound nonnegative]
    _ = _ := (mul_sum ..).symm

end Shellsort.DyadicCutBudget
