import Shellsort.PackedResidueWindows

open Shellsort

private def p6 : RankPlacement 6 :=
  (Equiv.swap (1:Fin 6) 2).trans ((Equiv.swap (1:Fin 6) 4).trans (Equiv.swap (1:Fin 6) 3))

private def cell6 (p : RankPlacement 6) (s d r : ℕ) : ℕ :=
  ∑ x : Fin 6, if (s ≤ x.val ∧ x.val < s+2) ∧ (p x).val % d = r then 1 else 0

private theorem c6 (p : RankPlacement 6) (s d r : ℕ) :
    rankWindowCount p 2 s d r = cell6 p s d r := by
  unfold rankWindowCount cell6
  push_cast
  rfl

private def difference (u v : ℕ) := (u-v)+(v-u)

private theorem difference_real (u v : ℕ) : |(u:ℝ)-v| = (difference u v : ℝ) := by
  unfold difference
  rcases le_total u v with h|h
  · rw [Nat.sub_eq_zero_of_le h, Nat.zero_add, Nat.cast_sub h, abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (u:ℝ) ≤ v by exact_mod_cast h))]
    ring
  · rw [Nat.sub_eq_zero_of_le h, Nat.add_zero, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

private def q6 (d : ℕ) :=
  ∑ s ∈ Finset.range 5, ∑ r ∈ Finset.range d,
    difference (cell6 p6 s d r) (cell6 (Equiv.refl _) s d r)

private theorem q6_eq (d : ℕ) : rankWindowDiscrepancy p6 d 2 = (q6 d : ℝ) := by
  simp only [rankWindowDiscrepancy, c6, difference_real, q6, Nat.cast_sum]

set_option maxRecDepth 8192 in
example : rankWindowDiscrepancy p6 2 2 = 8 ∧ rankWindowDiscrepancy p6 3 2 = 8 := by
  rw [q6_eq, q6_eq]
  have h : q6 2 = 8 ∧ q6 3 = 8 := by decide
  simp [h.1, h.2]

