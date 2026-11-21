import Shellsort.PaidResidueWindows
import Shellsort.SlotCollisionPenalty

/-! Combine many residue-window certificates while charging each executed shift once. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

private theorem weightedWordShifts_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (w : ι → ℕ → ℝ) (p : RankPlacement n) (ks : List {k : ℕ // 0 < k}) :
    (∑ j, a j * weightedWordShifts (w j) p ks) =
      weightedWordShifts (fun h => ∑ j, a j * w j h) p ks := by
  induction ks generalizing p with
  | nil => simp [weightedWordShifts]
  | cons k ks ih =>
    simp only [weightedWordShifts, mul_add, Finset.sum_add_distrib, ← mul_assoc,
      ← Finset.sum_mul, ih]

private theorem weightedWordShifts_mono {n : ℕ} (w v : ℕ → ℝ)
    (p : RankPlacement n) (ks : List {k : ℕ // 0 < k})
    (h : ∀ k ∈ ks, w k.val ≤ v k.val) :
    weightedWordShifts w p ks ≤ weightedWordShifts v p ks := by
  induction ks generalizing p with
  | nil => rfl
  | cons k ks ih =>
    exact add_le_add
      (mul_le_mul_of_nonneg_right (h k (by simp)) (Nat.cast_nonneg _))
      (ih (gapSort p k.val) (fun j hj => h j (by simp [hj])))

/-- Arbitrary moduli, window lengths and nonnegative weights. Each real pass
pays its own combined tariff on exactly the non-divisors of its gap. -/
theorem rankWindows_combined_price {n : ℕ} {ι : Type*} [Fintype ι]
    (d L : ι → ℕ) (a : ι → ℝ) (hd : ∀ j, 0 < d j) (ha : ∀ j, 0 ≤ a j)
    (p : RankPlacement n) (ks : List {k : ℕ // 0 < k}) :
    let mid := sortWord p (ks.map Subtype.val)
    (∑ j, a j * rankWindowDiscrepancy p (d j) (L j)) ≤
      weightedWordShifts (fun k => ∑ j, (a j * (4 * (L j : ℝ))) * nondivisorPrice (d j) k) p ks +
      (∑ j, a j * 4) * (gapInsertionCost mid 1 (by decide) : ℝ) := by
  dsimp only
  have each (j : ι) := mul_le_mul_of_nonneg_left
    (rankWindowDiscrepancy_paid_unit (hd j) (L j) p ks) (ha j)
  calc
    _ ≤ _ := Finset.sum_le_sum (fun j _ => each j)
    _ = _ := by
      simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib]
      rw [weightedWordShifts_sum, Finset.sum_mul]

/-- Under the displayed packing constraints, all window certificates together charge
at most one unit per real successful shift, including the last unit pass. -/
theorem rankWindows_packed_lower {n : ℕ} {ι : Type*} [Fintype ι]
    (d L : ι → ℕ) (a : ι → ℝ) (hd : ∀ j, 0 < d j) (ha : ∀ j, 0 ≤ a j)
    (p : RankPlacement n) (ks : List {k : ℕ // 0 < k})
    (hpre : ∀ k ∈ ks, (∑ j, (a j * (4 * (L j : ℝ))) * nondivisorPrice (d j) k.val) ≤ 1)
    (hlast : (∑ j, a j * 4) ≤ 1) :
    (∑ j, a j * rankWindowDiscrepancy p (d j) (L j)) ≤
      (ordinaryWordShifts p ks : ℝ) +
      (gapInsertionCost (sortWord p (ks.map Subtype.val)) 1 (by decide) : ℝ) := by
  have pay := weightedWordShifts_mono
    (fun k => ∑ j, (a j * (4 * (L j : ℝ))) * nondivisorPrice (d j) k)
    (fun _ => 1) p ks hpre
  rw [weightedWordShifts_unit] at pay
  refine (rankWindows_combined_price d L a hd ha p ks).trans (add_le_add pay ?_)
  simpa using mul_le_mul_of_nonneg_right hlast
    (Nat.cast_nonneg (gapInsertionCost (sortWord p (ks.map Subtype.val)) 1 (by decide)) : (0:ℝ) ≤ _)

end Shellsort
end

