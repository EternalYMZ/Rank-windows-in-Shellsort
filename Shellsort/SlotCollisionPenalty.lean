import Shellsort.WordSlotPotential

/-! Uniform price per executed shift and a Hall-type penalty at one checkpoint. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

theorem weightedWordShifts_unit {n : ℕ} (p : RankPlacement n) (ks : List {k : ℕ // 0 < k}) :
    weightedWordShifts (fun _ => 1) p ks = (ordinaryWordShifts p ks : ℝ) := by
  induction ks generalizing p with
  | nil => simp [weightedWordShifts, ordinaryWordShifts]
  | cons k ks ih => simp [weightedWordShifts, ordinaryWordShifts, ih]

/-- If a key in T cannot realize its baseline potential outside S without
an extra charge δ, at least |T|−|S| such charges are forced. -/
theorem twoBlock_slot_deficit {n : ℕ} (p : RankPlacement n)
    (as bs : List {k : ℕ // 0 < k}) (U V : Fin n → ℕ → ℝ)
    (hU : ∀ k ∈ as, gapPotentialBound U k.val 1)
    (hV : ∀ k ∈ bs, gapPotentialBound V k.val 1)
    (T S : Finset (Fin n)) (base : Fin n → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbase : ∀ x i : Fin n, U x i.val - V x i.val ≤ -base x)
    (hextra : ∀ x ∈ T, ∀ i ∉ S, U x i.val - V x i.val ≤ -base x - δ) :
    let mid := sortWord p (as.map Subtype.val)
    slotPotential U p - slotPotential V (sortWord mid (bs.map Subtype.val)) +
      (∑ x, base x) + ((T.card : ℝ)-(S.card : ℝ))*δ ≤
      2*((ordinaryWordShifts p as : ℝ) + (ordinaryWordShifts mid bs : ℝ)) := by
  classical
  let row := fun x : Fin n => -base x - if x ∈ T then δ else 0
  let col := fun i : Fin n => if i ∈ S then δ else 0
  have feasible (x i : Fin n) : U x i.val - V x i.val ≤ row x + col i := by
    by_cases hx : x ∈ T <;> by_cases hi : i ∈ S <;> simp [row, col, hx, hi]
    all_goals first | linarith [hbase x i] | linarith [hextra x hx i hi]
  have r : (∑ x, row x) = -(∑ x, base x) - (T.card : ℝ)*δ := by
    simp [row, Finset.sum_sub_distrib, Finset.sum_ite_mem]
  have c : (∑ i, col i) = (S.card : ℝ)*δ := by
    simp [col, Finset.sum_ite_mem]
  have h := slotPotential_twoBlock p as bs U V (fun _ => 1) (fun _ => 1)
    (fun _ _ => zero_le_one) (fun _ _ => zero_le_one) hU hV row col feasible
  dsimp only at *
  rw [r, c, weightedWordShifts_unit, weightedWordShifts_unit] at h
  linarith

end Shellsort
end
