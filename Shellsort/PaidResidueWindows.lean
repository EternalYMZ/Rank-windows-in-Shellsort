import Shellsort.WordSlotPotential

/-! True residue inventories of consecutive rank windows with a paid exceptional prefix. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

/-- A positive-gap pass is charged once per successful right shift exactly when it changes
the modulus class of an adjacent chain step. -/
def nondivisorPrice (d k : ℕ) : ℝ := if d ∣ k then 0 else 1

theorem changedResidues_le_paid {n d : ℕ} (p : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) :
    let mid := sortWord p (ks.map Subtype.val)
    (∑ x : Fin n, if (mid x).val % d = (p x).val % d then (0 : ℝ) else 1)
      ≤ 2 * weightedWordShifts (nondivisorPrice d) p ks := by
  let U := fun (x : Fin n) (i : ℕ) => if i % d = (p x).val % d then (0:ℝ) else 1
  have hU (k : ℕ) : gapPotentialBound U k (nondivisorPrice d k) := by
    intro x i hi
    by_cases hd : d ∣ k
    · have he : (i+k)%d = i%d := by simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
      simp [U, he, nondivisorPrice, hd]
    · simp only [nondivisorPrice, ite_eq_right hd, U]
      split_ifs <;> norm_num
  have h := slotPotential_word p ks U (nondivisorPrice d)
    (fun k _ => by unfold nondivisorPrice; split <;> norm_num) (fun k _ => hU k)
  have hz : slotPotential U p = 0 := by simp [slotPotential, U]
  rw [hz, zero_sub, abs_neg] at h
  exact (le_abs_self _).trans h

private def windowMember (L s x : ℕ) : Prop := s ≤ x ∧ x < s+L

private instance (L s x : ℕ) : Decidable (windowMember L s x) := by
  unfold windowMember; infer_instance

/-- The number of keys in the rank window [s,s+L) whose slot has the specified colour. -/
def rankWindowCount {n : ℕ} (p : RankPlacement n) (L s d r : ℕ) : ℝ :=
  ∑ x : Fin n, if windowMember L s x.val ∧ (p x).val%d = r then 1 else 0

def rankWindowDiscrepancy {n : ℕ} (p : RankPlacement n) (d L : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (n+1-L), ∑ r ∈ Finset.range d,
    |rankWindowCount p L s d r - rankWindowCount (Equiv.refl (Fin n)) L s d r|

private theorem overlap_bound (n L x : ℕ) :
    (∑ s ∈ Finset.range (n+1-L), if windowMember L s x then (1:ℝ) else 0) ≤ L := by
  rw [Finset.sum_boole]
  have h : (Finset.range (n+1-L)).filter (fun s => windowMember L s x)
      ⊆ Finset.Ico (x+1-L) (x+1) := by
    intro s hs
    have hh := (Finset.mem_filter.mp hs).2
    unfold windowMember at hh
    exact Finset.mem_Ico.mpr (by omega)
  have hh := Finset.card_le_card h
  rw [Nat.card_Ico] at hh
  exact_mod_cast (show ((Finset.range (n+1-L)).filter (fun s => windowMember L s x)).card ≤ L by omega)

private def windowTest (n L : ℕ) (a : ℕ → ℕ → ℝ) (x r : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (n+1-L), if windowMember L s x then a s r else 0

private theorem test_abs {n L : ℕ} {a : ℕ → ℕ → ℝ} (ha : ∀ s r, |a s r| ≤ 1) (x r : ℕ) :
    |windowTest n L a x r| ≤ L := by
  unfold windowTest
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum ?_).trans (overlap_bound n L x))
  intro s hs
  by_cases h : windowMember L s x <;> simp [h, ha]

private theorem test_rank_step {n L : ℕ} {a : ℕ → ℕ → ℝ} (ha : ∀ s r, |a s r| ≤ 1) (x r : ℕ) :
    |windowTest n L a x r - windowTest n L a (x+1) r| ≤ 2 := by
  unfold windowTest
  rw [← Finset.sum_sub_distrib]
  have each (s : ℕ) : |(if windowMember L s x then a s r else 0) -
      (if windowMember L s (x+1) then a s r else 0)| ≤
      (if s = x+1-L then (1:ℝ) else 0) + (if s = x+1 then (1:ℝ) else 0) := by
    unfold windowMember
    split_ifs <;> norm_num <;> first | linarith [ha s r] | exfalso; omega
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun s _ => each s)).trans ?_)
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range]
  split_ifs <;> norm_num

private theorem test_rank_lipschitz {n L : ℕ} {a : ℕ → ℕ → ℝ} (ha : ∀ s r, |a s r| ≤ 1)
    (x y r : ℕ) : |windowTest n L a x r - windowTest n L a y r| ≤ 2 * |(x:ℝ)-y| := by
  suffices steps : ∀ (i j : ℕ), |windowTest n L a i r - windowTest n L a (i+j) r| ≤ 2*(j:ℝ) by
    rcases le_total x y with h|h
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le h
      simpa using steps x j
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le h
      rw [abs_sub_comm (windowTest _ _ _ _ _), abs_sub_comm ((_:ℕ):ℝ)]
      simpa using steps y j
  intro i j
  induction j with
  | zero => simp
  | succ j ih =>
    have h := abs_sub_le (windowTest n L a i r) (windowTest n L a (i+j) r)
      (windowTest n L a (i+j+1) r)
    have hh := test_rank_step (n:=n) (L:=L) ha (i+j) r
    push_cast
    rw [← Nat.add_assoc]
    linarith

private theorem test_reindex {n d L : ℕ} (hd : 0 < d) (a : ℕ → ℕ → ℝ) (p : RankPlacement n) :
    (∑ s ∈ Finset.range (n+1-L), ∑ r ∈ Finset.range d, a s r * rankWindowCount p L s d r)
      = ∑ x : Fin n, windowTest n L a x.val ((p x).val % d) := by
  unfold rankWindowCount windowTest
  simp_rw [Finset.mul_sum]
  conv_lhs => enter [2,s]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : windowMember L s x.val
  · simp [h, mul_ite, Finset.sum_ite_eq, Nat.mod_lt _ hd]
  · simp [h]

/-- Each non-divisor shift in the prefix can erase at most 4L units of total
inventory error over all complete length-L rank windows. -/
theorem rankWindowDiscrepancy_paid_cut {n d : ℕ} (hd : 0 < d) (L : ℕ) (p : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) :
    let mid := sortWord p (ks.map Subtype.val)
    rankWindowDiscrepancy p d L ≤
      4 * (L:ℝ) * weightedWordShifts (nondivisorPrice d) p ks +
      2 * footrule mid := by
  let mid := sortWord p (ks.map Subtype.val)
  let idp := Equiv.refl (Fin n)
  let a := fun s r => if 0 ≤ rankWindowCount p L s d r - rankWindowCount idp L s d r
      then (1:ℝ) else -1
  have ha (s r : ℕ) : |a s r| ≤ 1 := by dsimp [a]; split <;> norm_num
  let V := fun (q : RankPlacement n) => ∑ x : Fin n, windowTest n L a x.val ((q x).val % d)
  have hreal : rankWindowDiscrepancy p d L = V p - V idp := by
    unfold V
    rw [← test_reindex hd a p, ← test_reindex hd a idp, ← Finset.sum_sub_distrib]
    unfold rankWindowDiscrepancy
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [← mul_sub]
    dsimp only [a, idp]
    split
    · next h => rw [abs_of_nonneg h, one_mul]
    · next h => rw [abs_of_neg (lt_of_not_ge h)]; ring
  have hpre : V p - V mid ≤ 2*(L:ℝ) *
      (∑ x : Fin n, if (mid x).val % d = (p x).val % d then (0:ℝ) else 1) := by
    unfold V
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    split_ifs with h
    · rw [h]; simp
    · have h1 := abs_le.mp (test_abs (n:=n) (L:=L) ha x.val ((p x).val%d))
      have h2 := abs_le.mp (test_abs (n:=n) (L:=L) ha x.val ((mid x).val%d))
      linarith
  have hcut : V mid - V idp ≤ 2 * footrule mid := by
    have he := Equiv.sum_comp mid (fun x => windowTest n L a x.val (x.val%d))
    change (∑ x : Fin n, _) - (∑ x : Fin n, windowTest n L a x.val (x.val%d)) ≤ _
    rw [← he, ← Finset.sum_sub_distrib]
    unfold footrule transport
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    simpa only [Equiv.refl_apply, abs_sub_comm (x.val:ℝ) ((mid x).val:ℝ)] using
      (le_abs_self _).trans (test_rank_lipschitz (n:=n) (L:=L) ha x.val (mid x).val ((mid x).val%d))
  have count := changedResidues_le_paid (d:=d) p ks
  change (∑ x : Fin n, if (mid x).val%d = (p x).val%d then (0:ℝ) else 1) ≤ _ at count
  have pay := mul_le_mul_of_nonneg_left count (show 0 ≤ 2*(L:ℝ) by positivity)
  rw [hreal]
  change _ ≤ _ + 2 * footrule mid
  linarith

/-- The residual term is charged to actual successful shifts in the last unit pass. -/
theorem rankWindowDiscrepancy_paid_unit {n d : ℕ} (hd : 0 < d) (L : ℕ) (p : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) :
    let mid := sortWord p (ks.map Subtype.val)
    rankWindowDiscrepancy p d L ≤ 4 * (L:ℝ) * weightedWordShifts (nondivisorPrice d) p ks +
      4 * (gapInsertionCost mid 1 (by decide) : ℝ) := by
  let mid := sortWord p (ks.map Subtype.val)
  have hz : footrule (Equiv.refl (Fin n)) = 0 := by simp [footrule, transport]
  have h := footrule_le_wordShiftDistance mid [⟨1,by decide⟩]
  simp only [List.map_cons, List.map_nil, sortWord, wordShiftDistance, gapSort_one, hz,
    Nat.cast_one, one_mul, add_zero, zero_add] at h
  have cut := rankWindowDiscrepancy_paid_cut hd L p ks
  change _ ≤ _ + 2 * footrule mid at cut
  change _ ≤ _ + 4 * (gapInsertionCost mid 1 (by decide) : ℝ)
  linarith

end Shellsort
end

