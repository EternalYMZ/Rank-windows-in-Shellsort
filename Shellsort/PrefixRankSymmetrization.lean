import Shellsort.PrefixSlotSelectors

/-! Finite rank transfer by exchangeability. Even tied physical keys admit a
weakly monotone relabeling of ranks. This can delete strict inversions. -/
noncomputable section
open Finset MeasureTheory
open scoped unitInterval
namespace Shellsort.PrefixRankSymmetrization
open HarvestBlockIteration HarvestOperationalAudit PrefixSlotSelectors DisjointConeBins

private theorem chain_map {α β : Type} [LinearOrder α] [LinearOrder β] (f : α → β)
    (hf : Monotone f) (l : List α) : (insertionComparedExecution (l.map f)).output =
      (insertionComparedExecution l).output.map f := by
  simp only [insertionComparedExecution_output]
  exact ((insertionExecution_perm _).trans ((insertionExecution_perm l).map f).symm).eq_of_pairwise'
    (insertionExecution_sorted _) ((insertionExecution_sorted l).map _ (fun _ _ h => hf h))

private theorem pass_map {α β : Type} [LinearOrder α] [LinearOrder β] (f : α → β)
    (hf : Monotone f) {n : ℕ} (a : Vector α n) (h : Gap) :
    (runPass (a.map f) h).1 = (runPass a h).1.map f := by
  apply Vector.ext
  intro i hi
  let s : Fin h.val := ⟨i%h.val,Nat.mod_lt _ h.property⟩
  let row := List.ofFn fun v : Fin (sourceTrialLength (n/h.val) (n%h.val) s.val) =>
    a[s.val+h.val*v.val]'(actual_chain_prefix_lt n h.val h.property s v)
  have e := chain_map f hf row
  simp only [row, List.map_ofFn, Function.comp_def] at e
  simp only [runPass,Vector.getElem_ofFn,Vector.getElem_map]
  rw [e,List.getElem?_map]
  cases (insertionComparedExecution row).output[i/h.val]? <;> rfl

/-- Weakly monotone relabelings preserve the recorded slot contents after mapping.
The proposition only concerns the checkpoint array. -/
theorem word_map {α β : Type} [LinearOrder α] [LinearOrder β] (f : α → β)
    (hf : Monotone f) {n : ℕ} (a : Vector α n) (w : PositiveWord) :
    (runWord (a.map f) w).1 = (runWord a w).1.map f := by
  induction w generalizing a with
  | nil => rfl
  | cons h w ih => simpa only [runWord, pass_map f hf] using ih (runPass a h).1

def reward {α : Type} [LinearOrder α] {n : ℕ} (w : PositiveWord) (g : ℕ)
    (a : Vector α n) : ℝ := ∑ p ∈ gapPositionPairs n g,
      if (runWord a w).1[p.2.val] < (runWord a w).1[p.1.val] then 1 else 0

theorem reward_map_le {α β : Type} [LinearOrder α] [LinearOrder β] (f : α → β)
    (hf : Monotone f) {n : ℕ} (a : Vector α n) (w : PositiveWord) (g : ℕ) :
    reward w g (a.map f) ≤ reward w g a := by
  simp only [reward,word_map f hf,Vector.getElem_map]
  apply sum_le_sum
  intro p _
  split_ifs with hl hr hr <;> norm_num
  exact (hr (lt_of_not_ge fun h => hl.not_ge (hf h))).elim

theorem reward_slots {n : ℕ} (p : RankPlacement n) (w : PositiveWord) (g : ℕ) :
    reward w g (slots p) = gapInversions (sortWord p (w.map Subtype.val)) g := by
  unfold reward
  rw [runWord_slots, gapInversions_eq_indicator_sum]
  simp [slots,pairInversionIndicator]

private def reindex {n : ℕ} (s : RankPlacement n) : RankPlacement n ≃ RankPlacement n where
  toFun p := s.trans p
  invFun p := s.symm.trans p
  left_inv p := by ext i; simp
  right_inv p := by ext i; simp

/-- Refine the ties in one fixed sample and permute its physical slots. -/
theorem orbit_bound {n : ℕ} (w : PositiveWord) (g : ℕ) (x : Fin n → ℝ) :
    uniformAverage (fun p : RankPlacement n => reward w g (Vector.ofFn fun i => x (p.symm i))) ≤
      uniformAverage (fun p : RankPlacement n => (gapInversions (sortWord p (w.map Subtype.val)) g : ℝ)) := by
  let s := Tuple.sort x
  let f := x ∘ s
  have hf : Monotone f := Tuple.monotone_sort x
  rw [← uniformAverage_reindex (reindex s) (fun p : RankPlacement n => (gapInversions (sortWord p (w.map Subtype.val)) g : ℝ))]
  apply uniformAverage_mono
  intro p
  have e : Vector.ofFn (fun i => x (p.symm i)) = (slots (reindex s p)).map f := by
    apply Vector.ext
    intro i hi
    simp [slots,reindex,f]
  rw [e,← reward_slots]
  exact reward_map_le f hf _ w g

private abbrev P (n : ℕ) := Measure.pi (fun _ : Fin n => (volume : Measure I))
private def physical {n : ℕ} (x : Fin n → I) := Vector.ofFn fun i => (x i : ℝ)

private theorem reward_integrable {n : ℕ} (w : PositiveWord) (g : ℕ) (p : RankPlacement n) :
    Integrable (fun x : Fin n → I => reward w g (physical fun i => x (p.symm i))) (P n) := by
  have ms (i : Fin n) : Measurable (fun x : Fin n → I =>
      (runWord (physical fun i => x (p.symm i)) w).1[i.val]) := by
    apply measurable_slot
    intro j
    simp only [physical,Vector.getElem_ofFn]
    exact measurable_subtype_coe.comp (measurable_pi_apply (p.symm j))
  apply integrable_finsetSum
  intro ij _
  exact (integrable_const (1:ℝ)).indicator (measurableSet_lt (ms ij.2) (ms ij.1))

private theorem integral_shuffle {n : ℕ} (p : RankPlacement n) (f : (Fin n → I) → ℝ) :
    (∫ x, f (fun i => x (p.symm i)) ∂(P n)) = ∫ x, f x ∂(P n) := by
  have mp := measurePreserving_piCongrLeft (fun _ : Fin n => (volume : Measure I)) p
  have he (x : Fin n → I) : (fun i => x (p.symm i)) =
      MeasurableEquiv.piCongrLeft (fun _ : Fin n => I) p x := by
    funext i
    obtain ⟨j,rfl⟩ := p.surjective i
    simp [MeasurableEquiv.piCongrLeft_apply_apply]
  simp_rw [he]
  exact mp.integral_comp' f

theorem uniform_dominates_product {n : ℕ} (w : PositiveWord) (g : ℕ) :
    (∫ x, reward w g (physical x) ∂(P n)) ≤ uniformAverage (fun p : RankPlacement n =>
      (gapInversions (sortWord p (w.map Subtype.val)) g : ℝ)) := by
  let F := fun (p : RankPlacement n) (x : Fin n → I) => reward w g (physical fun i => x (p.symm i))
  have integ p : Integrable (F p) (P n) := reward_integrable w g p
  let c := uniformAverage (fun p : RankPlacement n => (gapInversions (sortWord p (w.map Subtype.val)) g : ℝ))
  have integr : Integrable (fun x => (∑ p, F p x)/(n.factorial:ℝ)) (P n) :=
    (integrable_finsetSum univ (fun p _ => integ p)).div_const _
  have bound (x : Fin n → I) : (∑ p, F p x)/(n.factorial:ℝ) ≤ c :=
    orbit_bound w g (fun i => (x i : ℝ))
  have mono : (∫ x, (∑ p, F p x)/(n.factorial:ℝ) ∂(P n)) ≤ ∫ _, c ∂(P n) :=
    integral_mono integr (integrable_const c) bound
  rw [integral_div,integral_finsetSum univ (fun p _ => integ p), integral_const] at mono
  have e (p : RankPlacement n) : (∫ x, F p x ∂(P n)) = ∫ x, reward w g (physical x) ∂(P n) :=
    integral_shuffle p (fun x : Fin n → I => reward w g (physical x))
  simp_rw [e] at mono
  have hn : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simpa [RankPlacement, Fintype.card_perm, hn,c] using mono

theorem uniform_next_inversions {n g B : ℕ} (hg : 0 < g) (w : PositiveWord) (hB : 0 < B)
    (hin : ∀ i : Fin n, (cone w i).card ≤ B) (hout : ∀ j : Fin n, (readers (cone w) j).card ≤ B)
    (many : 8*g*B^3 ≤ n) : (n:ℝ)^2 ≤ 128*(g:ℝ)*B*uniformAverage (fun p : RankPlacement n =>
      (gapInversions (sortWord p (w.map Subtype.val)) g : ℝ)) := by
  let res := fun i : Fin n => (⟨i.val%g,Nat.mod_lt _ hg⟩ : Fin g)
  have e := executed_chain_inversions w hB res hin hout many
  have hprod : (n:ℝ)^2 ≤ 128*(g:ℝ)*B*(∫ x, reward w g (physical x) ∂(P n)) := by
    simp only [res,Fin.ext_iff,Set.indicator_apply,Set.mem_ofPred_eq,Pi.one_apply] at e
    apply e.trans_eq
    congr 1
  exact hprod.trans (mul_le_mul_of_nonneg_left (uniform_dominates_product w g) (by positivity))

/-- The actual next ordinary insertion pass under the uniform distribution on
input permutations, at every prefix with the stated fan-in and fan-out. -/
theorem uniform_next_comparisons {n g B : ℕ} (hg : 0 < g) (w : PositiveWord) (hB : 0 < B)
    (hin : ∀ i : Fin n, (cone w i).card ≤ B) (hout : ∀ j : Fin n, (readers (cone w) j).card ≤ B)
    (many : 8*g*B^3 ≤ n) : (n:ℝ)^2 ≤ 128*(g:ℝ)*B*uniformAverage (fun p : RankPlacement n =>
      (gapComparisonCost (sortWord p (w.map Subtype.val)) g hg : ℝ)) := by
  apply (uniform_next_inversions hg w hB hin hout many).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply uniformAverage_mono
  intro p
  exact_mod_cast (gapInsertionCost_eq_gapInversions _ g hg) ▸ (gapComparisonCost_lower (sortWord p (w.map Subtype.val)) g hg)

#print axioms uniform_next_comparisons
end Shellsort.PrefixRankSymmetrization
