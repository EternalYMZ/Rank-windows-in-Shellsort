import Shellsort.HarvestOperationalAudit
import Shellsort.BinnedMedianInversions
import Mathlib.Data.Fin.Tuple.Sort

/-! The physical slots after a fixed prefix of ordinary insertion passes are
measurable selectors of their backward dependency sets. No random input or
independence assumption enters the representation. -/
noncomputable section
open Finset MeasureTheory
namespace Shellsort.PrefixSlotSelectors
open HarvestBlockIteration HarvestOperationalAudit DisjointConeBins

abbrev Gap := {k : ℕ // 0 < k}

def neighborhood {n : ℕ} (h : Gap) (i : Fin n) := chainPositions n h.val (i.val % h.val)

def cone {n : ℕ} : PositiveWord → Fin n → Finset (Fin n)
  | [], i => {i}
  | h :: w, i => (cone w i).biUnion (neighborhood h)

def width (n : ℕ) (h : Gap) := sourceTrialLength (n/h.val) (n%h.val) 0

def budget (n : ℕ) : PositiveWord → ℕ
  | [] => 1
  | h :: w => width n h * budget n w

theorem neighborhood_card_le {n : ℕ} (h : Gap) (i : Fin n) :
    (neighborhood h i).card ≤ width n h := by
  rw [neighborhood, actual_chain_length n h.val h.property ⟨_,Nat.mod_lt _ h.property⟩]
  simp only [width, sourceTrialLength]
  split_ifs <;> omega

theorem cone_card_le {n : ℕ} (w : PositiveWord) (i : Fin n) :
    (cone w i).card ≤ budget n w := by
  induction w with
  | nil => simp [cone,budget]
  | cons h w ih =>
    calc
      _ ≤ ∑ j ∈ cone w i, (neighborhood h j).card := card_biUnion_le
      _ ≤ ∑ _j ∈ cone w i, width n h := sum_le_sum (fun j _ => neighborhood_card_le h j)
      _ ≤ _ := by simpa [budget, Nat.mul_comm] using Nat.mul_le_mul_right (width n h) ih

theorem readers_card_le {n : ℕ} (w : PositiveWord) (i : Fin n) :
    (readers (cone w) i).card ≤ budget n w := by
  induction w generalizing i with
  | nil =>
    have e : readers (cone ([] : PositiveWord)) i = {i} := by
      ext a
      simp [readers, cone, eq_comm]
    simp [e,budget]
  | cons h w ih =>
    have eqn : readers (cone (h :: w)) i = (neighborhood h i).biUnion (readers (cone w)) := by
      ext a
      simp only [readers, cone, neighborhood, chainPositions, mem_filter, mem_univ, true_and,
        mem_biUnion]
      constructor
      · rintro ⟨j,hj,hk⟩; exact ⟨j,hk.symm,hj⟩
      · rintro ⟨j,hj,hk⟩; exact ⟨j,hk,hj.symm⟩
    rw [eqn]
    calc
      _ ≤ ∑ j ∈ neighborhood h i, (readers (cone w) j).card := card_biUnion_le
      _ ≤ ∑ _j ∈ neighborhood h i, budget n w := sum_le_sum (fun j _ => ih j)
      _ ≤ _ := by simpa [budget] using Nat.mul_le_mul_right (budget n w) (neighborhood_card_le h i)

private def source {n : ℕ} (h : Gap) (i : Fin n)
    (v : Fin (sourceTrialLength (n/h.val) (n%h.val) (i.val%h.val))) : Fin n :=
  ⟨i.val%h.val+h.val*v.val, actual_chain_prefix_lt n h.val h.property ⟨_,Nat.mod_lt _ h.property⟩ v⟩

private theorem source_mem {n : ℕ} (h : Gap) (i : Fin n) (v) : source h i v ∈ neighborhood h i := by
  simp [source,neighborhood,chainPositions,Nat.add_mod]

private def stat {m : ℕ} {α : Type} [LinearOrder α] (a : Fin m → α) (j : Fin m) : α :=
  a (Tuple.sort a j)

private theorem slot_pass {α : Type} [LinearOrder α] {n : ℕ} (a : Vector α n) (h : Gap) (i : Fin n) :
    (runPass a h).1[i.val] = stat (fun v => a[(source h i v).val])
      ⟨i.val/h.val, actual_chain_quotient_lt h.property i⟩ := by
  let x := fun v => a[(source h i v).val]
  have eqn : (insertionComparedExecution (List.ofFn x)).output = List.ofFn (x ∘ Tuple.sort x) := by
    rw [insertionComparedExecution_output]
    exact ((insertionExecution_perm _).trans ((Tuple.sort x).ofFn_comp_perm x).symm).eq_of_pairwise'
      (insertionExecution_sorted _) (Tuple.monotone_sort x).sortedLE_ofFn.pairwise
  simp only [runPass,Vector.getElem_ofFn]
  change (((insertionComparedExecution (List.ofFn x)).output)[i.val/h.val]?).getD _ = _
  rw [eqn,List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using actual_chain_quotient_lt h.property i)]
  simp [stat,x]

private theorem measurable_stat {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (f : Fin m → Ω → ℝ) (mf : ∀ k, Measurable (f k)) (j : Fin m) :
    Measurable (fun t => stat (fun k => f k t) j) := by
  classical
  intro S mS
  let X := fun t k => f k t
  have eqn : (fun t => stat (X t) j) ⁻¹' S = ⋃ σ : Equiv.Perm (Fin m),
      {t | Monotone (X t ∘ σ)} ∩ (f (σ j)) ⁻¹' S := by
    ext t
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro ht
      exact ⟨Tuple.sort (X t),Tuple.monotone_sort (X t),ht⟩
    · rintro ⟨σ,hm,hs⟩
      have e := congrFun (Tuple.unique_monotone (Tuple.monotone_sort (X t)) hm) j
      change (X t ∘ Tuple.sort (X t)) j ∈ S
      rw [e]; exact hs
  change MeasurableSet ((fun t => stat (X t) j) ⁻¹' S)
  rw [eqn]
  refine MeasurableSet.iUnion (fun σ => MeasurableSet.inter ?_ (mf _ mS))
  have mono : {t | Monotone (X t ∘ σ)} = ⋂ i : Fin m, ⋂ k : Fin m, ⋂ (_ : i ≤ k),
      {t | f (σ i) t ≤ f (σ k) t} := by ext t; simp [Monotone,X]
  rw [mono]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    measurableSet_le (mf _) (mf _)

theorem measurable_slot {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (w : PositiveWord)
    (a : Ω → Vector ℝ n) (ma : ∀ i : Fin n, Measurable (fun t => (a t)[i.val])) (i : Fin n) :
    Measurable (fun t => (runWord (a t) w).1[i.val]) := by
  induction w generalizing a i with
  | nil => exact ma i
  | cons h w ih =>
    apply ih (fun t => (runPass (a t) h).1)
    intro k
    simp_rw [slot_pass]
    exact measurable_stat _ (fun v => ma (source h k v)) _

theorem slot_congr {α : Type} [LinearOrder α] {n : ℕ} (w : PositiveWord)
    (a b : Vector α n) (i : Fin n) (agree : ∀ k ∈ cone w i, a[k.val] = b[k.val]) :
    (runWord a w).1[i.val] = (runWord b w).1[i.val] := by
  induction w generalizing a b i with
  | nil => exact agree i (by simp [cone])
  | cons h w ih =>
    apply ih (runPass a h).1 (runPass b h).1 i
    intro j hj
    rw [slot_pass,slot_pass]
    have eqn : (fun v => a[(source h j v).val]) = (fun v => b[(source h j v).val]) := by
      funext v
      exact agree _ (mem_biUnion.mpr ⟨j,hj,source_mem h j v⟩)
    rw [eqn]

theorem slot_origin {α : Type} [LinearOrder α] {n : ℕ} (w : PositiveWord)
    (a : Vector α n) (i : Fin n) : ∃ k ∈ cone w i, (runWord a w).1[i.val] = a[k.val] := by
  induction w generalizing a i with
  | nil => exact ⟨i,by simp [cone],rfl⟩
  | cons h w ih =>
    obtain ⟨j,hj,he⟩ := ih (runPass a h).1 i
    rw [slot_pass] at he
    exact ⟨_,mem_biUnion.mpr ⟨j,hj,source_mem h j _⟩,he⟩

private def extend {n : ℕ} (s : Finset (Fin n)) (v : s → ℝ) : Vector ℝ n :=
  Vector.ofFn fun i => if hi : i ∈ s then v ⟨i,hi⟩ else 0

/-- Run the ordinary executable on an extension of just the supplied local values. -/
def selector {n : ℕ} (w : PositiveWord) (i : Fin n) (v : cone w i → ℝ) : ℝ :=
  (runWord (extend (cone w i) v) w).1[i.val]

theorem measurable_selector {n : ℕ} (w : PositiveWord) (i : Fin n) :
    Measurable (selector w i) := by
  apply measurable_slot
  intro k
  by_cases hk : k ∈ cone w i
  · simpa [extend,hk] using (measurable_pi_apply (⟨k,hk⟩ : cone w i) :
      Measurable (fun v : cone w i → ℝ => v ⟨k,hk⟩))
  · simp [extend,hk]

theorem selector_origin {n : ℕ} (w : PositiveWord) (i : Fin n) (v : cone w i → ℝ) :
    ∃ k, selector w i v = v k := by
  obtain ⟨k,hk,eqn⟩ := slot_origin w (extend (cone w i) v) i
  exact ⟨⟨k,hk⟩,by simpa [selector,extend,hk] using eqn⟩

theorem selector_read {n : ℕ} (w : PositiveWord) (i : Fin n) (x : Fin n → ℝ) :
    selector w i (fun k => x k) = (runWord (Vector.ofFn x) w).1[i.val] := by
  apply slot_congr
  intro k hk
  simp [extend,hk]

open scoped unitInterval

private theorem selector_read_uniform {n : ℕ} (w : PositiveWord) (i : Fin n) (z : Fin n → I) :
    selector w i (fun j => (z j : ℝ)) = (runWord (Vector.ofFn fun j => (z j : ℝ)) w).1[i.val] :=
  selector_read w i (fun j => (z j : ℝ))

/-- All terms in the integral are comparisons of values read from the actual vector
after the given prefix. `B` can use the exact finite neighborhoods on both sides. -/
theorem executed_chain_inversions {n g B : ℕ} (w : PositiveWord) (hB : 0 < B)
    (res : Fin n → Fin g) (hin : ∀ i : Fin n, (cone w i).card ≤ B)
    (hout : ∀ j : Fin n, (readers (cone w) j).card ≤ B) (many : 8*g*B^3 ≤ n) :
    (n:ℝ)^2 ≤ 128*(g:ℝ)*B*
      ∫ u : Fin n → I, ∑ p ∈ (univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ res p.1 = res p.2),
        ({z : Fin n → I | (runWord (Vector.ofFn fun i => (z i : ℝ)) w).1[p.2.val] <
          (runWord (Vector.ofFn fun i => (z i : ℝ)) w).1[p.1.val]} : Set (Fin n → I)).indicator 1 u
          ∂(Measure.pi fun _ : Fin n => (volume : Measure I)) := by
  have e := BinnedMedianInversions.uniform_selector_chain hB res (cone w) hin hout
    (by simpa using many) (selector w) (measurable_selector w) (selector_origin w)
  simpa only [Fintype.card_fin,selector_read_uniform] using e

theorem budget_pos {n : ℕ} (hn : 0 < n) (w : PositiveWord) : 0 < budget n w := by
  induction w with
  | nil => exact Nat.zero_lt_one
  | cons h w ih =>
    let i : Fin n := ⟨0,hn⟩
    have mem : i ∈ neighborhood h i := by simp [neighborhood, chainPositions]
    exact Nat.mul_pos ((card_pos.mpr ⟨i,mem⟩).trans_le (neighborhood_card_le h i)) ih

/-- Uniform product-input bound for an ordinary gap `g` after any fixed word.
The simple width estimate counts possible dependency paths, including overlaps. -/
theorem executed_prefix_inversions {n g : ℕ} (hn : 0 < n) (hg : 0 < g) (w : PositiveWord)
    (many : 8*g*(budget n w)^3 ≤ n) :
    (n:ℝ)^2 ≤ 128*(g:ℝ)*(budget n w)*
      ∫ u : Fin n → I, ∑ p ∈ (univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ p.1.val%g = p.2.val%g),
        ({z : Fin n → I | (runWord (Vector.ofFn fun i => (z i : ℝ)) w).1[p.2.val] <
          (runWord (Vector.ofFn fun i => (z i : ℝ)) w).1[p.1.val]} : Set (Fin n → I)).indicator 1 u
          ∂(Measure.pi fun _ : Fin n => (volume : Measure I)) := by
  let res := fun i : Fin n => (⟨i.val%g, Nat.mod_lt _ hg⟩ : Fin g)
  simpa [res,Fin.ext_iff] using executed_chain_inversions w (budget_pos hn w) res
    (cone_card_le w) (readers_card_le w) many

#print axioms executed_prefix_inversions
end Shellsort.PrefixSlotSelectors
