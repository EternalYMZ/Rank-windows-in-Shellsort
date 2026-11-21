import Shellsort.MedianConeInversion
import Shellsort.DisjointConeBins
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-! Turning the ordered-pair counting certificate into strict inversions of
finite families of local selectors. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators
namespace Shellsort.BinnedMedianInversions
open DisjointConeBins MedianConeInversion

variable {α ι : Type*} [Fintype α] [LinearOrder α] [DecidableEq ι]

def goodOriented {g B : ℕ} (grp : α → Fin g × Fin (4*B)) (C : α → Finset ι) :
    Finset (α × α) := by
  classical
  exact univ.filter fun p => p.1 < p.2 ∧ grp p.1 = grp p.2 ∧ Disjoint (C p.1) (C p.2)

theorem oriented_count {g B : ℕ} (grp : α → Fin g × Fin (4*B)) (C : α → Finset ι)
    (nonempty : ∀ i, (C i).Nonempty)
    (fanin : ∀ i, (C i).card ≤ B) (fanout : ∀ k, (readers C k).card ≤ B)
    (many : 8*g*B^3 ≤ Fintype.card α) :
    (Fintype.card α)^2 ≤ 16*g*B*(goodOriented grp C).card := by
  classical
  let N := fun i => fiber grp (grp i) \ overlap C i
  let Q := univ.filter (fun p : α × α => p.2 ∈ N p.1)
  have memN (i j : α) : j ∈ N i ↔ grp i = grp j ∧ Disjoint (C i) (C j) := by
    simp [N, fiber, overlap_iff, Finset.disjoint_left, eq_comm]
  have eqCount : Q.card = ∑ i, (N i).card := by
    change (univ.filter (fun p : α × α => p.2 ∈ N p.1)).card = _
    rw [Finset.card_filter, Fintype.sum_prod_type]
    simp
  have src := disjoint_in_bins grp C fanin fanout many
  change _ ≤ 8*g*B* ∑ i, (N i).card at src
  rw [← eqCount] at src
  let asc := goodOriented grp C
  have cover : Q ⊆ asc ∪ asc.image Prod.swap := by
    intro p hp
    have cond := (memN p.1 p.2).1 ((mem_filter.1 hp).2)
    rcases lt_trichotomy p.1 p.2 with h|e|h
    · exact mem_union_left _ (by simpa [asc,goodOriented] using And.intro h cond)
    · have dis := cond.2
      rw [e] at dis
      obtain ⟨k,hk⟩ := nonempty p.2
      exact False.elim (Finset.disjoint_left.1 dis hk hk)
    · refine Finset.mem_union_right _ (mem_image.mpr ⟨p.swap,?_,rfl⟩)
      simpa [asc,goodOriented] using And.intro h (And.intro cond.1.symm cond.2.symm)
  have bound : Q.card ≤ asc.card+asc.card :=
    (Finset.card_le_card cover).trans ((Finset.card_union_le ..).trans
      (Nat.add_le_add_left card_image_le _))
  change _ ≤ 16*g*B*asc.card
  calc
    _ ≤ _ := src
    _ ≤ 8*g*B*(asc.card+asc.card) := Nat.mul_le_mul_left _ bound
    _ = _ := by ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem expected_inversions {g B : ℕ} (grp : α → Fin g × Fin (4*B))
    (C : α → Finset ι) (fanin : ∀ i, (C i).card ≤ B)
    (fanout : ∀ k, (readers C k).card ≤ B) (many : 8*g*B^3 ≤ Fintype.card α)
    (X : ι → Ω → ℝ) (ind : iIndepFun X P) (mx : ∀ i, Measurable (X i))
    (f : (i : α) → (C i → ℝ) → ℝ) (mf : ∀ i, Measurable (f i))
    (sel : ∀ i v, ∃ k, f i v = v k)
    (bound : ∀ k x y, x ≤ y → P.real (X k ⁻¹' Icc x y) ≤ y-x)
    (t : α → ℝ)
    (upper : ∀ i, 1/2 ≤ P.real {w | t i < f i (fun j => X j w)})
    (lower : ∀ i, 1/2 ≤ P.real {w | f i (fun j => X j w) ≤ t i})
    (bins : ∀ i j, grp i = grp j → (B:ℝ)*|t j - t i| ≤ 1/4) :
    (Fintype.card α:ℝ)^2 ≤ 128*(g:ℝ)*B*
       ∫ w, ∑ p ∈ goodOriented grp C,
          ({z | f p.2 (fun i => X i z) < f p.1 (fun i => X i z)} : Set Ω).indicator 1 w ∂P := by
  classical
  have src := oriented_count grp C (fun i => by
    obtain ⟨k,_⟩ := sel i (fun _ => 0)
    exact ⟨k,k.property⟩) fanin fanout many
  have sc : (Fintype.card α:ℝ)^2 ≤ 16*(g:ℝ)*B*((goodOriented grp C).card:ℝ) := by
    exact_mod_cast src
  have pair := mean_inversions_on_pairs (goodOriented grp C) X ind mx C f mf sel bound t upper lower
    (fun p hp => (show p.1 < p.2 ∧ grp p.1 = grp p.2 ∧ Disjoint (C p.1) (C p.2) from
      by simpa [goodOriented] using hp).2.2)
    (fun p hp => by
      have h : p.1 < p.2 ∧ grp p.1 = grp p.2 ∧ Disjoint (C p.1) (C p.2) := by
        simpa [goodOriented] using hp
      exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (fanin _)) (abs_nonneg _)).trans
        (bins _ _ h.2.1))
  have nn : 0 ≤ (128:ℝ)*g*B := by positivity
  nlinarith only [sc, mul_le_mul_of_nonneg_left pair nn]

/-- Source bounds and supports produce the quantile labels internally. -/
theorem selector_chain_inversions {g B : ℕ} (pos : 0 < B) (res : α → Fin g)
    (C : α → Finset ι) (fanin : ∀ i, (C i).card ≤ B)
    (fanout : ∀ k, (readers C k).card ≤ B) (many : 8*g*B^3 ≤ Fintype.card α)
    (X : ι → Ω → ℝ) (ind : iIndepFun X P) (mx : ∀ i, Measurable (X i))
    (support : ∀ k w, X k w ∈ Set.Icc (0:ℝ) 1)
    (bound : ∀ k a b, a ≤ b → P.real (X k ⁻¹' Set.Icc a b) ≤ b-a)
    (f : (i : α) → (C i → ℝ) → ℝ) (mf : ∀ i, Measurable (f i))
    (sel : ∀ i v, ∃ k, f i v = v k) :
    (Fintype.card α:ℝ)^2 ≤ 128*(g:ℝ)*B*
       ∫ w, ∑ p ∈ (univ.filter fun p : α × α => p.1 < p.2 ∧ res p.1 = res p.2),
          ({z | f p.2 (fun i => X i z) < f p.1 (fun i => X i z)} : Set Ω).indicator 1 w ∂P := by
  classical
  let Y := fun i w => f i (fun j => X j w)
  have mY (i : α) : Measurable (Y i) := (mf i).comp (Measurable.of_eval (fun j => mx j.val))
  have selector (i : α) (w : Ω) : ∃ k ∈ C i, Y i w = X k w := by
    obtain ⟨k,h⟩ := sel i (fun j => X j w)
    exact ⟨k,k.property,h⟩
  have inUnit (i : α) (w : Ω) : Y i w ∈ Set.Icc (0:ℝ) 1 := by
    obtain ⟨k,_,he⟩ := selector i w
    rw [he]; exact support _ _
  have threshold (i : α) := exists_median (mY i) (C i).card (inUnit i)
    (fun _ _ h => interval_of_selector X (C i) (Y i) (selector i) (fun k _ => bound k) h)
  choose t unit masses using threshold
  have ltOne (i : α) : t i < 1 := by
    apply lt_of_le_of_ne (unit i).2
    intro eq
    have emptySet : (Y i ⁻¹' Ioi (t i)) = ∅ := by
      ext w
      change (t i < Y i w) ↔ False
      rw [eq]; exact iff_false_intro (not_lt.mpr (inUnit i w).2)
    have m := (masses i).2
    rw [emptySet] at m
    norm_num at m
  let M : ℕ := 4*B
  have mp : (0:ℝ) < M := by dsimp [M]; positivity
  let bin (i : α) : Fin M := ⟨⌊(M:ℝ)*t i⌋₊, by
    apply (Nat.floor_lt (mul_nonneg mp.le (unit i).1)).2
    nlinarith only [mul_lt_mul_of_pos_left (ltOne i) mp]⟩
  let grp := fun i => (res i,bin i)
  have close (i j : α) (eq : grp i = grp j) : (B:ℝ)*|t j - t i| ≤ 1/4 := by
    have bins : ⌊(M:ℝ)*t i⌋₊ = ⌊(M:ℝ)*t j⌋₊ := congrArg Fin.val (congrArg Prod.snd eq)
    have left := Nat.floor_le (mul_nonneg mp.le (unit i).1)
    have right := Nat.floor_le (mul_nonneg mp.le (unit j).1)
    have li := Nat.lt_floor_add_one ((M:ℝ)*t i)
    have lj := Nat.lt_floor_add_one ((M:ℝ)*t j)
    rw [bins] at left li
    have dist : (M:ℝ)*|t j-t i| ≤ 1 := by
      rw [←abs_of_pos mp, ←abs_mul, abs_le]
      constructor <;> nlinarith only [left,right,li,lj]
    have mval : (M:ℝ)=4*B := by simp [M]
    rw [mval] at dist
    linarith
  have base := expected_inversions grp C fanin fanout many X ind mx f mf sel bound t
    (fun i => (masses i).2.ge) (fun i => (masses i).1.ge) close
  let allPairs := univ.filter (fun p : α × α => p.1 < p.2 ∧ res p.1 = res p.2)
  have sub : goodOriented grp C ⊆ allPairs := by
    intro p hp
    obtain ⟨lt,e,_⟩ : p.1 < p.2 ∧ grp p.1 = grp p.2 ∧ Disjoint (C p.1) (C p.2) := by
      simpa [goodOriented] using hp
    exact mem_filter.mpr ⟨mem_univ _,lt,congrArg Prod.fst e⟩
  let val := fun p : α × α => ({z | Y p.2 z < Y p.1 z} : Set Ω).indicator (1:Ω → ℝ)
  have integr (p : α × α) : Integrable (val p) P :=
    (integrable_const (1:ℝ)).indicator (measurableSet_lt (mY _) (mY _))
  apply base.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change (∫ w, ∑ p ∈ goodOriented grp C, val p w ∂P) ≤ ∫ w, ∑ p ∈ allPairs, val p w ∂P
  rw [integral_finsetSum _ (fun p _ => integr p),integral_finsetSum _ (fun p _ => integr p)]
  apply sum_le_sum_of_subset_of_nonneg sub
  intro p _ _
  exact integral_nonneg (fun w => Set.indicator_nonneg (fun _ _ => zero_le_one) _)

open scoped unitInterval

/-- Uniform source model. Every function sees exactly its indicated coordinates
and returns one of their values; no marginal law is assumed for the outputs. -/
theorem uniform_selector_chain [Fintype ι] {g B : ℕ} (pos : 0 < B) (res : α → Fin g)
    (C : α → Finset ι) (fanin : ∀ i, (C i).card ≤ B)
    (fanout : ∀ k, (readers C k).card ≤ B) (many : 8*g*B^3 ≤ Fintype.card α)
    (f : (i : α) → (C i → ℝ) → ℝ) (mf : ∀ i, Measurable (f i))
    (sel : ∀ i v, ∃ k, f i v = v k) :
    (Fintype.card α:ℝ)^2 ≤ 128*(g:ℝ)*B*
       ∫ w : ι → I, ∑ p ∈ (univ.filter fun p : α × α => p.1 < p.2 ∧ res p.1 = res p.2),
          ({z : ι → I | f p.2 (fun i => (z i : ℝ)) < f p.1 (fun i => (z i : ℝ))} : Set (ι → I)).indicator 1 w
        ∂(Measure.pi fun _ : ι => (volume : Measure I)) := by
  let U : ι → Measure I := fun _ => volume
  let X := fun (k : ι) (w : ι → I) => (w k : ℝ)
  have ind : iIndepFun X (Measure.pi U) :=
    iIndepFun_pi (X:=fun _ (x : I) => (x:ℝ)) (fun _ => measurable_subtype_coe.aemeasurable)
  apply selector_chain_inversions pos res C fanin fanout many X ind
    (fun k => measurable_subtype_coe.comp (measurable_pi_apply k)) (fun k w => (w k).property)
    _ f mf sel
  intro k a b ab
  have mp : MeasurePreserving (X k) (Measure.pi U) (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    unitInterval.measurePreserving_coe.comp (measurePreserving_eval U k)
  change ((Measure.pi U) ((X k) ⁻¹' Set.Icc a b)).toReal ≤ b-a
  rw [←Measure.map_apply mp.measurable measurableSet_Icc, mp.map_eq]
  calc
    _ ≤ (volume (Set.Icc a b)).toReal :=
      ENNReal.toReal_mono (by simp [Real.volume_Icc]) (Measure.restrict_le_self _)
    _ = b-a := by simp [Real.volume_Icc, sub_nonneg.mpr ab]

#print axioms uniform_selector_chain
end Shellsort.BinnedMedianInversions
