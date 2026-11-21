import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! Disjoint local selectors and close medians force genuine inversions. -/
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace Shellsort.MedianConeInversion

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Each selected value is one of the input values in its finite source. -/
theorem interval_of_selector (X : ι → Ω → ℝ) (S : Finset ι) (Y : Ω → ℝ)
    (sel : ∀ w, ∃ i ∈ S, Y w = X i w)
    (bound : ∀ i ∈ S, ∀ a b : ℝ, a ≤ b → P.real (X i ⁻¹' Icc a b) ≤ b-a)
    {a b : ℝ} (ab : a ≤ b) :
    P.real (Y ⁻¹' Icc a b) ≤ (S.card:ℝ)*(b-a) := by
  calc
    _ ≤ P.real (⋃ i ∈ S, X i ⁻¹' Icc a b) := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro w hw
      obtain ⟨i,hi,he⟩ := sel w
      exact mem_iUnion₂.mpr ⟨i,hi,by simpa only [mem_preimage,←he] using hw⟩
    _ ≤ ∑ i ∈ S, P.real (X i ⁻¹' Icc a b) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _ ∈ S, (b-a) := Finset.sum_le_sum fun i hi => bound i hi a b ab
    _ = _ := by simp; ring

/-- Interval concentration and bounded support give an exact median in [0,1]. -/
theorem exists_median {Y : Ω → ℝ} (mY : Measurable Y) (B : ℕ)
    (unit : ∀ w, Y w ∈ Icc 0 1)
    (interval : ∀ x y, x ≤ y → P.real (Y ⁻¹' Icc x y) ≤ B*(y-x)) :
    ∃ t ∈ Icc (0:ℝ) 1, P.real (Y ⁻¹' Iic t) = 1/2 ∧ P.real (Y ⁻¹' Ioi t) = 1/2 := by
  let F := fun x => P.real (Y ⁻¹' Iic x)
  have mono : Monotone F := fun x y h => measureReal_mono (preimage_mono (Iic_subset_Iic.mpr h))
  have inc (x y : ℝ) (h : x ≤ y) : F y - F x ≤ B*(y-x) := by
    have sub : Y ⁻¹' Iic y ⊆ (Y ⁻¹' Iic x) ∪ (Y ⁻¹' Icc x y) := by
      intro w hw
      by_cases hwx : Y w ≤ x
      · exact Or.inl hwx
      · exact Or.inr ⟨(lt_of_not_ge hwx).le,hw⟩
    have u := (measureReal_mono (μ:=P) sub).trans (measureReal_union_le _ _)
    dsimp [F]
    linarith [interval x y h]
  have lip : LipschitzWith (B:NNReal) F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq,NNReal.coe_natCast]
    rcases le_total x y with xy|yx
    · rw [abs_of_nonpos (sub_nonpos.mpr (mono xy)),abs_of_nonpos (sub_nonpos.mpr xy)]
      linarith [inc x y xy]
    · rw [abs_of_nonneg (sub_nonneg.mpr (mono yx)),abs_of_nonneg (sub_nonneg.mpr yx)]
      exact inc y x yx
  have F0 : F 0 = 0 := by
    have sub : Y ⁻¹' Iic 0 ⊆ Y ⁻¹' Icc 0 0 := fun w hw => ⟨(unit w).1,hw⟩
    have cap := (measureReal_mono (μ:=P) sub).trans (interval 0 0 le_rfl)
    dsimp [F]
    exact le_antisymm (by simpa using cap) measureReal_nonneg
  have F1 : F 1 = 1 := by
    have full : Y ⁻¹' Iic 1 = univ := eq_univ_of_forall fun w => (unit w).2
    simp [F,full]
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (show (0:ℝ)≤1 by norm_num) lip.continuous.continuousOn
    (show (1/2:ℝ) ∈ Icc (F 0) (F 1) by rw [F0,F1]; constructor <;> norm_num)
  refine ⟨t,ht,he,?_⟩
  have comp : (Y ⁻¹' Iic t)ᶜ = Y ⁻¹' Ioi t := by
    ext w
    exact show (¬ Y w ≤ t) ↔ t < Y w from not_le
  rw [←comp, measureReal_compl (mY measurableSet_Iic), probReal_univ]
  change 1 - F t = 1/2
  rw [he]; norm_num

/-- The threshold event is a subset of a strict inversion. -/
theorem nearby_median_inversion {Y Z : Ω → ℝ} (ind : IndepFun Y Z P)
    {a b B : ℝ} (medY : 1/2 ≤ P.real (Y ⁻¹' Ioi a))
    (medZ : 1/2 ≤ P.real (Z ⁻¹' Iic b))
    (interval : ∀ x y, x ≤ y → P.real (Y ⁻¹' Icc x y) ≤ B*(y-x))
    (close : B*|b-a| ≤ 1/4) :
    1/8 ≤ P.real {w | Z w < Y w} := by
  have tail : 1/4 ≤ P.real (Y ⁻¹' Ioi b) := by
    by_cases ab : a ≤ b
    · have sub : Y ⁻¹' Ioi a ⊆ (Y ⁻¹' Ioi b) ∪ (Y ⁻¹' Icc a b) := by
        intro w hw
        by_cases h : b < Y w
        · exact Or.inl h
        · exact Or.inr ⟨le_of_lt hw, le_of_not_gt h⟩
      rw [abs_of_nonneg (sub_nonneg.mpr ab)] at close
      linarith [measureReal_mono (μ:=P) sub,
        measureReal_union_le (μ:=P) (Y ⁻¹' Ioi b) (Y ⁻¹' Icc a b),interval a b ab]
    · have mono := measureReal_mono (μ:=P) (preimage_mono (Ioi_subset_Ioi (le_of_not_ge ab)))
      linarith [show P.real (Y ⁻¹' Ioi a) ≤ P.real (Y ⁻¹' Ioi b) from mono]
  have joint : P.real ((Y ⁻¹' Ioi b) ∩ (Z ⁻¹' Iic b)) =
      P.real (Y ⁻¹' Ioi b)*P.real (Z ⁻¹' Iic b) := by
    simp only [measureReal_def, ind.measure_inter_preimage_eq_mul _ _ measurableSet_Ioi
      measurableSet_Iic, ENNReal.toReal_mul]
  have sub : (Y ⁻¹' Ioi b) ∩ (Z ⁻¹' Iic b) ⊆ {w | Z w < Y w} :=
    fun w hw => show Z w < Y w from lt_of_le_of_lt (show Z w ≤ b from hw.2) (show b < Y w from hw.1)
  calc
    (1/8:ℝ) = (1/4:ℝ)*(1/2:ℝ) := by norm_num
    _ ≤ _ := mul_le_mul tail medZ (by norm_num) measureReal_nonneg
    _ = _ := joint.symm
    _ ≤ _ := measureReal_mono sub

/-- Measurable computations on disjoint independent sources may be nonlinear. -/
theorem disjoint_selector_inversion (X : ι → Ω → ℝ) (ind : iIndepFun X P)
    (mx : ∀ i, Measurable (X i)) (S T : Finset ι) (apart : Disjoint S T)
    (f : (S → ℝ) → ℝ) (g : (T → ℝ) → ℝ) (mf : Measurable f) (mg : Measurable g)
    (sel : ∀ v, ∃ i, f v = v i)
    (bound : ∀ i ∈ S, ∀ a b : ℝ, a ≤ b → P.real (X i ⁻¹' Icc a b) ≤ b-a)
    (a b : ℝ)
    (ma : 1/2 ≤ P.real {w | a < f (fun i => X i w)})
    (mb : 1/2 ≤ P.real {w | g (fun i => X i w) ≤ b})
    (close : (S.card:ℝ)*|b-a| ≤ 1/4) :
    1/8 ≤ P.real {w | g (fun i => X i w) < f (fun i => X i w)} := by
  let Y := fun w => f (fun i => X i w)
  let Z := fun w => g (fun i => X i w)
  have sel' (w : Ω) : ∃ i ∈ S, Y w = X i w := by
    obtain ⟨i,hi⟩ := sel (fun i => X i w)
    exact ⟨i,i.property,hi⟩
  have independent : IndepFun Y Z P := (ind.indepFun_finset S T apart mx).comp mf mg
  apply nearby_median_inversion independent ma mb _ close
  exact fun _ _ h => interval_of_selector X S Y sel' bound h

/-- Integration of the true finite sum of comparison indicators; only the
two outputs in each specified pair must be independent. -/
theorem mean_inversions_on_pairs {α : Type*} (pairs : Finset (α × α))
    (X : ι → Ω → ℝ) (ind : iIndepFun X P) (mx : ∀ i, Measurable (X i))
    (cone : α → Finset ι) (f : (i : α) → (cone i → ℝ) → ℝ)
    (mf : ∀ i, Measurable (f i)) (sel : ∀ i v, ∃ j, f i v = v j)
    (bound : ∀ i x y, x ≤ y → P.real (X i ⁻¹' Icc x y) ≤ y-x)
    (t : α → ℝ)
    (upper : ∀ i, 1/2 ≤ P.real {w | t i < f i (fun j => X j w)})
    (lower : ∀ i, 1/2 ≤ P.real {w | f i (fun j => X j w) ≤ t i})
    (apart : ∀ p ∈ pairs, Disjoint (cone p.1) (cone p.2))
    (close : ∀ p ∈ pairs, ((cone p.1).card:ℝ)*|t p.2 - t p.1| ≤ 1/4) :
    (pairs.card:ℝ)/8 ≤ ∫ w, ∑ p ∈ pairs,
        ({z | f p.2 (fun i => X i z) < f p.1 (fun i => X i z)} : Set Ω).indicator 1 w ∂P := by
  classical
  let Y := fun i w => f i (fun j => X j w)
  have hm (i : α) : Measurable (Y i) := (mf i).comp (Measurable.of_eval (fun j => mx j.val))
  let event := fun p : α × α => {w | Y p.2 w < Y p.1 w}
  have he (p) : MeasurableSet (event p) := measurableSet_lt (hm _) (hm _)
  change (pairs.card:ℝ)/8 ≤ ∫ w, ∑ p ∈ pairs, (event p).indicator 1 w ∂P
  rw [integral_finsetSum pairs (f:=fun p => (event p).indicator (1 : Ω → ℝ))
    (fun p _ => (integrable_const (1:ℝ)).indicator (he p))]
  calc
    (pairs.card:ℝ)/8 = ∑ _ ∈ pairs, (1/8:ℝ) := by simp; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [integral_indicator_one (he p)]
      exact disjoint_selector_inversion X ind mx (cone p.1) (cone p.2) (apart p hp)
        _ _ (mf _) (mf _) (sel _) (fun i _ => bound i) (t p.1) (t p.2)
        (upper _) (lower _) (close p hp)

#print axioms exists_median
#print axioms mean_inversions_on_pairs
end Shellsort.MedianConeInversion
