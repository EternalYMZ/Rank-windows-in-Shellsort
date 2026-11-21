import Shellsort.OnePassFluctuationLower
import Shellsort.ComparisonWordLower
import Shellsort.WordShiftDistance

noncomputable section
namespace Shellsort.StrictSuffixTransportLower
open HarvestBlockIteration

theorem distance_le_cost {n H : ℕ} (p : RankPlacement n) (v : PositiveWord)
    (cap : ∀ g ∈ v, g.val ≤ H) :
    wordShiftDistance p v ≤ (H:ℝ)*ordinaryWordComparisons p v := by
  induction v generalizing p with
  | nil => simp [ordinaryWordComparisons,wordShiftDistance]
  | cons k ks ih =>
    have c := gapComparisonCost_lower p k.val k.property
    have first : (k.val:ℝ) * (gapInsertionCost p k.val k.property : ℝ) ≤
      (H:ℝ)*(gapComparisonCost p k.val k.property:ℝ) := by
      gcongr
      · exact_mod_cast cap k (List.mem_cons_self ..)
    have rem := ih (gapSort p k.val) (fun g hg => cap g (List.mem_cons_of_mem _ hg))
    simpa [wordShiftDistance,ordinaryWordComparisons,mul_add] using add_le_add first rem

theorem suffix_fluctuation_lower {n h : ℕ} (hh : 2≤h) (fits : h≤n) (v : PositiveWord)
    (cap : ∀ g ∈ v, g.val ≤ h) (last : (v.map Subtype.val).getLast? = some 1) :
    (n:ℝ)*Real.sqrt ((n:ℝ)/h)/2048 ≤
      uniformAverage (fun p : RankPlacement n => (ordinaryWordComparisons (gapSort p h) v:ℝ)) := by
  have point (p : RankPlacement n) : footrule (gapSort p h) ≤
      (2*(h:ℝ))*(ordinaryWordComparisons (gapSort p h) v:ℝ) := by
    have base := footrule_le_wordShiftDistance (gapSort p h) v
    rw [ComparisonAudit.sorted_last _ _ last] at base
    have zero : footrule (Equiv.refl (Fin n)) = 0 := by simp [footrule,transport]
    rw [zero,zero_add] at base
    linarith [distance_le_cost (gapSort p h) v cap]
  have avg := uniformAverage_mono _ _ point
  rw [uniformAverage_const_mul] at avg
  have both := (uniform_onePass_footrule_fluctuation_lower n h hh fits).trans avg
  have hpos : (0:ℝ)<h := by exact_mod_cast (by omega : 0<h)
  have root : Real.sqrt ((n:ℝ)*h) = Real.sqrt ((n:ℝ)/h)*h := by
    calc
      _ = Real.sqrt (((n:ℝ)/h)*(h:ℝ)^2) := by congr 1; field_simp
      _ = _ := by rw [Real.sqrt_mul (by positivity),Real.sqrt_sq hpos.le]
  rw [root] at both
  apply (mul_le_mul_iff_right₀ hpos).mp
  linarith

#print axioms suffix_fluctuation_lower
end Shellsort.StrictSuffixTransportLower
