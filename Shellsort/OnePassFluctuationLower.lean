import Shellsort.OnePassLowerGeometry
import Shellsort.BernoulliAbsoluteLower

/-! First-pass fluctuation under the uniform permutation law. For three
ordinary insertion passes this resolves the noncoprime and small-second-gap
branches, with a common numerical constant. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

theorem uniform_onePass_footrule_fluctuation_lower (n h : ℕ) (hh : 2 ≤ h) (hhn : h ≤ n) :
    (n:ℝ)*Real.sqrt ((n:ℝ)*h)/1024 ≤
      uniformAverage (fun p : RankPlacement n => footrule (gapSort p h)) := by
  have hp : 0 < h := by omega
  by_cases hlen : 2*h ≤ n
  · rw [uniform_onePass_footrule_by_original_positions]
    have perTag (i : Fin n) :
        Real.sqrt ((n:ℝ)*h)/1024 ≤ uniformAverage (fun p : RankPlacement n =>
            |((gapSort p h (p.symm i)).val : ℝ) - ((p.symm i).val : ℝ)|) := by
      have central (t : ℝ) (htl : 1/4 ≤ t) (htu : t ≤ 3/4) :
          Real.sqrt ((n:ℝ)*h)/512 ≤
            mean (bernoulliVectorWeight t n) (fun z => |firstPassBitDisplacement h i z|) := by
        have source := bernoulliWeighted_abs_lower t (↑(i.val % h) : ℝ)
          (firstPassCoefficient h i) htl htu
        change Real.sqrt (∑ j : Fin n, firstPassCoefficient h i j ^ 2)/128 ≤
          mean (bernoulliVectorWeight t n) (fun z => |firstPassBitDisplacement h i z|) at source
        linarith [onePass_coefficient_norm_lower hh hlen i]
      have lower := uniform_onePass_tag_abs_lower_of_central hp i _ central
      linarith
    apply le_trans _ (Finset.sum_le_sum fun i _ => perTag i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_of_eq (by ring)
  · have hr : (2:ℝ) ≤ h := by exact_mod_cast hh
    have hn' : (n:ℝ) ≤ 2*h := by exact_mod_cast (le_of_lt (lt_of_not_ge hlen))
    have hrsq : Real.sqrt ((n:ℝ)*h) ≤ 2*(h:ℝ) := by
      apply (Real.sqrt_le_left (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hn' (Nat.cast_nonneg h), sq_nonneg (h:ℝ)]
    have drift := uniform_onePass_footrule_drift_lower n h hp hhn
    have scale : Real.sqrt ((n:ℝ)*h) ≤ 64*((h:ℝ)-1) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left scale (Nat.cast_nonneg n)]

/-- Only the large, coprime, genuinely two-pass probability input remains.
The coefficient c can be fixed once and for all, independently of the gaps. -/
theorem uniform_threePass_lower_of_coprime_fluctuation (n h g : ℕ)
    (hn : 4 ≤ n) (hh : 2 ≤ h) (hnH : h ≤ n) (hg : 0 < g)
    (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 1/2048)
    (two : n < h^2 → h < g^2 → Nat.Coprime h g →
       2*c*(n:ℝ)*min ((g:ℝ)*Real.sqrt h)
         (Real.sqrt g * Real.sqrt (Real.sqrt ((n:ℝ)*h))) ≤
       uniformAverage (fun p : RankPlacement n => footrule (gapSort (gapSort p h) g))) :
    c*(n:ℝ)*Real.sqrt n ≤ uniformAverage
        (fun p : RankPlacement n => (threePassInsertionCost p h g (by omega) hg : ℝ)) ∧
    c*(n:ℝ)*Real.sqrt n ≤ uniformAverage
        (fun p : RankPlacement n => (threePassComparisonCost p h g (by omega) hg : ℝ)) := by
  apply uniform_threePass_lower_of_checkpoint_estimates n h g hn (by omega) hg c hc (by linarith)
  · intro _ _
    apply le_trans _ (uniform_onePass_footrule_fluctuation_lower n h hh hnH)
    nlinarith [mul_le_mul_of_nonneg_right hc' (show 0 ≤ (n:ℝ)*Real.sqrt ((n:ℝ)*h) by positivity)]
  · exact two
  · intro _ _ ncp
    let d := Nat.gcd h g
    have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ (by omega)
    have hd : 2 ≤ d := by
      change ¬d = 1 at ncp
      omega
    have hdle : d ≤ n := (Nat.le_of_dvd (by omega : 0 < h) (Nat.gcd_dvd_left h g)).trans hnH
    apply le_trans _ (uniform_onePass_footrule_fluctuation_lower n d hd hdle)
    have dr : 1 ≤ (d:ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
    have roots : Real.sqrt (n:ℝ) ≤ Real.sqrt ((n:ℝ)*d) := by
      apply Real.sqrt_le_sqrt
      nlinarith [mul_le_mul_of_nonneg_left dr (Nat.cast_nonneg n)]
    nlinarith [mul_le_mul_of_nonneg_left roots (Nat.cast_nonneg n),
      mul_le_mul_of_nonneg_right hc' (show 0 ≤ (n:ℝ)*Real.sqrt n by positivity)]

/-- Finite unconditional lower bound for the union of the protected regions. -/
theorem uniform_threePass_lower_outside_large_coprime (n h g : ℕ)
    (hn : 4 ≤ n) (hh : 2 ≤ h) (hnH : h ≤ n) (hg : 0 < g)
    (covered : h^2 ≤ n ∨ g^2 ≤ h ∨ ¬Nat.Coprime h g) :
    (n:ℝ)*Real.sqrt n/2048 ≤ uniformAverage
        (fun p : RankPlacement n => (threePassInsertionCost p h g (by omega) hg : ℝ)) ∧
    (n:ℝ)*Real.sqrt n/2048 ≤ uniformAverage
        (fun p : RankPlacement n => (threePassComparisonCost p h g (by omega) hg : ℝ)) := by
  have result := uniform_threePass_lower_of_coprime_fluctuation n h g hn hh hnH hg (1/2048)
      (by norm_num) (by norm_num) (by
        intro large long cop
        rcases covered with small | short | no
        · omega
        · omega
        · contradiction)
  constructor <;> linarith [result.1, result.2]

end Shellsort
end
