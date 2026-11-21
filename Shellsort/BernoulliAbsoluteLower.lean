import Shellsort.BernoulliCounts

/-! An absolute-deviation lower bound for weighted sums of independent Bernoulli
bits. The center may be translated arbitrarily and the coefficients may have
either sign. All expectations below use an explicit finite product law. -/

noncomputable section
namespace Shellsort
open scoped BigOperators

private def centeredBits {n : ℕ} (t : ℝ) (c : Fin n → ℝ) (z : Fin n → Bool) : ℝ :=
  ∑ i, ((if z i then c i else 0) - t * c i)

private theorem centeredBits_cons {n : ℕ} (t : ℝ) (c : Fin (n+1) → ℝ)
    (b : Bool) (z : Fin n → Bool) :
    centeredBits t c (Fin.cons b z) =
      ((if b then c 0 else 0) - t*c 0) + centeredBits t (fun i => c i.succ) z := by
  simp only [centeredBits, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

private theorem average_head_bit {n : ℕ} (t : ℝ) (c : Fin (n+1) → ℝ) (f : ℝ → ℝ) :
    mean (bernoulliVectorWeight t (n+1)) (fun z => f (centeredBits t c z)) =
      mean (bernoulliVectorWeight t n) (fun z =>
        t * f ((c 0 - t*c 0) + centeredBits t (fun i => c i.succ) z) +
        (1-t) * f ((0 - t*c 0) + centeredBits t (fun i => c i.succ) z)) := by
  unfold mean
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, centeredBits_cons,
    bernoulliVectorWeight_cons, Fintype.sum_bool, bernoulliWeight, ite_true,
    Bool.false_eq_true, ite_false, mul_add, Finset.sum_add_distrib]
  apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intros <;> ring

private theorem average_scale {α : Type*} [Fintype α] (w f : α → ℝ) (a : ℝ) :
    mean w (fun z => a*f z) = a * mean w f := by
  simp only [mean, Finset.mul_sum, mul_left_comm]

/-- Mean, variance and a fourth-moment upper bound, obtained by exposing one
bit. The final estimate is uniform in the number of terms. -/
private theorem centeredBits_moments {n : ℕ} (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (c : Fin n → ℝ) :
    mean (bernoulliVectorWeight t n) (centeredBits t c) = 0 ∧
    mean (bernoulliVectorWeight t n) (fun z => (centeredBits t c z)^2) =
      t*(1-t)*(∑ i, (c i)^2) ∧
    mean (bernoulliVectorWeight t n) (fun z => (centeredBits t c z)^4) ≤
      (∑ i, (c i)^2)^2 := by
  induction n with
  | zero => simp [mean, centeredBits]
  | succ n ih =>
    let w := bernoulliVectorWeight t n
    let s := centeredBits t (fun i : Fin n => c i.succ)
    let A := ∑ i : Fin n, (c i.succ)^2
    let b := c 0
    let v := t*(1-t)
    have ⟨h1,h2,h4⟩ := ih (fun i => c i.succ)
    change mean w s = 0 at h1
    change mean w (fun z => (s z)^2) = v*A at h2
    change mean w (fun z => (s z)^4) ≤ A^2 at h4
    have hw : ∑ z, w z = 1 := bernoulliVectorWeight_sum t n
    have hv : 0 ≤ v := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
    have hv' : v ≤ 1/4 := by dsimp [v]; nlinarith [sq_nonneg (t-1/2)]
    have ha : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have B2 (x : ℝ) : t*((b-t*b)+x)^2+(1-t)*((0-t*b)+x)^2 = x^2+v*b^2 := by
      dsimp [v]; ring
    have B4 (x : ℝ) : t*((b-t*b)+x)^4+(1-t)*((0-t*b)+x)^4 =
        ((x^4+(6*v*b^2)*x^2)+(4*v*(1-2*t)*b^3)*x) + v*(1-3*v)*b^4 := by
      dsimp [v]; ring
    constructor
    · rw [show mean (bernoulliVectorWeight t (n+1)) (centeredBits t c) =
        _ from average_head_bit t c id]
      change mean w (fun z => t*((b-t*b)+s z)+(1-t)*((0-t*b)+s z)) = 0
      convert h1 using 2 with z
      ring
    constructor
    · rw [average_head_bit t c (fun x => x^2), Fin.sum_univ_succ]
      change mean w (fun z => t*((b-t*b)+s z)^2+(1-t)*((0-t*b)+s z)^2) = v*(b^2+A)
      simp only [B2, mean_add, mean_const w hw, h2]
      ring
    · rw [average_head_bit t c (fun x => x^4), Fin.sum_univ_succ]
      change mean w (fun z => t*((b-t*b)+s z)^4+(1-t)*((0-t*b)+s z)^4) ≤ (b^2+A)^2
      simp only [B4, mean_add, average_scale, mean_const w hw, h1, h2, mul_zero, add_zero]
      have hv2 : 6*v^2 ≤ 2 := by nlinarith [mul_nonneg hv (sub_nonneg.mpr hv')]
      have hcoeff : v*(1-3*v) ≤ 1 := by nlinarith [sq_nonneg v]
      nlinarith [mul_le_mul_of_nonneg_right hv2 (mul_nonneg (sq_nonneg b) ha),
        mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ b^4 by positivity)]

private theorem average_le {α : Type*} [Fintype α] {w f g : α → ℝ}
    (hw : ∀ i, 0 ≤ w i) (h : ∀ i, f i ≤ g i) : mean w f ≤ mean w g :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hw i)

/-- The clipping estimate used to convert the fourth moment into a lower
bound on the first absolute moment. -/
private theorem clip_square (q : ℝ) (hq : 0 ≤ q) (x : ℝ) :
    16*q^2*x^2 ≤ 64*q^3*|x| + x^4 := by
  by_cases hx : |x| ≤ 4*q
  · have h := mul_le_mul_of_nonneg_left hx (abs_nonneg x)
    rw [← sq, sq_abs] at h
    nlinarith [mul_le_mul_of_nonneg_left h (show 0 ≤ 16*q^2 by positivity),
      sq_nonneg (x^2)]
  · have h := mul_self_le_mul_self (by positivity : 0 ≤ 4*q) (le_of_not_ge hx)
    rw [← sq |x|, sq_abs] at h
    nlinarith [mul_le_mul_of_nonneg_right h (sq_nonneg x),
      mul_nonneg (pow_nonneg hq 3) (abs_nonneg x)]

/-- Arbitrary centering costs at most a factor two versus the true mean. -/
theorem bernoulliWeighted_abs_lower {n : ℕ} (t r : ℝ) (c : Fin n → ℝ)
    (htl : 1/4 ≤ t) (htu : t ≤ 3/4) :
    Real.sqrt (∑ i, (c i)^2) / 128 ≤ mean (bernoulliVectorWeight t n)
      (fun z => |r + ∑ i, if z i then c i else 0|) := by
  let A := ∑ i, (c i)^2
  let q := Real.sqrt A
  let w := bernoulliVectorWeight t n
  let s := centeredBits t c
  let a := r + ∑ i, t*c i
  have ha : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q^2 = A := Real.sq_sqrt ha
  have ht : 0 ≤ t ∧ t ≤ 1 := ⟨by linarith, by linarith⟩
  have hw : ∀ z, 0 ≤ w z := bernoulliVectorWeight_nonneg t ht n
  have hw1 : ∑ z, w z = 1 := bernoulliVectorWeight_sum t n
  have ⟨h1,h2,h4⟩ := centeredBits_moments t ht c
  change mean w s = 0 at h1
  change mean w (fun z => (s z)^2) = t*(1-t)*A at h2
  change mean w (fun z => (s z)^4) ≤ A^2 at h4
  have hid (z : Fin n → Bool) : r + (∑ i, if z i then c i else 0) = a + s z := by
    simp only [a,s,centeredBits,Finset.sum_sub_distrib]; ring
  simp_rw [hid]
  change q / 128 ≤ mean w (fun z => |a+s z|)
  have habs : |a| ≤ mean w (fun z => |a+s z|) := by
    have hm : mean w (fun z => a+s z) = a := by rw [mean_add,mean_const w hw1,h1,add_zero]
    calc
      |a| = |mean w (fun z => a+s z)| := congrArg abs hm.symm
      _ ≤ ∑ z, |w z * (a+s z)| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := Finset.sum_congr rfl fun z _ => by rw [abs_mul, abs_of_nonneg (hw z)]
  have hb := average_le hw (fun z => show |s z| ≤ |a+s z| + |a| by
    simpa only [add_sub_cancel_left, sub_zero, zero_sub, abs_neg] using (abs_sub_le (a+s z) 0 a))
  rw [mean_add, mean_const w hw1] at hb
  have hp := average_le hw (fun z => clip_square q hq (s z))
  simp only [mean_add, average_scale, h2] at hp
  have hv : 3/16 ≤ t*(1-t) := by nlinarith [mul_nonneg (sub_nonneg.mpr htl) (sub_nonneg.mpr htu)]
  have hl : 16*q^2*(3/16*A) ≤ 16*q^2*(t*(1-t)*A) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv ha) (by positivity)
  rw [← hq2] at hl hp h4
  by_cases hzero : q = 0
  · rw [hzero,zero_div]; exact Finset.sum_nonneg fun z _ => mul_nonneg (hw z) (abs_nonneg _)
  · have hpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
    apply le_of_mul_le_mul_left (a := 128*q^3) _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left (show mean w (fun z => |s z|) ≤
      2*mean w (fun z => |a+s z|) by linarith) (show 0 ≤ 64*q^3 by positivity)]

end Shellsort
end
