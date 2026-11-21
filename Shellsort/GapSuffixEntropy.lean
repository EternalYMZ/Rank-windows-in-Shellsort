import Shellsort.ComparisonWordLower
import Shellsort.FiberEquivalences
import Shellsort.SourceDecomposition

/-! How much comparison information remains after sorting the residue chains?
The probability here is the genuine pushforward of a uniform permutation. -/
noncomputable section
namespace Shellsort.GapSuffixEntropy
open Finset ComparisonAudit HarvestBlockIteration HarvestOperationalAudit
open scoped Classical

private def multiplicity (n h : ℕ) : ℕ :=
  ∏ s : Fin h, (residuePrefixCount h s.val n).factorial

private theorem fiber_bound {n h : ℕ} (hh : 0<h) (q : RankPlacement n) :
    Fintype.card {p : RankPlacement n // gapSort p h=q} ≤ multiplicity n h := by
  let R := fun i : Fin n => (⟨i.val % h,Nat.mod_lt _ hh⟩ : Fin h)
  let f := fun x : Fin n => R (q x)
  let incl (p : {p : RankPlacement n // gapSort p h=q}) : matchingEquiv f R :=
    ⟨p.val, fun x => Fin.ext (by
      change (p.val x).val%h=(q x).val%h
      exact (gapSort_preserves_residue p.val h x).symm.trans
        (congrArg (fun e : RankPlacement n => (e x).val%h) p.property))⟩
  have inject : Function.Injective incl := by
    intro p t eq
    exact Subtype.ext (congrArg (fun e : matchingEquiv f R => e.val) eq)
  have c (s : Fin h) : Fintype.card {x // f x=s} = Fintype.card {i // R i=s} :=
    Fintype.card_congr (q.subtypeEquiv (fun _ => Iff.rfl))
  have size (s : Fin h) : Fintype.card {i // R i=s} = residuePrefixCount h s.val n := by
    rw [Fintype.card_subtype,←chainPositions_card]
    simp [chainPositions,R,Fin.ext_iff]
  apply (Fintype.card_le_of_injective incl inject).trans_eq
  trans ∏ s : Fin h, (Fintype.card {x // f x=s}).factorial
  · convert matchingEquiv_card f R c using 1
    exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
  · exact prod_congr rfl fun s _ => congrArg Nat.factorial ((c s).trans (size s))

private theorem cost_kraft {n : ℕ} (w : PositiveWord)
    (last : (w.map Subtype.val).getLast?=some 1) :
    (∑ p : RankPlacement n, ((2:ℝ)^(ordinaryWordComparisons p w))⁻¹) ≤ 1 := by
  let t := wordTree (Vector.ofFn (id : Fin n → Fin n)) w
  have recover (p : RankPlacement n) (i : Fin n) : (t.run p).1[i.val] = p i := by
    have out := (initial_wordTree w p).1
    rw [runWord_slots, sorted_last p _ last] at out
    have v := congrArg (fun a : Vector (Fin n) n => a[i.val]) out
    apply p.symm.injective
    simpa [t,slots] using v
  have sep := separates_of_injective_output t (by
    intro p q eq
    apply Equiv.ext
    intro i
    exact (recover p i).symm.trans ((congrArg (fun a : Vector (Fin n) n => a[i.val]) eq).trans (recover q i)))
  have k := ComparisonTranscriptBound.kraft _ sep
  exact (show (∑ p : RankPlacement n, ((2:ℝ)^(ordinaryWordComparisons p w))⁻¹) =
    ∑ p : RankPlacement n, ((2:ℝ)^(t.run p).2.length)⁻¹ from
    sum_congr rfl fun p _ => by rw [show (t.run p).2.length=_ from (initial_wordTree w p).2]).le.trans k

private theorem bounded_kraft {n h : ℕ} (hh : 0<h) (w : PositiveWord)
    (last : (w.map Subtype.val).getLast?=some 1) :
    (∑ p : RankPlacement n, ((2:ℝ)^(ordinaryWordComparisons (gapSort p h) w))⁻¹) ≤
      (multiplicity n h:ℝ) := by
  let A := fun q : RankPlacement n => ((2:ℝ)^(ordinaryWordComparisons q w))⁻¹
  change (∑ p : RankPlacement n, A (gapSort p h)) ≤ _
  rw [← Fintype.sum_fiberwise' (fun p : RankPlacement n => gapSort p h) A]
  simp only [sum_const,card_univ,nsmul_eq_mul]
  calc
    _ ≤ ∑ q : RankPlacement n, (multiplicity n h:ℝ)*A q := by
      apply sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_right _ (by dsimp [A]; positivity)
      exact_mod_cast fiber_bound hh q
    _ = _ := (mul_sum ..).symm
    _ ≤ _ := mul_le_of_le_one_right (Nat.cast_nonneg _) (cost_kraft w last)

theorem mean_suffix_entropy {n h : ℕ} (hh : 0<h) (w : PositiveWord)
    (last : (w.map Subtype.val).getLast?=some 1) :
    Real.logb 2 (n.factorial:ℝ) -
      (∑ s : Fin h, Real.logb 2 ((residuePrefixCount h s.val n).factorial:ℝ)) ≤
      uniformAverage (fun p : RankPlacement n => (ordinaryWordComparisons (gapSort p h) w:ℝ)) := by
  let M : ℝ := n.factorial
  let D : ℝ := multiplicity n h
  let m := M/D
  let L := fun p : RankPlacement n => ordinaryWordComparisons (gapSort p h) w
  have hM : 0<M := by dsimp [M]; positivity
  have hD : 0<D := by
    change (0:ℝ)<(∏ s : Fin h, (residuePrefixCount h s.val n).factorial : ℕ)
    exact_mod_cast Finset.prod_pos (fun s _ => Nat.factorial_pos _)
  have hm : 0<m := div_pos hM hD
  have card : (Fintype.card (RankPlacement n) : ℝ) = M := by
    simp [RankPlacement,Fintype.card_perm,M]
  have term (p : RankPlacement n) :
      Real.log m-(L p:ℝ)*Real.log 2 ≤ m*((2:ℝ)^(L p))⁻¹-1 := by
    have e := Real.log_le_sub_one_of_pos (show 0<m*((2:ℝ)^(L p))⁻¹ by positivity)
    rw [Real.log_mul hm.ne' (by positivity),Real.log_inv,Real.log_pow] at e
    linarith
  have total := sum_le_sum (s:=(univ : Finset (RankPlacement n))) (fun p _ => term p)
  simp only [sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,card,
    ← sum_mul,← mul_sum,mul_one] at total
  have cap : (∑ p, ((2:ℝ)^(L p))⁻¹) ≤ D := bounded_kraft hh w last
  have limited := mul_le_mul_of_nonneg_left cap hm.le
  have exactM : m*D=M := by dsimp [m]; field_simp
  have key : Real.logb 2 m ≤ (∑ p, (L p:ℝ))/M := by
    apply (div_le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2)) hM).2
    nlinarith
  have logD : Real.logb 2 D =
      ∑ s : Fin h, Real.logb 2 ((residuePrefixCount h s.val n).factorial:ℝ) := by
    change Real.logb 2 (↑(∏ s : Fin h, (residuePrefixCount h s.val n).factorial : ℕ) : ℝ) = _
    rw [Nat.cast_prod]
    exact Real.logb_prod _ _ (fun s _ => by positivity)
  rw [←logD,←Real.logb_div (b:=2) hM.ne' hD.ne']
  exact key

#print axioms mean_suffix_entropy
end Shellsort.GapSuffixEntropy
