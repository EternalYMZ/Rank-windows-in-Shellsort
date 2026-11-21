import Shellsort.RankMesh
import Mathlib.Order.Interval.Finset.Fin

/-! The actual threshold moment is a pair count on the inverse permutation.
Ranks and slots start at 0. The lower side is [0,T); T can exceed n. -/
namespace Shellsort.RankMesh
open Finset

/-- The low rank x is physically behind the high rank y. -/
def zoneCrossings {n : ℕ} (p : RankPlacement n) (T : ℕ) : ℕ :=
  ∑ x : Fin n, ∑ y : Fin n,
    if x.val < T ∧ T ≤ y.val ∧ p y < p x then 1 else 0

private theorem before_count {n : ℕ} (x : Fin n) :
    (∑ y : Fin n, if y < x then (1:ℤ) else 0) = x.val := by
  have same : univ.filter (fun y : Fin n => y < x) = Iio x := by ext; simp
  rw [sum_boole, same, Fin.card_Iio]

/-- All pairs of low ranks cancel upon exchanging the two endpoints. -/
theorem cut_eq_zoneCrossings {n : ℕ} (p : RankPlacement n) (T : ℕ) :
    cut p T = (zoneCrossings p T : ℤ) := by
  classical
  let inside (x y : Fin n) : ℤ :=
    if x.val < T ∧ y.val < T ∧ x < y ∧ p y < p x then 1 else 0
  let cross (x y : Fin n) : ℤ :=
    if x.val < T ∧ T ≤ y.val ∧ p y < p x then 1 else 0
  have point (x y : Fin n) :
      (if x.val < T then
        ((if p y < p x then (1:ℤ) else 0) - (if y < x then 1 else 0)) else 0)
      = inside x y - inside y x + cross x y := by
    by_cases e : x = y
    · subst y; simp [inside, cross]
    · have ne : p x ≠ p y := fun h => e (p.injective h)
      have dx : x.val ≠ y.val := fun h => e (Fin.ext h)
      have dp : (p x).val ≠ (p y).val := fun h => ne (Fin.ext h)
      dsimp only [inside, cross]; simp only [Fin.lt_def]
      split_ifs <;> omega
  have row (x : Fin n) :
      (if x.val<T then ((p x).val:ℤ)-x.val else 0) =
      ∑ y : Fin n, (inside x y - inside y x + cross x y) := by
    simp_rw [← point]
    by_cases h : x.val<T
    · simp only [h, ite_true,sum_sub_distrib]
      have tr := Equiv.sum_comp p (fun y : Fin n => if y < p x then (1:ℤ) else 0)
      rw [tr, before_count, before_count]
    · simp [h]
  have eqn : (∑ x : Fin n, ∑ y : Fin n, inside x y) = ∑ x : Fin n, ∑ y : Fin n, inside y x :=
    sum_comm
  unfold cut
  simp_rw [row, sum_add_distrib, sum_sub_distrib]
  rw [eqn, sub_self, zero_add]
  unfold zoneCrossings
  push_cast
  simp [cross]

#print axioms cut_eq_zoneCrossings
end Shellsort.RankMesh

