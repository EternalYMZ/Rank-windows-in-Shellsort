import Shellsort.CutZoneCrossings
import Shellsort.TagPosition

namespace Shellsort.RankMesh
open Finset
noncomputable section

def chainCrossings {n : ℕ} (p : RankPlacement n) (h T : ℕ) : ℕ :=
  ∑ x : Fin n, ∑ y : Fin n, if (p x).val%h = (p y).val%h ∧
    x.val<T ∧ T≤y.val ∧ p y<p x then 1 else 0

private theorem chain_before {n : ℕ} (p : RankPlacement n) (h : ℕ) (x : Fin n) :
    (∑ y : Fin n, if (p x).val%h=(p y).val%h ∧ p y<p x then (1:ℕ) else 0) =
      chainOrdinal h (p x) := by
  have a := Equiv.sum_comp p (fun j : Fin n =>
    if (p x).val%h=j.val%h ∧ j<p x then (1:ℕ) else 0)
  rw [a, sum_boole]
  simp [chainOrdinal, chainPositions, filter_filter, eq_comm]

private theorem chain_rank {n : ℕ} (p : RankPlacement n) (h : ℕ) (x : Fin n) :
    (∑ y : Fin n, if (p x).val%h=(p y).val%h ∧ y<x then (1:ℕ) else 0) =
      chainLowerCount (thresholdSet p x.val) h ((p x).val%h) := by
  rw [sum_boole, threshold_chain_count_keys, Fintype.card_subtype]
  apply congrArg card
  ext y
  simp only [mem_filter, mem_univ, true_and, Fin.lt_def]
  tauto

private theorem initial_position {n : ℕ} (p : RankPlacement n) (h : ℕ)
    (hh : 0<h) (x : Fin n) :
    (p x).val = (p x).val%h + h *
      ∑ y : Fin n, if (p x).val%h=(p y).val%h ∧ p y<p x then (1:ℕ) else 0 := by
  rw [chain_before, chainOrdinal_eq_div h hh, Nat.mod_add_div]

/-- Exact decrease of actual cut on an ordinary h-sort, h>0. -/
theorem gapSort_cut_drop {n : ℕ} (p : RankPlacement n) {h : ℕ} (hh : 0<h) (T : ℕ) :
    cut p T - cut (gapSort p h) T = (h:ℤ) * chainCrossings p h T := by
  let inside (x y : Fin n) : ℤ := if (p x).val%h=(p y).val%h ∧
    x.val<T ∧ y.val<T ∧ x<y ∧ p y<p x then 1 else 0
  let cross (x y : Fin n) : ℤ := if (p x).val%h=(p y).val%h ∧
    x.val<T ∧ T≤y.val ∧ p y<p x then 1 else 0
  have point (x y : Fin n) :
      (if x.val<T then
        ((if (p x).val%h=(p y).val%h ∧ p y<p x then (1:ℤ) else 0) -
         (if (p x).val%h=(p y).val%h ∧ y<x then 1 else 0))
       else 0) = inside x y - inside y x + cross x y := by
    by_cases e : x=y
    · subst y; simp [inside,cross]
    · have ne : p x ≠ p y := fun h => e (p.injective h)
      have dx : x.val ≠ y.val := fun h => e (Fin.ext h)
      have dp : (p x).val ≠ (p y).val := fun h => ne (Fin.ext h)
      dsimp only [inside,cross]; simp only [Fin.lt_def]
      split_ifs <;> omega
  have row (x : Fin n) :
      (if x.val<T then ((p x).val:ℤ)-x.val else 0) -
      (if x.val<T then ((gapSort p h x).val:ℤ)-x.val else 0) =
      (h:ℤ) * ∑ y : Fin n, (inside x y - inside y x + cross x y) := by
    simp_rw [←point]
    by_cases hx : x.val<T
    · simp only [hx, ite_true, sum_sub_distrib]
      have a := congrArg (fun k : ℕ => (k:ℤ)) (initial_position p h hh x)
      have b := congrArg (fun k : ℕ => (k:ℤ)) (gapSort_tag_position p h hh x)
      rw [←chain_rank] at b
      push_cast at a b
      try dsimp only at a b
      linarith
    · simp [hx]
  unfold cut
  rw [←sum_sub_distrib]
  simp_rw [row, sum_add_distrib, sum_sub_distrib]
  rw [←mul_sum, sum_add_distrib, sum_sub_distrib, sum_comm (f := fun x y => inside x y)]
  unfold chainCrossings
  push_cast
  simp [cross]

#print axioms gapSort_cut_drop
end
end Shellsort.RankMesh

