import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-! Same-bin ordered pairs with disjoint source sets. Bin labels can
contain both a residue and a discretized quantile. -/
noncomputable section
namespace Shellsort.DisjointConeBins
open Finset
open scoped Classical

def fiber {α β : Type*} [Fintype α] [DecidableEq β] (color : α → β) (b : β) :=
  univ.filter (fun i => color i = b)

def readers {α σ : Type*} [Fintype α] [DecidableEq σ] (cone : α → Finset σ) (s : σ) :=
  univ.filter (fun i => s ∈ cone i)

def overlap {α σ : Type*} [Fintype α] [DecidableEq σ] [DecidableEq α]
    (cone : α → Finset σ) (i : α) :=
  (cone i).biUnion (readers cone)

theorem overlap_iff {α σ : Type*} [Fintype α] [DecidableEq σ] [DecidableEq α]
    (cone : α → Finset σ) (i j : α) :
    j ∈ overlap cone i ↔ ∃ s ∈ cone i, s ∈ cone j := by
  simp [overlap,readers]

theorem overlap_card {α σ : Type*} [Fintype α] [DecidableEq σ] [DecidableEq α]
    (cone : α → Finset σ) {B : ℕ} (fanin : ∀ i, (cone i).card ≤ B)
    (fanout : ∀ s, (readers cone s).card ≤ B) (i : α) :
    (overlap cone i).card ≤ B^2 := by
  calc
    _ ≤ ∑ s ∈ cone i, (readers cone s).card := card_biUnion_le
    _ ≤ ∑ _s ∈ cone i, B := sum_le_sum (fun s _ => fanout s)
    _ = (cone i).card * B := by simp
    _ ≤ B^2 := by simpa [pow_two] using Nat.mul_le_mul_right B (fanin i)

/-- A finite sum of squares with a separate exclusion budget per output. -/
theorem same_color_after_exclusions {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (color : α → β) (bad : α → Finset α)
    {D : ℕ} (budget : ∀ i, (bad i).card ≤ D) :
    (Fintype.card α)^2 ≤ Fintype.card β *
      ((∑ i, ((fiber color (color i)) \ bad i).card) + Fintype.card α * D) := by
  let k := fun b => Fintype.card {i // color i = b}
  have size (b) : k b = (fiber color b).card := by
    simp [k,fiber,Fintype.card_subtype]
  have total : ∑ b, k b = Fintype.card α := by
    simpa [k] using Fintype.sum_fiberwise' color (fun _ : β => (1:ℕ))
  have squares : (∑ b, (k b)^2) = ∑ i, k (color i) := by
    simpa [k,pow_two] using Fintype.sum_fiberwise' color k
  have left : (Fintype.card α)^2 ≤ Fintype.card β * ∑ i, k (color i) := by
    simpa [total,squares] using sq_sum_le_card_mul_sum_sq (s:=univ) (f:=k)
  apply left.trans
  apply Nat.mul_le_mul_left
  calc
    _ ≤ ∑ i, (((fiber color (color i)) \ bad i).card+D) := by
      apply sum_le_sum
      intro i _
      rw [size]
      exact card_le_card_sdiff_add_card.trans (Nat.add_le_add_left (budget i) _)
    _ = _ := by simp [sum_add_distrib]

/-- With n ≥ 8 g B³, at least n²/(8 g B) *ordered* pairs lie in the same
    gap residue and quantile bin and have disjoint sets of input sources. -/
theorem disjoint_in_bins {α σ : Type*} [Fintype α] [DecidableEq α] [DecidableEq σ]
    {g B : ℕ} (group : α → Fin g × Fin (4*B)) (cone : α → Finset σ)
    (fanin : ∀ i, (cone i).card ≤ B) (fanout : ∀ s, (readers cone s).card ≤ B)
    (many : 8*g*B^3 ≤ Fintype.card α) :
    (Fintype.card α)^2 ≤ 8*g*B *
      (∑ i, ((fiber group (group i)) \ overlap cone i).card) := by
  have count := same_color_after_exclusions group (overlap cone)
    (fun i => overlap_card cone fanin fanout i)
  simp only [Fintype.card_prod,Fintype.card_fin] at count
  have error := Nat.mul_le_mul_left (Fintype.card α) many
  nlinarith only [count,error]

#print axioms disjoint_in_bins
end Shellsort.DisjointConeBins
