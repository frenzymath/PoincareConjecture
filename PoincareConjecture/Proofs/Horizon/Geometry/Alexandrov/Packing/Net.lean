import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Comparison.Collinear
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Preorder.Finite

noncomputable section
set_option autoImplicit false

open Set

namespace Poincare.Alexandrov

variable {X : Type*} [MetricSpace X] {α : ℝ} {N : ℕ}

theorem ComparisonAnglePackingBound.card_le
    (h : ComparisonAnglePackingBound X α N) (p : X) (s : Finset X)
    (hp : p ∉ s)
    (hs : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      α < comparisonAngle (dist p x) (dist p y) (dist x y)) : s.card ≤ N := by
  classical
  let e := (Fintype.equivFin s).symm
  have hcard := h (Fintype.card s) p (fun i => (e i : X))
    (fun i heq => hp (heq ▸ (e i).property)) (fun i j hij =>
      hs _ (e i).property _ (e j).property (fun heq =>
        hij (e.injective (Subtype.ext heq))))
  simpa only [Fintype.card_coe] using hcard

theorem ComparisonAnglePackingBound.exists_finite_cover
    (h : ComparisonAnglePackingBound X α N) (p : X) :
    ∃ s : Finset X, s.card ≤ N ∧ p ∉ s ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        α < comparisonAngle (dist p x) (dist p y) (dist x y)) ∧
      ∀ y : X, y ≠ p → y ∈ s ∨
        ∃ q ∈ s, comparisonAngle (dist p y) (dist p q) (dist y q) ≤ α := by
  classical
  let S : Set (Finset X) := {s | p ∉ s ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
    α < comparisonAngle (dist p x) (dist p y) (dist x y)}
  have hfinite : (Finset.card '' S).Finite := by
    apply (Finset.range (N + 1)).finite_toSet.subset
    rintro _ ⟨s, hs, rfl⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (h.card_le p s hs.1 hs.2))
  have hempty : (∅ : Finset X) ∈ S := by simp [S]
  obtain ⟨s, hs, hmax⟩ := hfinite.exists_maximalFor' Finset.card S ⟨∅, hempty⟩
  refine ⟨s, h.card_le p s hs.1 hs.2, hs.1, hs.2, ?_⟩
  intro y hyp
  by_cases hys : y ∈ s
  · exact Or.inl hys
  right
  by_contra hnone
  have hsep (q : X) (hq : q ∈ s) :
      α < comparisonAngle (dist p y) (dist p q) (dist y q) := by
    exact lt_of_not_ge (fun hle => hnone ⟨q, hq, hle⟩)
  have hinsert : insert y s ∈ S := by
    refine ⟨?_, ?_⟩
    · simpa only [Finset.mem_insert, not_or] using And.intro hyp.symm hs.1
    · intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · rcases Finset.mem_insert.mp hb with rfl | hb'
        · exact (hab rfl).elim
        · exact hsep b hb'
      · rcases Finset.mem_insert.mp hb with rfl | hb'
        · simpa only [comparisonAngle_comm, dist_comm] using hsep a ha'
        · exact hs.2 a ha' b hb' hab
  have hle := hmax hinsert (Finset.card_le_card (Finset.subset_insert y s))
  rw [Finset.card_insert_of_notMem hys] at hle
  omega

theorem ComparisonAnglePackingBound.exists_angle_net
    (h : ComparisonAnglePackingBound X α N) (hα : 0 ≤ α) (p : X) :
    ∃ s : Finset X, s.card ≤ N ∧ p ∉ s ∧
      ∀ y : X, y ≠ p →
        ∃ q ∈ s, comparisonAngle (dist p y) (dist p q) (dist y q) ≤ α := by
  obtain ⟨s, hcard, hp, _, hcover⟩ := h.exists_finite_cover p
  refine ⟨s, hcard, hp, ?_⟩
  intro y hyp
  rcases hcover y hyp with hy | hy
  · refine ⟨y, hy, ?_⟩
    simpa only [dist_self, comparisonAngle_self_zero (dist_pos.mpr hyp.symm)] using hα
  · exact hy

end Poincare.Alexandrov
