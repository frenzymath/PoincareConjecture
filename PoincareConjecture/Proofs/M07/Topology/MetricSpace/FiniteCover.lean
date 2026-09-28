import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Order.Preorder.Finite








set_option autoImplicit false

open Set
open scoped ENNReal

namespace Poincare



theorem exists_finset_cover_of_separated_card_le
    {X : Type*} [PseudoEMetricSpace X] (s : Set X) {ε : ℝ≥0∞}
    (hε : 0 < ε) (N : ℕ)
    (hbound : ∀ S : Finset X, (↑S : Set X) ⊆ s →
      (↑S : Set X).Pairwise (fun x y => ε ≤ edist x y) → S.card ≤ N) :
    ∃ S : Finset X, (↑S : Set X) ⊆ s ∧ S.card ≤ N ∧
      (↑S : Set X).Pairwise (fun x y => ε ≤ edist x y) ∧
      ∀ x ∈ s, ∃ y ∈ S, edist x y < ε := by
  classical
  let A : Set (Finset X) := {S | (↑S : Set X) ⊆ s ∧
    (↑S : Set X).Pairwise (fun x y => ε ≤ edist x y)}
  have hfinite : (Finset.card '' A).Finite := by
    apply (Set.finite_le_nat N).subset
    rintro _ ⟨S, hS, rfl⟩
    exact hbound S hS.1 hS.2
  obtain ⟨S, hS, hmax⟩ := hfinite.exists_maximalFor' Finset.card A
    ⟨∅, by simp [A]⟩
  refine ⟨S, hS.1, hbound S hS.1 hS.2, hS.2, ?_⟩
  intro x hx
  by_contra! hcover
  have hxS : x ∉ S := by
    intro hxS
    have h := hcover x hxS
    exact hε.not_ge (by simpa using h)
  have hins : insert x S ∈ A := by
    refine ⟨?_, ?_⟩
    · simpa only [Finset.coe_insert, insert_subset_iff] using ⟨hx, hS.1⟩
    · rw [Finset.coe_insert, Set.pairwise_insert]
      exact ⟨hS.2, fun y hy _ => ⟨hcover y hy,
        by simpa only [edist_comm] using hcover y hy⟩⟩
  have hc := hmax hins (Finset.card_le_card (Finset.subset_insert x S))
  rw [Finset.card_insert_of_notMem hxS] at hc
  omega

end Poincare
