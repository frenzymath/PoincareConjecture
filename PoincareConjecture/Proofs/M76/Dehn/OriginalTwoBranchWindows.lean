import PoincareConjecture.Proofs.M76.Dehn.OriginalBranchCoordinates
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTwoBranchWindows










set_option autoImplicit false

open Set Topology Geometry

namespace Geometry.OriginalPLTower






theorem Step.exists_finite_PL_twoBranchWindows
    {U E M ι D : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [TopologicalSpace D] [CompactSpace D]
    {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
    {f : U → M} {r : M → ℝ} {C : Set M}
    {s t : Stage e S f r C} (step : Step s t)
    {j : D → t.Carrier} (hj : IsEmbedding j) :
    ∃ W : Finset (TwoBranchWindow (step.projection ∘ step.inclusion)),
      (∀ w ∈ W, ∀ k l,
        (t.charts k).symm.trans (w.left.trans (s.charts l)) ∈ piecewiseAffineGroupoid E ∧
        (t.charts k).symm.trans (w.right.trans (s.charts l)) ∈ piecewiseAffineGroupoid E) ∧
      ∀ x y : D,
        step.projection (step.inclusion (j x)) = step.projection (step.inclusion (j y)) →
        x ≠ y → ∃ w ∈ W, j x ∈ w.left.source ∧ j y ∈ w.right.source := by
  obtain ⟨W, hW⟩ := step.projectionInclusion_local.exists_finite_twoBranchWindows
    (fun y => (step.projectionInclusion_fiber y).1)
    (fun y => (step.projectionInclusion_fiber y).2) hj
  refine ⟨W, ?_, hW⟩
  intro w _ k l
  exact ⟨step.branch_chart_PL w.left (fun x _ => congrFun w.left_eq x) k l,
    step.branch_chart_PL w.right (fun x _ => congrFun w.right_eq x) k l⟩

end Geometry.OriginalPLTower
