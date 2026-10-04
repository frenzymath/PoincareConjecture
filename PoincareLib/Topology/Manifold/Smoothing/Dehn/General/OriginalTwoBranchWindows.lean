import PoincareLib.Topology.Manifold.Smoothing.Dehn.Coordinates.OriginalBranchCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.FiniteTwoBranchWindows

/-!
# Finite original PL windows for the actual projected disk

The actual tower step supplies the local homeomorphism and finite
fiber bounds. Compactness selects finitely many actual paired
branches, and the retained original coordinates prove both branches
PL. See Dehn028, sections2--4, and Hatcher p.46.
-/

set_option autoImplicit false

open Set Topology Geometry

namespace Geometry.OriginalPLTower

/-- The actual step and compact embedded source construct finitely
many original PL windows covering every ordered double pair.
Each window retains disjoint branches, a common full open target,
and the exact whole inverse-image equation. No transverse-curve
or surgery data are assumed. See Dehn028, sections2--4. -/
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
