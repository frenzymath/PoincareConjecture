import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace Poincare.Manifold

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem dense_manifoldInterior : Dense (I.interior M) := by
  intro x
  have hx := extChartAt_target_subset_closure_interior (mem_extChartAt_target (I := I) x)
  have himage := mem_closure_image (continuousAt_extChartAt_symm (I := I) x) hx
  rw [extChartAt_to_inv] at himage
  apply closure_mono (s := (extChartAt I x).symm '' interior (extChartAt I x).target) ?_ himage
  rintro y ⟨z, hz, rfl⟩
  have hzt := interior_subset hz
  have hys := (extChartAt I x).map_target hzt
  apply (I.isInteriorPoint_iff_of_mem_atlas (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    (chart_mem_atlas H x) (by simpa only [extChartAt_source] using hys)).2
  change extChartAt I x ((extChartAt I x).symm z) ∈ interior (extChartAt I x).target
  simpa only [(extChartAt I x).right_inv hzt] using hz

end Poincare.Manifold
