import PoincareConjecture.Definitions.M14GeneralizedLGeometry
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} (G : GeneralizedLGeometryTransport n X time I)

theorem exists_smooth_gauge_lift (p : G.Point) :
    ∃ (b : G.gaugeCover.index) (U : Set G.Point)
      (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
        G.gaugeCover.spatial b),
      IsOpen U ∧ p ∈ U ∧
      ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U ∧
      (∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q) ∧
      (∀ q ∈ U, (lift q).1.val = G.spacetime.timeFunction q) := by
  obtain ⟨b, z, hz⟩ := G.gaugeCover.covers p
  let h := G.gaugeCover.local_diffeomorph b z
  refine ⟨b, h.localInverse.source, h.localInverse, h.localInverse_open_source,
    hz ▸ h.localInverse_mem_source, h.localInverse_contMDiffOn,
    (fun _ hq => h.localInverse_right_inv hq), ?_⟩
  intro q hq
  exact ((G.gaugeCover.cylinder b).time_eq (h.localInverse q)).symm.trans
    (congrArg G.spacetime.timeFunction (h.localInverse_right_inv hq))

end PoincareConjecture.M14
