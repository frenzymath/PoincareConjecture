import PoincareConjecture.Statements.M11GeneralizedFlow

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

structure SpacetimeGaugeCover (F : GeneralizedFlowSpacetime n X time I)
    (D : SpacetimeIntervalSystem) where
  index : Type u
  interval : index → SpacetimeInterval
  spatial : index → TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))
  cylinder : ∀ b, CompatibleSpacetimeCylinder F (D.interval (interval b)) (spatial b)
  metric : ∀ b, SpacetimeCylinderMetric (cylinder b)
  local_diffeomorph : ∀ b,
    IsLocalDiffeomorph (spacetimeModel n) (spacetimeModel n) ∞ (cylinder b).toSpacetime
  covers : ∀ p : F.Point, ∃ b, ∃ q, (cylinder b).toSpacetime q = p

noncomputable def GeneralizedFlowCarrierConclusion.gaugeCover
    {A : AdaptedMetricAtlas n X} (R : GeneralizedFlowCarrierConclusion A) :
    SpacetimeGaugeCover R.spacetime R.timeIntervals where
  index := A.box_index
  interval b := (A.box b).interval
  spatial b := (A.box b).spatial
  cylinder := R.boxCylinder
  metric := R.boxMetric
  local_diffeomorph := R.box_localDiffeomorph
  covers p := by
    obtain ⟨b, q, h⟩ := A.box_covers p
    exact ⟨b, q, (R.boxCylinder_eq b q).trans h⟩

end PoincareConjecture
