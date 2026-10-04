import PoincareLib.Geometry.Spacetime.GeometryTheory

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M12GaugeCover.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Declaration bodies are unchanged;
only imports and module placement differ. See
`references/ricci-flow/mapher/spacetime-port.json`. -/

/-!
# Actual adapted gauges used by M12

The intrinsic calculation uses a supplied covering by actual compatible
coordinate cylinders. Bare spacetime and slice records do not silently
supply a new straightening theorem. M11's atlas realization gives this
cover by projection; M12 constructs the ordinary-product cover separately.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

/-- Actual coordinate cylinders and their metric pullbacks covering the same
spacetime, with interval charts from one supplied system. -/
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

/-- The existing M11 realization already supplies every field of this cover. -/
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

end PoincareMT
