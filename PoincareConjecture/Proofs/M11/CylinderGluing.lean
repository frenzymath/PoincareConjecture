import PoincareConjecture.Proofs.M11.CylinderGluingTopology
import PoincareConjecture.Proofs.M11.CylinderGluingDifferential

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.Proofs.M11.CylinderTimeCover

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {C : Type v} [TopologicalSpace C] [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
  [IsManifold (𝓡 n) ∞ C] (D : CylinderTimeCover.{u, v, w} F K C)

noncomputable def glued : CompatibleSpacetimeCylinder F (smoothInterval K) C where
  interval_subset := by
    intro t ht
    obtain ⟨b, hb⟩ := D.covers ⟨t, ht⟩
    exact (D.cylinder b).interval_subset hb
  toSpacetime := D.map
  embedding := D.map_embedding
  time_eq := D.map_time
  worldline_smooth := D.map_worldline_smooth
  worldline_derivative := D.map_worldline_derivative
  smooth := D.map_smooth
  differential_injective := D.map_differential_injective

theorem glued_eq (b : D.index) (t : (smoothInterval (D.interval b)).Point) (x : C) :
    D.glued.toSpacetime (spacetimeIntervalInclusion (smoothInterval (D.interval b))
      (smoothInterval K) (D.subset b) t, x) = (D.cylinder b).toSpacetime (t, x) :=
  D.map_eq b t x

theorem glued_based (b : D.index) (t : (smoothInterval (D.interval b)).Point)
    (source : C → F.Point) (h : (D.cylinder b).toCompatibleSpacetimeEmbedding.IsBasedAt t source) :
    D.glued.toCompatibleSpacetimeEmbedding.IsBasedAt
      (spacetimeIntervalInclusion (smoothInterval (D.interval b)) (smoothInterval K) (D.subset b) t)
      source :=
  fun x ↦ (D.map_eq b t x).trans (h x)

end PoincareConjecture.Proofs.M11.CylinderTimeCover
