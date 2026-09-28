import PoincareConjecture.Proofs.M11.SliceMetric
import PoincareConjecture.Definitions.M11SpacetimeSlices

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]

noncomputable def adaptedSliceGeometry (A : AdaptedMetricAtlas n X) (t : ℝ) :
    SpacetimeSliceGeometry (adaptedSpacetime A) t where
  chartedSpace := adaptedSliceChartedSpace A t
  isManifold := adaptedSlice_isManifold A t
  t3Space := by
    let : T3Space X := adapted_t3Space A
    infer_instance
  secondCountable := @TopologicalSpace.Subtype.secondCountableTopology X _ {p | A.time p = t}
    ‹SecondCountableTopology X›
  measurableSpace := borel _
  borelSpace := by
    change @BorelSpace (spacetimeSlice A.time t) _ (borel (spacetimeSlice A.time t))
    exact @BorelSpace.mk (spacetimeSlice A.time t) _ (borel _) rfl
  inclusion_smooth := slice_inclusion_smooth A t
  inclusion_embedding := Topology.IsEmbedding.subtypeVal
  inclusion_differential_injective := slice_inclusion_differential_injective A t
  tangentEquiv := sliceHorizontalEquiv A t
  tangentEquiv_eq := sliceHorizontalEquiv_eq A t
  metric := adaptedSliceMetric A t
  metric_eq := fun _ _ _ ↦ rfl

end PoincareConjecture.Proofs.M11
