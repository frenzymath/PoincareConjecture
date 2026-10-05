import PoincareLib.Topology.Manifold.Surgery.Event.Closed.ClosedComponentMaps
import PoincareLib.Topology.Manifold.Surgery.Event.Component.ComponentMetrics

/-!
# Positive-spaceform certificates on actual components

The sphere and projective alternatives of the frozen closed-component
certificate provide their exact smooth models. Their verified metrics and
connections give the positive-spaceform data required by Proposition 15.3
on the literal component, with its inherited smooth structure.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M38

/-- Package the verified metric transport together with actual compactness
and connectedness of the specified target carrier. -/
noncomputable def spaceformAlongDiffeomorph (S : GeneralizedSliceCarrier.{u})
    {Q : Type*} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q] [IsManifold (𝓡 3) ∞ Q]
    (g : RiemannianMetric 3 Q) (D : LeviCivitaData g)
    (e : Diffeomorph (𝓡 3) (𝓡 3) S.carrier Q ∞)
    (hcompact : IsCompact (Set.univ : Set S.carrier))
    (hconnected : IsConnected (Set.univ : Set S.carrier))
    (hround : ConstantPositiveSectionalCurvature g D) : SurgeryPositiveSpaceform S where
  metric := metricAlongDiffeomorph g e
  connection := connectionAlongDiffeomorph D e
  compact := hcompact
  connected := hconnected
  round := positiveCurvatureAlongDiffeomorph D e hround

attribute [local instance] SmoothClosedComponentModel.model_topology
  SmoothClosedComponentModel.model_charted SmoothClosedComponentModel.model_manifold

/-- The frozen smooth sphere model gives a positive-spaceform structure
on precisely the certified ambient component. -/
noncomputable def sphereSpaceformOnComponent (S : GeneralizedSliceCarrier.{u})
    (x : S.carrier) (C : ClosedComponentCertificate .threeSphere (connectedComponent x)) :
    SurgeryPositiveSpaceform (componentCarrier S x) := by
  let e := (componentClosedModelDiffeomorph S x C.smooth_model).trans
    (Classical.choice C.smooth_model.standard_smooth)
  apply spaceformAlongDiffeomorph (componentCarrier S x) threeSphereMetric
    threeSphereConnection e ?_ (componentCarrier_connected S x)
    (threeSphere_constantPositiveSectionalCurvature threeSphereConnection)
  change IsCompact (Set.univ : Set (connectedComponent x))
  exact isCompact_univ_iff.mpr (isCompact_iff_compactSpace.mp C.compact)

/-- The frozen projective cover descends the verified sphere geometry onto
precisely the certified ambient component. -/
noncomputable def projectiveSpaceformOnComponent (S : GeneralizedSliceCarrier.{u})
    (x : S.carrier)
    (C : ClosedComponentCertificate .realProjectiveThree (connectedComponent x)) :
    SurgeryPositiveSpaceform (componentCarrier S x) := by
  let d := componentClosedModelDiffeomorph S x C.smooth_model
  let q := projectiveCoverAlongDiffeomorph
    (Classical.choice C.smooth_model.standard_smooth) d
  exact {
    metric := projectiveMetric q
    connection := projectiveConnection q
    compact := by
      change IsCompact (Set.univ : Set (connectedComponent x))
      exact isCompact_univ_iff.mpr (isCompact_iff_compactSpace.mp C.compact)
    connected := componentCarrier_connected S x
    round := projective_constantPositiveSectionalCurvature q (projectiveConnection q) }

end PoincareMT.M38
