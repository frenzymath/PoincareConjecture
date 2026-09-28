import PoincareConjecture.Proofs.M38.ClosedComponentMaps
import PoincareConjecture.Proofs.M38.ComponentMetrics

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M38

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

end PoincareConjecture.M38
