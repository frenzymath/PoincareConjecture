import PoincareConjecture.Definitions.Ch11.BlowupLimits
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Small















set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] RiemannianMetric.smallCarrier
  RiemannianMetric.smallChartedSpace RiemannianMetric.smallIsManifold
  RiemannianMetric.smallT3Space RiemannianMetric.smallMeasurableSpace
  RiemannianMetric.smallBorelSpace




noncomputable def smallSliceCarrier (C : GeneralizedSliceCarrier.{u}) :
    GeneralizedSliceCarrier.{0} where
  carrier := Shrink.{0} C.carrier
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := (Poincare.Topology.SecondCountable.homeomorphShrink C.carrier).t2Space
  t3Space := inferInstance
  secondCountable := by
    let e := Poincare.Topology.SecondCountable.homeomorphShrink C.carrier
    exact e.symm.isEmbedding.secondCountableTopology



noncomputable def smallSliceDiffeomorph (C : GeneralizedSliceCarrier.{u}) :
    C.carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (smallSliceCarrier C).carrier :=
  Poincare.Manifold.shrinkDiffeomorph (𝓡 3) C.carrier



@[simp] theorem smallSliceDiffeomorph_toEquiv (C : GeneralizedSliceCarrier.{u}) :
    (smallSliceDiffeomorph C).toEquiv = equivShrink C.carrier := rfl



noncomputable def smallSliceMetric (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) :
    RiemannianMetric 3 (smallSliceCarrier C).carrier :=
  g.shrink



@[simp] theorem smallSliceMetric_inner (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) (x : (smallSliceCarrier C).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (smallSliceMetric C g).inner x v w =
      g.inner ((smallSliceDiffeomorph C).symm x)
        (mfderiv (𝓡 3) (𝓡 3) (smallSliceDiffeomorph C).symm x v)
        (mfderiv (𝓡 3) (𝓡 3) (smallSliceDiffeomorph C).symm x w) := rfl



@[simp] theorem smallSliceMetric_edist (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) (x y : (smallSliceCarrier C).carrier) :
    (smallSliceMetric C g).edist x y =
      g.edist ((smallSliceDiffeomorph C).symm x) ((smallSliceDiffeomorph C).symm y) :=
  g.shrink_edist x y



theorem smallSliceMetric_image_ball (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) (x : (smallSliceCarrier C).carrier) (r : ℝ) :
    (smallSliceDiffeomorph C).symm '' (smallSliceMetric C g).ball x r =
      g.ball ((smallSliceDiffeomorph C).symm x) r :=
  g.shrink_image_ball x r



@[simp] theorem smallSliceMetric_metricComplete_iff (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) :
    MetricComplete (smallSliceMetric C g) ↔ MetricComplete g :=
  g.shrink_metricComplete_iff



@[simp] theorem smallSliceMetric_scalarCurvature (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) (D : LeviCivitaData g)
    (x : (smallSliceCarrier C).carrier) :
    (smallSliceMetric C g).leviCivitaData.scalarCurvature x =
      D.scalarCurvature ((smallSliceDiffeomorph C).symm x) :=
  g.shrink_scalarCurvature D x



theorem smallSliceMetric_volumeMeasure_image (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) (s : Set (smallSliceCarrier C).carrier) :
    g.volumeMeasure ((smallSliceDiffeomorph C).symm '' s) =
      (smallSliceMetric C g).volumeMeasure s :=
  RiemannianMetric.volumeMeasure_image_diffeomorph (smallSliceMetric C g) g
    (smallSliceDiffeomorph C).symm (smallSliceMetric_inner C g) s



@[simp] theorem smallSliceMetric_volumeMeasure_ball (C : GeneralizedSliceCarrier.{u})
    (g : RiemannianMetric 3 C.carrier) (x : (smallSliceCarrier C).carrier) (r : ℝ) :
    (smallSliceMetric C g).volumeMeasure ((smallSliceMetric C g).ball x r) =
      g.volumeMeasure (g.ball ((smallSliceDiffeomorph C).symm x) r) :=
  RiemannianMetric.volumeMeasure_ball_diffeomorph (smallSliceMetric C g) g
    (smallSliceDiffeomorph C).symm (smallSliceMetric_inner C g) x r

end PoincareConjecture.M30
