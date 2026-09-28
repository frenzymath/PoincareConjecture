import PoincareConjecture.Definitions.Ch11.BlowupLimits
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.ConnectedComponent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable



noncomputable def basedSliceCarrier (C : GeneralizedSliceCarrier.{u}) (p : C.carrier) :
    FlowCarrier.{u} 3 where
  carrier := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance
  connected := isConnected_univ



noncomputable def basedSliceMetric (C : GeneralizedSliceCarrier.{u}) (p : C.carrier)
    (g : RiemannianMetric 3 C.carrier) : (basedSliceCarrier C p).metric :=
  g.connectedComponentMetric p



theorem basedSliceMetric_inner (C : GeneralizedSliceCarrier.{u}) (p : C.carrier)
    (g : RiemannianMetric 3 C.carrier) (x : (basedSliceCarrier C p).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (basedSliceMetric C p g).inner x v w = g.inner x.val
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : (basedSliceCarrier C p).carrier → C.carrier) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : (basedSliceCarrier C p).carrier → C.carrier) x w) :=
  rfl



theorem basedSliceMetric_edist (C : GeneralizedSliceCarrier.{u}) (p : C.carrier)
    (g : RiemannianMetric 3 C.carrier) (x y : (basedSliceCarrier C p).carrier) :
    (basedSliceMetric C p g).edist x y = g.edist x.val y.val :=
  g.edist_subtype_val isClosed_connectedComponent (basedSliceMetric C p g)
    (basedSliceMetric_inner C p g) x y



theorem basedSliceMetric_image_ball (C : GeneralizedSliceCarrier.{u}) (p : C.carrier)
    (g : RiemannianMetric 3 C.carrier) (x : (basedSliceCarrier C p).carrier) (r : ℝ) :
    Subtype.val '' (basedSliceMetric C p g).ball x r = g.ball x.val r :=
  g.image_ball_subtype_val isClosed_connectedComponent (basedSliceMetric C p g)
    (basedSliceMetric_inner C p g) x r



theorem basedSliceMetric_volume_ball (C : GeneralizedSliceCarrier.{u}) (p : C.carrier)
    (g : RiemannianMetric 3 C.carrier) (x : (basedSliceCarrier C p).carrier) (r : ℝ) :
    (basedSliceMetric C p g).volumeMeasure ((basedSliceMetric C p g).ball x r) =
      g.volumeMeasure (g.ball x.val r) :=
  g.volumeMeasure_ball_subtype_val isClosed_connectedComponent (basedSliceMetric C p g)
    (basedSliceMetric_inner C p g) x r



theorem basedSliceMetric_isCompact_closure_ball
    (C : GeneralizedSliceCarrier.{u}) (p : C.carrier)
    (g : RiemannianMetric 3 C.carrier) (x : (basedSliceCarrier C p).carrier) (r : ℝ)
    (hcompact : IsCompact (closure (g.ball x.val r))) :
    IsCompact (closure ((basedSliceMetric C p g).ball x r)) := by
  have hclosed : IsClosed (Poincare.connectedComponentOpens
      (EuclideanSpace ℝ (Fin 3)) p : Set C.carrier) := isClosed_connectedComponent
  have hpre := hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hcompact
  apply hpre.of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_closure.preimage continuous_subtype_val)
  intro y hy
  apply subset_closure
  change g.edist x.val y.val < ENNReal.ofReal r
  exact (basedSliceMetric_edist C p g x y).symm.trans_lt hy



theorem basedSliceMetric_curvatureDerivativeNorm
    (C : GeneralizedSliceCarrier.{u}) (p : C.carrier)
    (g : RiemannianMetric 3 C.carrier) (D : LeviCivitaData g)
    (m : ℕ) (x : (basedSliceCarrier C p).carrier) :
    (basedSliceMetric C p g).leviCivitaData.curvatureDerivativeNorm m x =
      D.curvatureDerivativeNorm m x.val := by
  have hlocal : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (Subtype.val : (basedSliceCarrier C p).carrier → C.carrier) :=
    Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) _
  exact (basedSliceMetric C p g).leviCivitaData.curvatureDerivativeNorm_eq_pullback D
    isOpen_univ hlocal.contMDiff.contMDiffOn
    (fun y _ => ⟨hlocal.mfderivToContinuousLinearEquiv (by simp) y, rfl⟩)
    (fun y _ v w => basedSliceMetric_inner C p g y v w) m (mem_univ x)

end PoincareConjecture.M30
