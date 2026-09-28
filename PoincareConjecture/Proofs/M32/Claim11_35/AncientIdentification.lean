import PoincareConjecture.Definitions.M30ControlledBlowupLimits














set_option autoImplicit false

universe u

namespace PoincareConjecture.M32

open scoped Manifold ContDiff ENNReal

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable




theorem m30AncientIdentification_scalarCurvature_eq
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) {κ : ℝ}
    (I : M30AncientKappaIdentification L κ) (t : ℝ) (ht : t ≤ 0)
    (x : L.carrier.carrier) :
    letI : ConnectedSpace L.carrier.carrier := L.connectedSpace
    (I.certificate.solution.flow.connection t).scalarCurvature x =
      (L.flow.connection t).scalarCurvature x := by
  let : ConnectedSpace L.carrier.carrier := L.connectedSpace
  have hdata :
      (⟨I.certificate.solution.flow.metric t, I.certificate.solution.flow.connection t⟩ :
        Σ g : RiemannianMetric 3 L.carrier.carrier, LeviCivitaData g) =
      ⟨L.flow.metric t, L.flow.connection t⟩ :=
    Sigma.ext (I.certificate.metric_eq t ht) (I.connection_eq t ht)
  have hscalar := congrArg
    (fun d : Σ g : RiemannianMetric 3 L.carrier.carrier, LeviCivitaData g =>
      d.2.scalarCurvature x) hdata
  exact hscalar




theorem m30AncientIdentification_curvatureTensorNorm_eq
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval ⊤)) {κ : ℝ}
    (I : M30AncientKappaIdentification L κ) (t : ℝ) (ht : t ≤ 0)
    (x : L.carrier.carrier) :
    letI : ConnectedSpace L.carrier.carrier := L.connectedSpace
    (I.certificate.solution.flow.connection t).curvatureTensorNorm x =
      (L.flow.connection t).curvatureTensorNorm x := by
  let : ConnectedSpace L.carrier.carrier := L.connectedSpace
  have hdata :
      (⟨I.certificate.solution.flow.metric t, I.certificate.solution.flow.connection t⟩ :
        Σ g : RiemannianMetric 3 L.carrier.carrier, LeviCivitaData g) =
      ⟨L.flow.metric t, L.flow.connection t⟩ :=
    Sigma.ext (I.certificate.metric_eq t ht) (I.connection_eq t ht)
  have hnorm := congrArg
    (fun d : Σ g : RiemannianMetric 3 L.carrier.carrier, LeviCivitaData g =>
      d.2.curvatureTensorNorm x) hdata
  exact hnorm

end PoincareConjecture.M32
