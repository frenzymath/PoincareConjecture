import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data

/-!
# Curvature of the retained M30 ancient solution

The infinite-horizon M30 identification retains the original limit metric
and connection on the same carrier and real clock. Combining its metric
equality and heterogeneous connection equality in a dependent pair transports
scalar curvature and the curvature tensor norm.

These are the identification steps used in the final ancient-limit argument
after Morgan--Tian Claim 11.35, printed p. 291. See
`proof-work/tasks/M32/derivations/claim11_35-ancient-round-factor.md`.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M32

open scoped Manifold ContDiff ENNReal

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

/-- The actual ancient solution supplied by M30 has the original limit's
scalar curvature at every ancient time, with the same clock and point.
Morgan--Tian, the final ancient-limit argument after Claim 11.35, p. 291. -/
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

/-- The actual ancient solution supplied by M30 has the original limit's
curvature tensor norm at every ancient time, with the same clock and point.
Morgan--Tian, the final ancient-limit argument after Claim 11.35, p. 291. -/
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

end PoincareMT.M32
