import PoincareConjecture.Definitions.Ch11.BlowupLimits
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Lift
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M30



noncomputable def liftFlowCarrier {n : ℕ} (C : FlowCarrier.{0} n) :
    FlowCarrier.{u} n := by
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : MeasurableSpace C.carrier := C.measurableSpace
  letI : BorelSpace C.carrier := C.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : T2Space C.carrier := C.t2Space
  letI : T3Space C.carrier := C.t3Space
  letI : SecondCountableTopology C.carrier := C.secondCountable
  letI : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftChartedSpace _ C.carrier
  letI : IsManifold (𝓡 n) ∞ (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftIsManifold (𝓡 n) C.carrier
  letI : ConnectedSpace (ULift.{u} C.carrier) :=
    Homeomorph.ulift.connectedSpace_iff.mpr inferInstance
  exact {
    carrier := ULift.{u} C.carrier
    topologicalSpace := inferInstance
    measurableSpace := inferInstance
    borelSpace := inferInstance
    chartedSpace := inferInstance
    isManifold := inferInstance
    t2Space := inferInstance
    t3Space := inferInstance
    secondCountable := Homeomorph.ulift.secondCountableTopology
    connected := isConnected_univ }




noncomputable def liftBlowupLimit {J : Set ℝ}
    (L : BlowupLimitFlow.{0} J) : BlowupLimitFlow.{u} J := by
  let C := L.carrier
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : MeasurableSpace C.carrier := C.measurableSpace
  letI : BorelSpace C.carrier := C.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  letI : T2Space C.carrier := C.t2Space
  letI : T3Space C.carrier := C.t3Space
  letI : SecondCountableTopology C.carrier := C.secondCountable
  letI : ConnectedSpace C.carrier := L.connectedSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftChartedSpace _ C.carrier
  letI : IsManifold (𝓡 3) ∞ (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftIsManifold (𝓡 3) C.carrier
  exact {
    carrier := liftFlowCarrier C
    connectedSpace := by
      change ConnectedSpace (ULift.{u} C.carrier)
      exact Homeomorph.ulift.connectedSpace_iff.mpr inferInstance
    base := ULift.up L.base
    flow := L.flow.ulift
    zero_mem := L.zero_mem
    scalar_normalized := by
      rw [RicciFlow.ulift_scalarCurvature]
      exact L.scalar_normalized
    complete := by
      intro t ht
      exact (L.flow.ulift_metricComplete_iff t).mpr (L.complete t ht)
    nonnegative_curvature_operator := by
      intro t ht x
      exact (L.flow.ulift_nonnegativeCurvatureOperator_iff t x).mpr
        (L.nonnegative_curvature_operator t ht x.down)
    curvature_locally_bounded_in_time := by
      intro I hI hIJ
      obtain ⟨B, hB, hbound⟩ := L.curvature_locally_bounded_in_time I hI hIJ
      refine ⟨B, hB, ?_⟩
      intro t ht x
      rw [L.flow.ulift_curvatureTensorNorm t x]
      exact hbound t ht x.down }




theorem liftBlowupLimit_noncollapsed {J : Set ℝ}
    (L : BlowupLimitFlow.{0} J) {kappa : ℝ}
    (h : BlowupLimitNoncollapsed L kappa) :
    BlowupLimitNoncollapsed (liftBlowupLimit.{u} L) kappa := by
  let C := L.carrier
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : MeasurableSpace C.carrier := C.measurableSpace
  let : BorelSpace C.carrier := C.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  let : T2Space C.carrier := C.t2Space
  let : T3Space C.carrier := C.t3Space
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftChartedSpace _ C.carrier
  let : IsManifold (𝓡 3) ∞ (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftIsManifold (𝓡 3) C.carrier
  intro t ht p r hr htime hcurvature
  have hsource : ∀ s ∈ Ioc (t - r ^ 2) t,
      ∀ q ∈ (L.flow.metric t).ball p.down r,
        |(L.flow.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2 := by
    intro s hs q hq
    have hq' : (ULift.up q : ULift.{u} C.carrier) ∈ (L.flow.ulift.metric t).ball p r := by
      change (L.flow.ulift.metric t).edist p (ULift.up q) < ENNReal.ofReal r
      rw [RicciFlow.ulift_edist]
      exact hq
    have hqbound := hcurvature s hs (ULift.up q) hq'
    change |(L.flow.ulift.connection s).curvatureTensorNorm
      (ULift.up q : ULift.{u} C.carrier)| ≤ r⁻¹ ^ 2 at hqbound
    rw [L.flow.ulift_curvatureTensorNorm s (ULift.up q)] at hqbound
    exact hqbound
  have hvolume := h t ht p.down r hr htime hsource
  change ENNReal.ofReal (kappa * r ^ 3) ≤
    calibratedMetricVolume (L.flow.ulift.metric t) ((L.flow.ulift.metric t).ball p r)
  simpa only [calibratedMetricVolume_eq_volumeMeasure,
    RicciFlow.ulift_volumeMeasure_ball] using hvolume

end PoincareConjecture.M30
