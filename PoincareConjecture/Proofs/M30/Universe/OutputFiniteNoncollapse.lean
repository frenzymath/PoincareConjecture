import PoincareConjecture.Proofs.M30.Universe.OutputLift
import PoincareConjecture.Definitions.M30ControlledBlowupLimits

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M30

theorem liftBlowupLimit_limitNoncollapsedAtScale {J : Set ℝ}
    (L : BlowupLimitFlow.{0} J) {kappa r₀ : ℝ}
    (h : M30LimitNoncollapsedAtScale L kappa r₀) :
    M30LimitNoncollapsedAtScale (liftBlowupLimit.{u} L) kappa r₀ := by
  let C := L.carrier
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : MeasurableSpace C.carrier := C.measurableSpace
  let : BorelSpace C.carrier := C.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  let : T3Space C.carrier := C.t3Space
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftChartedSpace _ C.carrier
  let : IsManifold (𝓡 3) ∞ (ULift.{u} C.carrier) :=
    Poincare.Manifold.uliftIsManifold (𝓡 3) C.carrier
  intro t ht p r hr hr₀ htime hcurvature
  change ULift.{u} C.carrier at p
  change ∀ s ∈ Ioc (t - r ^ 2) t, ∀ q ∈ (L.flow.ulift.metric t).ball p r,
      |(L.flow.ulift.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2 at hcurvature
  have hsource : ∀ s ∈ Ioc (t - r ^ 2) t,
      ∀ q ∈ (L.flow.metric t).ball p.down r,
        |(L.flow.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2 := by
    intro s hs q hq
    have hq' : (ULift.up q : ULift.{u} C.carrier) ∈
        (L.flow.ulift.metric t).ball p r := by
      change (L.flow.ulift.metric t).edist p (ULift.up q) < ENNReal.ofReal r
      rw [RicciFlow.ulift_edist]
      exact hq
    have hqbound := hcurvature s hs (ULift.up q) hq'
    change |(L.flow.ulift.connection s).curvatureTensorNorm
      (ULift.up q : ULift.{u} C.carrier)| ≤ r⁻¹ ^ 2 at hqbound
    rw [L.flow.ulift_curvatureTensorNorm s (ULift.up q)] at hqbound
    exact hqbound
  have hvolume := h t ht p.down r hr hr₀ htime hsource
  change ENNReal.ofReal (kappa * r ^ 3) ≤
    calibratedMetricVolume (L.flow.ulift.metric t)
      ((L.flow.ulift.metric t).ball p r)
  simpa only [calibratedMetricVolume_eq_volumeMeasure,
    RicciFlow.ulift_volumeMeasure_ball] using hvolume

end PoincareConjecture.M30
