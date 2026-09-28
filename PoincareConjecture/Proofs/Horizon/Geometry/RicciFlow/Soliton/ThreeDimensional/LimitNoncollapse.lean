import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.AsymptoticSoliton
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Lift

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientLimitFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem curvatureTensorNorm_le_scalarCurvature
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientLimitFlow 3)
    (s : ℝ) (hs : s < 0) (x : L.carrier.carrier) :
    (L.flow.connection s).curvatureTensorNorm x ≤
      9 * (L.flow.connection s).scalarCurvature x := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} L.carrier.carrier) :=
    Poincare.Manifold.uliftChartedSpace _ L.carrier.carrier
  let : IsManifold (𝓡 3) ∞ (ULift.{u} L.carrier.carrier) :=
    Poincare.Manifold.uliftIsManifold (𝓡 3) L.carrier.carrier
  let G : RicciFlow 3 (ULift.{u} L.carrier.carrier) (Iio 0) := L.flow.ulift
  have hoperator := (L.flow.ulift_nonnegativeCurvatureOperator_iff s (ULift.up.{u} x)).mpr
    (L.nonnegative_curvature_operator s hs x)
  have hbound := (G.connection s).curvatureTensorNorm_le_scalarCurvature
    (hC.tensor_calculus 3 _ (G.metric s) (G.connection s)) (ULift.up.{u} x) hoperator
  simp only [G, L.flow.ulift_curvatureTensorNorm, L.flow.ulift_scalarCurvature] at hbound
  norm_num at hbound
  exact hbound

theorem scalarCurvature_monotoneOn_of_derivative_nonnegative
    (L : AncientLimitFlow 3)
    (hderivative : ∀ t : ℝ, t < 0 → ∀ x : L.carrier.carrier,
      ∃ dR : ℝ, HasDerivWithinAt
        (fun s => (L.flow.connection s).scalarCurvature x) dR (Iio 0) t ∧ 0 ≤ dR)
    (x : L.carrier.carrier) :
    MonotoneOn (fun t => (L.flow.connection t).scalarCurvature x) (Iio 0) := by
  classical
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iio 0)
    (fun s hs => (hderivative s hs x).choose_spec.1.continuousWithinAt)
    (f' := fun s => if hs : s < 0 then (hderivative s hs x).choose else 0)
  · intro s hs
    have hs' : s ∈ Iio (0 : ℝ) := interior_subset hs
    simpa only [dif_pos (show s < 0 from hs')] using
      (hderivative s hs' x).choose_spec.1.mono interior_subset
  · intro s hs
    have hs' : s ∈ Iio (0 : ℝ) := interior_subset hs
    simpa only [dif_pos (show s < 0 from hs')] using (hderivative s hs' x).choose_spec.2

theorem metricKappaNoncollapsed_of_scalar_derivative_nonnegative
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientLimitFlow 3)
    {κ : ℝ} (hκ : 0 < κ) (hnoncollapse : AncientLimitKappaNoncollapsed L κ)
    (hderivative : ∀ t : ℝ, t < 0 → ∀ x : L.carrier.carrier,
      ∃ dR : ℝ, HasDerivWithinAt
        (fun s => (L.flow.connection s).scalarCurvature x) dR (Iio 0) t ∧ 0 ≤ dR)
    {t : ℝ} (ht : t < 0) :
    MetricKappaNoncollapsed (L.flow.metric t) (L.flow.connection t) (κ / 729) := by
  classical
  let : PreconnectedSpace L.carrier.carrier := ⟨L.carrier.connected.isPreconnected⟩
  let : Nonempty L.carrier.carrier := ⟨L.base⟩
  let : ConnectedSpace L.carrier.carrier := ⟨inferInstance⟩
  apply RicciFlow.metricKappaNoncollapsed_of_scalar_comparison L.flow hκ
    (L.curvatureTensorNorm_le_scalarCurvature hC)
  · exact L.scalarCurvature_monotoneOn_of_derivative_nonnegative hderivative
  · intro s hs p r hr hbound
    exact hnoncollapse r hr s hs p r hr le_rfl hbound
  · exact ht

end PoincareConjecture.AncientLimitFlow
