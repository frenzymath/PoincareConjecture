import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.RescaledSlice
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Ancient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.SmallCarrier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Source
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.AncientRescaledLimit










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  RicciFlow.uliftChartedSpace RicciFlow.uliftIsManifold
  RicciFlow.smallCarrier RicciFlow.smallChartedSpace RicciFlow.smallIsManifold
  RicciFlow.smallMeasurableSpace RicciFlow.smallBorelSpace RicciFlow.smallT3Space
  uliftSecondCountable uliftConnected

local instance flowCarrierConnected {n : ℕ} (C : FlowCarrier n) : ConnectedSpace C.carrier :=
  connectedSpace_iff_univ.mpr C.connected

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}



theorem metricKappaNoncollapsed_of_selected_blowup_limit
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    {t₀ : ℝ} (ht₀ : t₀ < 0) :
    ∀ (q : ℕ → L.convergence.limit.carrier.carrier) (Q : ℕ → ℝ)
      (hQ : ∀ i, 0 < Q i) {δ : ℝ}, 0 < δ →
      let F := L.convergence.limit.flow
      let H := fun i =>
        (F.ulift : RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0)).openAncientRescaleAt
          (Q i) (hQ i) t₀
      ∀ G : AncientPointedGeometricConvergence
        (fun _ => (FlowCarrier.ofConnectedManifold 3
          (ULift.{u} L.convergence.limit.carrier.carrier)).shrink)
        (fun i t => (H i).shrink.metric (t - δ))
        (fun i => equivShrink (ULift.{u} L.convergence.limit.carrier.carrier)
          (ULift.up (q i))) δ,
        (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) →
        ∀ t ∈ Iio δ, MetricKappaNoncollapsed
          (G.limitFlow.metric t) (G.limitFlow.connection t) (K.kappa / 729) := by
  let : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  intro q Q hQ δ hδ
  let F := L.convergence.limit.flow
  let V : RicciFlow 3 (ULift.{u} L.convergence.limit.carrier.carrier) (Iio 0) := F.ulift
  let H := fun i => V.openAncientRescaleAt (Q i) (hQ i) t₀
  dsimp only
  intro G hcomplete
  let : ConnectedSpace G.limitCarrier.carrier :=
    connectedSpace_iff_univ.mpr G.limitCarrier.connected
  let Fseq := fun i => (H i).shrink.bufferedExpandingFlow δ
  have htime (a b : ℝ) (hb : b < δ) :
      ∀ᶠ i in atTop, Icc a b ⊆ (fun t : ℝ => t - δ) ⁻¹' Iio (-t₀ * Q i) := by
    exact Eventually.of_forall fun i s hs =>
      (sub_neg.mpr (hs.2.trans_lt hb)).trans (mul_pos (neg_pos.mpr ht₀) (hQ i))
  have hκH (i : ℕ) (t : ℝ) (ht : t < δ) :
      MetricKappaNoncollapsed ((H i).metric (t - δ)) ((H i).connection (t - δ))
        (K.kappa / 729) := by
    have hs : t₀ + (t - δ) / Q i < 0 :=
      (add_neg_of_neg_of_nonpos ht₀ (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht.le)
        (hQ i).le))
    have hκ := L.convergence.limit.metricKappaNoncollapsed_of_scalar_derivative_nonnegative
      hC K.kappa_pos L.kappa_noncollapsed L.scalar_curvature_nonnegative_time_derivative hs
    change MetricKappaNoncollapsed
      (rescaledMetric (V.metric (t₀ + (t - δ) / Q i)) (Q i) (hQ i))
      (rescaledMetric_connection (V.metric (t₀ + (t - δ) / Q i))
        (V.connection (t₀ + (t - δ) / Q i)) (Q i) (hQ i)) (K.kappa / 729)
    exact
      (F.metricKappaNoncollapsed_ulift (t₀ + (t - δ) / Q i) hκ :
        MetricKappaNoncollapsed (V.metric (t₀ + (t - δ) / Q i))
          (V.connection (t₀ + (t - δ) / Q i)) (K.kappa / 729)).rescaledMetric (Q i) (hQ i)
  have hvolume := AncientPointedGeometricConvergence.volume_lower_bound_of_static_noncollapse
    (C := fun _ => (FlowCarrier.ofConnectedManifold 3
      (ULift.{u} L.convergence.limit.carrier.carrier)).shrink) Fseq G hδ htime hcomplete
    (K.kappa / 729) (by
      intro t ht
      refine Eventually.of_forall fun i x r hr hcurv => ?_
      change ENNReal.ofReal ((K.kappa / 729) * r ^ 3) ≤
        ((H i).shrink.metric (t - δ)).volumeMeasure (((H i).shrink.metric (t - δ)).ball x r)
      rw [RicciFlow.shrink_volumeMeasure_ball]
      have hv := (hκH i t ht).2
        ((equivShrink (ULift.{u} L.convergence.limit.carrier.carrier)).symm x) r hr (by
          intro y hy
          have hmem : equivShrink (ULift.{u} L.convergence.limit.carrier.carrier) y ∈
              ((H i).shrink.metric (t - δ)).ball x r := by
            simpa only [RiemannianMetric.ball, mem_ofPred_eq, RicciFlow.shrink_edist,
              Equiv.symm_apply_apply] using hy
          have hb := hcurv (equivShrink (ULift.{u} L.convergence.limit.carrier.carrier) y) hmem
          change |((H i).shrink.connection (t - δ)).curvatureTensorNorm
            (equivShrink (ULift.{u} L.convergence.limit.carrier.carrier) y)| ≤ r⁻¹ ^ 2 at hb
          rw [(H i).shrink_curvatureTensorNorm] at hb
          simpa only [Equiv.symm_apply_apply] using hb)
      simpa only [calibratedMetricVolume_eq_volumeMeasure] using hv)
  intro t ht
  refine ⟨div_pos K.kappa_pos (by norm_num), ?_⟩
  intro x r hr hcurv
  rw [calibratedMetricVolume_eq_volumeMeasure]
  exact hvolume t ht x r hr hcurv

end AncientAsymptoticSolitonLimitData
end PoincareConjecture
