import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.BallComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Spheres
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.RadiusSqueeze
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.VolumeRatio.Monotonicity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

namespace PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

theorem tendsto_riemannianBallVolume
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    {t r : ℝ} (ht : t ∈ Ioo T' T) (hr : 0 < r)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt t)) :
    Tendsto (fun k => (S.flow (G.subsequence k)).riemannianBallVolume t r)
      atTop (𝓝 (G.limitFlow.riemannianBallVolume t r)) := by
  apply Poincare.tendsto_of_ball_volume_radius_squeeze n
  · exact (G.limitFlow.metricAt t).continuousAt_ball_volume_of_metricComplete
      hcomplete G.limitFlow.base hr
  · intro C hC
    exact (G.eventually_ball_volume_bounds hT ht hcomplete hr hC).mono (fun _ h => h.1)
  · intro C hC
    exact (G.eventually_ball_volume_bounds hT ht hcomplete hr hC).mono (fun _ h => h.2)

theorem ball_volume_lower_bound_of_eventually
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    {t : ℝ} (ht : t ∈ Ioo T' T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt t))
    (v : ℝ)
    (hvolume : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      ENNReal.ofReal (v * r ^ n) ≤
        (S.flow (G.subsequence k)).riemannianBallVolume t r) :
    ∀ r : ℝ, 0 < r → ENNReal.ofReal (v * r ^ n) ≤
      G.limitFlow.riemannianBallVolume t r := by
  intro r hr
  exact ge_of_tendsto (G.tendsto_riemannianBallVolume hT ht hr hcomplete) (hvolume r hr)

theorem le_asymptoticVolumeRatio_of_eventually
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    {t : ℝ} (ht : t ∈ Ioo T' T) (hn : 1 ≤ n)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt t))
    (hRic : ∀ x : G.limitCarrier.carrier, ∀ u : TangentSpace (𝓡 n) x,
      0 ≤ (G.limitFlow.flow.connection t).ricci x u u)
    (v : ℝ)
    (hvolume : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      ENNReal.ofReal (v * r ^ n) ≤
        (S.flow (G.subsequence k)).riemannianBallVolume t r) :
    v ≤ (G.limitFlow.metricAt t).asymptoticVolumeRatio G.limitFlow.base := by
  let g := G.limitFlow.metricAt t
  have hb := G.ball_volume_lower_bound_of_eventually hT ht hcomplete v hvolume
  apply ge_of_tendsto (g.tendsto_asymptoticVolumeRatio
    (G.limitFlow.flow.connection t) hn hcomplete hRic G.limitFlow.base)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  apply (le_div_iff₀ (pow_pos hr n)).mpr
  exact (ENNReal.ofReal_le_iff_le_toReal
    (g.ball_volume_ne_top_of_metricComplete hcomplete G.limitFlow.base r)).mp (hb r hr)

theorem ball_volume_convergence_of_complete_slices
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (_hsource : ∀ k : ℕ, ∀ t ∈ Ioo T' T,
      (S.carrier k).metricComplete ((S.flow k).metricAt t))
    (hlimit : ∀ t ∈ Ioo T' T,
      G.limitCarrier.metricComplete (G.limitFlow.metricAt t)) :
    ∀ t ∈ Ioo T' T, ∀ r : ℝ, 0 < r →
      Tendsto (fun k => (S.flow (G.subsequence k)).riemannianBallVolume t r)
        atTop (𝓝 (G.limitFlow.riemannianBallVolume t r)) := by
  intro t ht r hr
  exact G.tendsto_riemannianBallVolume hT ht hr (hlimit t ht)

end PointedGeometricConvergence
end PoincareConjecture
