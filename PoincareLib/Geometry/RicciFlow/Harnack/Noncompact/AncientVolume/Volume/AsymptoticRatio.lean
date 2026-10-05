import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.AncientLimit
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.VolumeRatio.Monotonicity

/-!
# Positive asymptotic volume of an ancient limit

An all-radius intrinsic volume lower bound bounds the canonical asymptotic
volume ratio below. Applied to the actual ancient pointed limit, this closes
the passage from source volume bounds to positive asymptotic volume used in
Kleiner--Lott, Proposition 41.13, printed p. 2678.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.RiemannianMetric

/-- Uniform intrinsic ball-volume lower bounds bound the canonical
asymptotic ratio below. Completeness makes the finite-radius volumes finite. -/
theorem le_asymptoticVolumeRatio_of_ball_volume_lower_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (p : M) {v : ℝ} (hv : 0 ≤ v)
    (hvolume : ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (v * r ^ n) ≤ g.volumeMeasure (g.ball p r)) :
    v ≤ g.asymptoticVolumeRatio p := by
  apply ge_of_tendsto (g.tendsto_asymptoticVolumeRatio D hn hc hRic p)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  apply (le_div_iff₀ (pow_pos hr n)).mpr
  have h := ENNReal.toReal_mono (g.ball_volume_ne_top_of_metricComplete hc p r)
    (hvolume r hr)
  simpa only [ENNReal.toReal_ofReal (mul_nonneg hv (pow_nonneg hr.le n))] using h

end PoincareMT.RiemannianMetric

namespace PoincareMT.AncientPointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

/-- The same ancient limit constructed by compactness has positive canonical
asymptotic volume if its source sequence has a positive uniform volume bound. -/
theorem asymptoticVolumeRatio_pos_of_source_ball_volume_lower_bound
    {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {J : ℕ → Set ℝ}
    (F : ∀ k, RicciFlow n (C k).carrier (J k)) {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C (fun k => (F k).metric) p T)
    (hn : 1 ≤ n) (hT : 0 < T)
    (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (hRic : ∀ x : G.limitCarrier.carrier, ∀ w : TangentSpace (𝓡 n) x,
      0 ≤ (G.limitFlow.connection 0).ricci x w w)
    {v : ℝ} (hv : 0 < v)
    (hvolume : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      ENNReal.ofReal (v * r ^ n) ≤
        ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) r)) :
    0 < (G.limitFlow.metric 0).asymptoticVolumeRatio G.base :=
  hv.trans_le ((G.limitFlow.metric 0).le_asymptoticVolumeRatio_of_ball_volume_lower_bound
    (G.limitFlow.connection 0) hn hcomplete hRic G.base hv.le
    (G.ball_volume_lower_bound_of_ancient_source_bounds F hT htime hcomplete v hvolume))

end PoincareMT.AncientPointedGeometricConvergence
