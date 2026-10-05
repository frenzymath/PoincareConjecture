import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.Volume
import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Seed.Nonnegative.SeedNonnegativeVolume
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.CapBallVolumeReference
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Distance.MetricComparison
import PoincareLib.Geometry.RicciFlow.Positivity.PointwiseFlatness

/-!
# Uniform small-ball density on the fixed standard birth model

One actual tip ball and nonnegative Ricci comparison control every
smaller ball with center in a fixed model region. The density is chosen
before the center and radius. Source: MT Theorem 1.34, p. 19, and the
Uniform Seed, pp. 392-394; derivations/seed-cap-model-density.md.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.Proofs.M47

/-- The actual complete standard initial metric has one positive cubic
density on every bounded center region and bounded positive radius. -/
theorem exists_seed_cap_model_density (g0 : StandardInitialMetric)
    {A0 Rmax : ℝ} (hA0 : 0 < A0) (hRmax : 0 < Rmax) :
    ∃ k : ℝ, 0 < k ∧ ∀ x ∈ g0.metric.ball 0 A0,
      ∀ r : ℝ, 0 < r → r ≤ Rmax →
        ENNReal.ofReal (k * r ^ 3) ≤
          calibratedMetricVolume g0.metric (g0.metric.ball x r) := by
  let D := A0 + Rmax + 1
  let V := calibratedMetricVolume g0.metric (g0.metric.ball 0 1)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hVpos : 0 < V := M15.calibratedMetricVolume_ball_pos g0.metric 0 (by norm_num)
  have hVfinite : V < ⊤ := M15.calibratedMetricVolume_ball_lt_top_of_precompact
    g0.metric 0 1 (M09.isCompact_closure_metric_ball g0.metric g0.complete 0 1)
  have hVreal : 0 < V.toReal := ENNReal.toReal_pos hVpos.ne' hVfinite.ne
  let k := V.toReal / D ^ 3
  have hk : 0 < k := div_pos hVreal (pow_pos hD 3)
  refine ⟨k, hk, ?_⟩
  intro x hx r hr hrmax
  have hball : g0.metric.ball 0 1 ⊆ g0.metric.ball x D := by
    intro y hy
    have hx' : g0.metric.edist x 0 < ENNReal.ofReal A0 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
        ⟨g0.metric.toRiemannianMetric⟩
      change Manifold.riemannianEDist (𝓡 3) x 0 < ENNReal.ofReal A0
      rw [Manifold.riemannianEDist_comm]
      exact hx
    calc
      g0.metric.edist x y ≤ g0.metric.edist x 0 + g0.metric.edist 0 y :=
        M36.metric_edist_triangle g0.metric x 0 y
      _ < ENNReal.ofReal A0 + ENNReal.ofReal 1 := ENNReal.add_lt_add hx' hy
      _ = ENNReal.ofReal (A0 + 1) := (ENNReal.ofReal_add hA0.le (by norm_num)).symm
      _ ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal (by dsimp only [D]; linarith)
  have hvolume : ENNReal.ofReal (k * D ^ 3) ≤
      calibratedMetricVolume g0.metric (g0.metric.ball x D) := by
    have hcancel : k * D ^ 3 = V.toReal := div_mul_cancel₀ _ (pow_ne_zero 3 hD.ne')
    rw [hcancel, ENNReal.ofReal_toReal hVfinite.ne]
    exact measure_mono hball
  exact seed_nonnegative_ball_volume g0.metric g0.connection x hD hr
    (hrmax.trans (by dsimp only [D]; linarith only [hA0]))
    (M09.isCompact_closure_metric_ball g0.metric g0.complete x D)
    (fun y _hy v => M04.nonneg_ricci_of_nonnegativeSectionalAt g0.connection y
      (g0.nonnegative_sectional y) v) hvolume

end PoincareMT.Proofs.M47
