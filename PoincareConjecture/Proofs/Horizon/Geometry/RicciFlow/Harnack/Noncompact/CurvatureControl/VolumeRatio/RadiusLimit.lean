import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Precompact
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import Mathlib.Topology.Order.MonotoneConvergence









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [SecondCountableTopology M] in
theorem ball_volume_ne_top_of_metricComplete
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) (r : ℝ) :
    g.volumeMeasure (g.ball p r) ≠ ⊤ := by
  exact (lt_of_le_of_lt (measure_mono (subset_closure : g.ball p r ⊆ _))
    (g.volumeMeasure_lt_top_of_isCompact
      (g.isCompact_closure_ball_of_metricComplete hc p r))).ne

theorem antitoneOn_ball_volume_div_pow
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (p : M) :
    AntitoneOn (fun r : ℝ => (g.volumeMeasure (g.ball p r)).toReal / r ^ n)
      (Ioi 0) := by
  intro r hr s hs hrs
  change 0 < r at hr
  change 0 < s at hs
  have hm := (g.relativeVolumeComparison_of_precompact_ball p hn
    (show 0 < s + 1 by linarith) (le_refl (0 : ℝ))
    (g.isCompact_closure_ball_of_metricComplete hc p (s + 1)) D
    (by intro x _ v; simpa only [mul_zero, neg_zero, zero_mul] using hRic x v)).1
      ⟨hr, by linarith⟩ ⟨hs, by linarith⟩ hrs
  have hden : ENNReal.ofReal (modelVolume n 0 r) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (modelVolume_pos hn (le_refl _) hr)).ne'
  have hreal := ENNReal.toReal_mono
    (ENNReal.div_ne_top (g.ball_volume_ne_top_of_metricComplete hc p r) hden) hm
  rw [ENNReal.toReal_div, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (modelVolume_pos hn (le_refl _) hs).le,
    ENNReal.toReal_ofReal (modelVolume_pos hn (le_refl _) hr).le,
    modelVolume_zero_curvature hn, modelVolume_zero_curvature hn,
    mul_comm (euclideanUnitBallVolume n) (s ^ n),
    mul_comm (euclideanUnitBallVolume n) (r ^ n), ← div_div, ← div_div] at hreal
  exact (div_le_div_iff_of_pos_right (euclideanUnitBallVolume_pos n)).mp hreal

theorem exists_tendsto_ball_volume_div_pow
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (p : M) :
    ∃ V : ℝ, Tendsto
      (fun r : ℝ => (g.volumeMeasure (g.ball p r)).toReal / r ^ n) atTop (𝓝 V) := by
  let f : ℝ → ℝ := fun r =>
    (g.volumeMeasure (g.ball p (max 1 r))).toReal / (max 1 r) ^ n
  have hf : Antitone f := by
    intro r s hrs
    exact g.antitoneOn_ball_volume_div_pow D hn hc hRic p
      (show max 1 r ∈ Ioi (0 : ℝ) from lt_of_lt_of_le zero_lt_one (le_max_left 1 r))
      (show max 1 s ∈ Ioi (0 : ℝ) from lt_of_lt_of_le zero_lt_one (le_max_left 1 s))
      (max_le_max_left 1 hrs)
  have hbdd : BddBelow (range f) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r, rfl⟩
    dsimp only [f]
    positivity
  refine ⟨_, (tendsto_atTop_ciInf hf hbdd).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  simp only [f, max_eq_right hr]

end PoincareConjecture.RiemannianMetric
