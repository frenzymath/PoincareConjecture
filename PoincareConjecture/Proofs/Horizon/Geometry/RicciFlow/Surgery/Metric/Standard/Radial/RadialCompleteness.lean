import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Standard.Radial.AxisLength
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Filter

namespace PoincareConjecture.MetricSurgery

theorem metricComplete_tendsto {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T3Space M] (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    (u : ℕ → M)
    (hu : ∀ epsilon : ℝ≥0∞, 0 < epsilon →
      ∃ N : ℕ, ∀ m ≥ N, ∀ k ≥ N, g.edist (u m) (u k) < epsilon) :
    ∃ x : M, Tendsto u atTop (𝓝 x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous,
      fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : CompleteSpace M := hcomplete
  exact cauchySeq_tendsto_of_complete (EMetric.cauchySeq_iff.mpr hu)

theorem radialArclength_nat_not_bddAbove (g₀ : StandardInitialMetric) :
    ¬ BddAbove (Set.range (fun n : ℕ => radialArclength g₀ (n : ℝ))) := by
  intro hbounded
  have hmono : Monotone (fun n : ℕ => radialArclength g₀ (n : ℝ)) :=
    (radialArclength_strictMono g₀).monotone.comp (fun _ _ h => Nat.cast_le.mpr h)
  have hcauchy : CauchySeq (fun n : ℕ => radialArclength g₀ (n : ℝ)) :=
    (tendsto_atTop_ciSup hmono hbounded).cauchySeq
  have haxis : ∀ epsilon : ℝ≥0∞, 0 < epsilon →
      ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
        g₀.metric.edist (axisPoint (m : ℝ)) (axisPoint (n : ℝ)) < epsilon := by
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hcauchy epsilon hepsilon
    refine ⟨N, fun m hm n hn => ?_⟩
    exact (axis_edist_le_arclength_edist g₀ _ _).trans_lt (hN m hm n hn)
  obtain ⟨x, hx⟩ := metricComplete_tendsto g₀.metric g₀.complete
    (fun n : ℕ => axisPoint (n : ℝ)) haxis
  have hxzero : Tendsto (fun n : ℕ => (n : ℝ)) atTop (𝓝 (x 0)) := by
    have hc : Continuous (fun y : StandardCapSpace => y 0) :=
      PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0
    simpa [Function.comp_def, axisPoint] using hc.continuousAt.tendsto.comp hx
  exact not_tendsto_nhds_of_tendsto_atTop
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop) _ hxzero

theorem radialArclength_not_bddAbove (g₀ : StandardInitialMetric) :
    ¬ BddAbove (Set.range (radialArclength g₀)) := by
  rintro ⟨B, hB⟩
  apply radialArclength_nat_not_bddAbove g₀
  refine ⟨B, ?_⟩
  rintro y ⟨n, rfl⟩
  exact hB ⟨(n : ℝ), rfl⟩

theorem radialArclength_tendsto_atTop (g₀ : StandardInitialMetric) :
    Tendsto (radialArclength g₀) atTop atTop :=
  tendsto_atTop_atTop_of_monotone' (radialArclength_strictMono g₀).monotone
    (radialArclength_not_bddAbove g₀)

end PoincareConjecture.MetricSurgery
