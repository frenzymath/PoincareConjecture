import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Balls
import PoincareConjecture.Proofs.Horizon.MeasureTheory.Integral.GaussianMoment.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RiemannianMetric

theorem exists_first_moment_bound_of_gaussian
    (n : ℕ) (A B c : ℝ) (hn : 0 < n) (hA : 1 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        [PreconnectedSpace M] (g : RiemannianMetric n M), MetricComplete g →
        (∀ x : M, ∀ r R : ℝ, 0 < r → r ≤ R →
          g.volumeMeasure.real (g.ball x R) ≤ A * (R / r) ^ n * Real.exp (B * R) *
            g.volumeMeasure.real (g.ball x r)) →
        ∀ H : M → M → ℝ → ℝ,
          (∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x : M,
            Measurable (fun y => H x y t) ∧ (∀ y, 0 ≤ H x y t) ∧
              (∀ y, H x y t ≤ A / g.volumeMeasure.real (g.ball x (Real.sqrt t)) *
                Real.exp (-(g.edist x y).toReal ^ 2 / (c * t)))) →
          (∀ x t, 0 < t → t ≤ 1 →
            Integrable (fun y => (g.edist x y).toReal * H x y t) g.volumeMeasure ∧
            (∫ y, (g.edist x y).toReal * H x y t ∂g.volumeMeasure) ≤ C * Real.sqrt t) ∧
          (∀ x t, 0 < t → t ≤ 1 →
            (∫ y, (g.edist x y).toReal * H x y t ∂g.volumeMeasure) ≤ C) ∧
          TendstoUniformly (fun t x => ∫ y, (g.edist x y).toReal * H x y t ∂g.volumeMeasure)
            (fun _ => 0) (𝓝[>] 0) ∧
          Tendsto (fun t => ⨆ x, ∫ y, (g.edist x y).toReal * H x y t ∂g.volumeMeasure)
            (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    Poincare.MeasureTheory.GaussianMoment.exists_gaussian_first_moment_bound.{u} n A B c hn hA hB hc
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ g hcomplete hgrowth H hH
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : MetricSpace M := EMetricSpace.toMetricSpace (fun x y => g.edist_ne_top x y)
  have hdist (x y : M) : dist x y = (g.edist x y).toReal := rfl
  have hball (x : M) (r : ℝ) : Metric.ball x r = g.ball x r := by
    ext y
    change dist y x < r ↔ EDist.edist x y < ENNReal.ofReal r
    rw [dist_comm, edist_lt_ofReal]
  have hballs (x : M) (r : ℝ) (hr : 0 < r) :
      0 < g.volumeMeasure (Metric.ball x r) ∧ g.volumeMeasure (Metric.ball x r) < ⊤ := by
    rw [hball]
    exact ⟨g.volumeMeasure_ball_pos x hr, g.volumeMeasure_ball_lt_top hcomplete x r⟩
  have hgrowth' : ∀ x : M, ∀ r R : ℝ, 0 < r → r ≤ R →
      g.volumeMeasure.real (Metric.ball x R) ≤
        A * (R / r) ^ n * Real.exp (B * R) * g.volumeMeasure.real (Metric.ball x r) := by
    simpa only [hball] using hgrowth
  have hH' : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x : M,
      Measurable (fun y => H x y t) ∧ (∀ y, 0 ≤ H x y t) ∧
        (∀ y, H x y t ≤ A / g.volumeMeasure.real (Metric.ball x (Real.sqrt t)) *
          Real.exp (-dist x y ^ 2 / (c * t))) := by
    simpa only [hball, hdist] using hH
  have hmoment (x : M) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
      Integrable (fun y => (g.edist x y).toReal * H x y t) g.volumeMeasure ∧
        (∫ y, (g.edist x y).toReal * H x y t ∂g.volumeMeasure) ≤ C * Real.sqrt t := by
    obtain ⟨hm, hn0, hg⟩ := hH' t ht ht1 x
    exact (hbound M g.volumeMeasure hballs hgrowth' x t ht ht1 (fun y => H x y t) hm hn0 hg).2
  refine ⟨hmoment, ?_, ?_, ?_⟩
  · intro x t ht ht1
    exact (hmoment x t ht ht1).2.trans
      (mul_le_of_le_one_right hC.le (Real.sqrt_le_one.mpr ht1))
  · exact Poincare.MeasureTheory.GaussianMoment.tendstoUniformly_gaussian_first_moment
      n A B c hn hA hB hc g.volumeMeasure hballs hgrowth' (fun t x y => H x y t) hH'
  · have hlim : Tendsto (fun t : ℝ => C * Real.sqrt t) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul
        (Real.continuous_sqrt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun t : ℝ => C * Real.sqrt t) (𝓝[>] 0) (𝓝 (C * Real.sqrt 0)))
    apply squeeze_zero' ?_ ?_ hlim
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
      exact Real.iSup_nonneg fun x => integral_nonneg
        (fun y => mul_nonneg ENNReal.toReal_nonneg ((hH t ht ht1.le x).2.1 y))
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
      exact Real.iSup_le (fun x => (hmoment x t ht ht1.le).2)
        (mul_nonneg hC.le (Real.sqrt_nonneg t))

end PoincareConjecture.RiemannianMetric
