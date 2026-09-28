import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.MinimizingGeodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.RadialCurve









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem isCompact_closure_ball_of_metricComplete
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) (R : ℝ) :
    IsCompact (closure (g.ball p R)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  apply (g.isCompact_closedBall_of_metricComplete hc p R).of_isClosed_subset
    isClosed_closure
  apply closure_minimal (fun q (hq : g.edist p q < ENNReal.ofReal R) => hq.le)
  exact isClosed_le (continuous_const.edist continuous_id) continuous_const

theorem exists_orthonormal_radial_exponential_of_metricComplete
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M)
    {R : ℝ} (hR : 0 < R) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    ∃ L : E ≃L[ℝ] E, ∃ e : E → M,
      (∀ v w, g.pullbackCoefficients c.symm (c p) (L v) (L w) = inner ℝ v w) ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R) ∧ e 0 = p ∧
      HasFDerivAt (fun v => c (e v)) L.toContinuousLinearMap 0 ∧
      ∀ v ∈ Metric.ball 0 R,
        g.IsGeodesicOn (fun t : ℝ => e (t • v))
          {t : ℝ | t • v ∈ Metric.ball 0 R} ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          g.tangentNorm (e (t • v))
            (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun u : ℝ => e (u • v)) t 1) = ‖v‖ ∧
          g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t :=
  g.exists_orthonormal_radial_exponential_of_precompact_ball p hR
    (g.isCompact_closure_ball_of_metricComplete hc p R)

theorem exists_minimizing_geodesic_of_metricComplete [PreconnectedSpace M]
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p x : M) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧
      γ 0 = p ∧ γ 1 = x ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p x := by
  let R := (g.edist p x).toReal + 1
  have hR : 0 < R := by dsimp [R]; positivity
  apply g.exists_minimizing_geodesic_of_precompact_ball p x hR
    (g.isCompact_closure_ball_of_metricComplete hc p R)
  change g.edist p x < ENNReal.ofReal R
  rw [← ENNReal.ofReal_toReal (g.edist_ne_top p x)]
  exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr (by dsimp [R]; linarith)

end PoincareConjecture.RiemannianMetric
