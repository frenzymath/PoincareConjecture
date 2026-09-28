import PoincareConjecture.Proofs.M47.TerminalSourceCharts
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.DistanceLower
import PoincareConjecture.Proofs.M36.MetricComparison










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M]



theorem terminalSourceNormal_chart_distance_bounds
    (g : RiemannianMetric 3 M) {R rho : ℝ} (C : TerminalSourceChart g R)
    (hrho : 0 < rho) (hrhoR : 2 * rho < R)
    (hbound : ∀ x ∈ Metric.closedBall (0 : E) (2 * rho), ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients C.chart x v v ∧
        g.pullbackCoefficients C.chart x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2)
    {x y : E} (hx : x ∈ Metric.ball 0 (rho / 2))
    (hy : y ∈ Metric.ball 0 (rho / 2)) :
    (1 / 2 : ℝ) * dist x y ≤ (g.edist (C.chart x) (C.chart y)).toReal ∧
      (g.edist (C.chart x) (C.chart y)).toReal ≤ (3 / 2 : ℝ) * dist x y := by
  have hsmall : Metric.ball (0 : E) (3 * (rho / 2)) ⊆
      Metric.closedBall 0 (2 * rho) :=
    (Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall
  have hxR : x ∈ Metric.ball (0 : E) R :=
    Metric.ball_subset_ball (by linarith) hx
  have hyR : y ∈ Metric.ball (0 : E) R :=
    Metric.ball_subset_ball (by linarith) hy
  have hfinite : g.edist (C.chart x) (C.chart y) ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
    calc
      _ ≤ g.edist (C.chart x) C.centre + g.edist C.centre (C.chart y) :=
        M36.metric_edist_triangle g _ _ _
      _ = ENNReal.ofReal ‖x‖ + ENNReal.ofReal ‖y‖ := by
        rw [show g.edist (C.chart x) C.centre = g.edist C.centre (C.chart x) by
          let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
            ⟨g.toRiemannianMetric⟩
          exact Manifold.riemannianEDist_comm,
          C.distance x hxR, C.distance y hyR]
  constructor
  · have h := g.edist_le_mul_edist_of_normal_pullback_lower C.centre C.chart
      (by positivity : 0 < rho / 2) (by linarith : 3 * (rho / 2) ≤ R)
      (by norm_num : (0 : ℝ) < 1 / 4) C.source C.target C.distance
      (fun z hz v => (hbound z (hsmall hz) v).1) hx hy
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) h
    have hsqrt : Real.sqrt ((1 : ℝ) / 4) = 1 / 2 := by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simp only [hsqrt, edist_dist, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal dist_nonneg] at hreal
    norm_num at hreal
    linarith only [hreal]
  · have h := g.toReal_edist_le_of_pullback_upper Metric.isOpen_ball
      (convex_ball (0 : E) (rho / 2))
      (C.smooth.mono (Metric.ball_subset_ball (by linarith : rho / 2 ≤ R)))
      (by norm_num : (0 : ℝ) ≤ 9 / 4)
      (fun z hz v => (hbound z (hsmall (Metric.ball_subset_ball (by linarith) hz)) v).2)
      hx hy
    have hsqrt : Real.sqrt ((9 : ℝ) / 4) = 3 / 2 := by
      rw [show (9 : ℝ) / 4 = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simpa only [hsqrt] using h

end PoincareConjecture.M47
