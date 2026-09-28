import PoincareConjecture.Proofs.M47.TerminalSourceNormalChartDistances
import PoincareConjecture.Proofs.M47.TerminalSourceNormalDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace E N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T3Space M]

theorem terminalSourceNormal_ambient_chart_readouts
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (hsource : e.source = univ)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w))
    (p0 : M) {A Rbig R rho : ℝ} (C : TerminalSourceChart g R)
    (hA : 0 < A) (hAR : A ≤ Rbig) (hRbig : R ≤ Rbig)
    (hrho : 0 < rho) (hrhoR : 2 * rho < R)
    (hcentre : C.centre ∈ g.ball p0 A)
    (hcover : h.ball (e p0) (6 * Rbig) ⊆ e.target) :
    (∀ x ∈ Metric.closedBall (0 : E) rho,
      e (C.chart x) ∈ h.ball (e p0) (A + R)) ∧
    (∀ x ∈ Metric.closedBall (0 : E) rho, ∀ y ∈ Metric.closedBall (0 : E) rho,
      h.edist (e (C.chart x)) (e (C.chart y)) = g.edist (C.chart x) (C.chart y)) := by
  have hR : 0 < R := by linarith only [hrho, hrhoR]
  have hpoint (x : E) (hx : x ∈ Metric.closedBall (0 : E) rho) :
      C.chart x ∈ g.ball p0 (A + R) := by
    have hxR : x ∈ Metric.ball (0 : E) R := Metric.closedBall_subset_ball (by linarith) hx
    have hradial : g.edist C.centre (C.chart x) < ENNReal.ofReal R := by
      rw [C.distance x hxR]
      exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr
        (by simpa only [Metric.mem_ball, dist_zero_right] using hxR)
    calc
      _ ≤ g.edist p0 C.centre + g.edist C.centre (C.chart x) :=
        M36.metric_edist_triangle g _ _ _
      _ < ENNReal.ofReal A + ENNReal.ofReal R := ENNReal.add_lt_add hcentre hradial
      _ = ENNReal.ofReal (A + R) := (ENNReal.ofReal_add hA.le hR.le).symm
  refine ⟨fun x hx => (terminalSourceNormal_edist_le g h e hsource hmetric _ _).trans_lt
    (hpoint x hx), ?_⟩
  intro x hx y hy
  have hbuffer (z : E) (hz : z ∈ Metric.closedBall (0 : E) rho) :
      C.chart z ∈ g.ball p0 (2 * Rbig) :=
    (hpoint z hz).trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  exact (terminalSourceNormal_edist_eq_on_buffer g h e hsource hmetric p0
    (hA.trans_le hAR) hcover (hbuffer x hx) (hbuffer y hy)).symm

theorem terminalSourceNormal_ambient_chart_distance_bounds
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (hsource : e.source = univ)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w))
    (p0 : M) {A Rbig R rho : ℝ} (C : TerminalSourceChart g R)
    (hA : 0 < A) (hAR : A ≤ Rbig) (hRbig : R ≤ Rbig)
    (hrho : 0 < rho) (hrhoR : 2 * rho < R)
    (hcentre : C.centre ∈ g.ball p0 A)
    (hcover : h.ball (e p0) (6 * Rbig) ⊆ e.target)
    (hbound : ∀ x ∈ Metric.closedBall (0 : E) (2 * rho), ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients C.chart x v v ∧
        g.pullbackCoefficients C.chart x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2)
    {x y : E} (hx : x ∈ Metric.ball 0 (rho / 2))
    (hy : y ∈ Metric.ball 0 (rho / 2)) :
    (1 / 2 : ℝ) * dist x y ≤ (h.edist (e (C.chart x)) (e (C.chart y))).toReal ∧
      (h.edist (e (C.chart x)) (e (C.chart y))).toReal ≤ (3 / 2 : ℝ) * dist x y := by
  have hxy : Metric.ball (0 : E) (rho / 2) ⊆ Metric.closedBall 0 rho :=
    (Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall
  rw [(terminalSourceNormal_ambient_chart_readouts g h e hsource hmetric p0 C
    hA hAR hRbig hrho hrhoR hcentre hcover).2 x (hxy hx) y (hxy hy)]
  exact terminalSourceNormal_chart_distance_bounds g C hrho hrhoR hbound hx hy

end PoincareConjecture.M47
