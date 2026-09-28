import PoincareConjecture.Proofs.M47.TerminalSourceNormalDistance
import PoincareConjecture.Proofs.M47.TerminalSourceChartsEllipticity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace E N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T3Space M]



theorem terminalSourceNormal_buffered_readouts
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (h : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (hsource : e.source = univ)
    (hmetric : ∀ x (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w))
    (p0 p : M) {R A ρ H : ℝ} (C : TerminalSourceChart g R)
    (hA : 0 < A) (hAR : A ≤ R) (hρ : 0 < ρ)
    (hρR : 2 * ρ < R) (hsmall : ∀ s : ℝ, |s| ≤ 2 * ρ →
      (H * s ^ 2) * Real.exp (max 1 (H * s ^ 2)) ≤ 3)
    (hcentre : C.centre = p)
    (hcurv : ∀ y ∈ C.chart '' Metric.ball 0 R, D.curvatureTensorNorm y ≤ H)
    (hp : p ∈ g.ball p0 A)
    (hcover : h.ball (e p0) (6 * R) ⊆ e.target) :
    (∀ x ∈ Metric.closedBall (0 : E) (2 * ρ), ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients C.chart x v v ∧
        g.pullbackCoefficients C.chart x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) ∧
    (∀ x ∈ Metric.closedBall (0 : E) ρ, ∀ y ∈ Metric.closedBall (0 : E) ρ,
      h.edist (e (C.chart x)) (e (C.chart y)) = g.edist (C.chart x) (C.chart y)) := by
  have hEll : ∀ x ∈ Metric.closedBall (0 : E) (2 * ρ), ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients C.chart x v v ∧
        g.pullbackCoefficients C.chart x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2 := by
    intro x hx v
    exact C.terminal_bounds D hρR hsmall hcurv hx v
  refine ⟨hEll, ?_⟩
  intro x hx y hy
  have hxR : x ∈ Metric.ball (0 : E) R :=
    Metric.closedBall_subset_ball (by linarith) hx
  have hyR : y ∈ Metric.ball (0 : E) R :=
    Metric.closedBall_subset_ball (by linarith) hy
  have hpx : g.edist p (C.chart x) < ENNReal.ofReal R := by
    have hdistx : g.edist p (C.chart x) = ENNReal.ofReal ‖x‖ := by
      simpa only [hcentre] using C.distance x hxR
    rw [hdistx]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < R)).mpr
      (by simpa only [Metric.mem_ball, dist_zero_right] using hxR)
  have hpy : g.edist p (C.chart y) < ENNReal.ofReal R := by
    have hdisty : g.edist p (C.chart y) = ENNReal.ofReal ‖y‖ := by
      simpa only [hcentre] using C.distance y hyR
    rw [hdisty]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < R)).mpr
      (by simpa only [Metric.mem_ball, dist_zero_right] using hyR)
  have hxp : g.edist p0 (C.chart x) < ENNReal.ofReal (2 * R) := by
    calc
      g.edist p0 (C.chart x) ≤ g.edist p0 p + g.edist p (C.chart x) :=
        M36.metric_edist_triangle g p0 p (C.chart x)
      _ < ENNReal.ofReal A + ENNReal.ofReal R := ENNReal.add_lt_add hp hpx
      _ = ENNReal.ofReal (A + R) := (ENNReal.ofReal_add hA.le (by linarith : 0 ≤ R)).symm
      _ ≤ ENNReal.ofReal (2 * R) := ENNReal.ofReal_le_ofReal (by linarith)
  have hyp : g.edist p0 (C.chart y) < ENNReal.ofReal (2 * R) := by
    calc
      g.edist p0 (C.chart y) ≤ g.edist p0 p + g.edist p (C.chart y) :=
        M36.metric_edist_triangle g p0 p (C.chart y)
      _ < ENNReal.ofReal A + ENNReal.ofReal R := ENNReal.add_lt_add hp hpy
      _ = ENNReal.ofReal (A + R) := (ENNReal.ofReal_add hA.le (by linarith : 0 ≤ R)).symm
      _ ≤ ENNReal.ofReal (2 * R) := ENNReal.ofReal_le_ofReal (by linarith)
  have hdist := terminalSourceNormal_edist_eq_on_buffer g h e hsource hmetric p0
    (by linarith : 0 < R) hcover hxp hyp
  exact hdist.symm

end PoincareConjecture.M47
