import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PrecompactDifferential
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PrecompactGauss









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]


structure TerminalSourceChart (g : RiemannianMetric 3 M) (R : ℝ) where
  chart : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞
  centre : M
  source : chart.source = Metric.ball 0 R
  target : chart.target = g.ball centre R
  zero : chart 0 = centre
  normalized : ∀ v w, g.pullbackCoefficients chart 0 v w = inner ℝ v w
  radial : ∀ v ∈ Metric.ball 0 R,
    g.IsGeodesicOn (fun t : ℝ => chart (t • v)) {t | t • v ∈ Metric.ball 0 R}
  speed : ∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
    g.tangentNorm (chart (t • v))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s : ℝ => chart (s • v)) t 1) = ‖v‖
  distance : ∀ v ∈ Metric.ball 0 R, g.edist centre (chart v) = ENNReal.ofReal ‖v‖

namespace TerminalSourceChart

variable {g : RiemannianMetric 3 M} {R : ℝ} (C : TerminalSourceChart g R)

theorem smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ C.chart (Metric.ball 0 R) := by
  simpa only [C.source] using C.chart.contMDiffOn

theorem invertible {x : E} (hx : x ∈ Metric.ball 0 R) :
    (mfderiv (𝓡 3) (𝓡 3) C.chart x).IsInvertible := by
  exact ⟨(C.chart.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
    (C.source.symm ▸ hx)).mfderivToContinuousLinearEquiv (by simp), rfl⟩

theorem gauss {x : E} (hx : x ∈ Metric.ball 0 R) (w : E) :
    g.pullbackCoefficients C.chart x x w = inner ℝ x w :=
  CoordinateExponential.gauss_identity_of_radial_family g C.smooth C.radial C.speed x hx w


theorem terminal_bounds (D : LeviCivitaData g) {H ρ : ℝ}
    (hρR : 2 * ρ < R)
    (hsmall : ∀ s : ℝ, |s| ≤ 2 * ρ →
      (H * s ^ 2) * Real.exp (max 1 (H * s ^ 2)) ≤ 3)
    (hcurv : ∀ y ∈ C.chart '' Metric.ball 0 R, D.curvatureTensorNorm y ≤ H)
    {x : E} (hx : x ∈ Metric.closedBall 0 (2 * ρ)) (v : E) :
    (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients C.chart x v v ∧
      g.pullbackCoefficients C.chart x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2 := by
  have hradial (w : E) (hw : w ∈ Metric.ball 0 R) :
      g.IsGeodesicOn (fun t : ℝ => C.chart (t • w))
          {t | t • w ∈ Metric.ball 0 R} ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          g.tangentNorm (C.chart (t • w))
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s : ℝ => C.chart (s • w)) t 1) = ‖w‖ ∧
          g.edist C.centre (C.chart (t • w)) ≤ ENNReal.ofReal ‖w‖ * ENNReal.ofReal t := by
    refine ⟨C.radial w hw, fun t ht => ⟨C.speed w hw t ht, ?_⟩⟩
    have htw : t • w ∈ Metric.ball 0 R := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg w)).trans_lt
        (by simpa only [one_mul, Metric.mem_ball, dist_zero_right] using hw)
    rw [C.distance _ htw, norm_smul, Real.norm_of_nonneg ht.1,
      ENNReal.ofReal_mul ht.1, mul_comm]
  have hball : ∀ y ∈ g.ball C.centre R, D.curvatureTensorNorm y ≤ H := by
    intro y hy
    have hyt : y ∈ C.chart.target := C.target.symm ▸ hy
    apply hcurv y
    exact ⟨C.chart.symm y, C.source ▸ C.chart.map_target hyt, C.chart.right_inv hyt⟩
  exact ((g.radial_exponential_uniform_bounds D hρR hsmall C.smooth C.normalized
    hradial hball x hx).2 v).2

end TerminalSourceChart

end PoincareConjecture.M47
