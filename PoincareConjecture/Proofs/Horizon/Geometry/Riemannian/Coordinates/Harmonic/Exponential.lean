import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.RadialCurve
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PrecompactDifferential
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PrecompactGauss
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.GaussMetricExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

universe u

variable {n : ℕ}

theorem exists_uniform_elliptic_radial_lift {K : ℝ} (hK : 0 ≤ K) :
    ∃ R : ℝ, 0 < R ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M] [T3Space M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g),
        MetricComplete g →
        (∀ x (v w : TangentSpace (𝓡 n) x), |D.sectionalCurvature x v w| ≤ K) →
        ∀ p : M, ∃ (e : EuclideanSpace ℝ (Fin n) → M)
          (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D' : LeviCivitaData h),
          ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 (2 * R)) ∧ e 0 = p ∧
          (∀ x ∈ Metric.ball 0 (2 * R), (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible) ∧
          (∀ x ∈ Metric.ball 0 R, h.euclideanCoefficients x = g.pullbackCoefficients e x) ∧
          (∀ x ∈ Metric.ball 0 R, ∀ v,
            (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ h.euclideanCoefficients x v v ∧
              h.euclideanCoefficients x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) ∧
          (∀ x w, h.euclideanCoefficients x x w = inner ℝ x w) ∧
          (∀ x ∈ Metric.ball 0 R, D'.curvatureTensorNorm x ≤ 4 * (n : ℝ) ^ 2 * K) ∧
          ∀ x ∈ Metric.ball 0 R, g.edist p (e x) ≤ ENNReal.ofReal ‖x‖ := by
  obtain ⟨R, hR, hR1, hsmall⟩ :=
    exists_uniform_radial_comparison_radius (by norm_num : (0 : ℝ) < 1)
      (4 * (n : ℝ) ^ 2 * K)
  refine ⟨R, hR, ?_⟩
  intro M _ _ _ _ g D hcomplete hsec p
  have hcompact := g.isCompact_closedBall_of_metricComplete hcomplete p 1
  have hclosure : IsCompact (closure (g.ball p 1)) :=
    hcompact.of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => show g.edist p x ≤ ENNReal.ofReal 1 from hx.le)
        hcompact.isClosed)
  obtain ⟨L, e, hL, he, he0, hed, hgeo⟩ :=
    g.exists_orthonormal_radial_exponential_of_precompact_ball p
      (by norm_num : (0 : ℝ) < 1) hclosure
  have hnorm := g.pullbackCoefficients_zero_of_normalized_chart
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (by simp))) he0 hed hL
  have hcurv (x : M) : D.curvatureTensorNorm x ≤ 4 * (n : ℝ) ^ 2 * K :=
    D.curvatureTensorNorm_le_of_sectional x hK (hsec x)
  have hb := g.radial_exponential_uniform_bounds D hR1 hsmall he hnorm hgeo
    (fun x _ => hcurv x)
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (2 * R) ⊆
      Metric.ball 0 1 := Metric.ball_subset_ball hR1.le
  have hinner : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R ⊆
      Metric.ball 0 (2 * R) := Metric.ball_subset_ball (by linarith)
  have he' := he.mono hsub
  have hinv (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 (2 * R)) :
      (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible :=
    (hb x (Metric.ball_subset_closedBall hx)).1
  have hbound (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 (2 * R))
      (v : EuclideanSpace ℝ (Fin n)) :
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients e x v v ∧
        g.pullbackCoefficients e x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2 :=
    ((hb x (Metric.ball_subset_closedBall hx)).2 v).2
  have hgauss (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 (2 * R))
      (w : EuclideanSpace ℝ (Fin n)) : g.pullbackCoefficients e x x w = inner ℝ x w :=
    CoordinateExponential.gauss_identity_of_radial_family g he (fun v hv => (hgeo v hv).1)
      (fun v hv t ht => ((hgeo v hv).2 t ht).1) x (hsub hx) w
  obtain ⟨h, D', heq, hgauss'⟩ := CoordinateExponential.exists_gauss_metric_extension
    hR (by linarith : R < 3 * R / 2) (by linarith : 3 * R / 2 < 2 * R)
    (g.pullbackCoefficients e)
    (fun x hx => (g.contDiffAt_pullbackCoefficients
      (he'.contMDiffAt (Metric.isOpen_ball.mem_nhds hx))).contDiffWithinAt)
    (fun _ _ v w => g.symm _ _ _)
    (fun x hx v hv => (mul_pos (by norm_num : (0 : ℝ) < 1 / 4)
      (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hbound x hx v).1)
    hgauss
  have hmetric (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 R) :
      h.euclideanCoefficients x = g.pullbackCoefficients e x :=
    heq x (Metric.ball_subset_closedBall hx)
  refine ⟨e, h, D', he', he0, hinv, hmetric, ?_, hgauss', ?_, ?_⟩
  · intro x hx v
    rw [hmetric x hx]
    exact hbound x (hinner hx) v
  · intro x hx
    have hnear : ∀ᶠ y in 𝓝 x, y ∈ Metric.ball 0 R := Metric.isOpen_ball.mem_nhds hx
    have hi : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible :=
      hnear.mono fun y hy => hinv y (hinner hy)
    have hm : ∀ᶠ y in 𝓝 x, ∀ u v : EuclideanSpace ℝ (Fin n),
        h.inner y u v = g.inner (e y) (mfderiv (𝓡 n) (𝓡 n) e y u)
          (mfderiv (𝓡 n) (𝓡 n) e y v) := by
      filter_upwards [hnear] with y hy u v
      exact congrArg (fun B => B u v) (hmetric y hy)
    rw [D'.curvatureTensorNorm_eq_pullback_euclidean D
      (he'.contMDiffAt (Metric.isOpen_ball.mem_nhds (hinner hx))) hi hm]
    exact hcurv (e x)
  · intro x hx
    simpa only [one_smul, ENNReal.ofReal_one, mul_one] using
      ((hgeo x (hsub (hinner hx))).2 1 ⟨by norm_num, le_rfl⟩).2

end PoincareConjecture.RiemannianMetric
