import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundModelCenterConnection
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundJetCompactEnvelope

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Metric
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M28.tube

open PoincareConjecture.CoordinateExponential PoincareConjecture.SpacetimeBounds

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

private theorem nested_metric_derivative_evaluation
    {B : ModelE → MetricCoefficient 3} {x : ModelE}
    (hB : ContDiffAt ℝ ∞ B x) (u v w z : ModelE) :
    fderiv ℝ (fun y => fderiv ℝ B y v w z) x u =
      fderiv ℝ (fderiv ℝ B) x u v w z := by
  have hD : DifferentiableAt ℝ (fderiv ℝ B) x :=
    (hB.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  rw [fderiv_clm_apply
    ((hD.clm_apply (differentiableAt_const (c := v))).clm_apply
      (differentiableAt_const (c := w))) (differentiableAt_const (c := z)),
    fderiv_clm_apply (hD.clm_apply (differentiableAt_const (c := v)))
      (differentiableAt_const (c := w)),
    fderiv_clm_apply hD (differentiableAt_const (c := v))]
  simp

theorem round_model_center_metric_jet_bounds
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {R : ℝ} (hR : 0 < R)
    (e : ModelE → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (hcenter : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w) :
    fderiv ℝ (N.model_metric.pullbackCoefficients e) 0 = 0 ∧
      ‖fderiv ℝ (fderiv ℝ (N.model_metric.pullbackCoefficients e)) 0‖ ≤ 4 := by
  let B := N.model_metric.pullbackCoefficients e
  let Γ := christoffelBilinear B
  have hB (y : ModelE) (hy : y ∈ ball 0 R) : ContDiffAt ℝ ∞ B y :=
    N.model_metric.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (isOpen_ball.mem_nhds hy))
  have hBinv (y : ModelE) (hy : y ∈ ball 0 R) : (B y).IsInvertible :=
    N.model_metric.isInvertible_pullbackCoefficients (hi y hy).injective
  have hB0 := hB 0 (mem_ball_self hR)
  have hB0d : DifferentiableAt ℝ B 0 := hB0.differentiableAt (by simp)
  have hΓd : DifferentiableAt ℝ Γ 0 :=
    (contDiffAt_christoffelBilinear hB0 (hBinv 0 (mem_ball_self hR))).differentiableAt
      (by simp)
  have hsymm (y v w : ModelE) : B y v w = B y w v :=
    N.model_metric.symm (e y) _ _
  have hΓzero : Γ 0 = 0 := by
    exact round_model_christoffel_zero N (by positivity : 0 < R / 2)
      (by linarith : R / 2 < R) e he hi hcenter hgauss
  have hmetric (y : ModelE) (hy : y ∈ ball 0 R) (v w z : ModelE) :
      fderiv ℝ B y v w z = B y (Γ y v w) z + B y w (Γ y v z) := by
    exact fderiv_metric_eq_christoffel ((hB y hy).differentiableAt (by simp))
      (hBinv y hy) (Eventually.of_forall fun x a b => hsymm x a b) w z v
  have hfirst : fderiv ℝ B 0 = 0 := by
    ext v w z
    rw [hmetric 0 (mem_ball_self hR), hΓzero]
    simp
  refine ⟨hfirst, ?_⟩
  have hconnection (u v w : ModelE) :
      ‖fderiv ℝ Γ 0 u v w‖ ≤ 2 * ‖u‖ * ‖v‖ * ‖w‖ := by
    have hG := norm_round_model_christoffel_fderiv_le_two N hR e he hi
      hcenter hgauss u
    exact (ContinuousLinearMap.le_opNorm ((fderiv ℝ Γ 0 u) v) w).trans
      (mul_le_mul_of_nonneg_right
        ((ContinuousLinearMap.le_opNorm (fderiv ℝ Γ 0 u) v).trans
          (mul_le_mul_of_nonneg_right hG (norm_nonneg v))) (norm_nonneg w))
  have hsecond (u v w z : ModelE) :
      fderiv ℝ (fderiv ℝ B) 0 u v w z =
        B 0 (fderiv ℝ Γ 0 u v w) z + B 0 w (fderiv ℝ Γ 0 u v z) := by
    have hcompat : (fun y => fderiv ℝ B y v w z) =ᶠ[𝓝 (0 : ModelE)]
        (fun y => B y (Γ y v w) z + B y w (Γ y v z)) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with y hy
      exact hmetric y hy v w z
    have hleft := ((hB0d.hasFDerivAt.clm_apply
      ((hΓd.hasFDerivAt.clm_apply (hasFDerivAt_const v 0)).clm_apply
        (hasFDerivAt_const w 0))).clm_apply (hasFDerivAt_const z 0)).fderiv
    have hright := ((hB0d.hasFDerivAt.clm_apply (hasFDerivAt_const w 0)).clm_apply
      ((hΓd.hasFDerivAt.clm_apply (hasFDerivAt_const v 0)).clm_apply
        (hasFDerivAt_const z 0))).fderiv
    have hl : fderiv ℝ (fun y => B y (Γ y v w) z) 0 u =
        B 0 (fderiv ℝ Γ 0 u v w) z := by
      simpa [hΓzero, hfirst] using congrArg (fun L => L u) hleft
    have hr : fderiv ℝ (fun y => B y w (Γ y v z)) 0 u =
        B 0 w (fderiv ℝ Γ 0 u v z) := by
      simpa [hΓzero, hfirst] using congrArg (fun L => L u) hright
    rw [← nested_metric_derivative_evaluation hB0, hcompat.fderiv_eq,
      fderiv_fun_add
        ((hB0d.clm_apply ((hΓd.clm_apply (differentiableAt_const (c := v))).clm_apply
          (differentiableAt_const (c := w)))).clm_apply
            (differentiableAt_const (c := z)))
        ((hB0d.clm_apply (differentiableAt_const (c := w))).clm_apply
          ((hΓd.clm_apply (differentiableAt_const (c := v))).clm_apply
            (differentiableAt_const (c := z)))), add_apply, hl, hr]
  have hpoint (u v w z : ModelE) :
      |fderiv ℝ (fderiv ℝ B) 0 u v w z| ≤
        4 * ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ := by
    rw [hsecond, hcenter, hcenter]
    calc
      _ ≤ |inner ℝ (fderiv ℝ Γ 0 u v w) z| +
          |inner ℝ w (fderiv ℝ Γ 0 u v z)| := abs_add_le _ _
      _ ≤ ‖fderiv ℝ Γ 0 u v w‖ * ‖z‖ +
          ‖w‖ * ‖fderiv ℝ Γ 0 u v z‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
      _ ≤ (2 * ‖u‖ * ‖v‖ * ‖w‖) * ‖z‖ +
          ‖w‖ * (2 * ‖u‖ * ‖v‖ * ‖z‖) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (hconnection u v w) (norm_nonneg z))
          (mul_le_mul_of_nonneg_left (hconnection u v z) (norm_nonneg w))
      _ = 4 * ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ := by ring
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  simpa only [Real.norm_eq_abs] using hpoint u v w z

theorem round_model_center_metricTwoJet_mem_boundSet
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {R : ℝ} (hR : 0 < R)
    (e : ModelE → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (hcenter : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w) :
    metricTwoJet (N.model_metric.pullbackCoefficients e) 0 ∈ roundJetBoundSet 0 4 := by
  obtain ⟨hfirst, hsecond⟩ := round_model_center_metric_jet_bounds N hR e he hi hcenter hgauss
  refine ⟨?_, ?_, hsecond⟩
  · ext v w
    exact hcenter v w
  · change ‖fderiv ℝ (N.model_metric.pullbackCoefficients e) 0‖ ≤ 0
    rw [hfirst, norm_zero]

end PoincareConjecture.M28.tube
