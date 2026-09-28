import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundGaussErrorJets

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Metric
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M28.tube

open PoincareConjecture.SpacetimeBounds

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem coefficient_fderiv_evaluation
    {B : GaussErrorE → MetricCoefficient 3} {x : GaussErrorE}
    (hB : DifferentiableAt ℝ B x) (u v w : GaussErrorE) :
    fderiv ℝ (fun y => B y v w) x u = (fderiv ℝ B x u) v w := by
  rw [fderiv_clm_apply (hB.clm_apply (differentiableAt_const (c := v)))
    (differentiableAt_const (c := w)),
    fderiv_clm_apply hB (differentiableAt_const (c := v))]
  simp

private theorem coefficient_second_fderiv_evaluation
    {B : GaussErrorE → MetricCoefficient 3} (hB : ContDiff ℝ ∞ B)
    (x u v w z : GaussErrorE) :
    fderiv ℝ (fun y => fderiv ℝ (fun a => B a w z) y v) x u =
      (fderiv ℝ (fderiv ℝ B) x u) v w z := by
  simp_rw [coefficient_fderiv_evaluation (hB.differentiable (by simp) _) ]
  have hDB : DifferentiableAt ℝ (fderiv ℝ B) x :=
    (hB.contDiffAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  rw [coefficient_fderiv_evaluation
    (hDB.clm_apply (differentiableAt_const (c := v)))]
  rw [fderiv_clm_apply hDB (differentiableAt_const (c := v))]
  simp

private theorem metricTwoJet_norm_le_of_component_bounds
    {B : GaussErrorE → MetricCoefficient 3} (hB : ContDiff ℝ ∞ B)
    {epsilon C : ℝ} (hepsilon : 0 ≤ epsilon) (hC : 0 ≤ C)
    (hzero : ∀ v w, |B 0 v w| ≤ epsilon * ‖v‖ * ‖w‖)
    (hfirst : ∀ u v w, |fderiv ℝ (fun y => B y v w) 0 u| ≤
      epsilon * ‖u‖ * ‖v‖ * ‖w‖)
    (hsecond : ∀ u v w z,
      |fderiv ℝ (fun y => fderiv ℝ (fun x => B x w z) y v) 0 u| ≤
        epsilon * ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ +
          C * ‖u‖ * ‖v‖ * epsilon * ‖w‖ * ‖z‖) :
    ‖metricTwoJet B 0‖ ≤ (1 + C) * epsilon := by
  have h0 : ‖B 0‖ ≤ epsilon := by
    apply ContinuousLinearMap.opNorm_le_bound _ hepsilon
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    simpa only [Real.norm_eq_abs] using hzero v w
  have h1 : ‖fderiv ℝ B 0‖ ≤ epsilon := by
    apply ContinuousLinearMap.opNorm_le_bound _ hepsilon
    intro u
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    rw [Real.norm_eq_abs,
      ← coefficient_fderiv_evaluation (hB.differentiable (by simp) 0)]
    exact hfirst u v w
  have h2 : ‖fderiv ℝ (fderiv ℝ B) 0‖ ≤ (1 + C) * epsilon := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    rw [Real.norm_eq_abs, ← coefficient_second_fderiv_evaluation hB]
    convert hsecond u v w z using 1
    ring
  have hbound : epsilon ≤ (1 + C) * epsilon := by nlinarith
  change max ‖B 0‖ (max ‖fderiv ℝ B 0‖ ‖fderiv ℝ (fderiv ℝ B) 0‖) ≤ _
  exact max_le (h0.trans hbound) (max_le (h1.trans hbound) h2)

theorem round_gauss_error_coefficient_le
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {e : GaussErrorE → N.model.carrier}
    (he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ e 0)
    (hcenter : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (horder : 2 ≤ ⌊epsilon⁻¹⌋₊) (v w : GaussErrorE) :
    |roundGaussErrorCoefficients N e 0 v w| ≤ epsilon * ‖v‖ * ‖w‖ := by
  have h := round_metric_covariant_error_le N horder (e 0) 0 (by omega)
    (fun i => mfderiv (𝓡 3) (𝓡 3) e 0 (![v, w] i))
  have hnorm (z : GaussErrorE) :
      N.model_metric.tangentNorm (e 0) (mfderiv (𝓡 3) (𝓡 3) e 0 z) = ‖z‖ := by
    change Real.sqrt (N.model_metric.pullbackCoefficients e 0 z z) = ‖z‖
    rw [hcenter, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)]
  rw [show roundGaussErrorCoefficients N e 0 v w =
      roundMetricError N (e 0)
        (fun i => mfderiv (𝓡 3) (𝓡 3) e 0 (![v, w] i)) from
    roundGaussErrorCoefficients_apply N he ![v, w]]
  simpa [LeviCivitaData.iteratedCovariantTensorDerivative,
    Fin.prod_univ_succ, hnorm, mul_assoc] using h

theorem round_gauss_error_two_jet_le
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {r s R : ℝ} (hr : 0 < r) (hrs : r < s) (hsR : s < R)
    (e : GaussErrorE → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R, (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (hcenter : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w)
    (horder : 2 ≤ ⌊epsilon⁻¹⌋₊) :
    ‖metricTwoJet (roundGaussErrorCoefficients N e) 0‖ ≤
      (1 + ‖modelTensorConnectionLiftMap‖ * 2) * epsilon := by
  obtain ⟨B, hB, hBactual, hsecond⟩ :=
    exists_round_gauss_error_second_coordinate_bound N hr hrs hsR e he hi
      hcenter hgauss horder
  obtain ⟨B₁, hB₁, hB₁actual, hfirst⟩ :=
    exists_round_gauss_error_first_coordinate_bound N hr hrs hsR e he hi
      hcenter hgauss horder
  have hBB₁ : B =ᶠ[𝓝 (0 : GaussErrorE)] B₁ := hBactual.trans hB₁actual.symm
  have hfirstB (u v w : GaussErrorE) :
      |fderiv ℝ (fun y => B y v w) 0 u| ≤
        epsilon * ‖u‖ * ‖v‖ * ‖w‖ := by
    have hev : (fun y => B y v w) =ᶠ[𝓝 (0 : GaussErrorE)]
        (fun y => B₁ y v w) :=
      hBB₁.mono (fun _ hy => congrArg (fun L : MetricCoefficient 3 => L v w) hy)
    rw [hev.fderiv_eq]
    exact hfirst u v w
  have hzero (v w : GaussErrorE) : |B 0 v w| ≤ epsilon * ‖v‖ * ‖w‖ := by
    rw [hBactual.self_of_nhds]
    exact round_gauss_error_coefficient_le N
      (he.contMDiffAt (isOpen_ball.mem_nhds (mem_ball_self (hr.trans (hrs.trans hsR)))))
      hcenter horder v w
  have hnorm := metricTwoJet_norm_le_of_component_bounds hB N.epsilon_pos.le
    (by positivity : 0 ≤ ‖modelTensorConnectionLiftMap‖ * 2)
    hzero hfirstB hsecond
  have hjet : metricTwoJet B 0 = metricTwoJet (roundGaussErrorCoefficients N e) 0 := by
    unfold metricTwoJet
    rw [hBactual.self_of_nhds, hBactual.fderiv_eq,
      (hBactual.fderiv (𝕜 := ℝ)).fderiv_eq]
  exact hjet ▸ hnorm

theorem metricTwoJet_sub_of_smooth
    {F G : GaussErrorE → MetricCoefficient 3} {x : GaussErrorE}
    (hF : ContDiffAt ℝ ∞ F x) (hG : ContDiffAt ℝ ∞ G x) :
    metricTwoJet (fun y => F y - G y) x = metricTwoJet F x - metricTwoJet G x := by
  have hF₁ : ContDiffAt ℝ 1 F x := hF.of_le (by simp)
  have hG₁ : ContDiffAt ℝ 1 G x := hG.of_le (by simp)
  have hder : fderiv ℝ (fun y => F y - G y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ F y - fderiv ℝ G y) := by
    filter_upwards [hF₁.eventually (by norm_num), hG₁.eventually (by norm_num)]
      with y hFy hGy
    exact fderiv_fun_sub (hFy.differentiableAt (by norm_num))
      (hGy.differentiableAt (by norm_num))
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hDG : DifferentiableAt ℝ (fderiv ℝ G) x :=
    (hG.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  unfold metricTwoJet
  rw [hder.self_of_nhds, hder.fderiv_eq, fderiv_fun_sub hDF hDG]
  rfl

theorem round_gauss_error_two_jet_eq_sub
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {e : GaussErrorE → N.model.carrier}
    (he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ e 0) :
    metricTwoJet (roundGaussErrorCoefficients N e) 0 =
      metricTwoJet (fun y => N.scale • g.pullbackCoefficients (N.forward ∘ e) y) 0 -
        metricTwoJet (N.model_metric.pullbackCoefficients e) 0 := by
  exact metricTwoJet_sub_of_smooth
    ((g.contDiffAt_pullbackCoefficients ((N.forward_smooth (e 0)).comp 0 he)).const_smul
      N.scale)
    (N.model_metric.contDiffAt_pullbackCoefficients he)

theorem round_gauss_two_jet_dist_le
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {R : ℝ} (hR : 0 < R)
    (e : GaussErrorE → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R, (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (hcenter : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w)
    (horder : 2 ≤ ⌊epsilon⁻¹⌋₊) :
    dist (metricTwoJet (fun y => N.scale •
      g.pullbackCoefficients (N.forward ∘ e) y) 0)
      (metricTwoJet (N.model_metric.pullbackCoefficients e) 0) ≤
        (1 + ‖modelTensorConnectionLiftMap‖ * 2) * epsilon := by
  rw [dist_eq_norm, ← round_gauss_error_two_jet_eq_sub N
    (he.contMDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR)))]
  exact round_gauss_error_two_jet_le N
    (r := R / 3) (s := 2 * R / 3)
    (by positivity) (by linarith) (by linarith) e he hi hcenter hgauss horder

end PoincareConjecture.M28.tube
