import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundModelTensorConnection










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Metric
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M28.tube

open PoincareConjecture.CoordinateExponential PoincareConjecture.ConnectionVariation

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem trilinear_gauss_polarization
    (A : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (hsymm : ∀ u v w, A u v w = A u w v)
    (hdiag : ∀ u, A u u u = 0) (u v w : E) :
    (3 : ℝ) • A u v w =
      (A u v w - A v u w) + (A u w v - A w u v) := by
  have hcyclic : A u v w + A v u w + A w u v = 0 := by
    apply ext_inner_right ℝ
    intro z
    have h₁ := congrArg (fun a => inner ℝ a z) (hdiag (u + v + w))
    have h₂ := congrArg (fun a => inner ℝ a z) (hdiag (u + v))
    have h₃ := congrArg (fun a => inner ℝ a z) (hdiag (u + w))
    have h₄ := congrArg (fun a => inner ℝ a z) (hdiag (v + w))
    have h₅ := congrArg (fun a => inner ℝ a z) (hdiag u)
    have h₆ := congrArg (fun a => inner ℝ a z) (hdiag v)
    have h₇ := congrArg (fun a => inner ℝ a z) (hdiag w)
    simp only [map_add, add_apply, inner_add_left, inner_zero_left] at *
    rw [hsymm u w v, hsymm v w u, hsymm w v u] at h₁
    linarith only [h₁, h₂, h₃, h₄, h₅, h₆, h₇]
  apply ext_inner_right ℝ
  intro z
  have hc := congrArg (fun a => inner ℝ a z) hcyclic
  rw [hsymm u w v]
  simp only [real_inner_smul_left, inner_add_left, inner_sub_left,
    inner_zero_left] at *
  linarith only [hc]

theorem gauss_connection_derivative_three_eq_curvature
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : DifferentiableAt ℝ Γ 0)
    (hsymm : ∀ x v w, Γ x v w = Γ x w v)
    (hradial : ∀ (x : E) (t : ℝ), Γ (t • x) x x = 0)
    (hzero : Γ 0 = 0) (u v w : E) :
    (3 : ℝ) • fderiv ℝ Γ 0 u v w =
      christoffelCurvature Γ 0 u v w + christoffelCurvature Γ 0 u w v := by
  have happ (a b c : E) :
      fderiv ℝ (fun y => Γ y b c) 0 a = fderiv ℝ Γ 0 a b c := by
    rw [fderiv_clm_apply (hΓ.clm_apply (differentiableAt_const (c := b)))
      (differentiableAt_const (c := c)),
      fderiv_clm_apply hΓ (differentiableAt_const (c := b))]
    simp
  have hsym (a b c : E) : fderiv ℝ Γ 0 a b c = fderiv ℝ Γ 0 a c b := by
    rw [← happ a b c, ← happ a c b]
    exact congrArg (fun L : E →L[ℝ] E => L a)
      (congrArg (fun f => fderiv ℝ f 0) (funext fun y => hsymm y b c))
  have hdiag (a : E) : fderiv ℝ Γ 0 a a a = 0 := by
    have hpath : HasDerivAt (fun t : ℝ => Γ (t • a)) (fderiv ℝ Γ 0 a) 0 := by
      have hΓ' : HasFDerivAt Γ (fderiv ℝ Γ 0) ((0 : ℝ) • a) := by
        simpa using hΓ.hasFDerivAt
      convert! hΓ'.comp_hasDerivAt 0
        ((hasDerivAt_id (0 : ℝ)).smul_const a) using 1
      simp
    have hd := (hpath.clm_apply (hasDerivAt_const 0 a)).clm_apply
      (hasDerivAt_const 0 a)
    have heq : (fun t : ℝ => Γ (t • a) a a) = fun _ => (0 : E) :=
      funext (hradial a)
    rw [heq] at hd
    simpa using hd.unique (hasDerivAt_const 0 (0 : E))
  simpa [christoffelCurvature, hzero] using
    trilinear_gauss_polarization (fderiv ℝ Γ 0) hsym hdiag u v w

theorem norm_fderiv_gauss_connection_le_of_curvature
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hΓ : DifferentiableAt ℝ Γ 0)
    (hsymm : ∀ x v w, Γ x v w = Γ x w v)
    (hradial : ∀ (x : E) (t : ℝ), Γ (t • x) x x = 0)
    (hzero : Γ 0 = 0) {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ u v w, ‖christoffelCurvature Γ 0 u v w‖ ≤
      K * ‖u‖ * ‖v‖ * ‖w‖) (u : E) :
    ‖fderiv ℝ Γ 0 u‖ ≤ K * ‖u‖ := by
  have hpoint (v w : E) :
      ‖fderiv ℝ Γ 0 u v w‖ ≤ K * ‖u‖ * ‖v‖ * ‖w‖ := by
    have hthree := congrArg norm
      (gauss_connection_derivative_three_eq_curvature hΓ hsymm hradial hzero u v w)
    have hsum := (norm_add_le (christoffelCurvature Γ 0 u v w)
      (christoffelCurvature Γ 0 u w v)).trans
      (add_le_add (hcurv u v w) (hcurv u w v))
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num :
      (0 : ℝ) ≤ 3)] at hthree
    have hn : 0 ≤ K * ‖u‖ * ‖v‖ * ‖w‖ := by positivity
    nlinarith only [hthree, hsum, hn]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  exact hpoint v w

end Algebra

section RoundModel

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]




theorem norm_round_model_christoffel_fderiv_le_two
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
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w)
    (u : ModelE) :
    ‖fderiv ℝ (christoffelBilinear
      (N.model_metric.pullbackCoefficients e)) 0 u‖ ≤ 2 * ‖u‖ := by
  let B := N.model_metric.pullbackCoefficients e
  let r := R / 3
  let s := 2 * R / 3
  have hr : 0 < r := by dsimp [r]; positivity
  have hrs : r < s := by dsimp [r, s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  have hB : ContDiffOn ℝ ∞ B (ball 0 R) := by
    intro y hy
    exact (N.model_metric.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (isOpen_ball.mem_nhds hy))).contDiffWithinAt
  have hsymm : ∀ y ∈ ball (0 : ModelE) R, ∀ v w, B y v w = B y w v := by
    intro y _hy v w
    exact N.model_metric.symm (e y) _ _
  have hpos : ∀ y ∈ ball (0 : ModelE) R, ∀ v, v ≠ 0 → 0 < B y v v := by
    intro y hy v hv
    apply N.model_metric.pos (e y)
    intro hz
    apply hv
    apply (hi y hy).injective
    rw [map_zero]
    convert! hz using 1
  obtain ⟨gE, DE, heq, hEgauss⟩ :=
    exists_gauss_metric_extension hr hrs hsR B hB hsymm hpos hgauss
  have hcoeff : B =ᶠ[𝓝 (0 : ModelE)] gE.euclideanCoefficients := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with y hy
    exact (heq y (ball_subset_closedBall hy)).symm
  have hΓeq : christoffelBilinear B =ᶠ[𝓝 (0 : ModelE)]
      christoffelBilinear gE.euclideanCoefficients := by
    filter_upwards [hcoeff.eventually_nhds] with y hy
    have hy' : B =ᶠ[𝓝 y] gE.euclideanCoefficients := hy
    unfold christoffelBilinear
    rw [hy'.self_of_nhds, hy'.fderiv_eq]
  have h0 : ∀ v w : ModelE, gE.inner 0 v w = inner ℝ v w := by
    intro v w
    have hc := congrArg (fun K => K v w) hcoeff.self_of_nhds
    exact hc.symm.trans (hcenter v w)
  have hmetric : ∀ᶠ y in 𝓝 (0 : ModelE), ∀ v w : ModelE,
      gE.inner y v w = N.model_metric.inner (e y)
        (mfderiv (𝓡 3) (𝓡 3) e y v) (mfderiv (𝓡 3) (𝓡 3) e y w) := by
    filter_upwards [hcoeff] with y hy v w
    exact (congrArg (fun K => K v w) hy).symm
  have hi' : ∀ᶠ y in 𝓝 (0 : ModelE),
      (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with y hy
    exact hi y hy
  have he0 := he.contMDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hmodel (v w : ModelE) : N.model_metric.inner (e 0)
      (mfderiv (𝓡 3) (𝓡 3) e 0 v) (mfderiv (𝓡 3) (𝓡 3) e 0 w) =
      inner ℝ v w := hcenter v w
  have hcurv (a b c : ModelE) : DE.curvature 0 a b c =
      inner ℝ b c • a - inner ℝ a c • b := by
    apply ext_inner_right ℝ
    intro z
    have hc := DE.curvatureTensor_eq_pullback_euclidean N.model_connection
      he0 hi' hmetric a b z c
    rw [singularRound_curvatureTensor_eq_metricGram N] at hc
    simp only [hmodel] at hc
    change gE.inner 0 (DE.curvature 0 a b c) z = _ at hc
    rw [h0] at hc
    simp only [inner_sub_left, real_inner_smul_left]
    calc
      _ = inner ℝ a z * inner ℝ b c - inner ℝ b z * inner ℝ a c := hc
      _ = _ := by ring
  let Γ := christoffelBilinear gE.euclideanCoefficients
  have hΓ : ContDiff ℝ ∞ Γ :=
    contDiff_iff_contDiffAt.mpr fun y => contDiffAt_christoffelBilinear
      (gE.contDiffAt_euclideanCoefficients y) (gE.inner_isInvertible y)
  have hΓd : DifferentiableAt ℝ Γ 0 := hΓ.contDiffAt.differentiableAt (by simp)
  have hΓsymm (y a b : ModelE) : Γ y a b = Γ y b a :=
    christoffelBilinear_symm ((gE.contDiffAt_euclideanCoefficients y).differentiableAt
      (by simp)) (Filter.Eventually.of_forall fun x v w => gE.symm x v w) a b
  have hΓradial (a : ModelE) (t : ℝ) : Γ (t • a) a a = 0 :=
    christoffelBilinear_radial_eq_zero_of_gauss
      (contDiff_iff_contDiffAt.mpr gE.contDiffAt_euclideanCoefficients)
      (fun y => gE.inner_isInvertible y) (fun y a b => gE.symm y a b) hEgauss a t
  have hΓzero : Γ 0 = 0 := by
    exact christoffelBilinear_zero_of_gauss
      (contDiff_iff_contDiffAt.mpr gE.contDiffAt_euclideanCoefficients)
      (fun y => gE.inner_isInvertible y) (fun y a b => gE.symm y a b) hEgauss
  have hΓcurv (a b c : ModelE) : ‖christoffelCurvature Γ 0 a b c‖ ≤
      2 * ‖a‖ * ‖b‖ * ‖c‖ := by
    rw [← coordinateCurvature_eq_christoffelCurvature hΓd,
      coordinateCurvature_eq_retained DE, hcurv]
    calc
      ‖inner ℝ b c • a - inner ℝ a c • b‖ ≤
          ‖inner ℝ b c • a‖ + ‖inner ℝ a c • b‖ := norm_sub_le _ _
      _ = |inner ℝ b c| * ‖a‖ + |inner ℝ a c| * ‖b‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ (‖b‖ * ‖c‖) * ‖a‖ + (‖a‖ * ‖c‖) * ‖b‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm b c) (norm_nonneg a))
          (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm a c) (norm_nonneg b))
      _ = 2 * ‖a‖ * ‖b‖ * ‖c‖ := by ring
  rw [hΓeq.fderiv_eq]
  exact norm_fderiv_gauss_connection_le_of_curvature hΓd hΓsymm hΓradial hΓzero
    (by norm_num) hΓcurv u




theorem norm_round_model_tensor_connection_fderiv_le_universal
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
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w)
    (u : ModelE) :
    ‖fderiv ℝ (roundModelTensorConnection
      (N.model_metric.pullbackCoefficients e)) 0 u‖ ≤
      (‖modelTensorConnectionLiftMap‖ * 2) * ‖u‖ := by
  apply norm_fderiv_roundModelTensorConnection_le
  · exact N.model_metric.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR)))
  · exact N.model_metric.isInvertible_pullbackCoefficients
      (hi 0 (mem_ball_self hR)).injective
  · norm_num
  · exact norm_round_model_christoffel_fderiv_le_two N hR e he hi hcenter hgauss

end RoundModel

end PoincareConjecture.M28.tube
