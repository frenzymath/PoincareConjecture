import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundGaussErrorSection
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundModelCenterConnection
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.GaussMetricExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorNaturality

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Metric
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M28.tube

open PoincareConjecture.SpacetimeBounds
open PoincareConjecture.CoordinateExponential
open PoincareConjecture.LeviCivitaData

abbrev GaussErrorE := EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

private theorem pullback_coefficients_contDiffOn
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {e : GaussErrorE → N.model.carrier} {R : ℝ}
    (_hR : 0 < R)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R)) :
    ContDiffOn ℝ ∞ (N.model_metric.pullbackCoefficients e) (ball 0 R) := by
  intro y hy
  exact (N.model_metric.contDiffAt_pullbackCoefficients
    (he.contMDiffAt (isOpen_ball.mem_nhds hy))).contDiffWithinAt

private theorem pullback_coefficients_pos
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {e : GaussErrorE → N.model.carrier} {R : ℝ}
    (_he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible) :
    ∀ y ∈ ball 0 R, ∀ v, v ≠ 0 →
      0 < N.model_metric.pullbackCoefficients e y v v := by
  intro y hy v hv
  apply N.model_metric.pos (e y)
  intro hz
  apply hv
  apply (hi y hy).injective
  rw [map_zero]
  convert! hz using 1

private theorem pullback_coefficients_symm
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    (e : GaussErrorE → N.model.carrier) :
    ∀ y v w, N.model_metric.pullbackCoefficients e y v w =
      N.model_metric.pullbackCoefficients e y w v := by
  intro y v w
  change N.model_metric.inner (e y)
      (mfderiv (𝓡 3) (𝓡 3) e y v)
      (mfderiv (𝓡 3) (𝓡 3) e y w) =
    N.model_metric.inner (e y)
      (mfderiv (𝓡 3) (𝓡 3) e y w)
      (mfderiv (𝓡 3) (𝓡 3) e y v)
  exact N.model_metric.symm (e y) _ _

private theorem error_source_metric_extension
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {r s R : ℝ} (hr : 0 < r) (hrs : r < s) (hsR : s < R)
    (e : GaussErrorE → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w) :
    ∃ (gE : RiemannianMetric 3 GaussErrorE),
      (∀ y ∈ closedBall (0 : GaussErrorE) r,
        gE.euclideanCoefficients y = N.model_metric.pullbackCoefficients e y) ∧
      (∀ y w, gE.euclideanCoefficients y y w = inner ℝ y w) := by
  have hR : 0 < R := hr.trans (hrs.trans hsR)
  have hB := pullback_coefficients_contDiffOn N hR he
  have hsymm : ∀ x ∈ ball (0 : GaussErrorE) R, ∀ v w,
      N.model_metric.pullbackCoefficients e x v w =
        N.model_metric.pullbackCoefficients e x w v := by
    intro x _hx v w
    exact pullback_coefficients_symm N e x v w
  have hpos := pullback_coefficients_pos N he hi
  obtain ⟨gE, _DE, ⟨heq, hEgauss⟩⟩ :=
    exists_gauss_metric_extension hr hrs hsR
      (N.model_metric.pullbackCoefficients e) hB hsymm hpos hgauss
  exact ⟨gE, heq, hEgauss⟩

private theorem source_tensor_connection_eventually_eq_model
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {r : ℝ} (hr : 0 < r)
    (e : GaussErrorE → N.model.carrier)
    {gE : RiemannianMetric 3 GaussErrorE} (DE : LeviCivitaData gE)
    (heq : ∀ y ∈ closedBall (0 : GaussErrorE) r,
      gE.euclideanCoefficients y = N.model_metric.pullbackCoefficients e y) :
    (fun y => DE.tensorCoordinateConnectionCoefficient 0 y 2) =ᶠ[𝓝 (0 : GaussErrorE)]
      roundModelTensorConnection (N.model_metric.pullbackCoefficients e) := by
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with y hy
  have hlocal : gE.euclideanCoefficients =ᶠ[𝓝 y]
      N.model_metric.pullbackCoefficients e := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    exact heq z (mem_closedBall.mpr (le_of_lt (mem_ball.mp hz)))
  have hder : fderiv ℝ gE.euclideanCoefficients y =
      fderiv ℝ (N.model_metric.pullbackCoefficients e) y :=
    hlocal.fderiv_eq
  have hcoeff : gE.euclideanCoefficients y =
      N.model_metric.pullbackCoefficients e y := hlocal.self_of_nhds
  have hΓ : DE.coordinateConnectionCoefficient 0 y =
      christoffelBilinear (N.model_metric.pullbackCoefficients e) y := by
    rw [DE.coordinateConnectionCoefficient_model]
    unfold christoffelBilinear
    rw [hcoeff, hder]
  apply ContinuousLinearMap.ext
  intro T
  apply ContinuousLinearMap.ext
  intro U
  apply TensorFiber.ext
  intro a
  simp only [tensorCoordinateConnectionCoefficient_apply,
    roundModelTensorConnection_apply,
    modelTensorSlotActionLift, hΓ,
    PoincareConjecture.TensorFiber.negativeSlotAction_apply]

theorem exists_round_gauss_error_covariant_norm_bound
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {r s R : ℝ} (hr : 0 < r) (hrs : r < s) (hsR : s < R)
    (e : GaussErrorE → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (hcenter : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w)
    (horder : 2 ≤ ⌊epsilon⁻¹⌋₊) :
    ∃ (B : GaussErrorE → MetricCoefficient 3)
      (gE : RiemannianMetric 3 GaussErrorE) (DE : LeviCivitaData gE),
      ContDiff ℝ ∞ B ∧
      (B =ᶠ[𝓝 (0 : GaussErrorE)] roundGaussErrorCoefficients N e) ∧
      IsSmoothCovariantTensor
        (fun (y : GaussErrorE)
          (v : Fin 2 → TangentSpace (𝓡 3) y) => B y (v 0) (v 1)) ∧
      (∀ y ∈ closedBall (0 : GaussErrorE) r,
        gE.euclideanCoefficients y = N.model_metric.pullbackCoefficients e y) ∧
      (∀ y w, gE.euclideanCoefficients y y w = inner ℝ y w) ∧
      (∀ j ≤ 2,
        gE.tensorNorm
          (DE.iteratedCovariantTensorDerivative
            (fun (y : GaussErrorE)
              (v : Fin 2 → TangentSpace (𝓡 3) y) => B y (v 0) (v 1)) j)
            (0 : GaussErrorE) ≤ epsilon) := by
  obtain ⟨B, hB, _hcompact, hSmooth, _hEq, _hEval, _hGerm⟩ :=
    exists_round_gauss_error_section N hr hrs hsR e he
  obtain ⟨gE, ⟨heq, _hEgauss⟩⟩ :=
    error_source_metric_extension N hr hrs hsR e he hi hgauss
  let DE : LeviCivitaData gE := gE.euclideanLeviCivitaData
  let S : CovariantTensorEvaluation 3 GaussErrorE 2 :=
    fun y v => B y (v 0) (v 1)
  have hU : IsOpen (ball (0 : GaussErrorE) r) := isOpen_ball
  have he' : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 r) :=
    he.mono (ball_subset_ball (le_of_lt (hrs.trans hsR)))
  have hi' : ∀ x ∈ ball 0 r,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible := by
    intro x hx
    exact hi x (ball_subset_ball (le_of_lt (hrs.trans hsR)) hx)
  have hmetric : ∀ y ∈ ball (0 : GaussErrorE) r, ∀ u v,
      gE.inner y u v = N.model_metric.inner (e y)
        (mfderiv (𝓡 3) (𝓡 3) e y u)
        (mfderiv (𝓡 3) (𝓡 3) e y v) := by
    intro y hy u v
    have hclosed : y ∈ closedBall (0 : GaussErrorE) r :=
      mem_closedBall.mpr (le_of_lt (mem_ball.mp hy))
    have hc := congrArg (fun K : MetricCoefficient 3 => K u v) (heq y hclosed)
    change gE.inner y u v = N.model_metric.inner (e y)
      (mfderiv (𝓡 3) (𝓡 3) e y u)
      (mfderiv (𝓡 3) (𝓡 3) e y v) at hc
    exact hc
  have hST : ∀ y ∈ ball (0 : GaussErrorE) r, ∀ v,
      S y v = roundMetricError N (e y)
        (fun i => mfderiv (𝓡 3) (𝓡 3) e y (v i)) := by
    intro y hy v
    exact _hEval y hy v
  have h0 : ∀ v w, gE.inner 0 v w = inner ℝ v w := by
    intro v w
    have hc := hmetric 0 (mem_ball_self hr) v w
    change gE.inner 0 v w = N.model_metric.pullbackCoefficients e 0 v w at hc
    rw [hcenter] at hc
    exact hc
  have hGerm : B =ᶠ[𝓝 (0 : GaussErrorE)] roundGaussErrorCoefficients N e := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with y hy
    exact _hEq y (ball_subset_closedBall hy)
  refine ⟨B, gE, DE, hB, hGerm, hSmooth, heq, _hEgauss, ?_⟩
  intro j hj
  have hj' : j ≤ 2 := hj
  have hnormeq :
      gE.tensorNorm (DE.iteratedCovariantTensorDerivative S j) 0 =
        N.model_metric.tensorNorm
          (N.model_connection.iteratedCovariantTensorDerivative
            (roundMetricError N) j) (e 0) := by
    obtain ⟨e0, he0⟩ := hi' 0 (mem_ball_self hr)
    have he0' (v : TangentSpace (𝓡 3) 0) :
        e0 v = mfderiv (𝓡 3) (𝓡 3) e 0 v :=
      congrArg (fun L => L v) he0
    obtain ⟨A, hA⟩ :=
      (N.model_connection.iteratedCovariantTensorDerivative_isSmooth
        (round_metric_error_smooth N) j).1 (e 0)
    apply RiemannianMetric.tensorNorm_eq_of_linearEquiv gE N.model_metric
      (DE.iteratedCovariantTensorDerivative S j)
      (N.model_connection.iteratedCovariantTensorDerivative
        (roundMetricError N) j) 0 (e 0) e0.toLinearEquiv
    · intro u v
      simpa only [S, ContinuousLinearEquiv.coe_toLinearEquiv,
        ContinuousLinearEquiv.coe_coe, he0'] using
        (hmetric 0 (mem_ball_self hr) u v).symm
    · intro v
      simpa only [S, ContinuousLinearEquiv.coe_toLinearEquiv,
        ContinuousLinearEquiv.coe_coe, he0'] using
        (LeviCivitaData.iteratedCovariantTensorDerivative_eq_pullback
          DE N.model_connection hU he' hi' hmetric hSmooth
          (round_metric_error_smooth N) hST j
          (mem_ball_self hr) v)
    · exact hA
  have hlt := roundMetricJetNorm_lt N horder (e 0) j hj'
  exact hnormeq ▸ hlt.le

theorem exists_round_gauss_error_first_coordinate_bound
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {r s R : ℝ} (hr : 0 < r) (hrs : r < s) (hsR : s < R)
    (e : GaussErrorE → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (hcenter : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w)
    (horder : 2 ≤ ⌊epsilon⁻¹⌋₊) :
    ∃ (B : GaussErrorE → MetricCoefficient 3),
      ContDiff ℝ ∞ B ∧
      (B =ᶠ[𝓝 (0 : GaussErrorE)] roundGaussErrorCoefficients N e) ∧
      (∀ u v w : GaussErrorE,
        |fderiv ℝ (fun y => B y v w) 0 u| ≤
          epsilon * ‖u‖ * ‖v‖ * ‖w‖) := by
  obtain ⟨B, hB, _hcompact, hSmooth, _hEq, _hEval, _hGerm⟩ :=
    exists_round_gauss_error_section N hr hrs hsR e he
  obtain ⟨gE, ⟨heq, hEgauss⟩⟩ :=
    error_source_metric_extension N hr hrs hsR e he hi hgauss
  let DE : LeviCivitaData gE := gE.euclideanLeviCivitaData
  let S : CovariantTensorEvaluation 3 GaussErrorE 2 :=
    fun y v => B y (v 0) (v 1)
  have he' : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 r) :=
    he.mono (ball_subset_ball (le_of_lt (hrs.trans hsR)))
  have hi' : ∀ x ∈ ball 0 r,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible := by
    intro x hx
    exact hi x (ball_subset_ball (le_of_lt (hrs.trans hsR)) hx)
  have hmetric : ∀ y ∈ ball (0 : GaussErrorE) r, ∀ u v,
      gE.inner y u v = N.model_metric.inner (e y)
        (mfderiv (𝓡 3) (𝓡 3) e y u)
        (mfderiv (𝓡 3) (𝓡 3) e y v) := by
    intro y hy u v
    have hclosed : y ∈ closedBall (0 : GaussErrorE) r :=
      mem_closedBall.mpr (le_of_lt (mem_ball.mp hy))
    have hc := congrArg (fun K : MetricCoefficient 3 => K u v) (heq y hclosed)
    change gE.inner y u v = N.model_metric.inner (e y)
      (mfderiv (𝓡 3) (𝓡 3) e y u)
      (mfderiv (𝓡 3) (𝓡 3) e y v) at hc
    exact hc
  have hST : ∀ y ∈ ball (0 : GaussErrorE) r, ∀ v,
      S y v = roundMetricError N (e y)
        (fun i => mfderiv (𝓡 3) (𝓡 3) e y (v i)) := by
    intro y hy v
    exact _hEval y hy v
  have h0 : ∀ v w, gE.inner 0 v w = inner ℝ v w := by
    intro v w
    have hc := hmetric 0 (mem_ball_self hr) v w
    change gE.inner 0 v w = N.model_metric.pullbackCoefficients e 0 v w at hc
    rw [hcenter] at hc
    exact hc
  have hnormeq :
      gE.tensorNorm (DE.covariantTensorDerivative S) 0 =
        N.model_metric.tensorNorm
          (N.model_connection.iteratedCovariantTensorDerivative
            (roundMetricError N) 1) (e 0) := by
    change gE.tensorNorm (DE.iteratedCovariantTensorDerivative S 1) 0 =
      N.model_metric.tensorNorm
        (N.model_connection.iteratedCovariantTensorDerivative
          (roundMetricError N) 1) (e 0)
    obtain ⟨e0, he0⟩ := hi' 0 (mem_ball_self hr)
    have he0' (v : TangentSpace (𝓡 3) 0) :
        e0 v = mfderiv (𝓡 3) (𝓡 3) e 0 v :=
      congrArg (fun L => L v) he0
    obtain ⟨A, hA⟩ :=
      (N.model_connection.iteratedCovariantTensorDerivative_isSmooth
        (round_metric_error_smooth N) 1).1 (e 0)
    apply RiemannianMetric.tensorNorm_eq_of_linearEquiv gE N.model_metric
      (DE.iteratedCovariantTensorDerivative S 1)
      (N.model_connection.iteratedCovariantTensorDerivative
        (roundMetricError N) 1) 0 (e 0) e0.toLinearEquiv
    · intro u v
      simpa [S, LeviCivitaData.iteratedCovariantTensorDerivative,
        ContinuousLinearEquiv.coe_toLinearEquiv,
        ContinuousLinearEquiv.coe_coe, he0'] using
        (hmetric 0 (mem_ball_self hr) u v).symm
    · intro v
      simpa [S, LeviCivitaData.iteratedCovariantTensorDerivative,
        ContinuousLinearEquiv.coe_toLinearEquiv,
        ContinuousLinearEquiv.coe_coe, he0'] using
        (LeviCivitaData.iteratedCovariantTensorDerivative_eq_pullback
          DE N.model_connection isOpen_ball he' hi' hmetric hSmooth
          (round_metric_error_smooth N) hST 1
          (mem_ball_self hr) v)
    · exact hA
  have hlt := roundMetricJetNorm_lt N horder (e 0) 1 (by omega)
  have hnorm : gE.tensorNorm (DE.iteratedCovariantTensorDerivative S 1) 0 ≤ epsilon :=
    hnormeq ▸ hlt.le
  have hzero : DE.coordinateConnectionCoefficient 0 0 = 0 :=
    gauss_center_coordinate_connection_zero DE hEgauss
  have hGerm : B =ᶠ[𝓝 (0 : GaussErrorE)] roundGaussErrorCoefficients N e := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with y hy
    exact _hEq y (ball_subset_closedBall hy)
  refine ⟨B, hB, hGerm, ?_⟩
  intro u v w
  obtain ⟨A, hA⟩ :=
    (DE.covariantTensorDerivative_isSmooth hSmooth).1 0
  have hev := abs_tensor_evaluation_le_tensorNorm gE
    (DE.covariantTensorDerivative S) 0 A hA ![u, v, w]
  have hconv := covariant_metric_error_eq_fderiv_of_zero_connection DE
    hSmooth 0 0 (by simp) u ![v, w] (by
      intro i
      rw [hzero]
      simp)
  have hconv' :
      DE.covariantTensorDerivative S 0 ![u, v, w] =
        fderiv ℝ (fun y => B y v w) 0 u := by
    convert hconv using 1 <;>
      simp [S, PartialEquiv.refl_symm,
        PartialEquiv.refl_coe, id_eq, tensorCoordinateEvaluation_model]
  rw [hconv'] at hev
  have ht (z : GaussErrorE) : 0 ≤ gE.tangentNorm 0 z := by
    exact Real.sqrt_nonneg _
  have hprod : 0 ≤ gE.tangentNorm 0 u * gE.tangentNorm 0 v *
      gE.tangentNorm 0 w :=
    mul_nonneg (mul_nonneg (ht u) (ht v)) (ht w)
  calc
    |fderiv ℝ (fun y => B y v w) 0 u| ≤
        gE.tensorNorm (DE.covariantTensorDerivative S) 0 *
          (gE.tangentNorm 0 u * gE.tangentNorm 0 v * gE.tangentNorm 0 w) := by
      simpa [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_assoc] using hev
    _ ≤ epsilon * (gE.tangentNorm 0 u * gE.tangentNorm 0 v *
        gE.tangentNorm 0 w) := mul_le_mul_of_nonneg_right hnorm hprod
    _ = epsilon * ‖u‖ * ‖v‖ * ‖w‖ := by
      simp only [tangentNorm_zero_eq_norm_of_normalized h0]
      ring

private theorem tensorFiber_two_eval_le
    (T : TensorFiber GaussErrorE 2) (v w : GaussErrorE) :
    |T ![v, w]| ≤ ‖T‖ * ‖v‖ * ‖w‖ := by
  have h := abs_multilinear_apply_le_orthonormal_tensor_norm
    (TensorFiber.toMultilinear T) (stdOrthonormalBasis ℝ GaussErrorE) ![v, w]
  simpa only [TensorFiber.toMultilinear_apply,
    TensorFiber.norm_eq_sqrt_sum (stdOrthonormalBasis ℝ GaussErrorE),
    Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_one, mul_one, mul_assoc] using h

private theorem tensorCoordinateSection_norm_eq_of_normalized
    {gE : RiemannianMetric 3 GaussErrorE} {k : ℕ}
    {T : CovariantTensorEvaluation 3 GaussErrorE k}
    (hT : IsSmoothCovariantTensor T)
    (h0 : ∀ v w : GaussErrorE, gE.inner 0 v w = inner ℝ v w) :
    ‖tensorCoordinateSection hT 0 0‖ = gE.tensorNorm T 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : GaussErrorE → Type _) :=
    ⟨gE.toRiemannianMetric⟩
  let b := gE.orthonormalBasis 0
  have hon : Orthonormal ℝ (E := GaussErrorE) (fun i => b i) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [← h0]
    exact b.inner_eq_ite i j
  let bb : Module.Basis
      (Fin (Module.finrank ℝ (TangentSpace (𝓡 3) (0 : GaussErrorE)))) ℝ GaussErrorE :=
    b.toBasis
  let b0 : OrthonormalBasis
      (Fin (Module.finrank ℝ (TangentSpace (𝓡 3) (0 : GaussErrorE)))) ℝ GaussErrorE :=
    bb.toOrthonormalBasis hon
  rw [TensorFiber.norm_eq_sqrt_sum b0]
  unfold RiemannianMetric.tensorNorm
  congr 1
  apply Finset.sum_congr rfl
  intro a _ha
  congr 1
  simp only [b0, Module.Basis.coe_toOrthonormalBasis, bb,
    tensorCoordinateSection_apply, tensorCoordinateEvaluation_model]
  rfl

theorem exists_round_gauss_error_second_coordinate_bound
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {r s R : ℝ} (hr : 0 < r) (hrs : r < s) (hsR : s < R)
    (e : GaussErrorE → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (hcenter : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w)
    (horder : 2 ≤ ⌊epsilon⁻¹⌋₊) :
    ∃ B : GaussErrorE → MetricCoefficient 3,
      ContDiff ℝ ∞ B ∧
      (B =ᶠ[𝓝 (0 : GaussErrorE)] roundGaussErrorCoefficients N e) ∧
      ∀ u v w z : GaussErrorE,
          |fderiv ℝ (fun y =>
              fderiv ℝ (fun x => B x w z) y v) 0 u| ≤
            epsilon * ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ +
              ((‖modelTensorConnectionLiftMap‖ * 2) * ‖u‖) *
                ‖v‖ * epsilon * ‖w‖ * ‖z‖ := by
  obtain ⟨B, gE, DE, hB, hGerm, hSmooth, heq, hEgauss, hcov⟩ :=
    exists_round_gauss_error_covariant_norm_bound N hr hrs hsR e he hi
      hcenter hgauss horder
  let S : CovariantTensorEvaluation 3 GaussErrorE 2 :=
    fun y v => B y (v 0) (v 1)
  let Γ := fun y => DE.tensorCoordinateConnectionCoefficient 0 y 2
  let Scoord := fun y => tensorCoordinateSection hSmooth 0 y
  have hΓeq : Γ = roundModelTensorConnection gE.euclideanCoefficients := by
    funext y
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro T
    apply TensorFiber.ext
    intro a
    simp only [Γ, tensorCoordinateConnectionCoefficient_apply,
      roundModelTensorConnection_apply, modelTensorSlotActionLift,
      PoincareConjecture.TensorFiber.negativeSlotAction_apply,
      DE.coordinateConnectionCoefficient_model]
  have hΓsmooth : ContDiffAt ℝ ∞ Γ 0 := by
    rw [hΓeq]
    exact contDiffAt_roundModelTensorConnection
      (gE.contDiffAt_euclideanCoefficients 0) (gE.inner_isInvertible 0)
  have hΓzero : Γ 0 = 0 := by
    have hz := gauss_center_coordinate_connection_zero DE hEgauss
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro T
    apply TensorFiber.ext
    intro a
    simp [Γ, tensorCoordinateConnectionCoefficient_apply, hz]
  have h0 : ∀ v w, gE.inner 0 v w = inner ℝ v w := by
    intro v w
    have hc := congrArg (fun K : MetricCoefficient 3 => K v w)
      (heq 0 (mem_closedBall.mpr (by simpa using hr.le)))
    change gE.inner 0 v w = N.model_metric.pullbackCoefficients e 0 v w at hc
    rw [hcenter] at hc
    exact hc
  let C : ℝ := ‖modelTensorConnectionLiftMap‖ * 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hΓev := source_tensor_connection_eventually_eq_model N hr e DE heq
  have hΓder := hΓev.fderiv_eq (𝕜 := ℝ)
  have hG (u : GaussErrorE) : ‖fderiv ℝ Γ 0 u‖ ≤ C * ‖u‖ := by
    rw [hΓder]
    exact norm_round_model_tensor_connection_fderiv_le_universal N
      (hr.trans (hrs.trans hsR)) e he hi hcenter hgauss u
  have hScoord : ContDiffAt ℝ ∞ Scoord 0 :=
    contDiffAt_tensorCoordinateSection hSmooth 0 (by simp)
  have hS0norm : ‖Scoord 0‖ ≤ epsilon := by
    have hn := hcov 0 (by omega)
    change ‖tensorCoordinateSection hSmooth 0 0‖ ≤ epsilon
    rw [tensorCoordinateSection_norm_eq_of_normalized hSmooth h0]
    exact hn
  refine ⟨B, hB, hGerm, ?_⟩
  intro u v w z
  have hQsmooth := DE.iteratedCovariantTensorDerivative_isSmooth hSmooth 2
  obtain ⟨AQ, hAQ⟩ := hQsmooth.1 0
  have hQ (a : Fin 2 → GaussErrorE) :
      |DE.iteratedCovariantTensorDerivative S 2 0
          (Fin.cons u (Fin.cons v a))| ≤
        epsilon * ‖u‖ * ‖v‖ * ∏ i, ‖a i‖ := by
    have h := abs_tensor_evaluation_le_tensorNorm gE
      (DE.iteratedCovariantTensorDerivative S 2) 0 AQ hAQ
      (Fin.cons u (Fin.cons v a))
    have hn := hcov 2 (by omega)
    calc
      _ ≤ gE.tensorNorm (DE.iteratedCovariantTensorDerivative S 2) 0 *
          (gE.tangentNorm 0 u * (gE.tangentNorm 0 v * ∏ i,
            gE.tangentNorm 0 (a i))) := by
            simpa [Fin.prod_univ_succ, mul_assoc] using h
      _ ≤ epsilon * (gE.tangentNorm 0 u * (gE.tangentNorm 0 v * ∏ i,
            gE.tangentNorm 0 (a i))) :=
            mul_le_mul_of_nonneg_right hn (by
              apply mul_nonneg (Real.sqrt_nonneg _)
              apply mul_nonneg (Real.sqrt_nonneg _)
              exact Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _))
      _ = epsilon * ‖u‖ * ‖v‖ * ∏ i, ‖a i‖ := by
            simp only [tangentNorm_zero_eq_norm_of_normalized h0]
            ring
  have hcov_eval :
      Poincare.Riemannian.RadialTransport.covariantDerivative Γ
          (fun y => Poincare.Riemannian.RadialTransport.covariantDerivative
            Γ Scoord y v) 0 u ![w, z] =
        DE.iteratedCovariantTensorDerivative S 2 0 ![u, v, w, z] := by
    have h := second_covariantDerivative_tensorCoordinateSection_apply DE
      hSmooth 0 (z := 0) (by simp) u v ![w, z]
    have hz := gauss_center_coordinate_connection_zero DE hEgauss
    simpa [Γ, Scoord, hz, tensorCoordinateEvaluation_model,
      Poincare.Riemannian.RadialTransport.covariantDerivative] using h
  have hAeval :
      |Poincare.Riemannian.RadialTransport.covariantDerivative Γ
          (fun y => Poincare.Riemannian.RadialTransport.covariantDerivative
            Γ Scoord y v) 0 u ![w, z]| ≤
        epsilon * ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ := by
    rw [hcov_eval]
    simpa [mul_assoc] using hQ ![w, z]
  have hsecond := second_fderiv_eq_covariant_sub_connectionJet
    hΓsmooth hScoord hΓzero u v
  have hsecond_eval := congrArg (fun T => T ![w, z]) hsecond
  have htarget :
      fderiv ℝ (fun y => fderiv ℝ (fun x => B x w z) y v) 0 u =
        Poincare.Riemannian.RadialTransport.covariantDerivative Γ
            (fun y => Poincare.Riemannian.RadialTransport.covariantDerivative
              Γ Scoord y v) 0 u ![w, z] -
          ((fderiv ℝ Γ 0 u) v (Scoord 0)) ![w, z] := by
    have hSall : ContDiff ℝ ∞ Scoord := by
      apply contDiff_iff_contDiffAt.mpr
      intro y
      exact contDiffAt_tensorCoordinateSection hSmooth 0 (z := y) (by simp)
    have hEval (y : GaussErrorE) :
        fderiv ℝ (fun x => B x w z) y v =
          (fderiv ℝ Scoord y v) ![w, z] := by
      have h := TensorFiber.fderiv_evaluation
        (hSall.differentiable (by simp) y) ![w, z] v
      simpa [Scoord, tensorCoordinateSection_apply,
        tensorCoordinateEvaluation_model] using h
    simp_rw [hEval]
    have hDall : ContDiffAt ℝ ∞ (fun y => fderiv ℝ Scoord y v) 0 :=
      (hSall.contDiffAt.fderiv_right (by simp)).clm_apply contDiffAt_const
    rw [TensorFiber.fderiv_evaluation
      (hDall.differentiableAt (by simp))]
    exact hsecond_eval
  rw [htarget]
  calc
    |Poincare.Riemannian.RadialTransport.covariantDerivative Γ
          (fun y => Poincare.Riemannian.RadialTransport.covariantDerivative
            Γ Scoord y v) 0 u ![w, z] -
        ((fderiv ℝ Γ 0 u) v (Scoord 0)) ![w, z]| ≤
      epsilon * ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ +
        |((fderiv ℝ Γ 0 u) v (Scoord 0)) ![w, z]| :=
          (abs_sub _ _).trans (add_le_add hAeval le_rfl)
    _ ≤ epsilon * ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ +
        (C * ‖u‖) * ‖v‖ * epsilon * ‖w‖ * ‖z‖ := by
      gcongr
      have hT := tensorFiber_two_eval_le
        ((fderiv ℝ Γ 0 u) v (Scoord 0)) w z
      calc
        |((fderiv ℝ Γ 0 u) v (Scoord 0)) ![w, z]| ≤
            ‖(fderiv ℝ Γ 0 u) v (Scoord 0)‖ * ‖w‖ * ‖z‖ := hT
        _ ≤ ((C * ‖u‖) * ‖v‖) * ‖Scoord 0‖ * ‖w‖ * ‖z‖ := by
          gcongr
          exact (ContinuousLinearMap.le_opNorm ((fderiv ℝ Γ 0 u) v)
            (Scoord 0)).trans (mul_le_mul_of_nonneg_right
              ((ContinuousLinearMap.le_opNorm (fderiv ℝ Γ 0 u) v).trans
                (mul_le_mul_of_nonneg_right (hG u) (norm_nonneg v)))
              (norm_nonneg (Scoord 0)))
        _ ≤ (C * ‖u‖) * ‖v‖ * epsilon * ‖w‖ * ‖z‖ := by
          gcongr

end PoincareConjecture.M28.tube
