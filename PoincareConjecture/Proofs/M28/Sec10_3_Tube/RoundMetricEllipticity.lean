import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundTransfer
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.NormBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Orthonormal
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.InverseEstimate











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M28.tube

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem round_metric_zero_norm_lt
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (x : N.model.carrier) :
    roundMetricJetNorm N 0 x < epsilon := by
  obtain ⟨bound, hbound, hmetric⟩ := N.metric_comparison
  exact singularMetricJetNorm_lt_of_error_lt N.model_metric N.model_connection
    (fun y v => N.scale * singularMetricPullback g N.forward y v)
    ⌊epsilon⁻¹⌋₊ 0 x (Nat.zero_le _) N.epsilon_pos (hmetric x) hbound


theorem round_metric_error_le
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (x : N.model.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    |N.scale * g.inner (N.forward x)
        (mfderiv (𝓡 3) (𝓡 3) N.forward x v)
        (mfderiv (𝓡 3) (𝓡 3) N.forward x w) - N.model_metric.inner x v w| ≤
      epsilon * N.model_metric.tangentNorm x v * N.model_metric.tangentNorm x w := by
  let T : CovariantTensorEvaluation 3 N.model.carrier 2 :=
    fun y a => N.scale * singularMetricPullback g N.forward y a -
      N.model_metric.inner y (a 0) (a 1)
  let A : MultilinearMap ℝ
      (fun _ : Fin 2 => TangentSpace (𝓡 3) x) ℝ :=
    MultilinearMap.mk' (T x)
      (by
        intro a i u v
        fin_cases i <;>
          simp [T, singularMetricPullback, map_add, mul_add] <;> ring)
      (by
        intro a i r v
        fin_cases i <;>
          simp [T, singularMetricPullback, map_smul, mul_sub] <;> ring)
  have h := abs_tensor_evaluation_le_tensorNorm N.model_metric T x A
    (fun _ => rfl) ![v, w]
  have hn := round_metric_zero_norm_lt N x
  change N.model_metric.tensorNorm T x < epsilon at hn
  have hN : 0 ≤ N.model_metric.tangentNorm x v *
      N.model_metric.tangentNorm x w :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hprod := mul_le_mul_of_nonneg_right hn.le hN
  exact h.trans (by
    simpa [T, singularMetricPullback, Fin.prod_univ_succ, mul_assoc] using hprod)


theorem round_metric_quadratic_bounds
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (x : N.model.carrier)
    (v : TangentSpace (𝓡 3) x) :
    (1 - epsilon) * N.model_metric.inner x v v ≤
        N.scale * g.inner (N.forward x)
          (mfderiv (𝓡 3) (𝓡 3) N.forward x v)
          (mfderiv (𝓡 3) (𝓡 3) N.forward x v) ∧
      N.scale * g.inner (N.forward x)
          (mfderiv (𝓡 3) (𝓡 3) N.forward x v)
          (mfderiv (𝓡 3) (𝓡 3) N.forward x v) ≤
        (1 + epsilon) * N.model_metric.inner x v v := by
  have h := round_metric_error_le N x v v
  have hpos : 0 ≤ N.model_metric.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (N.model_metric.pos x v hv).le
  have hs : N.model_metric.tangentNorm x v ^ 2 =
      N.model_metric.inner x v v := Real.sq_sqrt hpos
  rw [mul_assoc, ← sq, hs] at h
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  constructor <;> nlinarith


noncomputable def roundFrameCoefficients
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (x : N.model.carrier)
    (L : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3)) :
    SpacetimeBounds.MetricCoefficient 3 := by
  let A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (mfderiv (𝓡 3) (𝓡 3) N.forward x).comp L.toContinuousLinearMap
  exact N.scale • ContinuousLinearMap.bilinearComp
    (g.inner (N.forward x)) A A

noncomputable def roundEuclideanCoefficients : SpacetimeBounds.MetricCoefficient 3 :=
  innerSL ℝ



theorem exists_round_frame_ellipticity
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (hepsilon : epsilon ≤ 1 / 2)
    (x : N.model.carrier) :
    ∃ L : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3),
      (∀ v w, N.model_metric.inner x (L v) (L w) = inner ℝ v w) ∧
      ‖roundFrameCoefficients N x L - roundEuclideanCoefficients‖ ≤ epsilon ∧
      (∀ v, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ roundFrameCoefficients N x L v v) ∧
      ‖(roundFrameCoefficients N x L).inverse‖ ≤ 2 := by
  obtain ⟨L, hL⟩ := N.model_metric.exists_orthonormal_coordinate_frame x
  have hframe (v w : EuclideanSpace ℝ (Fin 3)) :
      N.model_metric.inner x (L v) (L w) = inner ℝ v w := by
    simpa only [RiemannianMetric.chartCoefficients_center] using hL v w
  have hnorm (v : EuclideanSpace ℝ (Fin 3)) :
      N.model_metric.tangentNorm x (L v) = ‖v‖ := by
    change Real.sqrt (N.model_metric.inner x (L v) (L v)) = ‖v‖
    rw [hframe, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)]
  have herror : ‖roundFrameCoefficients N x L - roundEuclideanCoefficients‖ ≤ epsilon := by
    apply ContinuousLinearMap.opNorm_le_bound₂ _ N.epsilon_pos.le
    intro v w
    have h := round_metric_error_le N x (L v) (L w)
    change |N.scale * g.inner (N.forward x)
      (mfderiv (𝓡 3) (𝓡 3) N.forward x (L v))
      (mfderiv (𝓡 3) (𝓡 3) N.forward x (L w)) - inner ℝ v w| ≤ _
    simpa only [hframe, hnorm] using h
  have hell (v : EuclideanSpace ℝ (Fin 3)) :
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ roundFrameCoefficients N x L v v := by
    have h := (round_metric_quadratic_bounds N x (L v)).1
    have hm : (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ (1 - epsilon) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    change _ ≤ N.scale * g.inner (N.forward x)
      (mfderiv (𝓡 3) (𝓡 3) N.forward x (L v))
      (mfderiv (𝓡 3) (𝓡 3) N.forward x (L v))
    exact hm.trans (by simpa only [hframe, real_inner_self_eq_norm_sq] using h)
  refine ⟨L, hframe, herror, hell, ?_⟩
  simpa using CoordinateExponential.norm_inverse_le_of_ellipticity
    (by norm_num : (0 : ℝ) < 1 / 2) hell


theorem exists_round_frame_inverse_error
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (hepsilon : epsilon ≤ 1 / 2)
    (x : N.model.carrier) :
    ∃ L : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3),
      (∀ v w, N.model_metric.inner x (L v) (L w) = inner ℝ v w) ∧
      ‖roundFrameCoefficients N x L - roundEuclideanCoefficients‖ ≤ epsilon ∧
      ‖(roundFrameCoefficients N x L).inverse‖ ≤ 2 ∧
      ‖(roundFrameCoefficients N x L).inverse -
          roundEuclideanCoefficients.inverse‖ ≤ 4 * epsilon := by
  obtain ⟨L, hL, herror, hell, hinv⟩ := exists_round_frame_ellipticity N hepsilon x
  refine ⟨L, hL, herror, hinv, ?_⟩
  have heuc (v : EuclideanSpace ℝ (Fin 3)) :
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ roundEuclideanCoefficients v v := by
    change _ ≤ inner ℝ v v
    rw [real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg ‖v‖]
  have h := CoordinateExponential.norm_inverse_sub_le_of_ellipticity
    (by norm_num : (0 : ℝ) < 1 / 2) hell heuc
  have he := div_le_div_of_nonneg_right herror (sq_nonneg (1 / 2 : ℝ))
  exact h.trans (by norm_num at he ⊢; linarith)

end PoincareConjecture.M28.tube
