import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundMetricEllipticity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Algebra










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M28.tube

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

noncomputable def roundMetricError
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) :
    CovariantTensorEvaluation 3 N.model.carrier 2 :=
  fun y a => N.scale * singularMetricPullback g N.forward y a -
    N.model_metric.inner y (a 0) (a 1)


theorem round_metric_error_smooth
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) :
    IsSmoothCovariantTensor (roundMetricError N) := by
  have hpull : IsSmoothCovariantTensor (singularMetricPullback g N.forward) := by
    constructor
    · intro y
      let A : MultilinearMap ℝ
          (fun _ : Fin 2 => TangentSpace (𝓡 3) y) ℝ :=
        MultilinearMap.mk' (singularMetricPullback g N.forward y)
          (by
            intro a i u v
            fin_cases i <;> simp [singularMetricPullback, map_add])
          (by
            intro a i r v
            fin_cases i <;> simp [singularMetricPullback, map_smul])
      exact ⟨A, fun _ => rfl⟩
    · intro U hU X hX
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      have ht := N.forward_smooth.contMDiff_tangentMap (m := ∞) (by simp)
      have h0 := ht.comp_contMDiffOn (hX 0)
      have h1 := ht.comp_contMDiffOn (hX 1)
      exact h0.inner_bundle h1
  have hmodel : IsSmoothCovariantTensor
      (fun (y : N.model.carrier)
        (a : Fin 2 → TangentSpace (𝓡 3) y) =>
        N.model_metric.inner y (a 0) (a 1)) := by
    constructor
    · intro y
      let A : MultilinearMap ℝ
          (fun _ : Fin 2 => TangentSpace (𝓡 3) y) ℝ :=
        MultilinearMap.mk' (fun a => N.model_metric.inner y (a 0) (a 1))
          (by
            intro a i u v
            fin_cases i <;> simp [map_add])
          (by
            intro a i r v
            fin_cases i <;> simp [map_smul])
      exact ⟨A, fun _ => rfl⟩
    · intro U hU X hX
      let : Bundle.RiemannianBundle
          (TangentSpace (𝓡 3) : N.model.carrier → Type _) :=
        ⟨N.model_metric.toRiemannianMetric⟩
      exact (hX 0).inner_bundle (hX 1)
  exact (hpull.const_mul N.scale).sub hmodel


theorem round_metric_covariant_error_le
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    (horder : 2 ≤ ⌊epsilon⁻¹⌋₊)
    (x : N.model.carrier) (j : ℕ) (hj : j ≤ 2)
    (v : Fin (2 + j) → TangentSpace (𝓡 3) x) :
    |N.model_connection.iteratedCovariantTensorDerivative (roundMetricError N) j x v| ≤
      epsilon * ∏ i, N.model_metric.tangentNorm x (v i) := by
  have hs := N.model_connection.iteratedCovariantTensorDerivative_isSmooth
    (round_metric_error_smooth N) j
  obtain ⟨A, hA⟩ := hs.1 x
  have h := abs_tensor_evaluation_le_tensorNorm N.model_metric
    (N.model_connection.iteratedCovariantTensorDerivative (roundMetricError N) j)
    x A hA v
  have hjet := roundMetricJetNorm_lt N horder x j hj
  change N.model_metric.tensorNorm
    (N.model_connection.iteratedCovariantTensorDerivative (roundMetricError N) j)
    x < epsilon at hjet
  exact h.trans (mul_le_mul_of_nonneg_right hjet.le
    (Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)))

end PoincareConjecture.M28.tube
