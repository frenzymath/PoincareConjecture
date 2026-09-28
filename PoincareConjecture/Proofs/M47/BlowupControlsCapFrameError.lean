import PoincareConjecture.Proofs.M47.BlowupControlsCapFrameNorm
import PoincareConjecture.Proofs.M47.BlowupControlsCapMetricError

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "I" => Fin 3
local notation "V" => EuclideanSpace ℝ I

variable {M : Type*} [TopologicalSpace M] [ChartedSpace V M] [IsManifold (𝓡 3) ∞ M]

theorem cap_frameInverseGram_symm (g : RiemannianMetric 3 M) (x : M)
    (e : V ≃L[ℝ] TangentSpace (𝓡 3) x) (i j : I) :
    M04.frameInverseGram g x e.toContinuousLinearMap i j =
      M04.frameInverseGram g x e.toContinuousLinearMap j i := by
  rw [← M04.frameInverseGram_eq_coordinate_sum g x e i j,
    ← M04.frameInverseGram_eq_coordinate_sum g x e j i]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem cap_frameError_components_norm (g0 g1 : RiemannianMetric 3 M) (x : M)
    (e : V ≃L[ℝ] TangentSpace (𝓡 3) x)
    (he : ∀ v w, g0.inner x (e v) (e w) = inner ℝ v w) :
    ‖capOperatorComponents
      (M04.frameGramOperator g1 x e.toContinuousLinearMap - ContinuousLinearMap.id ℝ V)‖ =
      g0.tensorNorm (fun y (w : Fin 2 → TangentSpace (𝓡 3) y) =>
        g1.inner y (w 0) (w 1) - g0.inner y (w 0) (w 1)) x := by
  let b := EuclideanSpace.basisFun I ℝ
  let H : CovariantTensorEvaluation 3 M 2 :=
    fun y w => g1.inner y (w 0) (w 1) - g0.inner y (w 0) (w 1)
  have hc : capOperatorComponents
      (M04.frameGramOperator g1 x e.toContinuousLinearMap - ContinuousLinearMap.id ℝ V) =
      WithLp.toLp 2 (fun p : I × I => H x ![e (b p.1), e (b p.2)]) := by
    ext p
    change inner ℝ (b p.1)
      (M04.frameGramOperator g1 x e.toContinuousLinearMap (b p.2) - b p.2) =
      g1.inner x (e (b p.1)) (e (b p.2)) - g0.inner x (e (b p.1)) (e (b p.2))
    rw [inner_sub_right,
      real_inner_comm (M04.frameGramOperator g1 x e.toContinuousLinearMap (b p.2)) (b p.1),
      cap_frameGram_inner]
    change g1.inner x (e (b p.2)) (e (b p.1)) - inner ℝ (b p.1) (b p.2) = _
    exact congrArg₂ (fun u v : ℝ => u - v)
      (g1.symm x (e (b p.2)) (e (b p.1))) (he (b p.1) (b p.2)).symm
  rw [hc]
  exact cap_tensorNorm_frame_pair g0 H x ((cap_metricDifference_smooth g0 g1).1 x) e he

theorem cap_inverseError_tensor_norm_le (g0 g1 : RiemannianMetric 3 M) (x : M)
    (e : V ≃L[ℝ] TangentSpace (𝓡 3) x)
    (he : ∀ v w, g0.inner x (e v) (e w) = inner ℝ v w) :
    let A := M04.frameGramOperator g1 x e.toContinuousLinearMap
    ‖capOperatorComponents (A.inverse - ContinuousLinearMap.id ℝ V)‖ ≤
      ‖A.inverse‖ * g0.tensorNorm (fun y (w : Fin 2 → TangentSpace (𝓡 3) y) =>
        g1.inner y (w 0) (w 1) - g0.inner y (w 0) (w 1)) x := by
  have h := cap_frameInverseGram_component_error_le g1 x e
  dsimp only at h
  rwa [cap_frameError_components_norm g0 g1 x e he] at h

theorem cap_inverseError_components (g0 g1 : RiemannianMetric 3 M) (x : M)
    (e : V ≃L[ℝ] TangentSpace (𝓡 3) x)
    (he : ∀ v w, g0.inner x (e v) (e w) = inner ℝ v w) :
    (WithLp.toLp 2 (fun p : I × I =>
      M04.frameInverseGram g1 x e.toContinuousLinearMap p.1 p.2 -
        M04.frameInverseGram g0 x e.toContinuousLinearMap p.1 p.2) :
      EuclideanSpace ℝ (I × I)) =
      capOperatorComponents ((M04.frameGramOperator g1 x e.toContinuousLinearMap).inverse -
        ContinuousLinearMap.id ℝ V) := by
  ext p
  change inner ℝ (EuclideanSpace.basisFun I ℝ p.1)
      ((M04.frameGramOperator g1 x e.toContinuousLinearMap).inverse
        (EuclideanSpace.basisFun I ℝ p.2)) -
    inner ℝ (EuclideanSpace.basisFun I ℝ p.1)
      ((M04.frameGramOperator g0 x e.toContinuousLinearMap).inverse
        (EuclideanSpace.basisFun I ℝ p.2)) = _
  rw [cap_frameGram_eq_identity g0 x e he, ContinuousLinearMap.inverse_id]
  exact (inner_sub_right _ _ _).symm

end PoincareConjecture.M47
