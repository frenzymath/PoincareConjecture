import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundModelPolarization
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundComponent
import PoincareConjecture.Proofs.M04.CurvatureSymmetries









set_option autoImplicit false
set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M28.tube

theorem singularRound_curvatureTensor_eq_metricGram
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (x : N.model.carrier)
    (a b c d : TangentSpace (𝓡 3) x) :
    N.model_connection.curvatureTensor x a b c d =
      N.model_metric.inner x a c * N.model_metric.inner x b d -
        N.model_metric.inner x b c * N.model_metric.inner x a d := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : N.model.carrier → Type _) :=
    ⟨N.model_metric.toRiemannianMetric⟩
  let E := TangentSpace (𝓡 3) x
  let B : LinearMap.BilinForm ℝ E :=
    LinearMap.mk₂ ℝ (fun u v => N.model_metric.inner x u v)
      (fun u v w => by simp only [map_add, add_apply])
      (fun r v w => by simp only [map_smul, smul_apply])
      (fun u v w => by simp only [map_add])
      (fun r v w => by simp only [map_smul])
  let T := PoincareConjecture.M13.curvatureTensorLinear N.model_connection x -
    roundModelGramForm B
  have hT (u v w z : E) : T u v w z =
      N.model_connection.curvatureTensor x u v w z -
        (N.model_metric.inner x u w * N.model_metric.inner x v z -
          N.model_metric.inner x v w * N.model_metric.inner x u z) := by
    rfl
  have hfirst (u v w z : E) : T u v w z = -T v u w z := by
    rw [hT, hT, M04.curvatureTensor_swap_first N.model_connection x u v w z]
    ring
  have hpair (u v w z : E) : T u v w z = T w z u v := by
    rw [hT, hT, M04.curvatureTensor_pair_exchange N.model_connection x,
      N.model_metric.symm x w u, N.model_metric.symm x z v,
      N.model_metric.symm x z u, N.model_metric.symm x w v]
    ring
  have hcyclic (u v w z : E) :
      T u v w z + T v w u z + T w u v z = 0 := by
    simp only [hT]
    rw [N.model_metric.symm x v u, N.model_metric.symm x w u,
      N.model_metric.symm x w v]
    linarith only [M04.curvatureTensor_cyclic N.model_connection x u v w z]
  have hunit (u v : E)
      (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0) : T u v u v = 0 := by
    have huu : N.model_metric.inner x u u = 1 := by
      change inner ℝ u u = 1
      rw [real_inner_self_eq_norm_sq, hu, one_pow]
    have hvv : N.model_metric.inner x v v = 1 := by
      change inner ℝ v v = 1
      rw [real_inner_self_eq_norm_sq, hv, one_pow]
    have huv' : N.model_metric.inner x u v = 0 := by
      change inner ℝ u v = 0
      exact huv
    have hvu' : N.model_metric.inner x v u = 0 := by
      rw [N.model_metric.symm x v u, huv']
    have h := N.model_curvature_one x u v ⟨huu, hvv, huv⟩
    simp only [LeviCivitaData.sectionalCurvature, huu, hvv, huv',
      one_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, div_one] at h
    rw [hT, h, huu, hvv, hvu', huv', mul_zero]
    norm_num
  exact sub_eq_zero.mp (roundModel_form_zero_of_unit_planes T hfirst hpair hcyclic hunit a b c d)

end PoincareConjecture.M28.tube
