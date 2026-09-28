import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundModelCurvature
import PoincareConjecture.Proofs.M04.SectionalMinimumDiffusion
import PoincareConjecture.Proofs.M04.TensorNorm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M28.tube

theorem singularRound_riemannEvaluation_eq_metricGram
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) :
    N.model_connection.riemannEvaluation =
      M04.metricGramEvaluation N.model_metric := by
  funext x v
  rw [LeviCivitaData.riemannEvaluation,
    singularRound_curvatureTensor_eq_metricGram N x
      (v 0) (v 1) (v 2) (v 3)]
  dsimp [M04.metricGramEvaluation]
  ring

theorem singularRound_covariant_curvature_zero
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) :
    N.model_connection.covariantTensorDerivative
        N.model_connection.riemannEvaluation = 0 := by
  rw [singularRound_riemannEvaluation_eq_metricGram N]
  exact M04.covariantTensorDerivative_metricGramEvaluation N.model_connection

theorem singularRound_iterated_curvature_zero
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (m : ℕ) :
    N.model_connection.iteratedCovariantTensorDerivative
        N.model_connection.riemannEvaluation (m + 1) = 0 := by
  induction m with
  | zero => exact singularRound_covariant_curvature_zero N
  | succ m ih =>
    rw [LeviCivitaData.iteratedCovariantTensorDerivative, ih]
    funext x v
    simp [LeviCivitaData.covariantTensorDerivative, mvfderiv_const]

theorem singularRound_curvatureDerivativeNorm_succ_zero
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (m : ℕ) (x : N.model.carrier) :
    N.model_connection.curvatureDerivativeNorm (m + 1) x = 0 := by
  simp [LeviCivitaData.curvatureDerivativeNorm,
    singularRound_iterated_curvature_zero N m, RiemannianMetric.tensorNorm]

theorem singularRound_curvatureTensorNorm_le_nine
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (x : N.model.carrier) :
    N.model_connection.curvatureTensorNorm x ≤ 9 := by
  classical
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : N.model.carrier → Type _) :=
    ⟨N.model_metric.toRiemannianMetric⟩
  let b := N.model_metric.orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    unfold TangentSpace
    simp
  have hb (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      N.model_metric.inner x (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  have hcomponent
      (i j k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      (N.model_connection.curvatureTensor x (b i) (b j) (b k) (b l)) ^ 2 ≤ 1 := by
    rw [singularRound_curvatureTensor_eq_metricGram N x
      (b i) (b j) (b k) (b l)]
    simp only [hb]
    split_ifs <;> norm_num
  change Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
    (N.model_connection.curvatureTensor x (b i) (b j) (b k) (b l)) ^ 2) ≤ 9
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by norm_num, ?_⟩
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
          ∑ _k : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
            ∑ _l : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)), (1 : ℝ) := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hcomponent i j k l
    _ = 9 ^ 2 := by norm_num [hdim]

theorem singularRound_curvatureDerivativeNorm_le_nine
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (m : ℕ) (x : N.model.carrier) :
    N.model_connection.curvatureDerivativeNorm m x ≤ 9 := by
  cases m with
  | zero =>
    rw [N.model_connection.curvatureDerivativeNorm_zero]
    exact singularRound_curvatureTensorNorm_le_nine N x
  | succ m =>
    rw [singularRound_curvatureDerivativeNorm_succ_zero N m x]
    norm_num

end PoincareConjecture.M28.tube
