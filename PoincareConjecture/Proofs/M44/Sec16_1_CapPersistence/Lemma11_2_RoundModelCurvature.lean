import PoincareConjecture.Proofs.M44.Mathlib.MetricCurvatureForm
import PoincareConjecture.Proofs.M13.CurvatureContractions
import PoincareConjecture.Proofs.M04.SectionalMinimumDiffusion
import PoincareConjecture.Proofs.M04.TensorNorm
import PoincareConjecture.Definitions.Ch04.Pinching

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M44

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] {g : RiemannianMetric 3 M}

theorem curvatureTensor_eq_metricGram_of_sectional_one (D : LeviCivitaData g)
    (hsec : ∀ x v w, LeviCivitaData.IsOrthonormalPair g x v w →
      D.sectionalCurvature x v w = 1)
    (x : M) (a b c d : TangentSpace (𝓡 3) x) :
    D.curvatureTensor x a b c d =
      g.inner x a c * g.inner x b d - g.inner x b c * g.inner x a d := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let B : TangentSpace (𝓡 3) x →ₗ[ℝ] TangentSpace (𝓡 3) x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => g.inner x u v)
      (fun u v w => by simp only [map_add, add_apply])
      (fun r v w => by simp only [map_smul, smul_apply])
      (fun u v w => by simp only [map_add])
      (fun r v w => by simp only [map_smul])
  let T := M13.curvatureTensorLinear D x - metricCurvatureForm B
  have hT (u v w z : TangentSpace (𝓡 3) x) : T u v w z =
      D.curvatureTensor x u v w z -
        (g.inner x u w * g.inner x v z - g.inner x v w * g.inner x u z) := rfl
  have hfirst (u v w z : TangentSpace (𝓡 3) x) : T u v w z = -T v u w z := by
    rw [hT, hT, M04.curvatureTensor_swap_first D x u v w z]
    ring
  have hpair (u v w z : TangentSpace (𝓡 3) x) : T u v w z = T w z u v := by
    rw [hT, hT, M04.curvatureTensor_pair_exchange D x,
      g.symm x w u, g.symm x z v, g.symm x z u, g.symm x w v]
    ring
  have hcyclic (u v w z : TangentSpace (𝓡 3) x) :
      T u v w z + T v w u z + T w u v z = 0 := by
    simp only [hT]
    rw [g.symm x v u, g.symm x w u, g.symm x w v]
    linarith only [M04.curvatureTensor_cyclic D x u v w z]
  have hunit (u v : TangentSpace (𝓡 3) x)
      (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0) : T u v u v = 0 := by
    have huu : g.inner x u u = 1 := by
      change inner ℝ u u = 1
      rw [real_inner_self_eq_norm_sq, hu, one_pow]
    have hvv : g.inner x v v = 1 := by
      change inner ℝ v v = 1
      rw [real_inner_self_eq_norm_sq, hv, one_pow]
    have huv' : g.inner x u v = 0 := huv
    have h := hsec x u v ⟨huu, hvv, huv'⟩
    simp only [LeviCivitaData.sectionalCurvature, huu, hvv, huv',
      one_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, div_one] at h
    rw [hT, h, huu, hvv, huv', mul_zero]
    norm_num
  exact sub_eq_zero.mp (curvatureForm_zero_of_orthonormal T hfirst hpair hcyclic hunit a b c d)

theorem riemannEvaluation_eq_metricGram_of_sectional_one (D : LeviCivitaData g)
    (hsec : ∀ x v w, LeviCivitaData.IsOrthonormalPair g x v w →
      D.sectionalCurvature x v w = 1) :
    D.riemannEvaluation = M04.metricGramEvaluation g := by
  funext x v
  rw [LeviCivitaData.riemannEvaluation,
    curvatureTensor_eq_metricGram_of_sectional_one D hsec]
  dsimp [M04.metricGramEvaluation]
  ring

theorem covariant_curvature_zero_of_sectional_one (D : LeviCivitaData g)
    (hsec : ∀ x v w, LeviCivitaData.IsOrthonormalPair g x v w →
      D.sectionalCurvature x v w = 1) :
    D.covariantTensorDerivative D.riemannEvaluation = 0 := by
  rw [riemannEvaluation_eq_metricGram_of_sectional_one D hsec]
  exact M04.covariantTensorDerivative_metricGramEvaluation D

theorem iterated_curvature_zero_of_sectional_one (D : LeviCivitaData g)
    (hsec : ∀ x v w, LeviCivitaData.IsOrthonormalPair g x v w →
      D.sectionalCurvature x v w = 1) (m : ℕ) :
    D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1) = 0 := by
  induction m with
  | zero => exact covariant_curvature_zero_of_sectional_one D hsec
  | succ m ih =>
    rw [LeviCivitaData.iteratedCovariantTensorDerivative, ih]
    funext x v
    simp [LeviCivitaData.covariantTensorDerivative, mvfderiv_const]

theorem curvatureDerivativeNorm_succ_zero_of_sectional_one (D : LeviCivitaData g)
    (hsec : ∀ x v w, LeviCivitaData.IsOrthonormalPair g x v w →
      D.sectionalCurvature x v w = 1) (m : ℕ) (x : M) :
    D.curvatureDerivativeNorm (m + 1) x = 0 := by
  simp [LeviCivitaData.curvatureDerivativeNorm,
    iterated_curvature_zero_of_sectional_one D hsec, RiemannianMetric.tensorNorm]

end PoincareConjecture.M44
