import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.Scalar.Trace
import PoincareConjecture.Definitions.Ch11.SingularLimits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

theorem SingularRoundComponent.model_scalar_eq_six
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    (x : N.model.carrier) :
    N.model_connection.scalarCurvature x = 6 := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : N.model.carrier → Type _) :=
    ⟨N.model_metric.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 3)), finrank_euclideanSpace]
    simp
  let b := (N.model_metric.orthonormalBasis x).reindex (finCongr hdim)
  have hb (i j : Fin 3) : N.model_metric.inner x (b i) (b j) =
      if i = j then 1 else 0 := by
    change inner ℝ (b i) (b j) = _
    exact b.inner_eq_ite i j
  have hdiag (i : Fin 3) :
      N.model_connection.curvatureTensor x (b i) (b i) (b i) (b i) = 0 := by
    have h := N.model_connection.curvatureTensor_swap_first x (b i) (b i) (b i) (b i)
    linarith
  have hterm (i j : Fin 3) :
      (if i = j then 0 else 1) =
        N.model_connection.curvatureTensor x (b i) (b j) (b i) (b j) := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true, hdiag]
    · have hp : LeviCivitaData.IsOrthonormalPair N.model_metric x (b i) (b j) :=
        ⟨by simp only [hb, ite_true], by simp only [hb, ite_true],
          by simp only [hb, hij, ite_false]⟩
      have h := N.model_curvature_one x (b i) (b j) hp
      simpa only [LeviCivitaData.sectionalCurvature, hb, hij, ite_false,
        ite_true, mul_one, zero_pow (by decide : 2 ≠ 0), sub_zero, div_one] using h.symm
  calc
    N.model_connection.scalarCurvature x =
        ∑ i : Fin 3, ∑ j : Fin 3,
          N.model_connection.curvatureTensor x (b i) (b j) (b i) (b j) :=
      N.model_connection.scalarCurvature_eq_sum_orthonormalBasis x b
    _ = ∑ i : Fin 3, ∑ j : Fin 3, if i = j then 0 else 1 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact (hterm i j).symm
    _ = 6 := by
      simp [Fin.sum_univ_succ]
      norm_num

end PoincareConjecture
