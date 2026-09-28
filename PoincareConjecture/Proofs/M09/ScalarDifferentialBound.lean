import PoincareConjecture.Proofs.M09.RicciDerivative
import PoincareConjecture.Proofs.M09.TensorEvaluationBound







set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators RealInnerProductSpace

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem scalarCurvature_mvfderiv_abs_le (hM04 : RicciFlowCurvatureTheory.{u})
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
    (X : TangentSpace (𝓡 n) p) :
    |mvfderiv (𝓡 n) D.scalarCurvature p X| ≤
      (n : ℝ) ^ 2 * D.curvatureDerivativeNorm 1 p * g.tangentNorm p X := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis p
  have hb (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) p))) :
      g.tangentNorm p (b i) = 1 := by
    change Real.sqrt ⟪b i, b i⟫ = 1
    rw [← norm_eq_sqrt_real_inner, b.norm_eq_one]
  have hcalc := hM04.tensor_calculus n M g D
  have hDR := hcalc.2.2.1 4 D.riemannEvaluation hcalc.1
  have hterm (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) p))) :
      |D.covariantTensorDerivative D.riemannEvaluation p ![X, b i, b j, b i, b j]| ≤
        D.curvatureDerivativeNorm 1 p * g.tangentNorm p X := by
    have h := tensor_abs_le_tensorNorm g (D.covariantTensorDerivative D.riemannEvaluation)
      hDR p ![X, b i, b j, b i, b j]
    simpa [LeviCivitaData.curvatureDerivativeNorm,
      LeviCivitaData.iteratedCovariantTensorDerivative, Fin.prod_univ_succ, hb] using h
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) p) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  rw [scalarCurvature_mvfderiv_contraction hM04 D]
  calc
    _ ≤ ∑ i, |∑ j, D.covariantTensorDerivative D.riemannEvaluation p
        ![X, b i, b j, b i, b j]| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |D.covariantTensorDerivative D.riemannEvaluation p
        ![X, b i, b j, b i, b j]| :=
      Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) p)),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) p)),
          D.curvatureDerivativeNorm 1 p * g.tangentNorm p X :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hterm i j
    _ = _ := by simp [hdim, pow_two, mul_assoc]

end PoincareConjecture.Proofs.M09
