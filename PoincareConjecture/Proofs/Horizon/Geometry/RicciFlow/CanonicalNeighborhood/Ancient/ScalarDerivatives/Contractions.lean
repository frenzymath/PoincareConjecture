import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Bounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.ScalarDerivatives

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem scalarGradientNorm_le_curvatureDerivativeNorm
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) :
    scalarGradientNorm g D x ≤ 9 * D.curvatureDerivativeNorm 1 x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 :=
    finrank_euclideanSpace_fin
  have hb (i) : g.tangentNorm x (b i) = 1 := by
    change Real.sqrt (inner ℝ (b i) (b i)) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one]
    norm_num
  have hn : Nonempty {v : TangentSpace (𝓡 3) x // g.inner x v v = 1} := by
    let i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)) := ⟨0, by omega⟩
    refine ⟨b i, ?_⟩
    change inner ℝ (b i) (b i) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one]
    norm_num
  unfold scalarGradientNorm
  apply csSup_le (Set.range_nonempty (f := fun v :
    {v : TangentSpace (𝓡 3) x // g.inner x v v = 1} =>
      |mvfderiv (𝓡 3) D.scalarCurvature x v.1|))
  rintro _ ⟨v, rfl⟩
  have hv : g.tangentNorm x v.1 = 1 := by
    simp only [RiemannianMetric.tangentNorm, v.2, Real.sqrt_one]
  change |mvfderiv (𝓡 3) D.scalarCurvature x v.1| ≤ _
  rw [← D.sum_covariantTensorDerivative_ricci_eq_scalar_derivative hD x v.1]
  calc
    _ ≤ ∑ i, |D.covariantTensorDerivative D.ricciEvaluation x ![v.1, b i, b i]| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
        3 * D.curvatureDerivativeNorm 1 x := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [hb, hv, mul_one, Nat.cast_ofNat] using
        D.abs_covariantTensorDerivative_ricci_le_curvatureDerivativeNorm hD x v.1 (b i) (b i)
    _ = _ := by simp [hdim]; ring

end PoincareConjecture.ScalarDerivatives
