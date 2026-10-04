import PoincareLib.Geometry.RicciFlow.Curvature.Estimates.QuadraticRicci
import PoincareLib.Geometry.RicciFlow.Curvature.Calculus.Identities.ScalarContractions

/-! Adapted from Mapher `PoincareMT/Proofs/M15/Prop8_2_CurvatureContractions.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

/-!
# Scalar contractions for the local curvature estimates

Morgan-Tian Claim 8.5, p. 172, and the scalar lower bound before (8.2),
p. 174. The full curvature tensor and its first covariant derivative bound
the scalar curvature and its differential, with a dimension-only factor.
See `references/ricci-flow/mapher/noncollapse/derivations/2026-09-20-curvature-contractions.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.Generalized.Noncollapse

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The full curvature norm controls the scalar term in Lemma 8.3,
p. 174, with a safe dimension-only constant valid also in dimension zero. -/
theorem abs_scalarCurvature_le_curvatureTensorNorm
    (D : LeviCivitaData g) (x : M) :
    |D.scalarCurvature x| ≤ (n : ℝ) ^ 2 * D.curvatureTensorNorm x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hb (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      g.inner x (b i) (b i) = 1 := by
    change inner ℝ (b i) (b i) = 1
    simp only [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow]
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  calc
    |D.scalarCurvature x| ≤ ∑ i, |D.ricci x (b i) (b i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (n : ℝ) * D.curvatureTensorNorm x := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [hb, mul_one] using RicciFlowAnalysis.abs_ricci_le_curvatureTensorNorm D x (b i)
    _ = _ := by simp [hdim, pow_two, mul_assoc]

/-- Contracting the first curvature derivative gives the scalar gradient
estimate used in Claim 8.5, p. 172. All norms use the specified metric. -/
theorem abs_scalarCurvature_derivative_le_curvatureDerivativeNorm
    (D : LeviCivitaData g) (x : M) (v : TangentSpace (𝓡 n) x) :
    |mvfderiv (𝓡 n) D.scalarCurvature x v| ≤
      (n : ℝ) ^ 2 * D.curvatureDerivativeNorm 1 x * g.tangentNorm x v := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hb (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      g.inner x (b i) (b i) = 1 := by
    change inner ℝ (b i) (b i) = 1
    simp only [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow]
  have hNorm : g.tensorNorm (D.covariantTensorDerivative D.riemannEvaluation) x =
      D.curvatureDerivativeNorm 1 x := rfl
  have hN : 0 ≤ D.curvatureDerivativeNorm 1 x := Real.sqrt_nonneg _
  have hV : 0 ≤ g.inner x v v := real_inner_self_nonneg (x := v)
  have hVsq : (g.tangentNorm x v) ^ 2 = g.inner x v v := Real.sq_sqrt hV
  have hNV : 0 ≤ D.curvatureDerivativeNorm 1 x * g.tangentNorm x v :=
    mul_nonneg hN (Real.sqrt_nonneg _)
  have hTerm (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      |D.covariantTensorDerivative D.riemannEvaluation x ![v, b i, b j, b i, b j]| ≤
        D.curvatureDerivativeNorm 1 x * g.tangentNorm x v := by
    have h := RicciFlowAnalysis.tensorEvaluation_sq_le_tensorNorm g
      (RicciFlowAnalysis.isSmoothCovariantTensor_covariantTensorDerivative D
        (RicciFlowAnalysis.isSmoothCovariantTensor_riemannEvaluation D)) x ![v, b i, b j, b i, b j]
    change D.covariantTensorDerivative D.riemannEvaluation x
        ![v, b i, b j, b i, b j] ^ 2 ≤
      g.tensorNorm (D.covariantTensorDerivative D.riemannEvaluation) x ^ 2 *
        ∏ k : Fin 5, g.inner x (![v, b i, b j, b i, b j] k)
          (![v, b i, b j, b i, b j] k) at h
    have hprod : (∏ k : Fin 5, g.inner x (![v, b i, b j, b i, b j] k)
        (![v, b i, b j, b i, b j] k)) = g.inner x v v := by
      simp [Fin.prod_univ_five, hb]
    rw [hNorm, hprod] at h
    have hAbs :
        |D.covariantTensorDerivative D.riemannEvaluation x ![v, b i, b j, b i, b j]| ^ 2 ≤
          (D.curvatureDerivativeNorm 1 x * g.tangentNorm x v) ^ 2 := by
      rw [sq_abs, mul_pow, hVsq]
      exact h
    nlinarith only [hAbs, hNV,
      abs_nonneg (D.covariantTensorDerivative D.riemannEvaluation x
        ![v, b i, b j, b i, b j])]
  have htrace : mvfderiv (𝓡 n) D.scalarCurvature x v =
      ∑ i, ∑ j, D.covariantTensorDerivative D.riemannEvaluation x
        ![v, b i, b j, b i, b j] := by
    rw [← RicciFlowAnalysis.ricci_covariantDerivative_metric_trace D x v]
    exact Finset.sum_congr rfl fun i _ ↦
      RicciFlowAnalysis.ricci_covariantDerivative_curvature_trace D x v (b i) (b i)
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  rw [htrace]
  calc
    _ ≤ ∑ i, |∑ j, D.covariantTensorDerivative D.riemannEvaluation x
        ![v, b i, b j, b i, b j]| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |D.covariantTensorDerivative D.riemannEvaluation x
        ![v, b i, b j, b i, b j]| :=
      Finset.sum_le_sum fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          D.curvatureDerivativeNorm 1 x * g.tangentNorm x v :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hTerm i j
    _ = _ := by simp [hdim, pow_two, mul_assoc]

end PoincareMT.Generalized.Noncollapse
