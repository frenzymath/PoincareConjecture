import PoincareConjecture.Proofs.M04.FlowCurvatureEnergy
import PoincareConjecture.Proofs.M09.TensorEvaluationBound
import PoincareConjecture.Statements.M62CurveEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem exists_uniform_tensor_bound
    (F : RicciFlow n M (Set.Icc a b)) (hcompact : IsCompact (Set.univ : Set M))
    {k : ℕ} (T : ℝ → CovariantTensorEvaluation n M k)
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hTime : ∀ U : Set M, IsOpen U →
      ∀ X : Fin k → (y : M) → TangentSpace (𝓡 n) y,
        (∀ i, ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞ (T% (X i)) U) →
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => T p.1 p.2 (fun i => X i p.2)) (Set.Icc a b ×ˢ U)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc a b, ∀ x : M,
      ∀ v : Fin k → TangentSpace (𝓡 n) x,
        (∀ i, (F.metric t).tangentNorm x (v i) ≤ 1) → |T t x v| ≤ K := by
  have hnonneg (p : ℝ × M) : 0 ≤ (F.metric p.1).tensorNorm (T p.1) p.2 :=
    Real.sqrt_nonneg _
  have hsqrt (p : ℝ × M) :
      Real.sqrt (((F.metric p.1).tensorNorm (T p.1) p.2) ^ 2) =
        (F.metric p.1).tensorNorm (T p.1) p.2 := Real.sqrt_sq (hnonneg p)
  have hcontinuous : ContinuousOn
      (fun p : ℝ × M => (F.metric p.1).tensorNorm (T p.1) p.2) (Icc a b ×ˢ univ) := by
    simpa only [hsqrt] using
      (M04.contMDiffOn_flow_tensorNorm_sq F T hT hTime).continuousOn.sqrt
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hcompact).exists_bound_of_continuousOn hcontinuous
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x v hv
  have hnorm : (F.metric t).tensorNorm (T t) x ≤ C := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg (t, x))] using
      hC (t, x) ⟨ht, mem_univ x⟩
  have hprod : (∏ i, (F.metric t).tangentNorm x (v i)) ≤ 1 :=
    Finset.prod_le_one (fun i _ => Real.sqrt_nonneg _) (fun i _ => hv i)
  calc
    |T t x v| ≤ (F.metric t).tensorNorm (T t) x *
        ∏ i, (F.metric t).tangentNorm x (v i) :=
      PoincareConjecture.Proofs.M09.tensor_abs_le_tensorNorm (F.metric t) (T t) (hT t) x v
    _ ≤ (F.metric t).tensorNorm (T t) x * 1 :=
      mul_le_mul_of_nonneg_left hprod (hnonneg (t, x))
    _ ≤ max C 0 := by simpa only [mul_one] using hnorm.trans (le_max_left C 0)

theorem exists_ambient_bounds
    (F : RicciFlow n M (Set.Icc a b)) (hcompact : IsCompact (Set.univ : Set M)) :
    ∃ K0 K1 K2 : ℝ, (0 ≤ K0 ∧ 0 ≤ K1 ∧ 0 ≤ K2) ∧
      CurveEvolutionAmbientBounds F K0 K1 K2 := by
  obtain ⟨K0, hK0, h0⟩ := exists_uniform_tensor_bound F hcompact
    (fun t => (F.connection t).riemannEvaluation)
    (fun t => M04.isSmoothCovariantTensor_riemannEvaluation (F.connection t))
    (fun U hU X hX => M04.contMDiffOn_flow_riemannEvaluation F hU X hX)
  obtain ⟨K1, hK1, h1⟩ := exists_uniform_tensor_bound F hcompact
    (fun t => (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation)
    (fun t => M04.isSmoothCovariantTensor_covariantTensorDerivative (F.connection t)
      (M04.isSmoothCovariantTensor_ricciEvaluation (F.connection t)))
    (fun U hU X hX => M04.contMDiffOn_flow_covariantTensorDerivative F
      (fun t => M04.isSmoothCovariantTensor_ricciEvaluation (F.connection t))
      (fun V hV Y hY => M04.contMDiffOn_flow_ricciEvaluation F hV hY) hU hX)
  obtain ⟨K2, hK2, h2⟩ := exists_uniform_tensor_bound F hcompact
    (fun t => (F.connection t).ricciEvaluation)
    (fun t => M04.isSmoothCovariantTensor_ricciEvaluation (F.connection t))
    (fun U hU X hX => M04.contMDiffOn_flow_ricciEvaluation F hU hX)
  refine ⟨K0, K1, K2, ⟨hK0, hK1, hK2⟩, ?_⟩
  refine ⟨h0, h1, ?_⟩
  intro t ht x v w hv hw
  apply h2 t ht x ![v, w]
  intro i
  fin_cases i
  · exact hv
  · exact hw

end PoincareConjecture.M62
