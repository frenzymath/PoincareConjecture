import PoincareConjecture.Statements.M47ComponentAnalytics
import PoincareConjecture.Proofs.M09.ScalarDifferentialBound
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Matrix.Bounds
import PoincareConjecture.Proofs.M04.TensorNorm
import PoincareConjecture.Proofs.M45.Ch9_Models.LocalScalar
import PoincareConjecture.Proofs.M35.RawFlow.MetricSpace










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M47

private theorem tangentNorm_orthonormal
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (x : M)
    (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
    g.tangentNorm x (g.orthonormalBasis x i) = 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Real.sqrt (inner ℝ (g.orthonormalBasis x i) (g.orthonormalBasis x i)) = 1
  rw [real_inner_self_eq_norm_sq, (g.orthonormalBasis x).norm_eq_one]
  norm_num



theorem component_ricciNormSq_le_curvatureTensorNorm
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) :
    D.ricciNormSq x ≤ 81 * (D.curvatureTensorNorm x) ^ 2 := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := finrank_euclideanSpace_fin
  have hb (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      (D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2 ≤
        (3 * D.curvatureTensorNorm x) ^ 2 := by
    have h := D.abs_ricci_le_curvatureDerivativeNorm_zero hD x
      (g.orthonormalBasis x i) (g.orthonormalBasis x j)
    simp only [Nat.cast_ofNat, tangentNorm_orthonormal, mul_one,
      LeviCivitaData.curvatureDerivativeNorm_zero] at h
    exact (sq_abs _).symm.trans_le ((sq_le_sq₀ (abs_nonneg _) (by
      have hnonneg : 0 ≤ D.curvatureTensorNorm x := Real.sqrt_nonneg _
      positivity)).mpr h)
  calc
    D.ricciNormSq x ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
          (3 * D.curvatureTensorNorm x) ^ 2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim, nsmul_eq_mul]
      ring




theorem exists_component_normalized_endpoint_constant
    (hC : RicciFlowCurvatureTheory.{u}) (PA : M47ComponentAnalyticPredecessors.{u})
    (T K : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hK : 0 < K) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [T2Space M] [SecondCountableTopology M] [CompactSpace M],
      ∀ F : RicciFlow 3 M (Icc 0 T),
        (∀ t ∈ Icc 0 T, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K) →
        ∀ x : M, scalarGradientNorm (F.metric T) (F.connection T) x ≤ A ∧
          |(F.connection T).laplacian (F.connection T).scalarCurvature x +
            2 * (F.connection T).ricciNormSq x| ≤ A := by
  obtain ⟨B1, hB1, hone⟩ := PA.local_derivative_estimates 1 K K 1 hK hK zero_lt_one
  obtain ⟨B2, hB2, htwo⟩ := PA.local_derivative_estimates 2 K K 1 hK hK zero_lt_one
  let A1 := B1 / T ^ (1 / 2 : ℝ)
  let A2 := B2 / T
  have hA1 : 0 < A1 := div_pos hB1 (Real.rpow_pos_of_pos hT _)
  have hA2 : 0 < A2 := div_pos hB2 hT
  refine ⟨9 * A1 + 27 * A2 + 162 * K ^ 2 + 1, by positivity, ?_⟩
  intro M _ _ _ _ _ _ F hcurvature x
  have htime : T ≤ K / K := by simpa only [div_self hK.ne'] using hT1
  have hcompact : IsCompact (closure ((F.metric 0).ball x 1)) := isClosed_closure.isCompact
  have hball : x ∈ (F.metric 0).ball x (1 / 2) := by
    change (F.metric 0).edist x x < ENNReal.ofReal (1 / 2)
    rw [← RiemannianMetric.toEMetricSpace_edist]
    have hz := @edist_self M (F.metric 0).toEMetricSpace.toPseudoEMetricSpace x
    rw [hz]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have h1 : (F.connection T).curvatureDerivativeNorm 1 x ≤ A1 := by
    simpa only [Nat.cast_one] using hone M T hT htime F x hcompact
      (fun t ht y _hy => hcurvature t ht y) T ⟨hT, le_rfl⟩ x hball
  have h2 : (F.connection T).curvatureDerivativeNorm 2 x ≤ A2 := by
    simpa only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one] using
      htwo M T hT htime F x hcompact (fun t ht y _hy => hcurvature t ht y)
        T ⟨hT, le_rfl⟩ x hball
  have hD := PA.tensor_calculus M (F.metric T) (F.connection T)
  constructor
  · apply M45.model_scalarGradientNorm_le
    intro v hv
    have h := Proofs.M09.scalarCurvature_mvfderiv_abs_le hC (F.metric T) (F.connection T) x v
    have hnorm : (F.metric T).tangentNorm x v = 1 := by
      change Real.sqrt _ = 1
      rw [hv, Real.sqrt_one]
    norm_num only [Nat.cast_ofNat, pow_succ, pow_zero, mul_one, hnorm] at h
    nlinarith [sq_nonneg K]
  · have hlap := (F.connection T).abs_laplacian_scalar_le_curvatureDerivativeNorm hD x
    have hric := component_ricciNormSq_le_curvatureTensorNorm (F.connection T) hD x
    have hric0 : 0 ≤ (F.connection T).ricciNormSq x :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hnorm0 : 0 ≤ (F.connection T).curvatureTensorNorm x := Real.sqrt_nonneg _
    have hsquare := (sq_le_sq₀ hnorm0 hK.le).mpr (hcurvature T ⟨hT.le, le_rfl⟩ x)
    have hsum := abs_add_le ((F.connection T).laplacian (F.connection T).scalarCurvature x)
      (2 * (F.connection T).ricciNormSq x)
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hric0)] at hsum
    norm_num only [Nat.cast_ofNat, pow_succ, pow_zero] at hlap
    nlinarith

end PoincareConjecture.M47
