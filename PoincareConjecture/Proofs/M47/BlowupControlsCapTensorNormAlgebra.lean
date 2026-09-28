import PoincareConjecture.Proofs.M47.BlowupControlsCapInverseMetric
import Mathlib.Analysis.InnerProductSpace.PiL2











set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

section Arrays

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem cap_array_norm_sq (T : ι → ℝ) :
    ‖(WithLp.toLp 2 T : EuclideanSpace ℝ ι)‖ ^ 2 = ∑ i, T i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]

theorem cap_array_norm_reindex (e : ι ≃ κ) (T : κ → ℝ) :
    ‖(WithLp.toLp 2 (fun i => T (e i)) : EuclideanSpace ℝ ι)‖ =
      ‖(WithLp.toLp 2 T : EuclideanSpace ℝ κ)‖ := by
  have hs := e.sum_comp (fun i => T i ^ 2)
  have hnorm : ‖(WithLp.toLp 2 (fun i => T (e i)) : EuclideanSpace ℝ ι)‖ ^ 2 =
      ‖(WithLp.toLp 2 T : EuclideanSpace ℝ κ)‖ ^ 2 := by
    simpa only [cap_array_norm_sq] using hs
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnorm

theorem cap_array_product_norm (T : ι → ℝ) (S : κ → ℝ) :
    ‖(WithLp.toLp 2 (fun p : ι × κ => T p.1 * S p.2) : EuclideanSpace ℝ (ι × κ))‖ =
      ‖(WithLp.toLp 2 T : EuclideanSpace ℝ ι)‖ *
        ‖(WithLp.toLp 2 S : EuclideanSpace ℝ κ)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  simp only [mul_pow, cap_array_norm_sq, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]

end Arrays

local notation "E₃" => EuclideanSpace ℝ (Fin 3)



noncomputable def capOperatorComponents (L : E₃ →L[ℝ] E₃) :
    EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  WithLp.toLp 2 (fun p => inner ℝ (EuclideanSpace.basisFun (Fin 3) ℝ p.1)
    (L (EuclideanSpace.basisFun (Fin 3) ℝ p.2)))

theorem cap_operatorComponents_norm_sq (L : E₃ →L[ℝ] E₃) :
    ‖capOperatorComponents L‖ ^ 2 =
      ∑ j : Fin 3, ‖L (EuclideanSpace.basisFun (Fin 3) ℝ j)‖ ^ 2 := by
  rw [capOperatorComponents, cap_array_norm_sq, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Real.norm_eq_abs, sq_abs] using
    (EuclideanSpace.basisFun (Fin 3) ℝ).sum_sq_norm_inner_right
      (L (EuclideanSpace.basisFun (Fin 3) ℝ j))

theorem cap_operatorComponents_identity_norm :
    ‖capOperatorComponents (ContinuousLinearMap.id ℝ E₃)‖ = Real.sqrt 3 := by
  have hs : ‖capOperatorComponents (ContinuousLinearMap.id ℝ E₃)‖ ^ 2 = 3 := by
    rw [cap_operatorComponents_norm_sq]
    simp only [ContinuousLinearMap.id_apply,
      (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.norm_eq_one,
      one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]



theorem cap_operatorComponents_norm_le (L : E₃ →L[ℝ] E₃) :
    ‖capOperatorComponents L‖ ≤ Real.sqrt 3 * ‖L‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [cap_operatorComponents_norm_sq, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  calc
    _ ≤ ∑ _j : Fin 3, ‖L‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := L.le_opNorm (EuclideanSpace.basisFun (Fin 3) ℝ j)
      rw [(EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.norm_eq_one, mul_one] at h
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
    _ = _ := by simp



theorem cap_operatorComponents_comp_norm_le (L K : E₃ →L[ℝ] E₃) :
    ‖capOperatorComponents (L.comp K)‖ ≤ ‖L‖ * ‖capOperatorComponents K‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, cap_operatorComponents_norm_sq, cap_operatorComponents_norm_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  change ‖L (K (EuclideanSpace.basisFun (Fin 3) ℝ j))‖ ^ 2 ≤ _
  have h := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg L) (norm_nonneg _))).mpr
      (L.le_opNorm (K (EuclideanSpace.basisFun (Fin 3) ℝ j)))
  simpa only [mul_pow] using h

theorem cap_operatorComponents_neg (L : E₃ →L[ℝ] E₃) :
    capOperatorComponents (-L) = -capOperatorComponents L := by
  ext p
  simp only [capOperatorComponents, WithLp.ofLp_toLp, neg_apply,
    inner_neg_right, PiLp.neg_apply]



theorem cap_frameInverseGram_component_error_le
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (x : M)
    (e : E₃ ≃L[ℝ] TangentSpace (𝓡 3) x) :
    let A := M04.frameGramOperator g x e.toContinuousLinearMap
    ‖capOperatorComponents (A.inverse - ContinuousLinearMap.id ℝ E₃)‖ ≤
      ‖A.inverse‖ * ‖capOperatorComponents (A - ContinuousLinearMap.id ℝ E₃)‖ := by
  dsimp only
  rw [cap_frameInverseGram_sub_identity, cap_operatorComponents_neg, norm_neg]
  exact cap_operatorComponents_comp_norm_le _ _

end PoincareConjecture.M47
