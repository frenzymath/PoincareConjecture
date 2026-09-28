import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Bilinear










set_option autoImplicit false

namespace PoincareConjecture.M63





theorem exists_dense_bilinear_extension
    {K E F G : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace K E] [NormedSpace K F] [NormedSpace K G] [CompleteSpace G]
    (S : Submodule K E) (T : Submodule K F)
    (hS : Dense (S : Set E)) (hT : Dense (T : Set F))
    (B : S →L[K] T →L[K] G) :
    ∃ Bfull : E →L[K] F →L[K] G,
      (∀ (u : S) (v : T), Bfull u v = B u v) ∧ ‖Bfull‖ ≤ ‖B‖ := by
  have hTd : DenseRange T.subtypeL := hT.denseRange_val
  have hSd : DenseRange S.subtypeL := hS.denseRange_val
  have hTu : IsUniformInducing T.subtypeL :=
    isUniformEmbedding_subtype_val.isUniformInducing
  have hSu : IsUniformInducing S.subtypeL :=
    isUniformEmbedding_subtype_val.isUniformInducing
  have hTn (x : T) : ‖x‖ ≤ ((1 : NNReal) : ℝ) * ‖T.subtypeL x‖ := by
    simp only [NNReal.coe_one, one_mul]
    exact le_rfl
  have hSextend (C : S →L[K] F →L[K] G) : ‖C.extend S.subtypeL‖ ≤ ‖C‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg C)
    intro x
    refine hSd.induction_on x ?_ ?_
    · exact isClosed_le (C.extend S.subtypeL).continuous.norm
        (continuous_const.mul continuous_norm)
    · intro u
      rw [C.extend_eq hSd hSu]
      exact C.le_opNorm u
  let A₀ : (T →L[K] G) →ₗ[K] (F →L[K] G) :=
    { toFun := fun f => f.extend T.subtypeL
      map_add' := by
        intro f g
        apply ContinuousLinearMap.extend_unique _ hTd hTu
        ext x
        simp only [ContinuousLinearMap.comp_apply, add_apply,
          ContinuousLinearMap.extend_eq _ hTd hTu]
      map_smul' := by
        intro c f
        apply ContinuousLinearMap.extend_unique _ hTd hTu
        ext x
        simp only [ContinuousLinearMap.comp_apply, smul_apply,
          ContinuousLinearMap.extend_eq _ hTd hTu, RingHom.id_apply] }
  have hA (f : T →L[K] G) : ‖A₀ f‖ ≤ 1 * ‖f‖ := by
    exact f.opNorm_extend_le (N := 1) (e := T.subtypeL) hTd hTn
  let A : (T →L[K] G) →L[K] (F →L[K] G) := A₀.mkContinuous 1 hA
  have hAnorm : ‖A‖ ≤ 1 := A₀.mkContinuous_norm_le zero_le_one hA
  let Bfull : E →L[K] F →L[K] G := (A.comp B).extend S.subtypeL
  refine ⟨Bfull, ?_, ?_⟩
  · intro u v
    change ((A.comp B).extend S.subtypeL (S.subtypeL u)) v = _
    rw [ContinuousLinearMap.extend_eq _ hSd hSu]
    exact (B u).extend_eq hTd hTu v
  · have he : ‖Bfull‖ ≤ ‖A.comp B‖ := hSextend (A.comp B)
    calc
      ‖Bfull‖ ≤ ‖A.comp B‖ := he
      _ ≤ ‖A‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖B‖ := mul_le_mul_of_nonneg_right hAnorm (norm_nonneg B)
      _ = ‖B‖ := one_mul _

end PoincareConjecture.M63
