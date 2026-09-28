import PoincareConjecture.Proofs.M76.Mathlib.TangentCylinderProjection
import Mathlib.Analysis.Convex.Contractible










set_option autoImplicit false

open Set

namespace ContinuousLinearMap

variable {E F T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup T] [NormedSpace ℝ T]



abbrev FrameEmbeddingSpace (J : F →L[ℝ] E) (S : Set E) :=
  {B : E →L[ℝ] F // Function.RightInverse J B ∧ InjOn B S}



abbrev TangentCylinderEmbeddingSpace (J : F →L[ℝ] E) (S : Set E)
    (T : Type*) [NormedAddCommGroup T] [NormedSpace ℝ T] :=
  {Q : (E × T) →L[ℝ] (F × T) //
    Function.RightInverse (J.prodMap (ContinuousLinearMap.id ℝ T)) Q ∧
      InjOn Q (S ×ˢ (univ : Set T))}



noncomputable def frameShears (J : F →L[ℝ] E)
    (T : Type*) [NormedAddCommGroup T] [NormedSpace ℝ T] :
    Submodule ℝ (E →L[ℝ] T) :=
  (J.precomp T : (E →L[ℝ] T) →L[ℝ] (F →L[ℝ] T)).ker




def tangentCylinderBlocks (J : F →L[ℝ] E) (S : Set E)
    (Q : TangentCylinderEmbeddingSpace J S T) :
    FrameEmbeddingSpace J S × J.frameShears T := by
  let B := (fst ℝ F T).comp (Q.val.comp (inl ℝ E T))
  let A := (snd ℝ F T).comp (Q.val.comp (inl ℝ E T))
  have hform : Q.val = tangentCylinderProjection B A :=
    Q.val.eq_tangentCylinderProjection_of_fixed_tangent
      (fixed_tangent_of_rightInverse_productFrame J Q.val Q.property.1)
  have hnorm := (rightInverse_tangentCylinderProjection_iff J B A).mp
    (hform ▸ Q.property.1)
  have hinj := (injOn_tangentCylinderProjection_iff B A S).mp (hform ▸ Q.property.2)
  exact (⟨B, hnorm.1, hinj⟩, ⟨A, hnorm.2⟩)



def assembleTangentCylinder (J : F →L[ℝ] E) (S : Set E)
    (R : FrameEmbeddingSpace J S × J.frameShears T) :
    TangentCylinderEmbeddingSpace J S T :=
  ⟨tangentCylinderProjection R.1.val R.2.val,
    (rightInverse_tangentCylinderProjection_iff J R.1.val R.2.val).mpr
      ⟨R.1.property.1, R.2.property⟩,
    (injOn_tangentCylinderProjection_iff R.1.val R.2.val S).mpr R.1.property.2⟩




noncomputable def tangentCylinderSpaceHomeomorph (J : F →L[ℝ] E) (S : Set E) :
    TangentCylinderEmbeddingSpace J S T ≃ₜ
      (FrameEmbeddingSpace J S × J.frameShears T) where
  toFun := tangentCylinderBlocks J S
  invFun := assembleTangentCylinder J S
  left_inv Q := by
    apply Subtype.ext
    exact (Q.val.eq_tangentCylinderProjection_of_fixed_tangent
      (fixed_tangent_of_rightInverse_productFrame J Q.val Q.property.1)).symm
  right_inv R := by
    apply Prod.ext
    · apply Subtype.ext
      apply ContinuousLinearMap.ext
      intro x
      rfl
    · apply Subtype.ext
      apply ContinuousLinearMap.ext
      intro x
      change (0 : T) + R.2.val x = R.2.val x
      exact zero_add _
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (continuous_const.clm_comp
        (continuous_subtype_val.clm_comp continuous_const)).subtype_mk (fun _ => _)
    · exact (continuous_const.clm_comp
        (continuous_subtype_val.clm_comp continuous_const)).subtype_mk (fun _ => _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (fun R : FrameEmbeddingSpace J S × J.frameShears T =>
      tangentCylinderProjection R.1.val R.2.val)
    exact (prodL ℝ).continuous.comp
      (((continuous_subtype_val.comp continuous_fst).clm_comp continuous_const).prodMk
        (continuous_const.add
          ((continuous_subtype_val.comp continuous_snd).clm_comp continuous_const)))




theorem contractible_tangentCylinderEmbeddingSpace (J : F →L[ℝ] E) (S : Set E)
    [ContractibleSpace (FrameEmbeddingSpace J S)] :
    ContractibleSpace (TangentCylinderEmbeddingSpace J S T) :=
  (tangentCylinderSpaceHomeomorph J S).contractibleSpace

end ContinuousLinearMap
