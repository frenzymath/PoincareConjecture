import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.TangentCylinderProjection
import Mathlib.Analysis.Convex.Contractible

/-!
# Projection spaces of tangent cylinders

Normalized projections embedding a full cylinder split into normal
embeddings and a linear space of tangent shears vanishing on the
frame. This gives the operator-space part of Cairns' face-star
reduction, Section 4, pp. 800--801; see M76 derivation 33.
-/

set_option autoImplicit false

open Set

namespace ContinuousLinearMap

variable {E F T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- Normalized operators embedding a prescribed source set.
See Cairns pp. 800--801 and M76 derivation 33. -/
abbrev FrameEmbeddingSpace (J : F →L[ℝ] E) (S : Set E) :=
  {B : E →L[ℝ] F // Function.RightInverse J B ∧ InjOn B S}

/-- Normalized operators embedding the entire tangent cylinder.
See Cairns pp. 800--801 and M76 derivation 33. -/
abbrev TangentCylinderEmbeddingSpace (J : F →L[ℝ] E) (S : Set E)
    (T : Type*) [NormedAddCommGroup T] [NormedSpace ℝ T] :=
  {Q : (E × T) →L[ℝ] (F × T) //
    Function.RightInverse (J.prodMap (ContinuousLinearMap.id ℝ T)) Q ∧
      InjOn Q (S ×ˢ (univ : Set T))}

/-- Tangent shear operators vanishing on the specified normal frame.
See Cairns pp. 800--801 and M76 derivation 33. -/
noncomputable def frameShears (J : F →L[ℝ] E)
    (T : Type*) [NormedAddCommGroup T] [NormedSpace ℝ T] :
    Submodule ℝ (E →L[ℝ] T) :=
  (J.precomp T : (E →L[ℝ] T) →L[ℝ] (F →L[ℝ] T)).ker

/-- Extract the normal operator and the tangent shear; the latter
vanishes on the fixed frame.
See Cairns pp. 800--801 and M76 derivation 33. -/
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

/-- The two operator factors reconstruct a normalized cylinder
embedding. See Cairns pp. 800--801 and M76 derivation 33. -/
def assembleTangentCylinder (J : F →L[ℝ] E) (S : Set E)
    (R : FrameEmbeddingSpace J S × J.frameShears T) :
    TangentCylinderEmbeddingSpace J S T :=
  ⟨tangentCylinderProjection R.1.val R.2.val,
    (rightInverse_tangentCylinderProjection_iff J R.1.val R.2.val).mpr
      ⟨R.1.property.1, R.2.property⟩,
    (injOn_tangentCylinderProjection_iff R.1.val R.2.val S).mpr R.1.property.2⟩

/-- The cylinder projection space is a product of its normal
projection space and the vector space of frame-vanishing shears.
See Cairns Section 4, pp. 800--801, and M76 derivation 33. -/
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

/-- A contractible normal projection space stays contractible after
adding tangent directions fixed by the frame normalization.
See Cairns Section 4, pp. 800--801, and M76 derivation 33. -/
theorem contractible_tangentCylinderEmbeddingSpace (J : F →L[ℝ] E) (S : Set E)
    [ContractibleSpace (FrameEmbeddingSpace J S)] :
    ContractibleSpace (TangentCylinderEmbeddingSpace J S T) :=
  (tangentCylinderSpaceHomeomorph J S).contractibleSpace

end ContinuousLinearMap
