import PoincareConjecture.Proofs.M76.Mathlib.EuclideanPlaneTopology
import Mathlib.Analysis.Convex.Contractible










set_option autoImplicit false

namespace Submodule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]




noncomputable def operatorOrthogonalSplitHomeomorph (V : Submodule ℝ E) :
    (E →L[ℝ] F) ≃ₜ ((V →L[ℝ] F) × (Vᗮ →L[ℝ] F)) where
  toFun Q := (Q.comp V.subtypeL, Q.comp Vᗮ.subtypeL)
  invFun R := R.1.comp V.orthogonalProjectionOnto + R.2.comp Vᗮ.orthogonalProjectionOnto
  left_inv Q := by
    apply ContinuousLinearMap.ext
    intro x
    change Q (V.starProjection x) + Q (Vᗮ.starProjection x) = Q x
    rw [← map_add, V.starProjection_add_starProjection_orthogonal x]
  right_inv R := by
    apply Prod.ext
    · apply ContinuousLinearMap.ext
      intro x
      change R.1 (V.orthogonalProjectionOnto (x : E)) +
        R.2 (Vᗮ.orthogonalProjectionOnto (x : E)) = R.1 x
      rw [V.orthogonalProjectionOnto_mem_subspace_eq_self,
        V.orthogonalProjectionOnto_orthogonal_apply_eq_zero x.property, map_zero, add_zero]
    · apply ContinuousLinearMap.ext
      intro x
      change R.1 (V.orthogonalProjectionOnto (x : E)) +
        R.2 (Vᗮ.orthogonalProjectionOnto (x : E)) = R.2 x
      rw [V.orthogonalProjectionOnto_apply_of_mem_orthogonal x.property,
        Vᗮ.orthogonalProjectionOnto_mem_subspace_eq_self, map_zero, zero_add]
  continuous_toFun := (continuous_id.clm_comp continuous_const).prodMk
    (continuous_id.clm_comp continuous_const)
  continuous_invFun := (continuous_fst.clm_comp continuous_const).add
    (continuous_snd.clm_comp continuous_const)




noncomputable def operatorRestrictionHomeomorph (V : Submodule ℝ E)
    (p : (V →L[ℝ] F) → Prop) :
    {Q : E →L[ℝ] F // p (Q.comp V.subtypeL)} ≃ₜ
      ({R : V →L[ℝ] F // p R} × (Vᗮ →L[ℝ] F)) := by
  let e : (E →L[ℝ] F) ≃ₜ ((V →L[ℝ] F) × (Vᗮ →L[ℝ] F)) :=
    V.operatorOrthogonalSplitHomeomorph
  refine
    { toFun := fun Q => (⟨(e Q.val).1, Q.property⟩, (e Q.val).2)
      invFun := fun R => ⟨e.symm (R.1.val, R.2), ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · change p ((e (e.symm (R.1.val, R.2))).1)
    rw [e.apply_symm_apply]
    exact R.1.property
  · intro Q
    apply Subtype.ext
    exact e.symm_apply_apply Q.val
  · intro R
    apply Prod.ext
    · apply Subtype.ext
      change (e (e.symm (R.1.val, R.2))).1 = R.1.val
      exact congrArg Prod.fst (e.apply_symm_apply (R.1.val, R.2))
    · change (e (e.symm (R.1.val, R.2))).2 = R.2
      exact congrArg Prod.snd (e.apply_symm_apply (R.1.val, R.2))
  · exact ((e.continuous.comp continuous_subtype_val).fst.subtype_mk (fun _ => _)).prodMk
      (e.continuous.comp continuous_subtype_val).snd
  · exact (e.symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk (fun _ => _)




theorem contractible_operatorRestriction (V : Submodule ℝ E)
    (p : (V →L[ℝ] F) → Prop) [ContractibleSpace {R : V →L[ℝ] F // p R}] :
    ContractibleSpace {Q : E →L[ℝ] F // p (Q.comp V.subtypeL)} :=
  (V.operatorRestrictionHomeomorph p).contractibleSpace

end Submodule
