import PoincareConjecture.Proofs.M76.Mathlib.FramePlaneCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.TransversePlaneDimension

set_option autoImplicit false

open Set Geometry

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

noncomputable def frameTransversePlaneHomeomorph (J : F →L[ℝ] E)
    (hJ : Function.Injective J) (A : Set E) :
    J.range.TransverseComplementPlaneSpace A ≃ₜ
      {Q : E →L[ℝ] F // Function.RightInverse J Q ∧ Q.ker.IsSecantTransverse A} := by
  let e : {Q : J.FrameProjectionSpace // Q.val.ker.IsSecantTransverse A} ≃ₜ
      {Q : E →L[ℝ] F // Function.RightInverse J Q ∧ Q.ker.IsSecantTransverse A} := {
    toFun := fun Q => ⟨Q.val.val, Q.val.property, Q.property⟩
    invFun := fun Q => ⟨⟨Q.val, Q.property.1⟩, Q.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := continuous_subtype_val.subtype_mk _ |>.subtype_mk _ }
  refine ((J.frameComplementPlaneHomeomorph hJ).subtype ?_).trans e
  intro P
  rw [J.ker_frameComplementPlaneHomeomorph hJ]

theorem contractible_frameTransverseSpace_of_planes (J : F →L[ℝ] E)
    (hJ : Function.Injective J) (A : Set E)
    (hdisjoint : ∀ P : Submodule ℝ E, P.IsSecantTransverse A → Disjoint J.range P)
    [ContractibleSpace (SecantTransversePlaneSpace (Module.finrank ℝ F) A)] :
    ContractibleSpace {Q : E →L[ℝ] F // Function.RightInverse J Q ∧
      Q.ker.IsSecantTransverse A} := by
  have hdim : Module.finrank ℝ J.range = Module.finrank ℝ F :=
    LinearMap.finrank_range_of_inj hJ
  exact ((transverseComplementHomeomorph (Module.finrank ℝ F) A J.range hdim hdisjoint).trans
    (J.frameTransversePlaneHomeomorph hJ A)).symm.contractibleSpace

end ContinuousLinearMap
