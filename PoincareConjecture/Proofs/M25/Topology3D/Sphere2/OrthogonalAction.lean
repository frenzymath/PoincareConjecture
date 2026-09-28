import PoincareConjecture.Proofs.M25.Topology3D.Services









set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D



noncomputable def sphereIsometryDiffeomorph (A : E3 ≃ₗᵢ[ℝ] E3) :
    UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere where
  toFun := sphereMap A
  invFun := sphereMap A.symm
  left_inv x := Subtype.ext (A.symm_apply_apply x.1)
  right_inv x := Subtype.ext (A.apply_symm_apply x.1)
  contMDiff_toFun := by
    have : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
    exact ContMDiff.codRestrict_sphere
      (A.toContinuousLinearMap.contMDiff.comp contMDiff_coe_sphere) _
  contMDiff_invFun := by
    have : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
    exact ContMDiff.codRestrict_sphere
      (A.symm.toContinuousLinearMap.contMDiff.comp contMDiff_coe_sphere) _



@[simp] theorem sphereIsometryDiffeomorph_apply (A : E3 ≃ₗᵢ[ℝ] E3)
    (x : UnitTwoSphere) : sphereIsometryDiffeomorph A x = sphereMap A x := rfl



@[simp] theorem sphereIsometryDiffeomorph_symm (A : E3 ≃ₗᵢ[ℝ] E3) :
    (sphereIsometryDiffeomorph A).symm = sphereIsometryDiffeomorph A.symm := by
  apply Diffeomorph.ext
  intro x
  rfl



@[simp] theorem sphereIsometryDiffeomorph_trans (A B : E3 ≃ₗᵢ[ℝ] E3) :
    (sphereIsometryDiffeomorph A).trans (sphereIsometryDiffeomorph B) =
      sphereIsometryDiffeomorph (A.trans B) := by
  apply Diffeomorph.ext
  intro x
  rfl

end PoincareConjecture.M25.Topology3D
