import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Topology3D.Geometry.Services

/-!
# Orthogonal actions on the unit two-sphere

Smale, Theorem 6, pp. 625-626. The frozen orthogonal endpoint map is an
actual smooth diffeomorphism, for either determinant sign. See
`smale/derivations/2026-09-22-sphere-reduction-transport.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareMT.M25.Topology3D

/-- The actual orthogonal endpoint diffeomorphism in Smale, Theorem 6,
pp. 625-626, with the frozen `sphereMap` as its forward function. -/
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

/-- The orthogonal diffeomorphism has the exact frozen endpoint values;
Smale, Theorem 6, pp. 625-626. -/
@[simp] theorem sphereIsometryDiffeomorph_apply (A : E3 ≃ₗᵢ[ℝ] E3)
    (x : UnitTwoSphere) : sphereIsometryDiffeomorph A x = sphereMap A x := rfl

/-- Restriction commutes with the actual inverse isometry; Smale,
Theorem 6, pp. 625-626. -/
@[simp] theorem sphereIsometryDiffeomorph_symm (A : E3 ≃ₗᵢ[ℝ] E3) :
    (sphereIsometryDiffeomorph A).symm = sphereIsometryDiffeomorph A.symm := by
  apply Diffeomorph.ext
  intro x
  rfl

/-- Both composition operations mean first A, then B; Smale,
Theorem 6, pp. 625-626, orthogonal endpoint assembly. -/
@[simp] theorem sphereIsometryDiffeomorph_trans (A B : E3 ≃ₗᵢ[ℝ] E3) :
    (sphereIsometryDiffeomorph A).trans (sphereIsometryDiffeomorph B) =
      sphereIsometryDiffeomorph (A.trans B) := by
  apply Diffeomorph.ext
  intro x
  rfl

end PoincareMT.M25.Topology3D
