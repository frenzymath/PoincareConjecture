import PoincareConjecture.Proofs.M38.PolarCoordinates










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

variable (L : StandardCapSpace ≃L[ℝ] StandardCapSpace)


noncomputable def linearSphereMap (z : UnitTwoSphere) : UnitTwoSphere :=
  capUnitDirection (L z.val)


theorem linearSphereVector_ne_zero (z : UnitTwoSphere) : L z.val ≠ 0 := by
  intro hzero
  apply ne_zero_of_mem_unit_sphere z
  apply L.injective
  simpa only [map_zero] using hzero


theorem linearSphereMap_coe (z : UnitTwoSphere) :
    (linearSphereMap L z).val = ‖L z.val‖⁻¹ • L z.val :=
  capUnitDirection_coe (linearSphereVector_ne_zero L z)


theorem linearSphereMap_left_inverse :
    Function.LeftInverse (linearSphereMap L.symm) (linearSphereMap L) := by
  intro z
  change capUnitDirection (L.symm (linearSphereMap L z).val) = z
  rw [linearSphereMap_coe, map_smul, L.symm_apply_apply]
  exact capUnitDirection_smul z
    (inv_pos.mpr (norm_pos_iff.mpr (linearSphereVector_ne_zero L z)))



theorem linearSphereMap_smooth :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (linearSphereMap L) := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) :=
    ⟨by simp [StandardCapSpace]⟩
  have hL : ContMDiff (𝓡 2) (𝓡 3) ∞
      (fun z : UnitTwoSphere => L z.val) :=
    L.contDiff.contMDiff.comp contMDiff_coe_sphere
  exact capUnitDirection_smooth.comp_contMDiff hL
    (fun z => linearSphereVector_ne_zero L z)



noncomputable def linearSphereDiffeomorph :
    Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞ where
  toFun := linearSphereMap L
  invFun := linearSphereMap L.symm
  left_inv := linearSphereMap_left_inverse L
  right_inv := linearSphereMap_left_inverse L.symm
  contMDiff_toFun := linearSphereMap_smooth L
  contMDiff_invFun := linearSphereMap_smooth L.symm


theorem linearSphereDiffeomorph_apply (z : UnitTwoSphere) :
    linearSphereDiffeomorph L z = capUnitDirection (L z.val) := rfl


theorem linearSphereDiffeomorph_symm_apply (z : UnitTwoSphere) :
    (linearSphereDiffeomorph L).symm z = capUnitDirection (L.symm z.val) := rfl


theorem linearSphereDiffeomorph_coe (z : UnitTwoSphere) :
    (linearSphereDiffeomorph L z).val = ‖L z.val‖⁻¹ • L z.val :=
  linearSphereMap_coe L z


theorem linearSphereDiffeomorph_symm_coe (z : UnitTwoSphere) :
    ((linearSphereDiffeomorph L).symm z).val =
      ‖L.symm z.val‖⁻¹ • L.symm z.val :=
  linearSphereMap_coe L.symm z



theorem linearSphereDiffeomorph_ray (z : UnitTwoSphere) (t : ℝ) :
    L (t • z.val) = (t * ‖L z.val‖) • (linearSphereDiffeomorph L z).val := by
  calc
    L (t • z.val) = t • L z.val := map_smul L t z.val
    _ = t • (‖L z.val‖ • (linearSphereDiffeomorph L z).val) :=
      congrArg (fun x : StandardCapSpace => t • x) (capUnitDirection_radial (L z.val)).symm
    _ = (t * ‖L z.val‖) • (linearSphereDiffeomorph L z).val :=
      smul_smul t ‖L z.val‖ (linearSphereDiffeomorph L z).val

end PoincareConjecture.M38
