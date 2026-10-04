import PoincareLib.Topology.Manifold.Surgery.Event.Polar.PolarCoordinates

/-!
# Angular diffeomorphisms induced by invertible linear maps

Normalize the actual linear image of each unit vector. Normalization of
the inverse linear map gives the inverse sphere map, including when the
linear map reverses orientation. These are the angular maps carried by
the actual derivatives of rectified surgery-ball coordinates.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareMT.M38

variable (L : StandardCapSpace ≃L[ℝ] StandardCapSpace)

/-- The normalized actual linear image of a unit vector. -/
noncomputable def linearSphereMap (z : UnitTwoSphere) : UnitTwoSphere :=
  capUnitDirection (L z.val)

/-- Invertibility keeps every actual unit-vector image away from zero. -/
theorem linearSphereVector_ne_zero (z : UnitTwoSphere) : L z.val ≠ 0 := by
  intro hzero
  apply ne_zero_of_mem_unit_sphere z
  apply L.injective
  simpa only [map_zero] using hzero

/-- The underlying vector is exactly the normalized linear image. -/
theorem linearSphereMap_coe (z : UnitTwoSphere) :
    (linearSphereMap L z).val = ‖L z.val‖⁻¹ • L z.val :=
  capUnitDirection_coe (linearSphereVector_ne_zero L z)

/-- Normalizing the actual inverse linear map reverses this sphere map. -/
theorem linearSphereMap_left_inverse :
    Function.LeftInverse (linearSphereMap L.symm) (linearSphereMap L) := by
  intro z
  change capUnitDirection (L.symm (linearSphereMap L z).val) = z
  rw [linearSphereMap_coe, map_smul, L.symm_apply_apply]
  exact capUnitDirection_smul z
    (inv_pos.mpr (norm_pos_iff.mpr (linearSphereVector_ne_zero L z)))

/-- The normalized image is smooth for the actual sphere atlas, since
the original invertible linear map never reaches the excluded origin. -/
theorem linearSphereMap_smooth :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (linearSphereMap L) := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) :=
    ⟨by simp [StandardCapSpace]⟩
  have hL : ContMDiff (𝓡 2) (𝓡 3) ∞
      (fun z : UnitTwoSphere => L z.val) :=
    L.contDiff.contMDiff.comp contMDiff_coe_sphere
  exact capUnitDirection_smooth.comp_contMDiff hL
    (fun z => linearSphereVector_ne_zero L z)

/-- Every invertible real linear map induces a smooth sphere
diffeomorphism, with no determinant or orientation restriction. -/
noncomputable def linearSphereDiffeomorph :
    Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞ where
  toFun := linearSphereMap L
  invFun := linearSphereMap L.symm
  left_inv := linearSphereMap_left_inverse L
  right_inv := linearSphereMap_left_inverse L.symm
  contMDiff_toFun := linearSphereMap_smooth L
  contMDiff_invFun := linearSphereMap_smooth L.symm

/-- Smooth packaging retains the original normalized forward map. -/
theorem linearSphereDiffeomorph_apply (z : UnitTwoSphere) :
    linearSphereDiffeomorph L z = capUnitDirection (L z.val) := rfl

/-- The actual packaged inverse is normalization after the original inverse linear map. -/
theorem linearSphereDiffeomorph_symm_apply (z : UnitTwoSphere) :
    (linearSphereDiffeomorph L).symm z = capUnitDirection (L.symm z.val) := rfl

/-- The diffeomorphism's underlying vector has the exact normalized formula. -/
theorem linearSphereDiffeomorph_coe (z : UnitTwoSphere) :
    (linearSphereDiffeomorph L z).val = ‖L z.val‖⁻¹ • L z.val :=
  linearSphereMap_coe L z

/-- Its inverse vector uses precisely the inverse linear map and its own norm. -/
theorem linearSphereDiffeomorph_symm_coe (z : UnitTwoSphere) :
    ((linearSphereDiffeomorph L).symm z).val =
      ‖L.symm z.val‖⁻¹ • L.symm z.val :=
  linearSphereMap_coe L.symm z

/-- The exact angular diffeomorphism records the radial factor of the
original linear map on every ray, including either sign of the parameter. -/
theorem linearSphereDiffeomorph_ray (z : UnitTwoSphere) (t : ℝ) :
    L (t • z.val) = (t * ‖L z.val‖) • (linearSphereDiffeomorph L z).val := by
  calc
    L (t • z.val) = t • L z.val := map_smul L t z.val
    _ = t • (‖L z.val‖ • (linearSphereDiffeomorph L z).val) :=
      congrArg (fun x : StandardCapSpace => t • x) (capUnitDirection_radial (L z.val)).symm
    _ = (t * ‖L z.val‖) • (linearSphereDiffeomorph L z).val :=
      smul_smul t ‖L z.val‖ (linearSphereDiffeomorph L z).val

end PoincareMT.M38
