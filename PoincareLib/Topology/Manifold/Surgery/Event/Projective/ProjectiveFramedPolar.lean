import PoincareLib.Topology.Manifold.Surgery.Event.Projective.ProjectivePolarCover
import PoincareLib.Topology.Manifold.Surgery.Event.Linear.LinearSphereDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Cylindrical projective coordinates with the actual ball derivative frame

Absorb an arbitrary invertible linear frame into the angular and height
coordinates. The reflection remains unchanged, and positive polar rays
become the exact affine rays of that same frame. This retains the angular
parametrization supplied by the actual surgery-ball normalization.
Source: Morgan--Tian Proposition 15.3, printed pp. 357-358.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

private instance sphereDimension : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp⟩

variable (L : StandardCapSpace ≃L[ℝ] StandardCapSpace)

/-- Normalizing a linear frame respects the actual angular antipode. -/
theorem linearSphereDiffeomorph_neg (z : UnitTwoSphere) :
    linearSphereDiffeomorph L (-z) = -linearSphereDiffeomorph L z := by
  apply Subtype.ext
  rw [linearSphereDiffeomorph_coe]
  change ‖L (-z.val)‖⁻¹ • L (-z.val) = -(linearSphereDiffeomorph L z).val
  rw [map_neg, norm_neg, smul_neg, linearSphereDiffeomorph_coe]

/-- The positive angular norm is smooth for this actual invertible frame. -/
theorem linearSphere_norm_smooth :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun z : UnitTwoSphere => ‖L z.val‖) := by
  intro z
  exact (contDiffAt_norm ℝ (linearSphereVector_ne_zero L z)).contMDiffAt.comp z
    ((L.contDiff.contMDiff.comp contMDiff_coe_sphere) z)

/-- The smooth cylinder coordinate change incorporates the original derivative frame. -/
noncomputable def linearCylinderFrame :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞ where
  toFun p := (linearSphereDiffeomorph L p.1, p.2 / ‖L p.1.val‖)
  invFun p := ((linearSphereDiffeomorph L).symm p.1,
    p.2 * ‖L ((linearSphereDiffeomorph L).symm p.1).val‖)
  left_inv p := by
    apply Prod.ext
    · exact (linearSphereDiffeomorph L).symm_apply_apply p.1
    · change p.2 / ‖L p.1.val‖ *
        ‖L ((linearSphereDiffeomorph L).symm (linearSphereDiffeomorph L p.1)).val‖ = p.2
      rw [Diffeomorph.symm_apply_apply, div_mul_cancel₀ _
        (norm_ne_zero_iff.mpr (linearSphereVector_ne_zero L p.1))]
  right_inv p := by
    apply Prod.ext
    · exact (linearSphereDiffeomorph L).apply_symm_apply p.1
    · change p.2 * ‖L ((linearSphereDiffeomorph L).symm p.1).val‖ /
        ‖L ((linearSphereDiffeomorph L).symm p.1).val‖ = p.2
      exact mul_div_cancel_right₀ _
        (norm_ne_zero_iff.mpr (linearSphereVector_ne_zero L _))
  contMDiff_toFun :=
    ((linearSphereDiffeomorph L).contMDiff.comp contMDiff_fst).prodMk
      (contMDiff_snd.div₀ ((linearSphere_norm_smooth L).comp contMDiff_fst)
        (fun p => norm_ne_zero_iff.mpr (linearSphereVector_ne_zero L p.1)))
  contMDiff_invFun :=
    ((linearSphereDiffeomorph L).symm.contMDiff.comp contMDiff_fst).prodMk
      (contMDiff_snd.mul ((linearSphere_norm_smooth L).comp
        ((linearSphereDiffeomorph L).symm.contMDiff.comp contMDiff_fst)))

/-- The derivative-frame change commutes with the free cylinder reflection. -/
theorem linearCylinderFrame_reflection (p : RoundCylinderSpace) :
    linearCylinderFrame L (-p.1, -p.2) =
      (-(linearCylinderFrame L p).1, -(linearCylinderFrame L p).2) := by
  apply Prod.ext
  · exact linearSphereDiffeomorph_neg L p.1
  · change -p.2 / ‖L (-p.1.val)‖ = -(p.2 / ‖L p.1.val‖)
    rw [map_neg, norm_neg, neg_div]

variable (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))

/-- The framed cover projects the exact transformed cylinder point. -/
noncomputable def projectiveFramedPolarMap (p : RoundCylinderSpace) : projectiveCarrier.{u}.carrier :=
  projectivePolarMap R (linearCylinderFrame L p)

/-- Changing the frame keeps precisely the same two-point reflection fibers. -/
theorem projectiveFramedPolar_fibers (x y : RoundCylinderSpace) :
    projectiveFramedPolarMap.{u} L R x = projectiveFramedPolarMap L R y ↔
      x = y ∨ x = (-y.1, -y.2) := by
  have hinj : Function.Injective (linearCylinderFrame L) := (linearCylinderFrame L).injective
  change projectivePolarMap R _ = projectivePolarMap R _ ↔ _
  rw [projectivePolar_fibers, ← linearCylinderFrame_reflection, hinj.eq_iff, hinj.eq_iff]

/-- The actual framed projection remains locally diffeomorphic. -/
theorem projectiveFramedPolar_localDiffeomorph :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (projectiveFramedPolarMap.{u} L R) := by
  intro p
  exact ((linearCylinderFrame L).isLocalDiffeomorph p).comp
    (𝓡 3) projectiveCarrier.carrier (projectivePolar_localDiffeomorph R _)

/-- The frame change preserves the exact omitted projective point. -/
theorem projectiveFramedPolar_range : range (projectiveFramedPolarMap.{u} L R) =
    {projectiveAffineMap R 0}ᶜ := by
  have hsurj : Function.Surjective (linearCylinderFrame L) := (linearCylinderFrame L).surjective
  change range (projectivePolarMap R ∘ linearCylinderFrame L) = _
  rw [range_comp, hsurj.range_eq, image_univ, projectivePolar_range]

/-- Every positive cylinder ray is the actual affine ray of the supplied frame. -/
theorem projectiveFramedPolar_affine (z : UnitTwoSphere) {t : ℝ} (ht : 0 < t) :
    projectiveFramedPolarMap.{u} L R (z, t) = projectiveAffineMap R (L (t⁻¹ • z.val)) := by
  have hn : 0 < ‖L z.val‖ := norm_pos_iff.mpr (linearSphereVector_ne_zero L z)
  change projectivePolarMap R (linearSphereDiffeomorph L z, t / ‖L z.val‖) = _
  rw [projectivePolar_affine R _ (div_pos ht hn), linearSphereDiffeomorph_coe,
    map_smul, smul_smul]
  congr 2
  field_simp

end PoincareMT.M38
