import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Geometry.Manifold.Instances.Sphere











set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

section Sphere

variable {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
variable {G : E → F} {c : sphere (0 : E) 1 → F}




theorem mvfderiv_sphere_restriction (q : sphere (0 : E) 1)
    (hG : DifferentiableAt ℝ G (q : E))
    (hGc : ∀ p : sphere (0 : E) 1, G (p : E) = c p) :
    mvfderiv (𝓡 n) c q = (fderiv ℝ G (q : E)).comp
      (mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) q) := by
  have heq : c = G ∘ (Subtype.val : sphere (0 : E) 1 → E) := by
    funext p
    exact (hGc p).symm
  rw [heq, mvfderiv]
  rw [mfderiv_comp q hG.mdifferentiableAt
    ((contMDiff_coe_sphere (m := 1) (n := n) q).mdifferentiableAt one_ne_zero)]
  rw [mfderiv_eq_fderiv]
  ext u
  rfl




theorem fderiv_ne_zero_of_sphere_immersion (q : sphere (0 : E) 1)
    (hG : DifferentiableAt ℝ G (q : E))
    (hGc : ∀ p : sphere (0 : E) 1, G (p : E) = c p)
    (hi : Injective (mfderiv (𝓡 n) 𝓘(ℝ, F) c q))
    {v : E} (hv : v ∈ (ℝ ∙ (q : E))ᗮ) (hv0 : v ≠ 0) :
    fderiv ℝ G (q : E) v ≠ 0 := by
  rw [← range_mvfderiv_subtypeVal (n := n) q] at hv
  obtain ⟨u, hu⟩ := hv
  change mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) q u = v at hu
  intro hzero
  have hinj : Injective (mvfderiv (𝓡 n) c q) :=
    (NormedSpace.fromTangentSpace (c q)).injective.comp hi
  have hcu : mvfderiv (𝓡 n) c q u = 0 := by
    rw [mvfderiv_sphere_restriction q hG hGc]
    simpa only [ContinuousLinearMap.comp_apply, hu] using hzero
  have hu0 : u = 0 := hinj (hcu.trans (map_zero _).symm)
  apply hv0
  rw [← hu, hu0, map_zero]

end Sphere




theorem fderiv_rightAngleRotation_ne_zero_of_sphere_immersion
    [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))
    {G : E → F} {c : sphere (0 : E) 1 → F} (q : sphere (0 : E) 1)
    (hG : DifferentiableAt ℝ G (q : E))
    (hGc : ∀ p : sphere (0 : E) 1, G (p : E) = c p)
    (hi : Injective (mfderiv (𝓡 1) 𝓘(ℝ, F) c q)) :
    fderiv ℝ G (q : E) (o.rightAngleRotation (q : E)) ≠ 0 := by
  apply fderiv_ne_zero_of_sphere_immersion q hG hGc hi
  · exact (Submodule.mem_orthogonal_singleton_iff_inner_left).mpr
      (o.inner_rightAngleRotation_self (q : E))
  · exact o.rightAngleRotation.injective.ne
      (ne_zero_of_mem_unit_sphere q) |>.trans_eq (map_zero _)

end Poincare.Manifold.Schoenflies.Plane
