import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPLInterior
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexNeighborhood

set_option autoImplicit false

open Set

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem FinitePiecewiseAffineOn.mem_interior_image_of_convex
    {f : E → F} {S : Set E} (hf : FinitePiecewiseAffineOn f S)
    (hcv : Convex ℝ S) (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hinj : InjOn f S) {x : E} (hx : x ∈ interior S) :
    f x ∈ interior (f '' S) := by
  obtain ⟨K, hK, rfl, hfK⟩ := hf
  exact hfK.mem_interior_image_of_convex_space hK hcv hdim hinj hx

theorem FinitePiecewiseAffineOn.mem_interior_image
    {f : E → F} {S : Set E} (hf : FinitePiecewiseAffineOn f S)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hinj : InjOn f S) {x : E} (hx : x ∈ interior S) :
    f x ∈ interior (f '' S) := by
  obtain ⟨K, hK, hcv, hxK, hKS⟩ := isOpen_interior.exists_finite_convex_neighborhood hx
  have hsub : K.space ⊆ S := hKS.trans interior_subset
  have hlocal := (hf.restrict K hK hsub).mem_interior_image_of_convex
    hcv hdim (hinj.mono hsub) hxK
  exact interior_mono (image_mono hsub) hlocal

end Geometry
