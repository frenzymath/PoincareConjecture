import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionPLInterior
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.BoundedRegionConvexNeighborhood

/-!
# Local interior openness of a finite PL injection

Restrict to an actual small convex polyhedral neighborhood in
the source interior. The convex-image theorem then supplies a
target neighborhood. See Cairns 1940, pp. 804--806, Hudson 1969,
pp. 60--61 and M76 derivation 247.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- A finite PL injection on a convex carrier of the same
dimension preserves ambient interior points. See Cairns
pp. 804--806 and M76 derivation 247. -/
theorem FinitePiecewiseAffineOn.mem_interior_image_of_convex
    {f : E → F} {S : Set E} (hf : FinitePiecewiseAffineOn f S)
    (hcv : Convex ℝ S) (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hinj : InjOn f S) {x : E} (hx : x ∈ interior S) :
    f x ∈ interior (f '' S) := by
  obtain ⟨K, hK, rfl, hfK⟩ := hf
  exact hfK.mem_interior_image_of_convex_space hK hcv hdim hinj hx

/-- A finite PL injection is open at every ambient interior
point of its carrier when source and target dimensions agree.
The carrier itself need not be convex. See Cairns pp. 804--806,
Hudson pp. 60--61 and M76 derivation 247. -/
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
