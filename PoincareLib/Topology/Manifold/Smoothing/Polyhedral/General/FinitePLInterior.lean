import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionPLLocalInterior
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.FinitePLHomeomorph

/-!
# Ambient interiors under finite PL carrier homeomorphisms

The actual finite affine representative is injective on
its full source and has exactly the target as image.
The checked interior-image theorem and the finite PL inverse
therefore preserve ambient interiors in both directions.
See Cairns 1940, pp. 804--806, Hudson 1969, pp. 60--61
and M76 derivations 247--248.
-/

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : Set E} {T : Set F} {e : S ≃ₜ T}

/-- An actual finite PL carrier homeomorphism preserves
ambient interior points in equal dimensions. Neither carrier
needs to be convex. See Cairns pp. 804--806 and
M76 derivations 247--248. -/
theorem IsFinitePL.mem_interior (he : e.IsFinitePL)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {x : S} (hx : (x : E) ∈ interior S) : (e x : F) ∈ interior T := by
  obtain ⟨f, hf, hef⟩ := he
  have hinj : InjOn f S := by
    intro y hy z hz hyz
    have h : e ⟨y, hy⟩ = e ⟨z, hz⟩ := by
      apply Subtype.ext
      simpa only [hef] using hyz
    exact congrArg Subtype.val (e.injective h)
  have himage : f '' S = T := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← hef ⟨z, hz⟩]
      exact (e ⟨z, hz⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hef, e.apply_symm_apply]
  have h := hf.mem_interior_image hdim hinj hx
  rwa [himage, ← hef x] at h

/-- Finite PL homeomorphisms between carriers in equal
ambient dimensions reflect as well as preserve every
interior point. See Cairns pp. 804--806 and
M76 derivations 247--248. -/
theorem IsFinitePL.mem_interior_iff (he : e.IsFinitePL)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (x : S) :
    (e x : F) ∈ interior T ↔ (x : E) ∈ interior S := by
  constructor
  · intro hx
    simpa only [e.symm_apply_apply] using he.symm.mem_interior hdim.symm hx
  · exact he.mem_interior hdim

end Homeomorph
