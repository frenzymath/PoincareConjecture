import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPLLocalInterior
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : Set E} {T : Set F} {e : S ≃ₜ T}

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

theorem IsFinitePL.mem_interior_iff (he : e.IsFinitePL)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (x : S) :
    (e x : F) ∈ interior T ↔ (x : E) ∈ interior S := by
  constructor
  · intro hx
    simpa only [e.symm_apply_apply] using he.symm.mem_interior hdim.symm hx
  · exact he.mem_interior hdim

end Homeomorph
