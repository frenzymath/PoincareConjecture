import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPLLocalInterior
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph

set_option autoImplicit false
open Set Geometry

namespace Homeomorph.IsFinitePL

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {S : Set E} {T : Set F} {c : S ≃ₜ T}

private theorem maps_interior (hc : c.IsFinitePL)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (p : S) (hp : (p : E) ∈ interior S) : (c p : F) ∈ interior T := by
  obtain ⟨f, hf, hfval⟩ := hc
  have hinj : InjOn f S := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (c.injective (Subtype.ext
      ((hfval ⟨x, hx⟩).trans (hxy.trans (hfval ⟨y, hy⟩).symm))))
  have hsub : f '' S ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hfval ⟨x, hx⟩]
    exact (c ⟨x, hx⟩).property
  rw [hfval]
  exact interior_mono hsub (hf.mem_interior_image hdim hinj hp)

theorem mem_interior_iff_of_finrank_eq (hc : c.IsFinitePL)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (p : S) :
    (c p : F) ∈ interior T ↔ (p : E) ∈ interior S := by
  constructor
  · intro hp
    simpa only [c.symm_apply_apply] using maps_interior hc.symm hdim.symm (c p) hp
  · exact maps_interior hc hdim p

theorem mem_frontier_iff_of_finrank_eq (hc : c.IsFinitePL)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (p : S) :
    (c p : F) ∈ frontier T ↔ (p : E) ∈ frontier S := by
  have hmem := hc.mem_interior_iff_of_finrank_eq hdim p
  obtain ⟨_, hg, _⟩ := hc.symm
  obtain ⟨_, hf, _⟩ := hc
  rw [frontier, frontier, hf.isCompact.isClosed.closure_eq,
    hg.isCompact.isClosed.closure_eq, mem_sdiff, mem_sdiff,
    and_iff_right (c p).property, and_iff_right p.property]
  exact not_congr hmem

end Homeomorph.IsFinitePL
