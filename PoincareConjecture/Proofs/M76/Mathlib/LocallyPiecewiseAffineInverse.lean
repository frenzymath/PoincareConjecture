import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineGroupoid
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedAffineHomeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

set_option autoImplicit false

open Set Geometry Topology

namespace OpenPartialHomeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem locallyPiecewiseAffineOn_symm (e : OpenPartialHomeomorph E F)
    (he : LocallyPiecewiseAffineOn e e.source) :
    LocallyPiecewiseAffineOn e.symm e.target := by
  intro y hy
  have hx := e.map_target hy
  obtain ⟨K, hK, hxK, hKU, hf⟩ := he (e.symm y) hx
  have hinj : InjOn e K.space := e.injOn.mono hKU
  refine ⟨hf.embeddedImage hinj, hf.embeddedImage_finite hinj hK, ?_, ?_,
    hf.inverse_on_embeddedImage hinj (e.leftInvOn.mono hKU)⟩
  · rw [hf.embeddedImage_space, mem_interior_iff_mem_nhds]
    simpa only [e.right_inv hy] using
      e.image_mem_nhds hx (mem_interior_iff_mem_nhds.mp hxK)
  · rw [hf.embeddedImage_space]
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hKU hx)

end OpenPartialHomeomorph

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem mem_piecewiseAffineGroupoid_iff_forward (e : OpenPartialHomeomorph E E) :
    e ∈ piecewiseAffineGroupoid E ↔ LocallyPiecewiseAffineOn e e.source := by
  rw [mem_piecewiseAffineGroupoid_iff]
  exact ⟨And.left, fun he => ⟨he, e.locallyPiecewiseAffineOn_symm he⟩⟩

end Geometry
