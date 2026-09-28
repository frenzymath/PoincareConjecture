import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FinitePiecewiseAffineOn.locallyPiecewiseAffineOn_of_subset_interior
    {f : E → F} {s U : Set E} (hf : FinitePiecewiseAffineOn f s)
    (hU : IsOpen U) (hUs : U ⊆ interior s) : LocallyPiecewiseAffineOn f U := by
  obtain ⟨K, hK, rfl, hfK⟩ := hf
  intro x hx
  obtain ⟨R, hR, hxR, hRU, hfR⟩ := hfK.exists_finite_neighborhood hK
    isCompact_singleton hU (singleton_subset_iff.mpr ⟨hUs hx, hx⟩)
  exact ⟨R, hR, hxR (mem_singleton x), fun _ hy => (hRU hy).2, hfR⟩

end Geometry

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem mem_piecewiseAffineGroupoid_of_local_finitePL
    (e : OpenPartialHomeomorph E E)
    (he : ∀ x ∈ e.source, ∃ s : Set E,
      x ∈ interior s ∧ FinitePiecewiseAffineOn (e : E → E) s) :
    e ∈ piecewiseAffineGroupoid E := by
  apply (mem_piecewiseAffineGroupoid_iff_forward e).mpr
  intro x hx
  obtain ⟨s, hxs, K, hK, rfl, hfK⟩ := he x hx
  obtain ⟨R, hR, hxR, hRU, hfR⟩ := hfK.exists_finite_neighborhood hK
    isCompact_singleton e.open_source (singleton_subset_iff.mpr ⟨hxs, hx⟩)
  exact ⟨R, hR, hxR (mem_singleton x), fun _ hy => (hRU hy).2, hfR⟩

theorem mem_piecewiseAffineGroupoid_of_finitePL_neighborhood
    (e : OpenPartialHomeomorph E E) {s : Set E}
    (he : FinitePiecewiseAffineOn (e : E → E) s)
    (hs : e.source ⊆ interior s) : e ∈ piecewiseAffineGroupoid E :=
  e.mem_piecewiseAffineGroupoid_of_local_finitePL fun _ hx => ⟨s, hs hx, he⟩

end OpenPartialHomeomorph
