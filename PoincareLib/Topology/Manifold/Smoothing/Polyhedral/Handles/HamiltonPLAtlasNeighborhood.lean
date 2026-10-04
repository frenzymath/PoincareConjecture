import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.FinitePiecewiseAffine
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.LocallyPiecewiseAffineInverse

/-!
# Finite certificates for local PL atlas transitions

Finite affine formulas on a polyhedron give local PL formulas
on open subsets of its carrier interior. Such local certificates
recognize the actual coordinate groupoid used in Hamilton's
atlas induction. See Hamilton 1976, p. 69, Hudson 1969,
pp. 15--19 and M76 derivation 258.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Finite PL formulas yield local PL formulas on an open set
contained in the carrier interior. Boundary points of the finite
carrier are not included without further neighborhood data.
See Hamilton p. 69 and M76 derivation 258. -/
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

/-- Finite affine neighborhoods of every point of the actual
transition source suffice for PL groupoid membership. Inverse
regularity follows from the existing local inverse theorem.
See Hamilton p. 69 and M76 derivation 258. -/
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

/-- One finite certificate containing a transition source in
its carrier interior certifies the whole coordinate change.
See Hamilton p. 69 and M76 derivation 258. -/
theorem mem_piecewiseAffineGroupoid_of_finitePL_neighborhood
    (e : OpenPartialHomeomorph E E) {s : Set E}
    (he : FinitePiecewiseAffineOn (e : E → E) s)
    (hs : e.source ⊆ interior s) : e ∈ piecewiseAffineGroupoid E :=
  e.mem_piecewiseAffineGroupoid_of_local_finitePL fun _ hx => ⟨s, hs hx, he⟩

end OpenPartialHomeomorph
