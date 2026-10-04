import Mathlib.Topology.ContinuousMap.Basic

/-!
# Ambient openness of saturated neighborhoods inside a compact carrier

Subtract the compact image of the carrier outside the neighborhood
from the known open image of its interior. This is the closed-quotient
argument in Brown derivation017, section4, with both ambient openness
and the saturation condition explicit.
-/

set_option autoImplicit false

open Set

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

/-- A saturated open neighborhood inside a compact carrier has an
ambient open image once the actual image of the carrier's interior
is ambient open. See Brown derivation017, section4. -/
theorem isOpen_image_inside_compact (g : C(X, Y)) {Q U : Set X}
    (hQ : IsCompact Q) (hU : IsOpen U) (hUQ : U ⊆ interior Q)
    (hsat : g ⁻¹' (g '' U) = U) (himage : IsOpen (g '' interior Q)) :
    IsOpen (g '' U) := by
  have he : g '' U = (g '' interior Q) \ (g '' (Q \ U)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, hUQ hx, rfl⟩, ?_⟩
      rintro ⟨z, hz, he⟩
      apply hz.2
      have hm : z ∈ g ⁻¹' (g '' U) := ⟨x, hx, he.symm⟩
      rwa [hsat] at hm
    · rintro ⟨⟨x, hx, rfl⟩, hn⟩
      have hxU : x ∈ U := by
        by_contra h
        exact hn ⟨x, ⟨interior_subset hx, h⟩, rfl⟩
      exact ⟨x, hxU, rfl⟩
  rw [he]
  exact IsOpen.sdiff himage ((hQ.diff hU).image g.continuous).isClosed

end ContinuousMap
