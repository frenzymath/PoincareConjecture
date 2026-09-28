import Mathlib.Topology.ContinuousMap.Basic










set_option autoImplicit false

open Set

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]




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
