import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Recognizing a compact image from a dense separated part

If two source pieces cover a target and map into two closed
sides, the dense part of either target side disjoint from
the other side determines its entire compact image.
See the convex-cap argument in M76 derivation 248f.
-/

set_option autoImplicit false

open Set

namespace Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

/-- A compact source piece maps onto a target side when the
part disjoint from the other image side is dense. Empty pieces
are allowed. See Cairns 1940, pp. 801--802 and M76 derivation 248f. -/
theorem IsCompact.image_eq_of_dense_sdiff {a b : Set X} {c d : Set Y} {f : X → Y}
    (ha : IsCompact a) (hf : ContinuousOn f a)
    (hcover : c ⊆ f '' (a ∪ b)) (hfa : MapsTo f a c) (hfb : MapsTo f b d)
    (hdense : closure (c \ d) = c) : f '' a = c := by
  apply Subset.antisymm hfa.image_subset
  rw [← hdense]
  apply closure_minimal ?_ (ha.image_of_continuousOn hf).isClosed
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hcover hy.1
  rcases hx with hx | hx
  · exact ⟨x, hx, hxy⟩
  · exact (hy.2 (hxy ▸ hfb hx)).elim

end Set
