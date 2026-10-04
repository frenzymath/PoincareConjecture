import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Homeomorph.Defs

/-!
# Affine height approaches in convex models

An open segment toward a strictly lower or higher point supplies
the corresponding height approach. Carrier homeomorphisms with
the exact height formula transport either sign separately.
See Alexander 1924, pp. 7--8 and M76 derivation 256.
-/

set_option autoImplicit false

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An affine height on a convex carrier approaches any point
from below whenever the carrier has a lower point. No interior
or compactness hypothesis is required. See Alexander pp. 7--8
and M76 derivation 256. -/
theorem Convex.mem_closure_lower_affine_height
    {C : Set E} (hC : Convex ℝ C) (A : E →ᵃ[ℝ] ℝ)
    {x z : E} (hx : x ∈ C) (hz : z ∈ C) (hlt : A z < A x) :
    x ∈ closure (C ∩ {y | A y < A x}) := by
  apply closure_mono _ (segment_subset_closure_openSegment (right_mem_segment ℝ z x))
  intro y hy
  refine ⟨hC.openSegment_subset hz hx hy, ?_⟩
  have hAy : A y ∈ openSegment ℝ (A z) (A x) := by
    rw [← image_openSegment ℝ A z x]
    exact mem_image_of_mem A hy
  exact (openSegment_subset_Ioo hlt hAy).2

/-- An affine height on a convex carrier approaches any point
from above whenever the carrier has a higher point.
See Alexander pp. 7--8 and M76 derivation 256. -/
theorem Convex.mem_closure_upper_affine_height
    {C : Set E} (hC : Convex ℝ C) (A : E →ᵃ[ℝ] ℝ)
    {x z : E} (hx : x ∈ C) (hz : z ∈ C) (hlt : A x < A z) :
    x ∈ closure (C ∩ {y | A x < A y}) := by
  simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_neg_iff] using
    hC.mem_closure_lower_affine_height (-A) hx hz (neg_lt_neg hlt)

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An exact carrier height equation transports the lower
height approach without an ambient extension of the map.
See Alexander pp. 7--8 and M76 derivation 256. -/
theorem mem_lower_height_closure_of_height_preserving
    {S : Set X} {T : Set Y} (H : S ≃ₜ T) (A : X → ℝ) (B : Y → ℝ)
    (hheight : ∀ y : S, B (H y) = A y) (x : S)
    (hlo : (x : X) ∈ closure (S ∩ {y | A y < A x})) :
    (H x : Y) ∈ closure (T ∩ {y | B y < B (H x)}) := by
  have hxlo : x ∈ closure ((Subtype.val : S → X) ⁻¹' {y | A y < A x}) := by
    rwa [closure_subtype, Subtype.image_preimage_val]
  have hcont : Continuous (fun y : S => (H y : Y)) :=
    continuous_subtype_val.comp H.continuous
  apply hcont.continuousWithinAt.mem_closure hxlo
  intro y hy
  refine ⟨(H y).property, ?_⟩
  change B (H y) < B (H x)
  rw [hheight y, hheight x]
  exact hy

/-- An exact carrier height equation transports the upper
height approach without an ambient extension of the map.
See Alexander pp. 7--8 and M76 derivation 256. -/
theorem mem_upper_height_closure_of_height_preserving
    {S : Set X} {T : Set Y} (H : S ≃ₜ T) (A : X → ℝ) (B : Y → ℝ)
    (hheight : ∀ y : S, B (H y) = A y) (x : S)
    (hhi : (x : X) ∈ closure (S ∩ {y | A x < A y})) :
    (H x : Y) ∈ closure (T ∩ {y | B (H x) < B y}) := by
  simpa only [neg_lt_neg_iff] using H.mem_lower_height_closure_of_height_preserving
    (fun y => -A y) (fun y => -B y) (fun y => congrArg Neg.neg (hheight y)) x
      (by simpa only [neg_lt_neg_iff] using hhi)

end Homeomorph
