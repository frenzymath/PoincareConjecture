import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Proper restrictions localized inside compact sets

If all points mapping into a target set lie in one compact set, compact
subsets of the restricted target have compact preimages. In particular,
every restriction of a real-valued continuous map with this localization
property is proper; the target set need not be open.
-/

set_option autoImplicit false

open Set Topology

namespace Poincare

theorem isProperMap_restrictPreimage_of_isCompact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (I : Set Y) [CompactlyCoherentSpace I]
    {K : Set X} (hK : IsCompact K) (hsub : f ⁻¹' I ⊆ K) :
    IsProperMap (I.restrictPreimage f) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hf.restrictPreimage, fun C hC => ?_⟩
  rw [IsEmbedding.subtypeVal.isCompact_iff, image_val_preimage_restrictPreimage]
  apply hK.of_isClosed_subset ((hC.image continuous_subtype_val).isClosed.preimage hf)
  rintro x ⟨y, hy, heq⟩
  apply hsub
  change f x ∈ I
  rw [← heq]
  exact y.property

/-- A real target set requires no openness or closedness hypothesis. -/
theorem isProperMap_real_restrictPreimage_of_isCompact
    {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) (I : Set ℝ) {K : Set X}
    (hK : IsCompact K) (hsub : f ⁻¹' I ⊆ K) :
    IsProperMap (I.restrictPreimage f) :=
  isProperMap_restrictPreimage_of_isCompact hf I hK hsub

end Poincare
