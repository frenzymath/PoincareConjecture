import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Instances.Real.Lemmas





open Set Topology

namespace Poincare.Coarea

variable {M : Type*} [TopologicalSpace M] {f : M → ℝ} {I : Set ℝ}


theorem isCompact_slab_of_isProperMap
    (hf : IsProperMap (I.restrictPreimage f))
    {a b : ℝ} (hab : Icc a b ⊆ I) : IsCompact (f ⁻¹' Icc a b) := by
  have hK : IsCompact ((Subtype.val : I → ℝ) ⁻¹' Icc a b) :=
    IsEmbedding.subtypeVal.isInducing.isCompact_preimage' isCompact_Icc (by simpa using hab)
  have hpre := (hf.isCompact_preimage hK).image continuous_subtype_val
  rw [image_val_preimage_restrictPreimage] at hpre
  simpa only [Subtype.image_preimage_coe, inter_eq_right.mpr hab] using hpre

end Poincare.Coarea
