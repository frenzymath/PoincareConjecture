import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Compat.ParabolicRescaling
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ParabolicRescaling
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Homothety
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.Seed.PrefixVolume

/-!
# The actual seed image in the selected realized history

Morgan--Tian Claim 16.27 and its use in Theorem 8.1, pp. 393-394.
The open history embedding and actual slice identification transfer
an open seed with compact regular closure to the same realized slice.
The selected volume calibration is preserved exactly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.M13
export PoincareMT.EpochExtension.SliceGeometry (originalSlice_volume)
end PoincareMT.M13

namespace PoincareMT.Proofs.M46

/-- A physical seed with compact regular closure gives the actual
realized comparison neighborhood, preserving image, closure and volume. -/
theorem realized_seed_of_regular_image (P : M46Predecessors.{u})
    {F : SurgeryFlowData.{u}} {window : M33RegularHistoryWindow F}
    (R : M46RegularSpacetimeData window) {t : ℝ}
    (ht : t ∈ R.history.generalized.interval)
    {A : Set (F.slice t).carrier} (hA : IsOpen A) (hcompact : IsCompact (closure A))
    (hregular : closure A ⊆ m33RegularRegion F t) :
    ∃ B : Set (R.geometry.toLGeometry.slices t).Point,
      IsOpen B ∧ IsCompact (closure B) ∧
      (R.history.history.forward t ht ∘ (R.geometry.sliceIdentification t).identification.symm)
        '' B = A ∧
      (R.history.history.forward t ht ∘ (R.geometry.sliceIdentification t).identification.symm)
        '' closure B = closure A ∧
      calibratedMetricVolume (R.geometry.toLGeometry.slices t).metricOnPoints B =
        calibratedMetricVolume (F.metric t) A := by
  let identify := (R.geometry.sliceIdentification t).identification
  let f := R.history.history.forward t ht ∘ identify.symm
  have hf : Topology.IsOpenEmbedding f :=
    (R.history.history.forward_openEmbedding t ht).comp identify.symm.toHomeomorph.isOpenEmbedding
  have hrange : range f = m33RegularRegion F t := by
    rw [← R.history.regular_range t ht]
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨identify.symm q, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨identify z, by simp only [f, Function.comp_apply, Diffeomorph.symm_apply_apply]⟩
  have hclrange : closure A ⊆ range f := hrange ▸ hregular
  let B := f ⁻¹' A
  have himage : f '' B = A := image_preimage_eq_of_subset (subset_closure.trans hclrange)
  have hclosure : closure B = f ⁻¹' closure A := by
    rw [hf.isEmbedding.closure_eq_preimage_closure_image, himage]
  have hBcompact : IsCompact (closure B) := by
    rw [hclosure]
    exact hf.isEmbedding.isInducing.isCompact_preimage' hcompact hclrange
  refine ⟨B, hA.preimage hf.continuous, hBcompact, himage, ?_, ?_⟩
  · rw [hclosure]
    exact image_preimage_eq_of_subset hclrange
  · have hidentify : identify '' (identify.symm '' B) = B := by
      ext q
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        simpa only [Diffeomorph.apply_symm_apply] using hz
      · intro hq
        exact ⟨identify.symm q, mem_image_of_mem _ hq, identify.apply_symm_apply q⟩
    have hphysical : R.history.history.forward t ht '' (identify.symm '' B) = A := by
      rw [← image_comp]
      exact himage
    change calibratedMetricVolume (R.geometry.realization.slices t).metricOnPoints B = _
    rw [← hidentify, M13.originalSlice_volume R.geometry P.m13 t,
      ← R.history.volume_image t ht, hphysical]

end PoincareMT.Proofs.M46
