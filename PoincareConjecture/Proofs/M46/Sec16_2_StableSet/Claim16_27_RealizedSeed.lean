import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_PrefixVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M46

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

end PoincareConjecture.Proofs.M46
