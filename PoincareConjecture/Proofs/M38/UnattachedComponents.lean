import PoincareConjecture.Proofs.M38.CappingComponents
import PoincareConjecture.Proofs.M38.CappingRegions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (x : eventDiscardedOpen F T hT)
  (hunattached : ∀ i, ConnectedComponents.mk (P i).attachmentPoint ≠ ConnectedComponents.mk x)

noncomputable local instance unattachedChartedSpace :
    ChartedSpace StandardCapSpace (CappedDiscardedSpace F T hT P) :=
  cappedDiscardedChartedSpace F T hT P

include hunattached

theorem unattached_component_subset_old :
    connectedComponent (cappedOldInclusion F T hT P x) ⊆
      Set.range (cappedOldInclusion F T hT P) := by
  rw [cappedOldInclusion_range]
  intro q hq hcap
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hcap
  obtain ⟨z, rfl⟩ := cappedCapBall_subset_patch F T hT P i hi
  apply hunattached i
  apply (cappedComponentsHomeomorph F T hT P).injective
  change ConnectedComponents.mk (cappedOldInclusion F T hT P (P i).attachmentPoint) =
    ConnectedComponents.mk (cappedOldInclusion F T hT P x)
  exact (cappedCapPatch_component F T hT P i z).symm.trans
    (ConnectedComponents.coe_eq_coe'.mpr hq)

theorem unattached_old_image_component :
    cappedOldInclusion F T hT P '' connectedComponent x =
      connectedComponent (cappedOldInclusion F T hT P x) := by
  apply Set.Subset.antisymm
  · exact (cappedOldInclusion_openEmbedding F T hT P).continuous.image_connectedComponent_subset x
  · intro q hq
    obtain ⟨y, rfl⟩ := unattached_component_subset_old F T hT P x hunattached hq
    refine ⟨y, ?_, rfl⟩
    have hy : y ∈ cappedOldInclusion F T hT P ⁻¹'
        connectedComponent (cappedOldInclusion F T hT P x) := hq
    rwa [cappedOldInclusion_preimage_component F T hT P x] at hy

theorem unattached_inverse_mem {q : CappedDiscardedSpace F T hT P}
    (hq : q ∈ connectedComponent (cappedOldInclusion F T hT P x)) :
    cappedOldInverse F T hT P q ∈ connectedComponent x := by
  rw [← cappedOldInclusion_preimage_component F T hT P x]
  change cappedOldInclusion F T hT P (cappedOldInverse F T hT P q) ∈
    connectedComponent (cappedOldInclusion F T hT P x)
  rw [cappedOldInverse_right F T hT P
    (unattached_component_subset_old F T hT P x hunattached hq)]
  exact hq

noncomputable def unattachedComponentDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3)
      (componentCarrier (openCarrier (F.slice (F.event T hT).tMinus)
        (eventDiscardedOpen F T hT)) x).carrier
      (componentCarrier (cappedDiscardedCarrier F T hT P)
        (cappedOldInclusion F T hT P x)).carrier ∞ := by
  let O := openCarrier (F.slice (F.event T hT).tMinus) (eventDiscardedOpen F T hT)
  let Q := cappedDiscardedCarrier F T hT P
  let forward : (componentCarrier O x).carrier →
      (componentCarrier Q (cappedOldInclusion F T hT P x)).carrier :=
    fun y => ⟨cappedOldInclusion F T hT P y.val,
      (cappedOldInclusion_openEmbedding F T hT P).continuous.image_connectedComponent_subset x
        (Set.mem_image_of_mem _ y.property)⟩
  let inverse : (componentCarrier Q (cappedOldInclusion F T hT P x)).carrier →
      (componentCarrier O x).carrier := fun q =>
    ⟨cappedOldInverse F T hT P q.val,
      unattached_inverse_mem F T hT P x hunattached q.property⟩
  refine {
    toEquiv := {
      toFun := forward
      invFun := inverse
      left_inv := fun y => Subtype.ext (cappedOldInverse_apply F T hT P y.val)
      right_inv := fun q => Subtype.ext (cappedOldInverse_right F T hT P
        (unattached_component_subset_old F T hT P x hunattached q.property)) }
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff
      (componentOpen Q (cappedOldInclusion F T hT P x)) forward).mp
    exact (cappedOldInclusion_smooth F T hT P).comp
      (contMDiff_subtype_val (U := componentOpen O x))
  · apply (ContMDiff.subtypeVal_comp_iff (componentOpen O x) inverse).mp
    exact (cappedOldInverse_smooth F T hT P).comp_contMDiff
      (contMDiff_subtype_val (U := componentOpen Q (cappedOldInclusion F T hT P x)))
      (fun q => unattached_component_subset_old F T hT P x hunattached q.property)

theorem unattached_old_component_compact :
    IsCompact (connectedComponentIn (F.event T hT).retained_preᶜ x.val) := by
  let O := openCarrier (F.slice (F.event T hT).tMinus) (eventDiscardedOpen F T hT)
  let Q := cappedDiscardedCarrier F T hT P
  let d := unattachedComponentDiffeomorph F T hT P x hunattached
  have hc := componentCarrier_compact Q (cappedDiscardedCarrier_compact F T hT P)
    (cappedOldInclusion F T hT P x)
  have hcO : IsCompact (Set.univ : Set (componentCarrier O x).carrier) := by
    rw [← Set.image_univ_of_surjective d.symm.surjective]
    exact hc.image d.symm.continuous
  have hcImage := hcO.image
    (continuous_subtype_val.comp (continuous_subtype_val :
      Continuous (Subtype.val : (componentCarrier O x).carrier → O.carrier)))
  have hrange : (fun y : (componentCarrier O x).carrier => y.val.val) '' Set.univ =
      connectedComponentIn (F.event T hT).retained_preᶜ x.val := by
    rw [connectedComponentIn_eq_image
      (show x.val ∈ (F.event T hT).retained_preᶜ from x.property)]
    ext y
    constructor
    · rintro ⟨z, _, rfl⟩
      exact ⟨z.val, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, Set.mem_univ _, rfl⟩
  change IsCompact ((fun y : (componentCarrier O x).carrier => y.val.val) '' Set.univ) at hcImage
  rwa [hrange] at hcImage

theorem unattached_component_eq_ambient :
    connectedComponentIn (F.event T hT).retained_preᶜ x.val = connectedComponent x.val := by
  let : LocallyConnectedSpace (F.slice (F.event T hT).tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace StandardCapSpace _
  have hopen := (F.event T hT).retained_pre_compact.isClosed.isOpen_compl.connectedComponentIn
    (x := x.val)
  have hclosed := (unattached_old_component_compact F T hT P x hunattached).isClosed
  exact Set.Subset.antisymm
    (isPreconnected_connectedComponentIn.subset_connectedComponent
      (mem_connectedComponentIn x.property))
    ((show IsClopen (connectedComponentIn (F.event T hT).retained_preᶜ x.val) from
      ⟨hclosed, hopen⟩).connectedComponent_subset (mem_connectedComponentIn x.property))

end PoincareConjecture.M38
