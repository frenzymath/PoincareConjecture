import PoincareConjecture.Proofs.M38.PartialCutRegions
import PoincareConjecture.Proofs.M38.SharedCutLocalModels









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))


noncomputable def partialOldCoordinates :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (eventCutOpen F T hT P S)
      (partialCappedCarrier F T hT P S).carrier ∞ :=
  regionPartialDiffeomorph (partialOldRegionEquivalence F T hT P S) isOpen_univ (by
    rw [← partialOldInclusion_range]
    exact (partialOldInclusion_openEmbedding F T hT P S).isOpen_range)

variable (i : Fin (F.event T hT).cap_count) (hi : i ∉ S)

include hi


theorem uncutCollar_target_old : (P i).collarChart.target ⊆ eventCutOpen F T hT P S := by
  intro x hx hbad
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hbad
  have hij : i ≠ j.val := fun h => hi (h.symm ▸ j.property)
  apply Set.disjoint_left.mp ((P i).collars_disjoint (P j.val) hij) hx
  apply Set.image_mono _ hj
  intro z hz
  have hz0 : z.2 = 0 := hz.2
  exact ⟨hz.1, by simpa only [hz0] using (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)⟩


noncomputable def uncutCollarOldChart :
    OpenPartialHomeomorph RoundCylinderSpace (eventCutOpen F T hT P S) :=
  ((P i).collarChart.symm.subtypeRestr (eventCutOpen_nonempty F T hT P S i false)).symm


theorem uncutCollarOldChart_source :
    (uncutCollarOldChart F T hT P S i).source = Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := by
  change ((P i).collarChart.symm.subtypeRestr _).target = _
  apply Set.Subset.antisymm ((P i).collarChart.symm.subtypeRestr_target_subset _)
  intro z hz
  refine ⟨hz, ?_⟩
  simpa only [Set.mem_preimage, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
    using uncutCollar_target_old F T hT P S i hi ((P i).collarChart.symm.map_target hz)


theorem uncutCollarOldChart_target :
    (uncutCollarOldChart F T hT P S i).target =
      Subtype.val ⁻¹' ((P i).collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  change ((P i).collarChart.symm.subtypeRestr _).source = _
  rw [OpenPartialHomeomorph.subtypeRestr_source]
  rfl


theorem uncutCollarOldChart_apply (z : RoundCylinderSpace)
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :
    (uncutCollarOldChart F T hT P S i z).val = (P i).collar z := by
  apply (P i).collarChart.symm.subtypeRestr_symm_apply
    (eventCutOpen_nonempty F T hT P S i false)
  change z ∈ (uncutCollarOldChart F T hT P S i).source
  rwa [uncutCollarOldChart_source F T hT P S i hi]


theorem uncutCollarOldChart_inverse (y : eventCutOpen F T hT P S) :
    (uncutCollarOldChart F T hT P S i).symm y = (P i).collarInverse y.val := rfl


noncomputable def uncutCollarOldDiffeomorph :
    PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace
      (eventCutOpen F T hT P S) ∞ where
  toPartialEquiv := (uncutCollarOldChart F T hT P S i).toPartialEquiv
  open_source := (uncutCollarOldChart F T hT P S i).open_source
  open_target := (uncutCollarOldChart F T hT P S i).open_target
  contMDiffOn_toFun := by
    change ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (uncutCollarOldChart F T hT P S i) (uncutCollarOldChart F T hT P S i).source
    rw [uncutCollarOldChart_source F T hT P S i hi]
    have hv : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (Subtype.val ∘ uncutCollarOldChart F T hT P S i) (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :=
      (event_cap_collar_smooth F T hT i (P i).width_pos (P i).width_lt (P i).shell_domain).congr
        (fun z hz => uncutCollarOldChart_apply F T hT P S i hi z hz)
    intro z hz
    exact (ContMDiffWithinAt.subtypeVal_comp_iff (eventCutOpen F T hT P S)
      (uncutCollarOldChart F T hT P S i) (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) z).mp (hv z hz)
  contMDiffOn_invFun := by
    change ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      ((P i).collarInverse ∘ Subtype.val) (uncutCollarOldChart F T hT P S i).target
    apply (event_cap_collar_inverse_smooth F T hT i
      (P i).width_pos (P i).width_lt (P i).shell_domain).comp contMDiff_subtype_val.contMDiffOn
    intro y hy
    rwa [uncutCollarOldChart_target F T hT P S i hi] at hy


noncomputable def uncutCollar :
    PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace
      (partialCappedCarrier F T hT P S).carrier ∞ :=
  (uncutCollarOldDiffeomorph F T hT P S i hi).trans (partialOldCoordinates F T hT P S)


theorem uncutCollar_source :
    (uncutCollar F T hT P S i hi).source = Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := by
  change (uncutCollarOldChart F T hT P S i).source ∩
    (uncutCollarOldChart F T hT P S i) ⁻¹' Set.univ = _
  rw [Set.preimage_univ, Set.inter_univ, uncutCollarOldChart_source F T hT P S i hi]


theorem uncutCollar_apply (z : RoundCylinderSpace) :
    uncutCollar F T hT P S i hi z =
      partialOldInclusion F T hT P S (uncutCollarOldChart F T hT P S i z) := rfl


theorem uncutCollar_inverse (q : (partialCappedCarrier F T hT P S).carrier) :
    (uncutCollar F T hT P S i hi).symm q =
      (P i).collarInverse (partialOldInverse F T hT P S q).val := rfl


theorem uncutCollar_image :
    uncutCollar F T hT P S i hi '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) =
      (uncutCollar F T hT P S i hi).target := by
  rw [← uncutCollar_source F T hT P S i hi]
  exact (uncutCollar F T hT P S i hi).toOpenPartialHomeomorph.image_source_eq_target


theorem uncutCollar_image_open :
    IsOpen (uncutCollar F T hT P S i hi '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  rw [uncutCollar_image]
  exact (uncutCollar F T hT P S i hi).open_target


theorem uncutCollar_central :
    uncutCollar F T hT P S i hi '' (Set.univ ×ˢ ({0} : Set ℝ)) =
      partialOldInclusion F T hT P S ''
        {y : eventCutOpen F T hT P S | y.val ∈ (P i).collar '' (Set.univ ×ˢ ({0} : Set ℝ))} := by
  have hsub : (Set.univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ) ⊆
      Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := by
    intro z hz
    have hz0 : z.2 = 0 := hz.2
    exact ⟨hz.1, by simpa only [hz0] using (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)⟩
  apply Set.Subset.antisymm
  · rintro q ⟨z, hz, rfl⟩
    exact ⟨uncutCollarOldChart F T hT P S i z,
      ⟨z, hz, (uncutCollarOldChart_apply F T hT P S i hi z (hsub hz)).symm⟩, rfl⟩
  · rintro q ⟨y, ⟨z, hz, hzy⟩, rfl⟩
    refine ⟨z, hz, ?_⟩
    rw [uncutCollar_apply]
    exact congrArg (partialOldInclusion F T hT P S)
      (Subtype.ext ((uncutCollarOldChart_apply F T hT P S i hi z (hsub hz)).trans hzy))

end PoincareConjecture.M38
