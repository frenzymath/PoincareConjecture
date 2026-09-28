import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.Maps
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace Topology
open scoped Manifold ContDiff Bundle

universe u

noncomputable section

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})

def regularInteriorInclusion :
    Ioo H.reference.tMinus T × H.regularRegion P04 →
      Ioc H.reference.tMinus T × H.regularRegion P04 :=
  Prod.map (Set.inclusion fun _ ht => ⟨ht.1, ht.2.le⟩) id

theorem regularInteriorInclusion_isOpenEmbedding :
    IsOpenEmbedding (H.regularInteriorInclusion P04) :=
  (IsOpenEmbedding.inclusion
    (show Ioo H.reference.tMinus T ⊆ Ioc H.reference.tMinus T from
      fun _ ht => ⟨ht.1, ht.2.le⟩)
    (isOpen_Ioo.preimage continuous_subtype_val)).prodMap IsOpenEmbedding.id

theorem regularSpacetimeForward_interior_eq
    (p : Ioo H.reference.tMinus T × H.regularRegion P04) :
    H.regularSpacetimeForward P04 (H.regularInteriorInclusion P04 p) =
      H.oldSpacetimeForward P04 (H.reference.openSpacetimeForward (H.regularRegion P04) p) := by
  rw [H.reference.openSpacetimeForward_eq]
  exact H.regularSpacetimeForward_old P04 p.1 ⟨p.1.property.1, p.1.property.2.le⟩
    p.1.property.2 p.2

theorem old_regular_spacetime_eq_iff (p : F.point)
    (q : Ioc H.reference.tMinus T × H.regularRegion P04) :
    H.oldSpacetimeForward P04 p = H.regularSpacetimeForward P04 q ↔
      ∃ r : Ioo H.reference.tMinus T × H.regularRegion P04,
        H.reference.openSpacetimeForward (H.regularRegion P04) r = p ∧
          H.regularInteriorInclusion P04 r = q := by
  constructor
  · intro hpq
    have ht : p.1 = (q.1 : ℝ) := by
      simpa only [oldSpacetimeForward_time, regularSpacetimeForward_time] using
        congrArg Sigma.fst hpq
    have hlt : (q.1 : ℝ) < T := ht ▸ (H.interval_preterminal (H.oldPoint_time_mem p)).2
    let r : Ioo H.reference.tMinus T × H.regularRegion P04 :=
      (⟨q.1, ⟨q.1.property.1, hlt⟩⟩, q.2)
    have hr : H.regularInteriorInclusion P04 r = q := by
      apply Prod.ext
      · exact Subtype.ext rfl
      · rfl
    refine ⟨r, H.oldSpacetimeForward_injective P04 ?_, hr⟩
    exact (H.regularSpacetimeForward_interior_eq P04 r).symm.trans
      ((congrArg (H.regularSpacetimeForward P04) hr).trans hpq.symm)
  · rintro ⟨r, rfl, rfl⟩
    exact (H.regularSpacetimeForward_interior_eq P04 r).symm

theorem old_preimage_regular_image
    (V : Set (Ioc H.reference.tMinus T × H.regularRegion P04)) :
    H.oldSpacetimeForward P04 ⁻¹' (H.regularSpacetimeForward P04 '' V) =
      H.reference.openSpacetimeForward (H.regularRegion P04) ''
        (H.regularInteriorInclusion P04 ⁻¹' V) := by
  ext p
  constructor
  · rintro ⟨q, hq, hqp⟩
    obtain ⟨r, hrp, hrq⟩ := (H.old_regular_spacetime_eq_iff P04 p q).mp hqp.symm
    refine ⟨r, ?_, hrp⟩
    change H.regularInteriorInclusion P04 r ∈ V
    exact hrq.symm ▸ hq
  · rintro ⟨r, hr, hrp⟩
    exact ⟨H.regularInteriorInclusion P04 r, hr,
      (H.regularSpacetimeForward_interior_eq P04 r).trans
        (congrArg (H.oldSpacetimeForward P04) hrp)⟩

theorem regular_preimage_old_image (U : Set F.point) :
    H.regularSpacetimeForward P04 ⁻¹' (H.oldSpacetimeForward P04 '' U) =
      H.regularInteriorInclusion P04 ''
        (H.reference.openSpacetimeForward (H.regularRegion P04) ⁻¹' U) := by
  ext q
  constructor
  · rintro ⟨p, hp, hpq⟩
    obtain ⟨r, hrp, hrq⟩ := (H.old_regular_spacetime_eq_iff P04 p q).mp hpq
    refine ⟨r, ?_, hrq⟩
    change H.reference.openSpacetimeForward (H.regularRegion P04) r ∈ U
    exact hrp.symm ▸ hp
  · rintro ⟨r, hr, hrq⟩
    exact ⟨H.reference.openSpacetimeForward (H.regularRegion P04) r, hr,
      (H.regularSpacetimeForward_interior_eq P04 r).symm.trans
        (congrArg (H.regularSpacetimeForward P04) hrq)⟩

theorem isOpen_old_preimage_regular_image
    (V : Set (Ioc H.reference.tMinus T × H.regularRegion P04)) (hV : IsOpen V) :
    IsOpen (H.oldSpacetimeForward P04 ⁻¹' (H.regularSpacetimeForward P04 '' V)) := by
  rw [H.old_preimage_regular_image P04]
  exact (H.reference.openSpacetimeForward_isOpenEmbedding (H.regularRegion P04)).isOpenMap _
    (hV.preimage (H.regularInteriorInclusion_isOpenEmbedding P04).continuous)

theorem isOpen_regular_preimage_old_image (U : Set F.point) (hU : IsOpen U) :
    IsOpen (H.regularSpacetimeForward P04 ⁻¹' (H.oldSpacetimeForward P04 '' U)) := by
  rw [H.regular_preimage_old_image P04]
  exact (H.regularInteriorInclusion_isOpenEmbedding P04).isOpenMap _
    (hU.preimage (H.reference.openSpacetimeForward_isOpenEmbedding (H.regularRegion P04)).continuous)

@[instance_reducible] def extendedSpacetimeTopology : TopologicalSpace (H.extendedPoint P04) :=
  SingularRegularLimit.TwoChart.topology (H.oldSpacetimeForward P04) (H.regularSpacetimeForward P04)

theorem oldSpacetimeForward_isOpenEmbedding :
    @IsOpenEmbedding F.point (H.extendedPoint P04) _ (H.extendedSpacetimeTopology P04)
      (H.oldSpacetimeForward P04) :=
  SingularRegularLimit.TwoChart.isOpenEmbedding_left _ _
    (H.oldSpacetimeForward_injective P04) (H.isOpen_regular_preimage_old_image P04)

theorem regularSpacetimeForward_isOpenEmbedding :
    @IsOpenEmbedding (Ioc H.reference.tMinus T × H.regularRegion P04) (H.extendedPoint P04)
      _ (H.extendedSpacetimeTopology P04) (H.regularSpacetimeForward P04) :=
  SingularRegularLimit.TwoChart.isOpenEmbedding_right _ _
    (H.regularSpacetimeForward_injective P04) (H.isOpen_old_preimage_regular_image P04)

theorem regularSpacetimeForward_time_continuous :
    Continuous (Sigma.fst ∘ H.regularSpacetimeForward P04) := by
  have h : Continuous (fun p : Ioc H.reference.tMinus T × H.regularRegion P04 =>
      (p.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  simpa only [Function.comp_def, regularSpacetimeForward_time] using h

theorem extendedSpacetime_time_continuous :
    @Continuous (H.extendedPoint P04) ℝ (H.extendedSpacetimeTopology P04) _ Sigma.fst := by
  apply (SingularRegularLimit.TwoChart.continuous_iff _ _ Sigma.fst).mpr
  exact ⟨F.time_continuous, H.regularSpacetimeForward_time_continuous P04⟩

theorem extendedSpacetime_secondCountable :
    @SecondCountableTopology (H.extendedPoint P04) (H.extendedSpacetimeTopology P04) := by
  let _ : SecondCountableTopology F.point := F.space_secondCountable
  exact SingularRegularLimit.TwoChart.secondCountableTopology _ _
    (H.oldSpacetimeForward_injective P04) (H.regularSpacetimeForward_injective P04)
    (H.isOpen_old_preimage_regular_image P04) (H.isOpen_regular_preimage_old_image P04)
    (H.old_regular_spacetime_cover P04)

theorem extendedSpacetime_t2 :
    @T2Space (H.extendedPoint P04) (H.extendedSpacetimeTopology P04) := by
  let _ : T2Space F.point := F.space_t2
  apply SingularRegularLimit.TwoChart.t2Space _ _
    (H.oldSpacetimeForward_injective P04) (H.regularSpacetimeForward_injective P04)
    (H.isOpen_old_preimage_regular_image P04) (H.isOpen_regular_preimage_old_image P04)
    Sigma.fst F.time_continuous (H.regularSpacetimeForward_time_continuous P04)
  intro p q hold hregular hpq
  by_cases hpT : p.1 = T
  · have hqT : q.1 = T := hpq.symm.trans hpT
    apply hregular
    constructor
    · rcases H.old_regular_spacetime_cover P04 p with h | h
      · exact False.elim ((H.mem_range_oldSpacetimeForward_iff P04 p).mp h hpT)
      · exact h
    · rcases H.old_regular_spacetime_cover P04 q with h | h
      · exact False.elim ((H.mem_range_oldSpacetimeForward_iff P04 q).mp h hqT)
      · exact h
  · exact hold ⟨(H.mem_range_oldSpacetimeForward_iff P04 p).mpr hpT,
      (H.mem_range_oldSpacetimeForward_iff P04 q).mpr (hpq ▸ hpT)⟩

theorem extendedSpacetime_slice_embedding (t : ℝ) :
    @IsEmbedding (H.extendedSliceGeometry P04 t).slice.carrier (H.extendedPoint P04)
      _ (H.extendedSpacetimeTopology P04) (fun x => ⟨t, x⟩) := by
  let _ := H.extendedSpacetimeTopology P04
  by_cases ht : t = T
  · subst t
    have h := (H.regularSpacetimeForward_isOpenEmbedding P04).isEmbedding.comp
      ((isEmbedding_prodMkRight (⟨T, ⟨H.reference.tMinus_lt, le_rfl⟩⟩ :
        Ioc H.reference.tMinus T)).comp (H.terminalSliceHomeomorph P04).isEmbedding)
    simpa only [Function.comp_def, regularSpacetimeForward_terminal,
      Homeomorph.symm_apply_apply] using h
  · have h := (H.oldSpacetimeForward_isOpenEmbedding P04).isEmbedding.comp
      ((F.slice_embedding t).comp (H.oldSliceHomeomorph P04 ht).symm.isEmbedding)
    simpa only [Function.comp_def, H.oldSpacetimeForward_eq P04 ht,
      Homeomorph.apply_symm_apply] using h

end PoincareConjecture.SingularTimeAssumptions
