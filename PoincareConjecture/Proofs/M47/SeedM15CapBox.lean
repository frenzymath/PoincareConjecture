import PoincareConjecture.Proofs.M47.PositiveHistory
import PoincareConjecture.Proofs.M47.ComponentEstimateCylinder
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveHistoryPaths









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.M47



theorem seedM15_cap_child_box_nonpositive
    (hC : RicciFlowCurvatureTheory.{u})
    {F : SurgeryFlowData.{u}} {G : GeneralizedRicciFlowData.{u}}
    (H : M33RegularHistoryRealization G F)
    {J : Set ℝ} (hpolicy : SurgeryFlowTerminalPolicyOn F J)
    {T : ℝ} (hTJ : T ∈ J) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (q : G.box_index) (x : (G.box q).carrier.carrier)
    (hTbox : T ∈ (G.box q).interval)
    (v : Ico (F.event T hT).tMinus T) (hvbox : v.val ∈ (G.box q).interval)
    {i : Fin (F.event T hT).cap_count}
    (hcontact : (connectedComponent
      (H.forward T (m33BoxIntervalSubset G q hTbox) ((G.box q).forward T hTbox x)) ∩
      ((F.event T hT).caps i).carrier).Nonempty) :
    ¬ SurgeryPositiveComponentAt F v.val
      (H.forward v.val (m33BoxIntervalSubset G q hvbox)
        ((G.box q).forward v.val hvbox x)) := by
  let E := F.event T hT
  let pre := (E.pre_identify v).symm
    (H.forward v.val (m33BoxIntervalSubset G q hvbox) ((G.box q).forward v.val hvbox x))
  have hretained : pre ∈ E.retained_pre := interior_subset
    (H.pre_retained_at_surgery q T hTbox hT v.val hvbox v.property x)
  have hchild := H.surgery_compatibility q T hTbox hT v.val hvbox v.property x
  have hchildContact : (connectedComponent (E.retention.map pre) ∩
      (E.caps i).carrier).Nonempty := by
    rw [hchild]
    exact hcontact
  have hnot := M47Positive.pre_component_nonpositive_of_retained_child_meets_cap
    hC F hpolicy hTJ hT v pre hretained hchildContact
  simpa only [pre, E, Diffeomorph.apply_symm_apply] using hnot



theorem seedM15_cap_birth_box_nonpositive
    (hC : RicciFlowCurvatureTheory.{u})
    {F : SurgeryFlowData.{u}} {G : GeneralizedRicciFlowData.{u}}
    (H : M33RegularHistoryRealization G F)
    {J : Set ℝ} (hpolicy : SurgeryFlowTerminalPolicyOn F J)
    {C : GeneralizedSliceCarrier.{u}} {origin a : ℝ}
    (U : TopologicalSpace.Opens C.carrier)
    (hcompact : IsCompact (U : Set C.carrier))
    (hconnected : IsConnected (U : Set C.carrier)) (x0 : U)
    (e : SurgeryFlowCylinder F C origin 1 (Icc a 0) U)
    (ha : a < 0) (hbirthJ : origin + a / 1 ∈ J)
    (hbirth : origin + a / 1 ∈ F.surgery_times)
    [Nonempty (F.slice (origin + a / 1)).carrier]
    {i : Fin (F.event (origin + a / 1) hbirth).cap_count}
    (hcontact : (connectedComponent (e.forward a ⟨le_rfl, ha.le⟩ x0.val) ∩
      ((F.event (origin + a / 1) hbirth).caps i).carrier).Nonempty)
    (q : G.box_index) (x : (G.box q).carrier.carrier)
    (hbbox : origin + a / 1 ∈ (G.box q).interval)
    (v : Ico (F.event (origin + a / 1) hbirth).tMinus (origin + a / 1))
    (hvbox : v.val ∈ (G.box q).interval)
    {s : ℝ} (hs : s ∈ Ioc a 0)
    (hsbox : origin + s / 1 ∈ (G.box q).interval)
    (hfree : Disjoint F.surgery_times (Ioc (origin + a / 1) (origin + s / 1)))
    (hpost : H.forward (origin + s / 1) (m33BoxIntervalSubset G q hsbox)
      ((G.box q).forward (origin + s / 1) hsbox x) ∈
        e.forward s ⟨hs.1.le, hs.2⟩ '' (U : Set C.carrier)) :
    ¬ SurgeryPositiveComponentAt F v.val
      (H.forward v.val (m33BoxIntervalSubset G q hvbox)
        ((G.box q).forward v.val hvbox x)) := by
  have haI : a ∈ Icc a 0 := ⟨le_rfl, ha.le⟩
  have hsI : s ∈ Icc a 0 := ⟨hs.1.le, hs.2⟩
  have hbs : origin + a / 1 < origin + s / 1 := by
    simp only [div_one]
    linarith [hs.1]
  have htime : Icc (origin + a / 1) (origin + s / 1) ⊆ F.time_domain :=
    F.time_domain_interval.out (e.time_subset (mem_image_of_mem _ haI))
      (e.time_subset (mem_image_of_mem _ hsI))
  let slab := F.regular_slabs _ _ hbs htime hfree
  obtain ⟨z, hz, hzpost⟩ := hpost
  have hactual : H.forward (origin + a / 1) (m33BoxIntervalSubset G q hbbox)
      ((G.box q).forward (origin + a / 1) hbbox x) = e.forward a haI z := by
    apply (show Function.Injective (slab.transport
      ⟨origin + a / 1, ⟨le_rfl, hbs.le⟩⟩ ⟨origin + s / 1, ⟨hbs.le, le_rfl⟩⟩) from
        (slab.identify ⟨origin + s / 1, ⟨hbs.le, le_rfl⟩⟩).injective.comp
          (slab.identify ⟨origin + a / 1, ⟨le_rfl, hbs.le⟩⟩).symm.injective)
    have hH := H.slab_compatibility q _ _ hbs htime hfree _ _
      ⟨le_rfl, hbs.le⟩ ⟨hbs.le, le_rfl⟩ hbbox hsbox x
    have he := e.slab_compatibility _ _ hbs htime hfree a haI s hsI
      ⟨le_rfl, hbs.le⟩ ⟨hbs.le, le_rfl⟩ z hz
    exact hH.trans (hzpost.symm.trans he.symm)
  have hzcomponent : e.forward a haI z ∈
      connectedComponent (e.forward a haI x0.val) := by
    rw [← component_cylinder_image_eq e U.isOpen hcompact hconnected a haI x0.property]
    exact mem_image_of_mem _ hz
  apply seedM15_cap_child_box_nonpositive hC H hpolicy hbirthJ hbirth
    q x hbbox v hvbox (i := i)
  rw [hactual, ← connectedComponent_eq hzcomponent]
  exact hcontact

end PoincareConjecture.M47
