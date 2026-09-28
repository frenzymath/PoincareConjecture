import PoincareConjecture.Proofs.M47.SeedM15Cylinder
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_BackwardOrdinaryCylinder
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_EventNeighborhood










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_strictLeft_cylinder_closed
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin a : ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin 1 (Ioc a 0) U)
    (ha : a < 0) (hU : IsOpen U) (hbottom : origin + a ∈ F.time_domain) :
    ∃ E : SurgeryFlowCylinder F C origin 1 (Icc a 0) U,
      ∀ s (hs : s ∈ Ioc a 0) (hs' : s ∈ Icc a 0), ∀ x ∈ U,
        E.forward s hs' x = e.forward s hs x := by
  have hzero : (0 : ℝ) ∈ Ioc a 0 := ⟨ha, le_rfl⟩
  have horigin : origin ∈ F.time_domain := by
    simpa only [zero_div, add_zero] using e.time_subset (mem_image_of_mem _ hzero)
  obtain ⟨b, hab, hbt, hfree⟩ := M44.exists_surgery_free_right_interval F hbottom
    (show origin + a < origin by linarith only [ha])
  let c := b - origin
  have hac : a < c := by dsimp only [c]; linarith only [hab]
  have hc : c < 0 := by dsimp only [c]; linarith only [hbt]
  have hsub : Icc c 0 ⊆ Ioc a 0 :=
    fun _ hs => ⟨hac.trans_le hs.1, hs.2⟩
  let f := e.restrict hsub ordConnected_Icc (Subset.refl U)
  have hclock : origin + c / 1 = b := by simp only [c, div_one, add_sub_cancel]
  have hJ : Icc (origin + a / 1) (origin + c / 1) ⊆ F.time_domain := by
    rw [div_one, hclock]
    exact (Icc_subset_Icc le_rfl hbt.le).trans
      (F.time_domain_interval.out hbottom horigin)
  have hfree' : Disjoint F.surgery_times
      (Ioc (origin + a / 1) (origin + c / 1)) := by
    simpa only [div_one, c, add_sub_cancel] using hfree
  obtain ⟨E, hE⟩ := M46.exists_cylinder_backward_along_ordinary_slab
    f hU hc.le hac hJ hfree'
  refine ⟨E, ?_⟩
  intro s hs hs' x hx
  apply PoincareConjecture.M47.seedM15_cylinder_eq_of_terminal E e hs.2
    (fun _ ht => ⟨hs'.1.trans ht.1, ht.2⟩)
    (fun _ ht => ⟨hs.1.trans_le ht.1, ht.2⟩) x hx x hx
  exact hE 0 ⟨hc.le, le_rfl⟩ ⟨ha.le, le_rfl⟩ x

end PoincareConjecture.Proofs.M47
