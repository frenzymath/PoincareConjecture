import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CylinderScalarCalculus
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CylinderScalarLimit
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_EventNeighborhood
import Mathlib.Topology.Order.LeftRight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale c : ℝ} {U : Set C.carrier}

theorem cylinderScalar_continuousWithinAt_right
    (P : M44CapPersistencePredecessors.{u})
    (e : SurgeryFlowCylinder F C origin scale (Icc c 0) U)
    {x : C.carrier} (hx : x ∈ U) {s : ℝ} (hs : s ∈ Ico c 0) :
    ContinuousWithinAt (cylinderScalar e x) (Ici s) s := by
  let clock : ℝ ≃o ℝ :=
    (OrderIso.divRight₀ scale e.scale_pos).trans (OrderIso.addLeft origin)
  have hsI : s ∈ Icc c 0 := ⟨hs.1, hs.2.le⟩
  have h0I : 0 ∈ Icc c 0 := ⟨hs.1.trans hs.2.le, le_rfl⟩
  obtain ⟨b, hsb, hb0, hfree⟩ := M44.exists_surgery_free_right_interval F
    (e.time_subset (mem_image_of_mem _ hsI)) (clock.strictMono hs.2)
  change clock s < b at hsb
  let r := clock.symm b
  have hsr : s < r := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [r, OrderIso.apply_symm_apply] using hsb
  have hr0 : r < 0 := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [r, OrderIso.apply_symm_apply] using hb0
  have hJ : Icc (clock s) b ⊆ F.time_domain := by
    intro t ht
    exact F.time_domain_interval.out (e.time_subset (mem_image_of_mem _ hsI))
      (e.time_subset (mem_image_of_mem _ h0I)) ⟨ht.1, ht.2.trans hb0.le⟩
  have hVI : Icc s r ⊆ Icc c 0 := Icc_subset_Icc hs.1 hr0.le
  have hVtime : MapsTo (fun t => origin + t / scale) (Icc s r) (Icc (clock s) b) := by
    intro t ht
    change clock t ∈ Icc (clock s) b
    refine ⟨clock.monotone ht.1, ?_⟩
    simpa only [r, OrderIso.apply_symm_apply] using (clock.monotone ht.2)
  have hc := cylinderScalar_continuousOn_slab P e hx hsb hJ hfree s hsI
    ⟨le_rfl, hsb.le⟩ hVI hVtime
  exact (hc s ⟨le_rfl, hsr.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hsr)

theorem cylinderScalar_continuousWithinAt_left_of_not_surgery
    (P : M44CapPersistencePredecessors.{u})
    (e : SurgeryFlowCylinder F C origin scale (Icc c 0) U)
    {x : C.carrier} (hx : x ∈ U) {s : ℝ} (hs : s ∈ Ioc c 0)
    (hnot : origin + s / scale ∉ F.surgery_times) :
    ContinuousWithinAt (cylinderScalar e x) (Iic s) s := by
  let clock : ℝ ≃o ℝ :=
    (OrderIso.divRight₀ scale e.scale_pos).trans (OrderIso.addLeft origin)
  have hsI : s ∈ Icc c 0 := ⟨hs.1.le, hs.2⟩
  have hcI : c ∈ Icc c 0 := ⟨le_rfl, hs.1.le.trans hs.2⟩
  obtain ⟨u, v, hus, hsv, hlocal⟩ := M44.isolated_surgery_neighborhood F
    (e.time_subset (mem_image_of_mem _ hsI))
  obtain ⟨a, ha, has⟩ := exists_between (max_lt (clock.strictMono hs.1) hus)
  have hca : clock c < a := (le_max_left _ _).trans_lt ha
  have hua : u < a := (le_max_right _ _).trans_lt ha
  have hJ : Icc a (clock s) ⊆ F.time_domain := by
    intro t ht
    exact F.time_domain_interval.out (e.time_subset (mem_image_of_mem _ hcI))
      (e.time_subset (mem_image_of_mem _ hsI)) ⟨hca.le.trans ht.1, ht.2⟩
  have hfree : Disjoint F.surgery_times (Ioc a (clock s)) := by
    apply Set.disjoint_left.mpr
    intro t ht htI
    have heq := hlocal t ht ⟨hua.trans htI.1, htI.2.trans_lt hsv⟩
    exact hnot (heq ▸ ht)
  let r := clock.symm a
  have hcr : c < r := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [r, OrderIso.apply_symm_apply] using hca
  have hrs : r < s := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [r, OrderIso.apply_symm_apply] using has
  have hVI : Icc r s ⊆ Icc c 0 := Icc_subset_Icc hcr.le hs.2
  have hVtime : MapsTo (fun t => origin + t / scale) (Icc r s) (Icc a (clock s)) := by
    intro t ht
    change clock t ∈ Icc a (clock s)
    refine ⟨?_, clock.monotone ht.2⟩
    simpa only [r, OrderIso.apply_symm_apply] using (clock.monotone ht.1)
  have hc := cylinderScalar_continuousOn_slab P e hx has hJ hfree s hsI
    ⟨has.le, le_rfl⟩ hVI hVtime
  exact (hc s ⟨hrs.le, le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hrs)

theorem cylinderScalar_continuousOn
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin scale (Icc c 0) U)
    {x : C.carrier} (hx : x ∈ U) :
    ContinuousOn (cylinderScalar e x) (Icc c 0) := by
  intro s hs
  apply continuousWithinAt_iff_continuous_left_right.mpr
  constructor
  · rcases lt_or_eq_of_le hs.1 with hcs | hcs
    · have hleft : ContinuousWithinAt (cylinderScalar e x) (Iic s) s := by
        by_cases hT : origin + s / scale ∈ F.surgery_times
        · exact continuousWithinAt_Iio_iff_Iic.mp
            (cylinderScalar_tendsto_left_at_surgery P hpinch e hx ⟨hcs, hs.2⟩ hT)
        · exact cylinderScalar_continuousWithinAt_left_of_not_surgery
            P e hx ⟨hcs, hs.2⟩ hT
      exact hleft.mono inter_subset_right
    · apply continuousWithinAt_singleton.mono
      intro t ht
      exact mem_singleton_iff.mpr
        (le_antisymm ht.2 (by simpa only [hcs] using ht.1.1))
  · rcases lt_or_eq_of_le hs.2 with hs0 | hs0
    · exact (cylinderScalar_continuousWithinAt_right P e hx ⟨hs.1, hs0⟩).mono
        inter_subset_right
    · apply continuousWithinAt_singleton.mono
      intro t ht
      exact mem_singleton_iff.mpr
        (le_antisymm (by simpa only [hs0] using ht.1.2) ht.2)

theorem cylinderScalar_hasDerivAt_of_not_surgery
    (P : M44CapPersistencePredecessors.{u})
    (e : SurgeryFlowCylinder F C origin scale (Icc c 0) U)
    {x : C.carrier} (hx : x ∈ U) {s : ℝ} (hs : s ∈ Ioo c 0)
    (hnot : origin + s / scale ∉ F.surgery_times) :
    HasDerivAt (cylinderScalar e x) (cylinderScalarRate e x s / scale) s := by
  let clock : ℝ ≃o ℝ :=
    (OrderIso.divRight₀ scale e.scale_pos).trans (OrderIso.addLeft origin)
  obtain ⟨a, b, hca, has, hsb, hb0, hfree⟩ :=
    M44.exists_surgery_free_closed_neighborhood F
      (e.time_subset (mem_image_of_mem _ (Ioo_subset_Icc_self hs)))
      (clock.strictMono hs.1) (clock.strictMono hs.2) hnot
  have hc0 := hs.1.trans hs.2
  have hJ : Icc a b ⊆ F.time_domain := by
    intro t ht
    exact F.time_domain_interval.out
      (e.time_subset (mem_image_of_mem _ (show c ∈ Icc c 0 from ⟨le_rfl, hc0.le⟩)))
      (e.time_subset (mem_image_of_mem _ (show 0 ∈ Icc c 0 from ⟨hc0.le, le_rfl⟩)))
      ⟨hca.le.trans ht.1, ht.2.trans hb0.le⟩
  exact cylinderScalar_hasDerivAt_slab P e hx (has.trans hsb) hJ
    (hfree.mono_right Ioc_subset_Icc_self) (by simpa only [interior_Icc] using hs)
    ⟨has, hsb⟩

end PoincareConjecture.Proofs.M46
