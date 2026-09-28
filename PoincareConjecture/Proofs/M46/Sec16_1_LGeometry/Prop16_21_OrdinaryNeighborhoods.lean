import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_21_CompactOrdinaryTrace
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_EventNeighborhood










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46





theorem exists_compact_nonsurgery_clock_neighborhood
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {T t : ℝ}
    (hwindow : Icc 0 T ⊆ H.generalized.interval) (ht : t ∈ Ico 0 T)
    (hnot : t ∉ F.surgery_times) :
    ∃ N : Set H.generalized.point, IsCompact N ∧ ∃ delta : ℝ, 0 < delta ∧
      ∀ v : H.generalized.point, v.1 ∈ Icc 0 T → |v.1 - t| < delta → v ∈ N := by
  have hphysical : Icc 0 T ⊆ F.time_domain := by
    intro s hs
    exact W.time_subset (H.interval_eq ▸ hwindow hs)
  rcases ht.1.eq_or_lt with ht0 | ht0
  · have htzero : t = 0 := ht0.symm
    subst t
    obtain ⟨b, hb, hbT, hNo⟩ := M44.exists_surgery_free_right_interval F F.zero_mem ht.2
    have hJ : Icc 0 b ⊆ F.time_domain :=
      fun _ hs => hphysical ⟨hs.1, hs.2.trans hbT.le⟩
    have hwin : Icc 0 b ⊆ H.generalized.interval :=
      fun _ hs => hwindow ⟨hs.1, hs.2.trans hbT.le⟩
    have hreg : (univ : Set (F.slice 0).carrier) ⊆ m33RegularRegion F 0 := by
      intro x _ hT
      exact (F.zero_not_surgery hT).elim
    obtain ⟨N, hN, hcover⟩ := exists_compact_ordinary_history_trace H hb hJ hNo hwin
      (F.slices_compact 0 F.zero_mem) hreg
    refine ⟨N, hN, b, hb, ?_⟩
    intro v hv hnear
    have hvb : v.1 ∈ Icc 0 b := ⟨hv.1, by simpa only [sub_zero, abs_of_nonneg hv.1] using
      (show |v.1 - 0| ≤ b from hnear.le)⟩
    exact hcover v.1 hvb v.2 (mem_univ _)
  · obtain ⟨a, b, ha, hat, htb, hbT, hNo⟩ :=
      M44.exists_surgery_free_closed_neighborhood F (hphysical ⟨ht.1, ht.2.le⟩)
        ht0 ht.2 hnot
    have hab : a < b := hat.trans htb
    have hJ : Icc a b ⊆ F.time_domain :=
      fun _ hs => hphysical ⟨ha.le.trans hs.1, hs.2.trans hbT.le⟩
    have hwin : Icc a b ⊆ H.generalized.interval :=
      fun _ hs => hwindow ⟨ha.le.trans hs.1, hs.2.trans hbT.le⟩
    have hfree : Disjoint F.surgery_times (Ioc a b) := hNo.mono_right Ioc_subset_Icc_self
    have hreg : (univ : Set (F.slice a).carrier) ⊆ m33RegularRegion F a := by
      intro x _ hT
      exact (Set.disjoint_left.mp hNo hT ⟨le_rfl, hab.le⟩).elim
    obtain ⟨N, hN, hcover⟩ := exists_compact_ordinary_history_trace H hab hJ hfree hwin
      (F.slices_compact a (hJ ⟨le_rfl, hab.le⟩)) hreg
    refine ⟨N, hN, min (t - a) (b - t), lt_min (sub_pos.mpr hat) (sub_pos.mpr htb), ?_⟩
    intro v _ hnear
    have hleft := (abs_lt.mp hnear).1
    have hright := (abs_lt.mp hnear).2
    have hv : v.1 ∈ Icc a b := by
      constructor
      · linarith [min_le_left (t - a) (b - t)]
      · linarith [min_le_right (t - a) (b - t)]
    exact hcover v.1 hv v.2 (mem_univ _)

end PoincareConjecture.Proofs.M46
