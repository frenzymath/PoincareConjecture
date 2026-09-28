import PoincareConjecture.Proofs.M47.CanonicalNeckCylinderBottom
import PoincareConjecture.Proofs.M47.ComponentEstimateRetained

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_closed_cylinder_backward_extension_or_cap
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin a l : ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin 1 (Icc a 0) U)
    (ha : a < 0) (hU : IsOpen U) (hne : U.Nonempty)
    (hl : l < origin + a) (hJ : Icc l origin ⊆ F.time_domain) :
    (∃ d : ℝ, d < a ∧ l ≤ origin + d ∧
      ∃ E : SurgeryFlowCylinder F C origin 1 (Icc d 0) U,
        ∀ s (hs : s ∈ Icc a 0) (hs' : s ∈ Icc d 0) x,
          E.forward s hs' x = e.forward s hs x) ∨
      ∃ hT : origin + a / 1 ∈ F.surgery_times,
        ∀ [Nonempty (F.slice (origin + a / 1)).carrier],
          ∃ i : Fin (F.event (origin + a / 1) hT).cap_count,
            (e.forward a ⟨le_rfl, ha.le⟩ '' U ∩
              ((F.event (origin + a / 1) hT).caps i).carrier).Nonempty := by
  classical
  have hbottom : origin + a ∈ F.time_domain := hJ ⟨hl.le, by linarith only [ha]⟩
  by_cases hT : origin + a / 1 ∈ F.surgery_times
  · obtain ⟨x0, _hx0⟩ := hne
    let : Nonempty (F.slice (origin + a / 1)).carrier :=
      ⟨e.forward a ⟨le_rfl, ha.le⟩ x0⟩
    let event := F.event (origin + a / 1) hT
    by_cases hcontact : ∃ i : Fin event.cap_count,
        (e.forward a ⟨le_rfl, ha.le⟩ '' U ∩ (event.caps i).carrier).Nonempty
    · exact Or.inr ⟨hT, fun [_] => hcontact⟩
    · let chart := (M44.cylinderSliceChart e hU a ⟨le_rfl, ha.le⟩).toOpenPartialHomeomorph
      have hopen : IsOpen (e.forward a ⟨le_rfl, ha.le⟩ '' U) :=
        chart.isOpen_image_of_subset_source hU (Subset.refl U)
      have hret : e.forward a ⟨le_rfl, ha.le⟩ '' U ⊆ interior event.retained_post := by
        apply hopen.subset_interior_iff.mpr
        intro z hz
        have hcover : z ∈ event.retained_post ∪ (⋃ i, (event.caps i).carrier) := by
          rw [event.post_cover]
          exact mem_univ z
        apply hcover.resolve_right
        intro hcap
        obtain ⟨i, hi⟩ := mem_iUnion.mp hcap
        exact hcontact ⟨i, z, hz, hi⟩
      let d := max (l - origin) (event.tMinus - origin)
      have hda : d < a := by
        apply max_lt
        · linarith only [hl]
        · have h := event.tMinus_lt
          simp only [div_one] at h
          linarith only [h]
      have hld : l ≤ origin + d := by
        have h := le_max_left (l - origin) (event.tMinus - origin)
        dsimp only [d]
        linarith only [h]
      have hpre : event.tMinus ≤ origin + d / 1 := by
        have h := le_max_right (l - origin) (event.tMinus - origin)
        simp only [div_one]
        dsimp only [d]
        linarith only [h]
      obtain ⟨E, hE⟩ := PoincareConjecture.M47.exists_component_cylinder_backward_across_retained_event
        e hU ha.le hda hT hpre hret
      exact Or.inl ⟨d, hda, hld, E, hE⟩
  · have hnot : origin + a ∉ F.surgery_times := by simpa only [div_one] using hT
    obtain ⟨c, b, hlc, hca, hab, _hbt, hfree⟩ :=
      M44.exists_surgery_free_closed_neighborhood F hbottom hl
        (show origin + a < origin by linarith only [ha]) hnot
    let d := c - origin
    have hda : d < a := by dsimp only [d]; linarith only [hca]
    have hld : l ≤ origin + d := by simpa only [d, add_sub_cancel] using hlc.le
    have htime : Icc (origin + d / 1) (origin + a / 1) ⊆ F.time_domain := by
      simpa only [div_one, d, add_sub_cancel] using
        (Icc_subset_Icc hlc.le (show origin + a ≤ origin by linarith only [ha])).trans hJ
    have hfree' : Disjoint F.surgery_times
        (Ioc (origin + d / 1) (origin + a / 1)) := by
      apply hfree.mono_right
      simp only [div_one, d, add_sub_cancel]
      exact fun _ ht => ⟨ht.1.le, ht.2.trans hab.le⟩
    obtain ⟨E, hE⟩ := M46.exists_cylinder_backward_along_ordinary_slab
      e hU ha.le hda htime hfree'
    exact Or.inl ⟨d, hda, hld, E, hE⟩

end PoincareConjecture.Proofs.M47
