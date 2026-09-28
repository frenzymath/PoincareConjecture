import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveFlowPieces
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.FiniteEventInduction
import PoincareConjecture.Proofs.M33.RegularHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

theorem positive_component_history_box_line
    {G : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}}
    (H : M33RegularHistoryRealization G F) (q : G.box_index)
    (x : (G.box q).carrier.carrier)
    {a b : ℝ} (ha : a ∈ (G.box q).interval) (hb : b ∈ (G.box q).interval)
    (hab : a ≤ b)
    (hpos : SurgeryPositiveComponentAt F a
      (H.forward a (m33BoxIntervalSubset G q ha) ((G.box q).forward a ha x))) :
    SurgeryPositiveComponentAt F b
      (H.forward b (m33BoxIntervalSubset G q hb) ((G.box q).forward b hb x)) := by
  let Q : ℝ → Prop := fun t => ∀ ht : t ∈ (G.box q).interval,
    SurgeryPositiveComponentAt F t
      (H.forward t (m33BoxIntervalSubset G q ht) ((G.box q).forward t ht x))
  have hbox : Icc a b ⊆ (G.box q).interval := (G.box q).flow.interval.out ha hb
  have htime : Icc a b ⊆ F.time_domain := fun t ht =>
    H.time_subset (m33BoxIntervalSubset G q (hbox ht))
  have hfinite : (F.surgery_times ∩ Ioc a b).Finite :=
    (F.surgery_times_finite_on_compact isCompact_Icc htime).subset
      (fun _ ht => ⟨ht.1, ht.2.1.le, ht.2.2⟩)
  have hQa : Q a := fun _ => hpos
  have hQb : Q b := by
    apply finite_event_forward_induction hab hfinite Q hQa
    · intro s hs t ht hst hfree hQs htbox
      rcases lt_or_eq_of_le hst with hlt | rfl
      · have hsmall : Icc s t ⊆ F.time_domain := fun u hu =>
          htime ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩
        have hsbox := hbox hs
        have hp := positive_component_regular_transport F hlt hsmall hfree
          ⟨s, ⟨le_rfl, hst⟩⟩ ⟨t, ⟨hst, le_rfl⟩⟩ hst
          (H.forward s (m33BoxIntervalSubset G q hsbox) ((G.box q).forward s hsbox x))
          (hQs hsbox)
        have heq := H.slab_compatibility q s t hlt hsmall hfree s t
          ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hsbox htbox x
        exact heq ▸ hp
      · exact hQs htbox
    · intro t ht hbefore htbox
      let y := H.forward t (m33BoxIntervalSubset G q htbox) ((G.box q).forward t htbox x)
      let : Nonempty (F.slice t).carrier := ⟨y⟩
      let event := F.event t ht.1
      obtain ⟨v, hv, hvt⟩ := exists_between
        (max_lt ht.2.1 event.tMinus_lt)
      have hav : a < v := (le_max_left _ _).trans_lt hv
      have hvm : event.tMinus < v := (le_max_right _ _).trans_lt hv
      have hvbox : v ∈ (G.box q).interval := hbox ⟨hav.le, hvt.le.trans ht.2.2⟩
      let z := (event.pre_identify ⟨v, ⟨hvm.le, hvt⟩⟩).symm
        (H.forward v (m33BoxIntervalSubset G q hvbox) ((G.box q).forward v hvbox x))
      have hpv : SurgeryPositiveComponentAt F v
          (event.pre_identify ⟨v, ⟨hvm.le, hvt⟩⟩ z) := by
        simpa only [z, Diffeomorph.apply_symm_apply] using hbefore v ⟨hav.le, hvt⟩ hvbox
      have hz : z ∈ interior event.retained_pre :=
        H.pre_retained_at_surgery q t htbox ht.1 v hvbox ⟨hvm.le, hvt⟩ x
      have hp := positive_component_surgery_from_reference F ht.1
        ⟨v, ⟨hvm.le, hvt⟩⟩ z hpv z ⟨interior_subset hz, mem_connectedComponent⟩
      have heq := H.surgery_compatibility q t htbox ht.1 v hvbox ⟨hvm.le, hvt⟩ x
      exact heq ▸ hp
  exact hQb hb

theorem positive_component_history_box_connected
    {G : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}}
    (H : M33RegularHistoryRealization G F) (q : G.box_index)
    {x y : (G.box q).carrier.carrier} (hxy : y ∈ connectedComponent x)
    {a b : ℝ} (ha : a ∈ (G.box q).interval) (hb : b ∈ (G.box q).interval)
    (hab : a ≤ b)
    (hpos : SurgeryPositiveComponentAt F a
      (H.forward a (m33BoxIntervalSubset G q ha) ((G.box q).forward a ha x))) :
    SurgeryPositiveComponentAt F b
      (H.forward b (m33BoxIntervalSubset G q hb) ((G.box q).forward b hb y)) := by
  have hx := positive_component_history_box_line H q x ha hb hab hpos
  have hc := ((H.forward_smooth b (m33BoxIntervalSubset G q hb)).continuous.comp
    ((G.box q).forward_smooth b hb).continuous).image_connectedComponent_subset x
    (mem_image_of_mem
      (H.forward b (m33BoxIntervalSubset G q hb) ∘ (G.box q).forward b hb) hxy)
  change H.forward b (m33BoxIntervalSubset G q hb) ((G.box q).forward b hb y) ∈
    connectedComponent (H.forward b (m33BoxIntervalSubset G q hb)
      ((G.box q).forward b hb x)) at hc
  intro z hz
  exact hx z (by simpa only [connectedComponent_eq hc] using hz)

end PoincareConjecture.Proofs.M46
