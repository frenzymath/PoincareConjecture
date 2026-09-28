import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveFlowPieces
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.FiniteEventInduction
import PoincareConjecture.Proofs.M33.RegularHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

theorem positive_component_cylinder_line
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale I U) {x : C.carrier} (hx : x ∈ U)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b)
    (hpos : SurgeryPositiveComponentAt F (origin + a / scale) (e.forward a ha x)) :
    SurgeryPositiveComponentAt F (origin + b / scale) (e.forward b hb x) := by
  have hclock : origin + a / scale ≤ origin + b / scale :=
    add_le_add le_rfl ((div_le_div_iff_of_pos_right e.scale_pos).mpr hab)
  have hparam : ∀ t ∈ Icc (origin + a / scale) (origin + b / scale),
      ∃ s ∈ I, origin + s / scale = t := by
    intro t ht
    let s := scale * (t - origin)
    have heq : origin + s / scale = t := by
      dsimp [s]
      field_simp [e.scale_pos.ne']
      ring
    refine ⟨s, e.interval_connected.out ha hb ⟨?_, ?_⟩, heq⟩
    · apply (div_le_div_iff_of_pos_right e.scale_pos).mp
      linarith only [ht.1, heq]
    · apply (div_le_div_iff_of_pos_right e.scale_pos).mp
      linarith only [ht.2, heq]
  have htime : Icc (origin + a / scale) (origin + b / scale) ⊆ F.time_domain := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := hparam t ht
    exact e.time_subset (mem_image_of_mem _ hs)
  let Q : ℝ → Prop := fun t => ∀ s (hs : s ∈ I), origin + s / scale = t →
    SurgeryPositiveComponentAt F (origin + s / scale) (e.forward s hs x)
  have hQa : Q (origin + a / scale) := by
    intro s hs heq
    have : s = a := (div_left_inj' e.scale_pos.ne').mp (by linarith)
    subst s
    exact hpos
  have hfinite : (F.surgery_times ∩
      Ioc (origin + a / scale) (origin + b / scale)).Finite :=
    (F.surgery_times_finite_on_compact isCompact_Icc htime).subset
      (fun _ ht => ⟨ht.1, ht.2.1.le, ht.2.2⟩)
  have hQb : Q (origin + b / scale) := by
    apply finite_event_forward_induction hclock hfinite Q hQa
    · intro s hs t ht hst hfree hQs v hv heq
      obtain ⟨w, hw, rfl⟩ := hparam s hs
      subst t
      rcases lt_or_eq_of_le hst with hlt | heq
      · have hsmall : Icc (origin + w / scale) (origin + v / scale) ⊆
            F.time_domain := fun u hu => htime ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩
        have hp := positive_component_regular_transport F hlt hsmall hfree
          ⟨origin + w / scale, ⟨le_rfl, hst⟩⟩
          ⟨origin + v / scale, ⟨hst, le_rfl⟩⟩ hst (e.forward w hw x) (hQs w hw rfl)
        have hmap := e.slab_compatibility _ _ hlt hsmall hfree w hw v hv
          ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ x hx
        exact hmap ▸ hp
      · exact hQs v hv heq.symm
    · intro t ht hbefore s hs heq
      subst t
      let : Nonempty (F.slice (origin + s / scale)).carrier := ⟨e.forward s hs x⟩
      let event := F.event (origin + s / scale) ht.1
      obtain ⟨v, hv, hvt⟩ := exists_between
        (max_lt ht.2.1 event.tMinus_lt)
      have hav : origin + a / scale < v := (le_max_left _ _).trans_lt hv
      have hvm : event.tMinus < v := (le_max_right _ _).trans_lt hv
      obtain ⟨w, hw, rfl⟩ := hparam v ⟨hav.le, hvt.le.trans ht.2.2⟩
      let z := (event.pre_identify ⟨origin + w / scale, ⟨hvm.le, hvt⟩⟩).symm
        (e.forward w hw x)
      have hpv : SurgeryPositiveComponentAt F (origin + w / scale)
          (event.pre_identify ⟨origin + w / scale, ⟨hvm.le, hvt⟩⟩ z) := by
        simpa only [z, Diffeomorph.apply_symm_apply] using
          hbefore (origin + w / scale) ⟨hav.le, hvt⟩ w hw rfl
      have hz : z ∈ interior event.retained_pre :=
        e.pre_retained_at_surgery s hs ht.1 w hw ⟨hvm.le, hvt⟩ x hx
      have hp := positive_component_surgery_from_reference F ht.1
        ⟨origin + w / scale, ⟨hvm.le, hvt⟩⟩ z hpv z
        ⟨interior_subset hz, mem_connectedComponent⟩
      have hmap := e.surgery_compatibility s hs ht.1 w hw ⟨hvm.le, hvt⟩ x hx
      exact hmap ▸ hp
  exact hQb b hb rfl

end PoincareConjecture.Proofs.M46
