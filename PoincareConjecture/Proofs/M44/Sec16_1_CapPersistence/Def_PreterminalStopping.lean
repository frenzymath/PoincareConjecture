import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_RetainedCylinderExtension
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_LaterSurgery











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale c : ℝ} {U : Set C.carrier}




theorem exists_preterminal_parameter (hscale : 0 < scale) (hc : 0 < c)
    {tMinus : ℝ} (hminus : tMinus < origin + c / scale) :
    ∃ r ∈ Ico 0 c, origin + r / scale ∈ Ico tMinus (origin + c / scale) := by
  have horigin : origin < origin + c / scale := by linarith [div_pos hc hscale]
  obtain ⟨t, ht, hT⟩ := exists_between (max_lt horigin hminus)
  let r := (t - origin) * scale
  have hr0 : 0 ≤ r := mul_nonneg (sub_nonneg.mpr (le_max_left origin tMinus |>.trans ht.le))
    hscale.le
  have hclock : origin + r / scale = t := by
    dsimp [r]
    field_simp
    ring
  have hrc : r < c := by
    apply (div_lt_div_iff_of_pos_right hscale).mp
    linarith
  exact ⟨r, ⟨hr0, hrc⟩, by rw [hclock]; exact ⟨(le_max_right _ _).trans ht.le, hT⟩⟩




theorem exists_fixed_lost_line
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (hpre : Disjoint F.surgery_times
      (Ioo (F.event (origin + c / scale) hT).tMinus (origin + c / scale)))
    (r : ℝ) (hr : r ∈ Ico 0 c)
    (hr' : origin + r / scale ∈
      Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale))
    (hlost : ¬ ∀ x ∈ U, ((F.event (origin + c / scale) hT).pre_identify
      ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x) ∈
        interior (F.event (origin + c / scale) hT).retained_pre) :
    ∃ x ∈ U, ∀ s (hs : s ∈ Ico 0 c),
      ∀ ht : origin + s / scale ∈
        Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale),
        ((F.event (origin + c / scale) hT).pre_identify
          ⟨origin + s / scale, ht⟩).symm (e.forward s hs x) ∉
            interior (F.event (origin + c / scale) hT).retained_pre := by
  push Not at hlost
  obtain ⟨x, hx, hlost⟩ := hlost
  refine ⟨x, hx, ?_⟩
  intro s hs ht
  rw [cylinder_preterminal_coordinates_eq e hT hpre s hs r hr ht hr' x hx]
  exact hlost





theorem exists_lost_line_of_no_extension
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U)
    (hU : IsOpen U) (hc : 0 < c) {d : ℝ} (hcd : c < d)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (hJ : Ico (origin + c / scale) (origin + d / scale) ⊆ F.time_domain)
    (hNo : Disjoint F.surgery_times (Ioo (origin + c / scale) (origin + d / scale)))
    (hstop : ¬ Nonempty (SurgeryFlowCylinder F C origin scale (Ico 0 d) U)) :
    ∃ x ∈ U, ∀ s (hs : s ∈ Ico 0 c),
      ∀ ht : origin + s / scale ∈
        Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale),
        ((F.event (origin + c / scale) hT).pre_identify
          ⟨origin + s / scale, ht⟩).symm (e.forward s hs x) ∉
            interior (F.event (origin + c / scale) hT).retained_pre := by
  obtain ⟨r, hr, hr'⟩ := exists_preterminal_parameter e.scale_pos hc
    (F.event (origin + c / scale) hT).tMinus_lt
  have hpre := event_preterminal_surgery_free P F hpinch hT
  apply exists_fixed_lost_line e hT hpre r hr hr'
  intro hret
  obtain ⟨e', _⟩ := exists_cylinder_across_retained_event e hU hc hcd hT hpre hJ hNo
    r hr hr' hret
  exact hstop ⟨e'⟩




theorem disappears_of_fixed_lost_line
    {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U)
    (hc : 0 < c) (hU : IsPreconnected U)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (hinitial : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (hlost : ∃ x ∈ U, ∀ s (hs : s ∈ Ico 0 c),
      ∀ ht : origin + s / scale ∈
        Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale),
        ((F.event (origin + c / scale) hT).pre_identify
          ⟨origin + s / scale, ht⟩).symm (e.forward s hs x) ∉
            interior (F.event (origin + c / scale) hT).retained_pre)
    (havoid : ∀ s (hs : s ∈ Ico 0 c),
      ∀ ht : origin + s / scale ∈
        Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale),
      ∀ i, Disjoint
        ((fun x => ((F.event (origin + c / scale) hT).pre_identify
          ⟨origin + s / scale, ht⟩).symm (e.forward s hs x)) '' U)
        ((F.event (origin + c / scale) hT).limit_identify.inverse ''
          ((F.event (origin + c / scale) hT).necks i).neck.central_sphere)) :
    SurgeryBallDisappearsAt F e (origin + c / scale) := by
  obtain ⟨x, hx, hlost⟩ := hlost
  apply e.disappears_of_late_neck_avoidance hT hinitial (hs0 := ⟨le_rfl, hc⟩)
  intro s hs _ ht
  exact ⟨e.preterminal_image_preconnected hU hT s hs ht, havoid s hs ht,
    ⟨_, mem_image_of_mem _ hx, hlost s hs ht⟩⟩

end PoincareConjecture.M44
