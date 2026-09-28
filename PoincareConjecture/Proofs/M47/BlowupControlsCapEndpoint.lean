import PoincareConjecture.Proofs.M47.BlowupControlsCapRetained
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_EventNeighborhood
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_RetainedCylinderExtension

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

theorem exists_cap_cylinder_across_retained_endpoint
    (P : M44CapPersistencePredecessors.{u})
    {F : SurgeryFlowData.{u}} (hpinch : SurgeryFlowPinched F)
    {origin scale c : ℝ} {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U)
    (hU : IsOpen U) (hc : 0 < c) (O : SurgeryObservation F)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier]
    (htH : origin + c / scale < O.H)
    (r : ℝ) (hr : r ∈ Ico 0 c)
    (hr' : origin + r / scale ∈
      Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale))
    (hretained : ∀ x ∈ U, ((F.event (origin + c / scale) hT).pre_identify
      ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x) ∈
        interior (F.event (origin + c / scale) hT).retained_pre) :
    ∃ d : ℝ, c < d ∧ origin + d / scale < O.H ∧
      ∃ e' : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 d) U,
        (∀ s (hs : s ∈ Ico 0 c) (hs' : s ∈ Ico 0 d) x,
          e'.forward s hs' x = e.forward s hs x) ∧
        ∀ (hd : c ∈ Ico 0 d) x,
          e'.forward c hd x = (F.event (origin + c / scale) hT).retention.map
            (((F.event (origin + c / scale) hT).pre_identify
              ⟨origin + r / scale, hr'⟩).symm (e.forward r hr x)) := by
  have htime := F.surgery_times_subset hT
  obtain ⟨b, htb, hbH, hfree⟩ := M44.exists_surgery_free_right_interval F htime htH
  let d := (b - origin) * scale
  have hclock : origin + d / scale = b := by
    dsimp only [d]
    rw [mul_div_cancel_right₀ _ e.scale_pos.ne']
    ring
  have hcd : c < d := by
    have h := (div_lt_iff₀ e.scale_pos).mp (show c / scale < b - origin by linarith)
    simpa only [d, mul_comm] using h
  have hpost : Ico (origin + c / scale) (origin + d / scale) ⊆ F.time_domain := by
    rw [hclock]
    intro t ht
    exact O.interval_subset ⟨(F.time_domain_nonnegative htime).trans ht.1, ht.2.trans hbH⟩
  have hpostFree : Disjoint F.surgery_times (Ioo (origin + c / scale) (origin + d / scale)) := by
    rw [hclock]
    exact hfree.mono_right Ioo_subset_Ioc_self
  obtain ⟨e', same, endpoint⟩ := M44.exists_cylinder_across_retained_event e hU hc hcd hT
    (M44.event_preterminal_surgery_free P F hpinch hT) hpost hpostFree r hr hr' hretained
  refine ⟨d, hcd, by rwa [hclock], e', same, ?_⟩
  intro hd x
  exact endpoint x

end PoincareConjecture.M47
