import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_MaximalCylinder
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_EventNeighborhood
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_OrdinaryCylinderExtension










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44

variable {F : SurgeryFlowData.{u}} {origin scale c B : ℝ}
  {U : Set (F.slice origin).carrier}




theorem maximal_cylinder_endpoint_is_surgery
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U)
    (hU : IsOpen U) (hc : 0 < c) (hcB : c < B)
    (htime : ∀ s ∈ Ico 0 B, origin + s / scale ∈ F.time_domain)
    (hinitial : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (hstop : ∀ d : ℝ, c < d → d ≤ B →
      ¬ ∃ E : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 d) U,
        ∀ h x, x ∈ U → HEq (E.forward 0 h x) x) :
    origin + c / scale ∈ F.surgery_times := by
  classical
  by_contra hnot
  let clock : ℝ ≃o ℝ :=
    (OrderIso.divRight₀ scale e.scale_pos).trans (OrderIso.addLeft origin)
  have hTc : clock c ∈ F.time_domain := htime c ⟨hc.le, hcB⟩
  obtain ⟨a, b, h0a, haT, hTb, hbB, hfree⟩ :=
    exists_surgery_free_closed_neighborhood F hTc (clock.strictMono hc)
      (clock.strictMono hcB) hnot
  let r := clock.symm a
  let d := clock.symm b
  have hr0 : 0 < r := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [r, OrderIso.apply_symm_apply] using h0a
  have hrc : r < c := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [r, OrderIso.apply_symm_apply] using haT
  have hcd : c < d := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [d, OrderIso.apply_symm_apply] using hTb
  have hdB : d < B := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [d, OrderIso.apply_symm_apply] using hbB
  have hK : Ico (clock r) (clock d) ⊆ F.time_domain :=
    Ico_subset_Icc_self.trans (F.time_domain_interval.out
      (htime r ⟨hr0.le, hrc.trans hcB⟩) (htime d ⟨hc.le.trans hcd.le, hdB⟩))
  have hNo : Disjoint F.surgery_times (Ioo (clock r) (clock d)) := by
    simpa only [r, d, OrderIso.apply_symm_apply] using hfree.mono_right Ioo_subset_Icc_self
  obtain ⟨E, hagree⟩ := exists_cylinder_through_ordinary_endpoint e hU hcd
    r ⟨hr0.le, hrc⟩ hK hNo
  apply hstop d hcd hdB.le
  refine ⟨E, ?_⟩
  intro h x hx
  rw [hagree 0 ⟨le_rfl, hc⟩ h x]
  exact hinitial _ x hx




theorem maximal_cylinder_has_fixed_lost_line
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U)
    (hU : IsOpen U) (hc : 0 < c) (hcB : c < B)
    (htime : ∀ s ∈ Ico 0 B, origin + s / scale ∈ F.time_domain)
    (hinitial : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (hstop : ∀ d : ℝ, c < d → d ≤ B →
      ¬ ∃ E : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 d) U,
        ∀ h x, x ∈ U → HEq (E.forward 0 h x) x)
    (hT : origin + c / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + c / scale)).carrier] :
    ∃ x ∈ U, ∀ s (hs : s ∈ Ico 0 c),
      ∀ ht : origin + s / scale ∈
        Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale),
        ((F.event (origin + c / scale) hT).pre_identify
          ⟨origin + s / scale, ht⟩).symm (e.forward s hs x) ∉
            interior (F.event (origin + c / scale) hT).retained_pre := by
  let clock : ℝ ≃o ℝ :=
    (OrderIso.divRight₀ scale e.scale_pos).trans (OrderIso.addLeft origin)
  obtain ⟨b, hcb, hbB, hfree⟩ := exists_surgery_free_right_interval F
    (htime c ⟨hc.le, hcB⟩) (clock.strictMono hcB)
  change clock c < b at hcb
  change Disjoint F.surgery_times (Ioc (clock c) b) at hfree
  let d := clock.symm b
  have hcd : c < d := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [d, OrderIso.apply_symm_apply] using hcb
  have hdB : d < B := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [d, OrderIso.apply_symm_apply] using hbB
  have hJ : Ico (clock c) (clock d) ⊆ F.time_domain :=
    Ico_subset_Icc_self.trans (F.time_domain_interval.out
      (htime c ⟨hc.le, hcB⟩) (htime d ⟨hc.le.trans hcd.le, hdB⟩))
  have hNo : Disjoint F.surgery_times (Ioo (clock c) (clock d)) := by
    simpa only [d, OrderIso.apply_symm_apply] using hfree.mono_right Ioo_subset_Ioc_self
  obtain ⟨r, hr, hr'⟩ := exists_preterminal_parameter e.scale_pos hc
    (F.event (origin + c / scale) hT).tMinus_lt
  have hpre := event_preterminal_surgery_free P F hpinch hT
  apply exists_fixed_lost_line e hT hpre r hr hr'
  intro hret
  obtain ⟨E, hagree, _⟩ := exists_cylinder_across_retained_event e hU hc hcd hT hpre
    hJ hNo r hr hr' hret
  apply hstop d hcd hdB.le
  refine ⟨E, ?_⟩
  intro h x hx
  rw [hagree 0 ⟨le_rfl, hc⟩ h x]
  exact hinitial _ x hx

end PoincareConjecture.M44
