import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_EventNeighborhood
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_OrdinaryCylinderExtension









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47



theorem exists_cap_cylinder_across_ordinary_endpoint
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale c : ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 c) U)
    (hU : IsOpen U) (hc : 0 < c) (O : SurgeryObservation F)
    (htH : origin + c / scale < O.H)
    (hnot : origin + c / scale ∉ F.surgery_times) :
    ∃ d : ℝ, c < d ∧ origin + d / scale < O.H ∧
      ∃ e' : SurgeryFlowCylinder F C origin scale (Ico 0 d) U,
        ∀ s (hs : s ∈ Ico 0 c) (hs' : s ∈ Ico 0 d) x,
          e'.forward s hs' x = e.forward s hs x := by
  have horigin : origin ∈ F.time_domain := by
    simpa only [zero_div, add_zero] using
      e.time_subset (mem_image_of_mem _ (show (0 : ℝ) ∈ Ico 0 c from ⟨le_rfl, hc⟩))
  have hlow : origin < origin + c / scale := lt_add_of_pos_right _ (div_pos hc e.scale_pos)
  have htime : origin + c / scale ∈ F.time_domain :=
    O.interval_subset ⟨(F.time_domain_nonnegative horigin).trans hlow.le, htH⟩
  obtain ⟨a, b, h0a, hat, htb, hbH, hfree⟩ :=
    M44.exists_surgery_free_closed_neighborhood F htime hlow htH hnot
  let clock : ℝ ≃o ℝ :=
    (OrderIso.divRight₀ scale e.scale_pos).trans (OrderIso.addLeft origin)
  change a < clock c at hat
  change clock c < b at htb
  let r := clock.symm a
  let d := clock.symm b
  have hr0 : 0 < r := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [r, OrderIso.apply_symm_apply, clock, OrderIso.trans_apply,
      OrderIso.divRight₀_apply, OrderIso.addLeft_apply, zero_div, add_zero] using h0a
  have hrc : r < c := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [r, OrderIso.apply_symm_apply] using hat
  have hcd : c < d := by
    apply clock.strictMono.lt_iff_lt.mp
    simpa only [d, OrderIso.apply_symm_apply] using htb
  have hdH : origin + d / scale < O.H := by
    change clock d < O.H
    simpa only [d, OrderIso.apply_symm_apply] using hbH
  have hJ : Ico (clock r) (clock d) ⊆ F.time_domain := by
    rw [show clock r = a from clock.apply_symm_apply a,
      show clock d = b from clock.apply_symm_apply b]
    intro s hs
    exact O.interval_subset
      ⟨(F.time_domain_nonnegative horigin).trans (h0a.le.trans hs.1), hs.2.trans hbH⟩
  have hNo : Disjoint F.surgery_times (Ioo (clock r) (clock d)) := by
    simpa only [r, d, OrderIso.apply_symm_apply] using hfree.mono_right Ioo_subset_Icc_self
  obtain ⟨e', same⟩ := M44.exists_cylinder_through_ordinary_endpoint e hU hcd
    r ⟨hr0.le, hrc⟩ hJ hNo
  exact ⟨d, hcd, hdH, e', same⟩

end PoincareConjecture.M47
