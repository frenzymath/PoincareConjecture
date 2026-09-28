import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_21_CompactOrdinaryTrace
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_FullAvoidance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

theorem basedCylinder_ordinary_forward
    {F : SurgeryFlowData.{u}} {origin top scale : ℝ} {I : Set ℝ}
    {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale I U)
    (hzero : (0 : ℝ) ∈ I) (hbase : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (htop : origin < top) (hJ : Icc origin top ⊆ F.time_domain)
    (hNo : Disjoint F.surgery_times (Ioc origin top))
    {s : ℝ} (hs : s ∈ I) (hs0 : 0 ≤ s)
    (hphysical : origin + s / scale ∈ Icc origin top)
    {x : (F.slice origin).carrier} (hx : x ∈ U) :
    e.forward s hs x = (F.regular_slabs origin top htop hJ hNo).identify
      ⟨origin + s / scale, hphysical⟩ x := by
  have htime : ∀ r ∈ Icc 0 s, origin + r / scale ∈ Icc origin top := by
    intro r hr
    refine ⟨by linarith [div_nonneg hr.1 e.scale_pos.le], ?_⟩
    exact (add_le_add_right ((div_le_div_iff_of_pos_right e.scale_pos).mpr hr.2)
      origin).trans hphysical.2
  let ordinary := F.regularCylinder htop hJ hNo e.scale_pos ordConnected_Icc htime U
  have hinit : e.forward 0 hzero x = ordinary.forward 0 ⟨le_rfl, hs0⟩ x :=
    eq_of_heq ((hbase hzero x hx).trans
      (F.regularCylinder_initial htop hJ hNo e.scale_pos ordConnected_Icc htime U
        ⟨le_rfl, hs0⟩ x).symm)
  have hclock0 : origin + 0 / scale ∈ Icc origin top := by simpa using htime 0 ⟨le_rfl, hs0⟩
  have h1 := e.slab_compatibility origin top htop hJ hNo 0 hzero s hs
    hclock0 hphysical x hx
  have h2 := ordinary.slab_compatibility origin top htop hJ hNo
    0 ⟨le_rfl, hs0⟩ s ⟨hs0, le_rfl⟩ hclock0 hphysical x hx
  rw [hinit] at h1
  exact h1.symm.trans h2

theorem CapBarrierOriginData.ordinary_forward
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {G : FlowBoxRicciGeometry H.generalized}
    {origin T A h c mu theta : ℝ} {center : (F.slice origin).carrier}
    (Q : CapBarrierWindow G (F.slice origin) (F.metric origin) center
      origin T A h c mu theta)
    (D : CapBarrierOriginData H Q) (hh : 0 < h)
    {top : ℝ} (htop : origin < top) (hJ : Icc origin top ⊆ F.time_domain)
    (hNo : Disjoint F.surgery_times (Ioc origin top))
    {s : ℝ} (hs : s ∈ Q.interval.domain)
    (hphysical : origin + s / (h⁻¹ ^ 2) ∈ Icc origin top)
    {x : (F.slice origin).carrier} (hx : x ∈ Q.source) :
    H.history.forward (origin + s / (h⁻¹ ^ 2)) (D.time_mem s hs)
      (Q.cylinder.forward s hs x) =
        (F.regular_slabs origin top htop hJ hNo).identify
          ⟨origin + s / (h⁻¹ ^ 2), hphysical⟩ x := by
  rw [D.forward s hs x hx]
  have hzero : (0 : ℝ) ∈ Ico 0 ((D.originalTop - origin) / h ^ 2) :=
    ⟨le_rfl, div_pos (sub_pos.mpr (Q.top_gt.trans_le D.top_le_original)) (sq_pos_of_pos hh)⟩
  exact basedCylinder_ordinary_forward D.original hzero D.based htop hJ hNo
    (D.interval_subset hs) (D.interval_subset hs).1 hphysical hx

theorem CapBarrierOriginData.ordinary_coordinate_not_inner
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {G : FlowBoxRicciGeometry H.generalized}
    {origin T A h c mu theta : ℝ} {center : (F.slice origin).carrier}
    (Q : CapBarrierWindow G (F.slice origin) (F.metric origin) center
      origin T A h c mu theta)
    (D : CapBarrierOriginData H Q) (hA : 0 < A) (hh : 0 < h)
    {top : ℝ} (htop : origin < top) (hJ : Icc origin top ⊆ F.time_domain)
    (hNo : Disjoint F.surgery_times (Ioc origin top))
    {s : ℝ} (hs : s ∈ Q.interval.domain) (hearly : s ≤ 1 / 2)
    (hphysical : origin + s / (h⁻¹ ^ 2) ∈ Icc origin top)
    (y : (H.generalized.slice (origin + s / (h⁻¹ ^ 2))).carrier)
    (hout : (⟨origin + s / (h⁻¹ ^ 2), y⟩ : H.generalized.point) ∉ Q.earlyInnerTrace) :
    ((F.regular_slabs origin top htop hJ hNo).identify
      ⟨origin + s / (h⁻¹ ^ 2), hphysical⟩).symm
        (H.history.forward (origin + s / (h⁻¹ ^ 2)) (D.time_mem s hs) y) ∉
      (F.metric origin).ball center (A * h / 2) := by
  intro hinner
  let S := F.regular_slabs origin top htop hJ hNo
  let x := (S.identify ⟨origin + s / (h⁻¹ ^ 2), hphysical⟩).symm
    (H.history.forward (origin + s / (h⁻¹ ^ 2)) (D.time_mem s hs) y)
  have hx : x ∈ Q.source := by
    change x ∈ (Q.source : Set (F.slice origin).carrier)
    rw [Q.source_eq]
    exact hinner.trans_le (ENNReal.ofReal_le_ofReal (by nlinarith [mul_pos hA hh]))
  have heq : Q.cylinder.forward s hs x = y := by
    apply (H.history.forward_openEmbedding _ (D.time_mem s hs)).injective
    rw [D.ordinary_forward H Q hh htop hJ hNo hs hphysical hx]
    exact (S.identify ⟨origin + s / (h⁻¹ ^ 2), hphysical⟩).apply_symm_apply _
  let w : (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval origin (h⁻¹ ^ 2) Q.cylinder.scale_pos Q.interval)).Point ×
        Q.source :=
    ((cylinderClockHomeomorph origin (h⁻¹ ^ 2) Q.cylinder.scale_pos Q.interval).symm
      ⟨s, hs⟩, ⟨x, hx⟩)
  apply hout
  refine ⟨w, hinner, ?_, ?_⟩
  · have hclock : (w.1.val - origin) / h ^ 2 = s := by
      change (parabolicTimeInv (h⁻¹ ^ 2) origin s - origin) / h ^ 2 = s
      simp only [parabolicTimeInv, inv_pow, div_inv_eq_mul, add_sub_cancel_left]
      exact mul_div_cancel_right₀ s (sq_pos_of_pos hh).ne'
    exact hclock ▸ hearly
  · rw [rawCylinderMap_at_parameter]
    exact congrArg (fun z => (⟨origin + s / (h⁻¹ ^ 2), z⟩ : H.generalized.point)) heq

end PoincareConjecture.Proofs.M46
