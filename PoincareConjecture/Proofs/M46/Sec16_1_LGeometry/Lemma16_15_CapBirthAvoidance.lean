import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_BirthApproach










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W) {G : FlowBoxRicciGeometry H.generalized}
  {origin T A h c mu theta : ℝ} {center : (F.slice origin).carrier}
  (Q : CapBarrierWindow G (F.slice origin) (F.metric origin) center
    origin T A h c mu theta)



def CapBarrierWindow.earlyInnerTrace : Set G.toLGeometry.Point :=
  {v | ∃ w : (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval origin (h⁻¹ ^ 2) Q.cylinder.scale_pos Q.interval)).Point ×
        Q.source,
    w.2.val ∈ (F.metric origin).ball center (A * h / 2) ∧
    (w.1.val - origin) / h ^ 2 ≤ 1 / 2 ∧ rawCylinderMap G.realization Q.cylinder w = v}




theorem CapBarrierOriginData.birth_capture
    (D : CapBarrierOriginData H Q) (hA : 0 < A) (hh : 0 < h)
    (horigin : origin ∈ H.generalized.interval)
    (y : (H.generalized.slice origin).carrier)
    (hy : H.history.forward origin horigin y ∈ (F.metric origin).ball center (A * h / 2)) :
    ∃ width > 0, Q.earlyInnerTrace ∈
      𝓝[G.realization.spacetime.timeFunction ⁻¹' Ioc origin (origin + width)]
        (⟨origin, y⟩ : H.generalized.point) := by
  have hsq : 0 < h ^ 2 := sq_pos_of_pos hh
  let b := (Q.top - origin) / h ^ 2
  have hb : 0 < b := div_pos (sub_pos.mpr Q.top_gt) hsq
  let d := min (1 / 2) (b / 2)
  have hd : 0 < d := lt_min (by norm_num) (half_pos hb)
  have hdb : d < b := (min_le_right _ _).trans_lt (half_lt_self hb)
  have hdhalf : d ≤ 1 / 2 := min_le_left _ _
  have hopen : IsOpen ((F.metric origin).ball center (A * h / 2)) := by
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : (F.slice origin).carrier → Type _) :=
      ⟨(F.metric origin).toRiemannianMetric⟩
    let : EMetricSpace (F.slice origin).carrier :=
      .ofRiemannianMetric (𝓡 3) (F.slice origin).carrier
    change IsOpen {z | edist center z < ENNReal.ofReal (A * h / 2)}
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  let V : TopologicalSpace.Opens (F.slice origin).carrier :=
    ⟨(F.metric origin).ball center (A * h / 2), hopen⟩
  have hVU : (V : Set (F.slice origin).carrier) ⊆ Q.source := by
    rw [Q.source_eq]
    intro z hz
    exact hz.trans_le (ENNReal.ofReal_le_ofReal (by nlinarith [mul_pos hA hh]))
  have hsmall : Icc 0 d ⊆ Ico 0 ((D.originalTop - origin) / h ^ 2) := by
    intro s hs
    refine ⟨hs.1, (hs.2.trans_lt hdb).trans_le ?_⟩
    exact (div_le_div_iff_of_pos_right hsq).mpr (sub_le_sub_right D.top_le_original origin)
  have hpositive : Ioc 0 d ⊆ Q.interval.domain := by
    rw [D.interval_eq]
    intro s hs
    exact ⟨hs.1, hs.2.trans_lt hdb⟩
  have htime : ∀ s ∈ Icc 0 d, origin + s / (h⁻¹ ^ 2) ∈ H.generalized.interval := by
    intro s hs
    by_cases hz : s = 0
    · simpa only [hz, zero_div, add_zero] using horigin
    · exact D.time_mem s (hpositive ⟨lt_of_le_of_ne hs.1 (Ne.symm hz), hs.2⟩)
  have hnear := capBirth_positiveTrace_mem_nhdsWithin H G.realization D.original Q.cylinder
    hd hVU hsmall hpositive D.interval_subset D.based htime D.time_mem D.forward horigin y hy
  refine ⟨d / (h⁻¹ ^ 2), div_pos hd Q.cylinder.scale_pos, ?_⟩
  apply mem_of_superset hnear
  rintro v ⟨s, hs, z, hz, rfl⟩
  let w : (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval origin (h⁻¹ ^ 2) Q.cylinder.scale_pos Q.interval)).Point ×
        Q.source :=
    ((cylinderClockHomeomorph origin (h⁻¹ ^ 2) Q.cylinder.scale_pos Q.interval).symm
      ⟨s, hpositive hs⟩, ⟨z, hVU hz⟩)
  refine ⟨w, hz, ?_, rawCylinderMap_at_parameter G.realization Q.cylinder _ _⟩
  have hclock : (w.1.val - origin) / h ^ 2 = s := by
    change (parabolicTimeInv (h⁻¹ ^ 2) origin s - origin) / h ^ 2 = s
    simp only [parabolicTimeInv, inv_pow, div_inv_eq_mul, add_sub_cancel_left]
    exact mul_div_cancel_right₀ s hsq.ne'
  rw [hclock]
  exact hs.2.trans hdhalf




theorem CapBarrierOriginData.avoids_birth
    [CompactSpace (F.slice origin).carrier]
    (D : CapBarrierOriginData H Q) (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hmu : 0 < mu) (hA : 0 < A) (hh : 0 < h) (hc : 0 < c) (htheta : theta < 1)
    {budget a tau safeBound : ℝ} (hbudget0 : 0 ≤ budget) (ha : 0 < a)
    (hside : budget / Real.sqrt a < mu * A ^ 2 / 4)
    (htop : budget / Real.sqrt a < -(c / 2) * (Real.log (1 - theta) + Real.log 2))
    (hseparation : safeBound < c / (2 * h ^ 2))
    {x z : G.toLGeometry.Point} (p : M14BackwardPath G.toLGeometry T 0 tau x z)
    (hscalar : horizontalScalarCurvature G.toLGeometry.leafwise (p.curve a) ≤ safeBound)
    (hbudget : (∫ t in 0..tau, Real.sqrt t * pathPositiveDensity p t) ≤ budget)
    {b : ℝ} (hb : b ∈ Ioc a tau) (hclock : T - b = origin)
    (horigin : origin ∈ H.generalized.interval)
    (y : (H.generalized.slice origin).carrier)
    (hy : H.history.forward origin horigin y ∈ (F.metric origin).ball center (A * h / 2)) :
    p.curve b ≠ (⟨origin, y⟩ : H.generalized.point) := by
  intro heq
  obtain ⟨width, hwidth, hnear⟩ := D.birth_capture H Q hA hh horigin y hy
  rw [← heq] at hnear
  obtain ⟨r, hr, w, hinner, hearly, hw⟩ := backwardPath_reaches_future_neighborhood G p
    ha.le hb.1 hb.2 hwidth hclock hnear
  exact Q.avoids_early_inner hM12 hmu hA hh hc htheta hbudget0 ha hside htop
    hseparation p hscalar hbudget ⟨hr.1, hr.2.le.trans hb.2⟩ w hinner hearly hw.symm

end PoincareConjecture.Proofs.M46
