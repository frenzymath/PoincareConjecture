import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_FullAvoidance









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.M47

open Proofs.M12 Proofs.M46



theorem seedRetained_avoids_early_cap
    {F : GeneralizedRicciFlowData.{u}} {G : FlowBoxRicciGeometry F}
    {C : GeneralizedSliceCarrier.{u}} [CompactSpace C.carrier]
    {gBirth : RiemannianMetric 3 C.carrier} {center : C.carrier}
    {origin T A h c mu theta : ℝ}
    (Q : CapBarrierWindow G C gBirth center origin T A h c mu theta)
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hmu : 0 < mu) (hA : 0 < A) (hh : 0 < h) (hc : 0 < c) (htheta : theta < 1)
    {budget a tau : ℝ} (hbudget0 : 0 ≤ budget) (ha : 0 < a)
    (hside : budget / Real.sqrt a < mu * A ^ 2 / 4)
    (htop : budget / Real.sqrt a < -(c / 2) * (Real.log (1 - theta) + Real.log 2))
    (hclock : Q.top ≤ T - a)
    {x y : G.toLGeometry.Point} (p : M14BackwardPath G.toLGeometry T 0 tau x y)
    (hbudget : (∫ t in 0..tau, Real.sqrt t * pathPositiveDensity p t) ≤ budget)
    {b : ℝ} (hb : b ∈ Icc 0 tau)
    (w : (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval origin (h⁻¹ ^ 2) Q.cylinder.scale_pos Q.interval)).Point ×
        Q.source)
    (hinner : w.2.val ∈ gBirth.ball center (A * h / 2))
    (hinnerTime : (w.1.val - origin) / h ^ 2 ≤ 1 / 2) :
    p.curve b ≠ rawCylinderMap G.realization Q.cylinder w := by
  have hout (s : ℝ) (hs : s ∈ Icc 0 tau) (hsa : s ≤ a) :
      p.curve s ∉ range (rawCylinderMap G.realization Q.cylinder) := by
    rintro ⟨z, hz⟩
    have hztime : z.1.val ∈ Ioo origin Q.top := Q.physical_eq ▸ z.1.property
    have heq := congrArg G.realization.spacetime.timeFunction hz
    rw [rawCylinderMap_time] at heq
    have hp : G.realization.spacetime.timeFunction (p.curve s) = T - s := p.curve_time s hs
    rw [hp] at heq
    linarith only [hztime.2, hclock, hsa, heq]
  intro heq
  by_cases hba : b ≤ a
  · exact hout b hb hba ⟨w, heq.symm⟩
  · have hab : a < b := lt_of_not_ge hba
    have hwidth : Q.top - origin ≤ h ^ 2 := by
      nlinarith [Q.top_le_model, sq_nonneg h]
    obtain ⟨r, hr, hentry⟩ := exists_actualTruncatedCapEntry_action_gt G hM12 Q.cylinder
      Q.time_subset gBirth Q.physical_eq hmu hA hh hc htheta hwidth hside htop
      Q.metric_lower Q.scalar_lower center Q.source_eq p Q.top_kind ha hab hb.2
      (hout a ⟨ha.le, hab.le.trans hb.2⟩ le_rfl) w heq hinner hinnerTime
    have hroot : budget / Real.sqrt r ≤ budget / Real.sqrt a :=
      div_le_div_of_nonneg_left hbudget0 (Real.sqrt_pos.mpr ha) (Real.sqrt_le_sqrt hr.1)
    have hweighted := weightedAction_gt_of_tail (ha.trans_le hr.1) hr.2.le hb.2
      (pathPositiveDensity_nonneg p) (pathPositiveAction_integrable hM12 p)
      (pathPositiveDensity_tail_integrable hM12 p (ha.trans_le hr.1) hr.2.le hb.2)
      (hroot.trans_lt hentry)
    exact (not_lt_of_ge hbudget) hweighted



theorem seedRetained_avoids_cap_birth
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {G : FlowBoxRicciGeometry H.generalized}
    {origin T A h c mu theta : ℝ} {center : (F.slice origin).carrier}
    (Q : CapBarrierWindow G (F.slice origin) (F.metric origin) center
      origin T A h c mu theta)
    [CompactSpace (F.slice origin).carrier]
    (D : CapBarrierOriginData H Q) (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hmu : 0 < mu) (hA : 0 < A) (hh : 0 < h) (hc : 0 < c) (htheta : theta < 1)
    {budget a tau : ℝ} (hbudget0 : 0 ≤ budget) (ha : 0 < a)
    (hside : budget / Real.sqrt a < mu * A ^ 2 / 4)
    (htop : budget / Real.sqrt a < -(c / 2) * (Real.log (1 - theta) + Real.log 2))
    (htopTime : Q.top ≤ T - a)
    {x z : G.toLGeometry.Point} (p : M14BackwardPath G.toLGeometry T 0 tau x z)
    (hbudget : (∫ t in 0..tau, Real.sqrt t * pathPositiveDensity p t) ≤ budget)
    {b : ℝ} (hb : b ∈ Ioc 0 tau) (hclock : T - b = origin)
    (horigin : origin ∈ H.generalized.interval)
    (y : (H.generalized.slice origin).carrier)
    (hy : H.history.forward origin horigin y ∈ (F.metric origin).ball center (A * h / 2)) :
    p.curve b ≠ (⟨origin, y⟩ : H.generalized.point) := by
  intro heq
  obtain ⟨width, hwidth, hnear⟩ := D.birth_capture H Q hA hh horigin y hy
  rw [← heq] at hnear
  obtain ⟨r, hr, w, hinner, hearly, hw⟩ := backwardPath_reaches_future_neighborhood G p
    le_rfl hb.1 hb.2 hwidth hclock hnear
  exact seedRetained_avoids_early_cap Q hM12 hmu hA hh hc htheta hbudget0 ha
    hside htop htopTime p hbudget ⟨hr.1.le, hr.2.le.trans hb.2⟩ w hinner hearly hw.symm

end PoincareConjecture.M47
