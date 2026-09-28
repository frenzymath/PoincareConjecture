import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_CapBarrierWindow










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

variable {F : GeneralizedRicciFlowData.{u}} {G : FlowBoxRicciGeometry F}
  {C : GeneralizedSliceCarrier.{u}} {gBirth : RiemannianMetric 3 C.carrier}
  {center : C.carrier} {origin T A h c mu theta : ℝ}



theorem CapBarrierWindow.scalar_birth_lower
    (Q : CapBarrierWindow G C gBirth center origin T A h c mu theta)
    (hh : 0 < h) (hc : 0 < c) (htheta : theta < 1)
    (w : (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval origin (h⁻¹ ^ 2) Q.cylinder.scale_pos Q.interval)).Point ×
        Q.source) :
    c / (2 * h ^ 2) ≤ horizontalScalarCurvature G.toLGeometry.leafwise
      (rawCylinderMap G.realization Q.cylinder w) := by
  have ht : w.1.val ∈ Ioo origin Q.top := Q.physical_eq ▸ w.1.property
  have hsq : 0 < h ^ 2 := sq_pos_of_pos hh
  have hs0 : 0 ≤ (w.1.val - origin) / h ^ 2 := div_nonneg (by linarith [ht.1]) hsq.le
  have hs1 : (w.1.val - origin) / h ^ 2 < 1 := by
    apply (div_lt_iff₀ hsq).mpr
    nlinarith [ht.2, Q.top_le_model]
  have hden : 0 < 2 * (1 - (w.1.val - origin) / h ^ 2) * h ^ 2 := by positivity
  apply (div_le_div_of_nonneg_left hc.le hden ?_).trans (Q.scalar_lower w)
  nlinarith [mul_nonneg hs0 hsq.le]




theorem CapBarrierWindow.avoids_early_inner
    [CompactSpace C.carrier]
    (Q : CapBarrierWindow G C gBirth center origin T A h c mu theta)
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hmu : 0 < mu) (hA : 0 < A) (hh : 0 < h) (hc : 0 < c) (htheta : theta < 1)
    {budget a tau safeBound : ℝ} (hbudget0 : 0 ≤ budget) (ha : 0 < a)
    (hside : budget / Real.sqrt a < mu * A ^ 2 / 4)
    (htop : budget / Real.sqrt a < -(c / 2) * (Real.log (1 - theta) + Real.log 2))
    (hseparation : safeBound < c / (2 * h ^ 2))
    {x y : G.toLGeometry.Point} (p : M14BackwardPath G.toLGeometry T 0 tau x y)
    (hscalar : horizontalScalarCurvature G.toLGeometry.leafwise (p.curve a) ≤ safeBound)
    (hbudget : (∫ t in 0..tau, Real.sqrt t * pathPositiveDensity p t) ≤ budget)
    {b : ℝ} (hb : b ∈ Ioc a tau)
    (w : (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval origin (h⁻¹ ^ 2) Q.cylinder.scale_pos Q.interval)).Point ×
        Q.source)
    (hinner : w.2.val ∈ gBirth.ball center (A * h / 2))
    (hinnerTime : (w.1.val - origin) / h ^ 2 ≤ 1 / 2) :
    p.curve b ≠ rawCylinderMap G.realization Q.cylinder w := by
  intro heq
  have hout : p.curve a ∉ Set.range (rawCylinderMap G.realization Q.cylinder) := by
    rintro ⟨z, hz⟩
    have hlow := Q.scalar_birth_lower hh hc htheta z
    rw [hz] at hlow
    exact (not_lt_of_ge (hlow.trans hscalar)) hseparation
  have hwidth : Q.top - origin ≤ h ^ 2 := by
    nlinarith [Q.top_le_model, sq_nonneg h]
  obtain ⟨r, hr, hentry⟩ := exists_actualTruncatedCapEntry_action_gt G hM12 Q.cylinder
    Q.time_subset gBirth Q.physical_eq hmu hA hh hc htheta hwidth hside htop
    Q.metric_lower Q.scalar_lower center Q.source_eq p Q.top_kind ha hb.1 hb.2 hout
      w heq hinner hinnerTime
  have hroot : budget / Real.sqrt r ≤ budget / Real.sqrt a :=
    div_le_div_of_nonneg_left hbudget0 (Real.sqrt_pos.mpr ha) (Real.sqrt_le_sqrt hr.1)
  have hweighted := weightedAction_gt_of_tail (ha.trans_le hr.1) hr.2.le hb.2
    (pathPositiveDensity_nonneg p) (pathPositiveAction_integrable hM12 p)
    (pathPositiveDensity_tail_integrable hM12 p (ha.trans_le hr.1) hr.2.le hb.2)
    (hroot.trans_lt hentry)
  exact (not_lt_of_ge hbudget) hweighted

end PoincareConjecture.Proofs.M46
