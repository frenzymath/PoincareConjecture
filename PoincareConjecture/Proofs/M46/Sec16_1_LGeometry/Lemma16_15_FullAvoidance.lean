import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_CapBirthAvoidance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

theorem CapBarrierWindow.avoids_early_inner_of_initial_scalar
    {F : GeneralizedRicciFlowData.{u}} {G : FlowBoxRicciGeometry F}
    {C : GeneralizedSliceCarrier.{u}} [CompactSpace C.carrier]
    {gBirth : RiemannianMetric 3 C.carrier} {center : C.carrier}
    {origin T A h c mu theta : ℝ}
    (Q : CapBarrierWindow G C gBirth center origin T A h c mu theta)
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hmu : 0 < mu) (hA : 0 < A) (hh : 0 < h) (hc : 0 < c) (htheta : theta < 1)
    {budget a tau safeBound : ℝ} (hbudget0 : 0 ≤ budget) (ha : 0 < a)
    (hside : budget / Real.sqrt a < mu * A ^ 2 / 4)
    (htop : budget / Real.sqrt a < -(c / 2) * (Real.log (1 - theta) + Real.log 2))
    (hseparation : safeBound < c / (2 * h ^ 2))
    {x y : G.toLGeometry.Point} (p : M14BackwardPath G.toLGeometry T 0 tau x y)
    (hscalar : ∀ s ∈ Icc 0 tau, s ≤ a →
      horizontalScalarCurvature G.toLGeometry.leafwise (p.curve s) ≤ safeBound)
    (hbudget : (∫ t in 0..tau, Real.sqrt t * pathPositiveDensity p t) ≤ budget)
    {b : ℝ} (hb : b ∈ Icc 0 tau)
    (w : (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval origin (h⁻¹ ^ 2) Q.cylinder.scale_pos Q.interval)).Point ×
        Q.source)
    (hinner : w.2.val ∈ gBirth.ball center (A * h / 2))
    (hinnerTime : (w.1.val - origin) / h ^ 2 ≤ 1 / 2) :
    p.curve b ≠ rawCylinderMap G.realization Q.cylinder w := by
  by_cases hba : b ≤ a
  · intro heq
    have hlow := Q.scalar_birth_lower hh hc htheta w
    rw [← heq] at hlow
    exact (not_lt_of_ge (hlow.trans (hscalar b hb hba))) hseparation
  · have hab : a < b := lt_of_not_ge hba
    exact Q.avoids_early_inner hM12 hmu hA hh hc htheta hbudget0 ha hside htop
      hseparation p (hscalar a ⟨ha.le, hab.le.trans hb.2⟩ le_rfl) hbudget
      ⟨hab, hb.2⟩ w hinner hinnerTime

theorem CapBarrierOriginData.avoids_birth_of_initial_scalar
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {G : FlowBoxRicciGeometry H.generalized}
    {origin T A h c mu theta : ℝ} {center : (F.slice origin).carrier}
    (Q : CapBarrierWindow G (F.slice origin) (F.metric origin) center
      origin T A h c mu theta)
    [CompactSpace (F.slice origin).carrier]
    (D : CapBarrierOriginData H Q) (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hmu : 0 < mu) (hA : 0 < A) (hh : 0 < h) (hc : 0 < c) (htheta : theta < 1)
    {budget a tau safeBound : ℝ} (hbudget0 : 0 ≤ budget) (ha : 0 < a)
    (hside : budget / Real.sqrt a < mu * A ^ 2 / 4)
    (htop : budget / Real.sqrt a < -(c / 2) * (Real.log (1 - theta) + Real.log 2))
    (hseparation : safeBound < c / (2 * h ^ 2))
    {x z : G.toLGeometry.Point} (p : M14BackwardPath G.toLGeometry T 0 tau x z)
    (hscalar : ∀ s ∈ Icc 0 tau, s ≤ a →
      horizontalScalarCurvature G.toLGeometry.leafwise (p.curve s) ≤ safeBound)
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
  exact Q.avoids_early_inner_of_initial_scalar hM12 hmu hA hh hc htheta hbudget0 ha
    hside htop hseparation p hscalar hbudget ⟨hr.1.le, hr.2.le.trans hb.2⟩
    w hinner hearly hw.symm

end PoincareConjecture.Proofs.M46
