import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_EntryAlternative
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_PhysicalTopEntry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Function
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

theorem exists_actualFullCapEntry_action_gt
    {F : GeneralizedRicciFlowData.{u}} (G : FlowBoxRicciGeometry F)
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {C : GeneralizedSliceCarrier.{u}} [CompactSpace C.carrier]
    {origin scale : ℝ} {J : SpacetimeInterval}
    {U : TopologicalSpace.Opens C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale J.domain U)
    (hI : (cylinderPhysicalInterval origin scale e.scale_pos J).domain ⊆ F.interval)
    (gBirth : RiemannianMetric 3 C.carrier) {mu A h c ell theta : ℝ}
    (hphysical : (cylinderPhysicalInterval origin scale e.scale_pos J).domain =
      Ioo origin (origin + theta * h ^ 2))
    (hmu : 0 < mu) (hA : 0 < A) (hh : 0 < h) (hc : 0 < c)
    (htheta : theta < 1)
    (hside : ell < mu * A ^ 2 / 4)
    (htop : ell < -(c / 2) * (Real.log (1 - theta) + Real.log 2))
    (hbound : ∀ (s : ℝ) (hs : s ∈ J.domain) (z : U)
      (v : TangentSpace (𝓡 3) z.val),
      scale * (mu * gBirth.inner z.val v v) ≤ e.pullbackInner s hs z.val v v)
    (hscalar : ∀ w : (G.realization.timeIntervals.interval
        (cylinderPhysicalInterval origin scale e.scale_pos J)).Point × U,
      c / (2 * (1 - (w.1.val - origin) / h ^ 2) * h ^ 2) ≤
        horizontalScalarCurvature G.toLGeometry.leafwise (rawCylinderMap G.realization e w))
    (center : C.carrier) (hsource : (U : Set C.carrier) = gBirth.ball center (A * h))
    {T tau a b : ℝ} {x y : G.toLGeometry.Point}
    (p : M14BackwardPath G.toLGeometry T 0 tau x y)
    (ha : 0 < a) (hab : a < b) (hbtau : b ≤ tau)
    (hout : p.curve a ∉ range (rawCylinderMap G.realization e))
    (z : (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval origin scale e.scale_pos J)).Point × U)
    (hend : p.curve b = rawCylinderMap G.realization e z)
    (hinner : z.2.val ∈ gBirth.ball center (A * h / 2))
    (hinnerTime : (z.1.val - origin) / h ^ 2 ≤ 1 / 2) :
    ∃ r ∈ Ico a b, ell < ∫ t in r..b, pathPositiveDensity p t := by
  have hwidth : origin + theta * h ^ 2 - origin ≤ h ^ 2 := by
    nlinarith [sq_nonneg h]
  obtain ⟨r, hr, _, hinside, _, hcase⟩ :=
    exists_actualCap_sideEntry_or_top G hM12 e hI hphysical gBirth hmu hA hh hwidth
      hbound center hsource p ha hab hbtau hout z hend hinner
  refine ⟨r, hr, ?_⟩
  rcases hcase with hsideActual | htopActual
  · exact hside.trans_le hsideActual
  have htimeR := p.curve_time r ⟨ha.le.trans hr.1, hr.2.le.trans hbtau⟩
  have htimeB := p.curve_time b ⟨ha.le.trans hab.le, hbtau⟩
  have hclockB : G.toLGeometry.spacetime.timeFunction (p.curve b) = z.1.val := by
    rw [hend]
    exact rawCylinderMap_time G.realization e z
  have hnormalizedTop : (T - origin - r) / h ^ 2 = theta := by
    change G.toLGeometry.spacetime.timeFunction (p.curve r) =
      origin + theta * h ^ 2 at htopActual
    apply (div_eq_iff (sq_pos_of_pos hh).ne').mpr
    linarith
  have hnormalizedInner : (T - origin - b) / h ^ 2 ≤ 1 / 2 := by
    have hnum : T - origin - b = z.1.val - origin := by linarith
    rwa [hnum]
  apply actualCapTopEntry_action_gt hM12 p hc htheta htop hh (ha.trans_le hr.1)
    hr.2.le hbtau hnormalizedTop hnormalizedInner
  intro t ht
  obtain ⟨w, hw⟩ := hinside ⟨ht.1, ht.2.le⟩
  have htimeT := p.curve_time t
    ⟨(ha.le.trans hr.1).trans ht.1.le, ht.2.le.trans hbtau⟩
  have hclock : w.1.val = T - t := by
    rw [← rawCylinderMap_time G.realization e w, hw]
    exact htimeT
  have h := hscalar w
  rw [hw, hclock] at h
  convert h using 1
  congr 2
  ring

end PoincareConjecture.Proofs.M46
