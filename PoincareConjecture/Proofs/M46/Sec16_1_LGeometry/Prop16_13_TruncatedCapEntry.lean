import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_FullCapEntry










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Function
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12



theorem exists_actualTruncatedCapEntry_action_gt
    {F : GeneralizedRicciFlowData.{u}} (G : FlowBoxRicciGeometry F)
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {C : GeneralizedSliceCarrier.{u}} [CompactSpace C.carrier]
    {origin scale top : ℝ} {J : SpacetimeInterval}
    {U : TopologicalSpace.Opens C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale J.domain U)
    (hI : (cylinderPhysicalInterval origin scale e.scale_pos J).domain ⊆ F.interval)
    (gBirth : RiemannianMetric 3 C.carrier) {mu A h c ell theta : ℝ}
    (hphysical : (cylinderPhysicalInterval origin scale e.scale_pos J).domain = Ioo origin top)
    (hmu : 0 < mu) (hA : 0 < A) (hh : 0 < h) (hc : 0 < c)
    (htheta : theta < 1) (hwidth : top - origin ≤ h ^ 2)
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
    (htopKind : top = T ∨ top = origin + theta * h ^ 2 ∨
      ∀ v : G.toLGeometry.Point, G.realization.spacetime.timeFunction v = top →
        v ∉ closure (range (rawCylinderMap G.realization e)))
    (ha : 0 < a) (hab : a < b) (hbtau : b ≤ tau)
    (hout : p.curve a ∉ range (rawCylinderMap G.realization e))
    (z : (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval origin scale e.scale_pos J)).Point × U)
    (hend : p.curve b = rawCylinderMap G.realization e z)
    (hinner : z.2.val ∈ gBirth.ball center (A * h / 2))
    (hinnerTime : (z.1.val - origin) / h ^ 2 ≤ 1 / 2) :
    ∃ r ∈ Ico a b, ell < ∫ t in r..b, pathPositiveDensity p t := by
  by_cases hfull : top = origin + theta * h ^ 2
  · exact exists_actualFullCapEntry_action_gt G hM12 e hI gBirth
      (hphysical.trans (congrArg (Ioo origin) hfull)) hmu hA hh hc htheta hside htop
      hbound hscalar center hsource p ha hab hbtau hout z hend hinner hinnerTime
  obtain ⟨r, hr, _, _, hclosure, hcase⟩ :=
    exists_actualCap_sideEntry_or_top G hM12 e hI hphysical gBirth hmu hA hh hwidth
      hbound center hsource p ha hab hbtau hout z hend hinner
  refine ⟨r, hr, ?_⟩
  rcases hcase with hsideActual | htopActual
  · exact hside.trans_le hsideActual
  exfalso
  rcases htopKind with htest | hfull' | hdisappears
  · have htime := p.curve_time r ⟨ha.le.trans hr.1, hr.2.le.trans hbtau⟩
    change G.realization.spacetime.timeFunction (p.curve r) = T - r at htime
    rw [htopActual, htest] at htime
    linarith [hr.1]
  · exact hfull hfull'
  · exact hdisappears (p.curve r) htopActual (hclosure ⟨le_rfl, hr.2.le⟩)

end PoincareConjecture.Proofs.M46
