import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_BackwardEntryEnergy
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_EntryFrontier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Function
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

theorem actualCapSideEntry_action_lower
    {F : GeneralizedRicciFlowData.{u}} (G : FlowBoxRicciGeometry F)
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {C : GeneralizedSliceCarrier.{u}} [CompactSpace C.carrier]
    {origin scale : ℝ} {J : SpacetimeInterval}
    {U : TopologicalSpace.Opens C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale J.domain U)
    (hI : (cylinderPhysicalInterval origin scale e.scale_pos J).domain ⊆ F.interval)
    (gBirth : RiemannianMetric 3 C.carrier) {mu A h : ℝ}
    (hmu : 0 < mu) (hA : 0 < A) (hh : 0 < h)
    (hbound : ∀ (s : ℝ) (hs : s ∈ J.domain) (z : U)
      (v : TangentSpace (𝓡 3) z.val),
      scale * (mu * gBirth.inner z.val v v) ≤ e.pullbackInner s hs z.val v v)
    (center : C.carrier) (hsource : (U : Set C.carrier) = gBirth.ball center (A * h))
    {T tau a b : ℝ} {x y : G.toLGeometry.Point}
    (p : M14BackwardPath G.toLGeometry T 0 tau x y)
    (ha : 0 < a) (hab : a < b) (hbtau : b ≤ tau) (hduration : b - a ≤ h ^ 2)
    (himage : MapsTo p.curve (Ioo a b) (range (rawCylinderMap G.realization e)))
    (haclock : G.realization.spacetime.timeFunction (p.curve a) ∈
      (cylinderPhysicalInterval origin scale e.scale_pos J).domain)
    (hout : p.curve a ∉ range (rawCylinderMap G.realization e))
    (z : (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval origin scale e.scale_pos J)).Point × U)
    (hend : p.curve b = rawCylinderMap G.realization e z)
    (hinner : z.2.val ∈ gBirth.ball center (A * h / 2)) :
    mu * A ^ 2 / 4 ≤ ∫ t in a..b, pathPositiveDensity p t := by
  obtain ⟨beta, heq, _, hregular, hclock, hpoint, hint, _⟩ :=
    exists_backwardCap_birthEnergy G hM12 e hI gBirth hmu hbound p ha hab hbtau himage
  obtain ⟨xi, hxi, hsame, hxiRegular, _, _⟩ :=
    exists_continuous_birthCurve_extension gBirth hab hregular hint
  have hpcont : ContinuousOn p.curve (Icc a b) :=
    p.curve_continuous.mono (Icc_subset_Icc ha.le hbtau)
  have hcoordinate : EqOn (fun t => (beta t).2.val) xi (Ioo a b) := hsame.symm
  have hfront := rawCylinder_entry_coordinate_mem_frontier G.realization e hab
    hpcont hxi.continuousOn beta heq hcoordinate hclock haclock hout
  have houter : xi a ∉ gBirth.ball center (A * h) := by
    rw [← hsource]
    rw [frontier, U.isOpen.interior_eq] at hfront
    exact hfront.2
  have hinnerXi : xi b ∈ gBirth.ball center (A * h / 2) := by
    rw [rawCylinder_completed_coordinate_eq G.realization e hab ⟨hab.le, le_rfl⟩
      hpcont hxi.continuousOn beta heq hcoordinate z hend]
    exact hinner
  apply capEntryAction_lower gBirth hab hmu hA hh hduration hxi.continuousOn
    hxiRegular (pathPositiveDensity p)
    (pathPositiveDensity_tail_integrable hM12 p ha hab.le hbtau) _ center hinnerXi houter
  intro t ht
  have hgerm : xi =ᶠ[𝓝 t] fun r => (beta r).2.val := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact hsame hr
  rw [referenceSpeedSq_congr_of_eventuallyEq gBirth hgerm]
  exact hpoint t ht

end PoincareConjecture.Proofs.M46
