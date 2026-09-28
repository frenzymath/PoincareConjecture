import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_ActualSideEntry
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_CylinderOpenImage
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_LastEntry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Function
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

theorem exists_actualCap_sideEntry_or_top
    {F : GeneralizedRicciFlowData.{u}} (G : FlowBoxRicciGeometry F)
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {C : GeneralizedSliceCarrier.{u}} [CompactSpace C.carrier]
    {origin scale top : ℝ} {J : SpacetimeInterval}
    {U : TopologicalSpace.Opens C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale J.domain U)
    (hI : (cylinderPhysicalInterval origin scale e.scale_pos J).domain ⊆ F.interval)
    (hphysical : (cylinderPhysicalInterval origin scale e.scale_pos J).domain = Ioo origin top)
    (gBirth : RiemannianMetric 3 C.carrier) {mu A h : ℝ}
    (hmu : 0 < mu) (hA : 0 < A) (hh : 0 < h) (hwidth : top - origin ≤ h ^ 2)
    (hbound : ∀ (s : ℝ) (hs : s ∈ J.domain) (z : U)
      (v : TangentSpace (𝓡 3) z.val),
      scale * (mu * gBirth.inner z.val v v) ≤ e.pullbackInner s hs z.val v v)
    (center : C.carrier) (hsource : (U : Set C.carrier) = gBirth.ball center (A * h))
    {T tau a b : ℝ} {x y : G.toLGeometry.Point}
    (p : M14BackwardPath G.toLGeometry T 0 tau x y)
    (ha : 0 < a) (hab : a < b) (hbtau : b ≤ tau)
    (hout : p.curve a ∉ range (rawCylinderMap G.realization e))
    (z : (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval origin scale e.scale_pos J)).Point × U)
    (hend : p.curve b = rawCylinderMap G.realization e z)
    (hinner : z.2.val ∈ gBirth.ball center (A * h / 2)) :
    ∃ c ∈ Ico a b,
      p.curve c ∉ range (rawCylinderMap G.realization e) ∧
      MapsTo p.curve (Ioc c b) (range (rawCylinderMap G.realization e)) ∧
      MapsTo p.curve (Icc c b) (closure (range (rawCylinderMap G.realization e))) ∧
      (mu * A ^ 2 / 4 ≤ ∫ t in c..b, pathPositiveDensity p t ∨
        G.realization.spacetime.timeFunction (p.curve c) = top) := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin 3)))
      F.point := G.realization.spacetime.chartedSpace
  have hopen : IsOpen (cylinderPhysicalInterval origin scale e.scale_pos J).domain := by
    rw [hphysical]
    exact isOpen_Ioo
  have hrawOpen := (rawCylinder_isOpenEmbedding G.realization e hI hopen).isOpen_range
  have hpcont : ContinuousOn p.curve (Icc a b) :=
    p.curve_continuous.mono (Icc_subset_Icc ha.le hbtau)
  obtain ⟨c, hc, hcout, hinside, hclosure⟩ :=
    exists_last_entry_of_continuousOn hab hpcont hrawOpen hout ⟨z, hend.symm⟩
  have hclockClosed : closure (range (rawCylinderMap G.realization e)) ⊆
      G.realization.spacetime.timeFunction ⁻¹' Icc origin top := by
    apply closure_minimal _
      (isClosed_Icc.preimage G.realization.spacetime.time_smooth.continuous)
    rintro v ⟨w, rfl⟩
    change G.realization.spacetime.timeFunction (rawCylinderMap G.realization e w) ∈
      Icc origin top
    rw [rawCylinderMap_time]
    exact Ioo_subset_Icc_self (hphysical ▸ w.1.property)
  have hclockC := hclockClosed (hclosure ⟨le_rfl, hc.2.le⟩)
  have hclockChi : G.toLGeometry.spacetime.timeFunction (p.curve c) ≤ top := hclockC.2
  have hclockB : origin < G.realization.spacetime.timeFunction (p.curve b) := by
    rw [hend, rawCylinderMap_time]
    exact (show z.1.val ∈ Ioo origin top from hphysical ▸ z.1.property).1
  have htimeC := p.curve_time c ⟨ha.le.trans hc.1, hc.2.le.trans hbtau⟩
  have htimeB := p.curve_time b ⟨ha.le.trans hab.le, hbtau⟩
  have hclockClo : origin < G.realization.spacetime.timeFunction (p.curve c) := by
    change G.toLGeometry.spacetime.timeFunction (p.curve c) = T - c at htimeC
    change G.toLGeometry.spacetime.timeFunction (p.curve b) = T - b at htimeB
    change origin < G.toLGeometry.spacetime.timeFunction (p.curve b) at hclockB
    change origin < G.toLGeometry.spacetime.timeFunction (p.curve c)
    linarith [hc.2]
  refine ⟨c, hc, hcout, hinside, hclosure, ?_⟩
  by_cases htop : G.realization.spacetime.timeFunction (p.curve c) < top
  · left
    have hclockMem : G.realization.spacetime.timeFunction (p.curve c) ∈
        (cylinderPhysicalInterval origin scale e.scale_pos J).domain := by
      rw [hphysical]
      exact ⟨hclockClo, htop⟩
    have hduration : b - c ≤ h ^ 2 := by
      change origin < G.toLGeometry.spacetime.timeFunction (p.curve b) at hclockB
      linarith
    exact actualCapSideEntry_action_lower G hM12 e hI gBirth hmu hA hh hbound
      center hsource p (ha.trans_le hc.1) hc.2 hbtau hduration
      (hinside.mono_left Ioo_subset_Ioc_self) hclockMem hcout z hend hinner
  · exact Or.inr (le_antisymm hclockC.2 (le_of_not_gt htop))

end PoincareConjecture.Proofs.M46
