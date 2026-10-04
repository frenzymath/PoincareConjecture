import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Compat.GeneralizedEquation
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Attainment.Minimum.SliceBound
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.MinimizingRegion.Producer
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.OrdinaryFlow

/-!
# Proposition 16.4 on the actual confined regular history

Morgan--Tian Proposition 16.4, p. 369 and pp. 389-391. The direct method,
moving-endpoint recovery, compact action sublevels and scalar comparison
now supply all fields of the literal minimizing-region producer. No
attainment, minimum-value regularity or continuation premise is added.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.Proofs.M46

/-- The actual history's compact action confinement produces its full
minimizing region, with the dimension-three estimate on every slice. -/
theorem actualHistory_minimizingRegion
    (P : M46Predecessors.{u}) {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (D : NoncollapseTest F O) (H : HalfRadiusHistory D) {start : ℝ} (hstart : 0 ≤ start)
    (C : ActionConfinement H.spacetime.geometry.toLGeometry D.time start
      ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val) :
    Nonempty (MinimizingRegion H.spacetime.geometry.toLGeometry D.time start
      ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val C) := by
  let G := H.spacetime.geometry.toLGeometry
  let x : G.Point :=
    ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val
  have hbase : G.spacetime.timeFunction x = D.time :=
    ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).property
  have hstrip : Icc start D.time ⊆ H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    intro t ht
    exact ⟨hstart.trans ht.1, ht.2⟩
  obtain ⟨LG⟩ := P.m14.conclusion _ _ _ G
  obtain ⟨E⟩ := LG.exponential.family D.time x hbase
  apply minimizingRegion_nonempty_of_slice_comparison ricciFlowCurvatureTheory.{0}
    P.m12 LG E C hstrip
  · intro a c ha hc
    exact cappedSliceAction_continuousOn ricciFlowCurvatureTheory.{0}
      P.m12 LG E C hstrip ha hc
  · intro b hb hbStart
    exact cappedSliceAction_le_three_mul (m12MetricPredecessors.{0} 3)
      ricciFlowCurvatureTheory.{0} P.m12 LG E C hstrip hb hbStart

/-- The literal pinned minimizing-region producer is proved from the
original predecessors and actual compact confinement, Proposition 16.4. -/
theorem minimizingRegionProducer (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    (rNext cutoff rho : ℝ) : MinimizingRegionProducer.{u} p rNext cutoff rho := by
  intro F O _inputs D H _htime _hr C _hbarrier
  exact actualHistory_minimizingRegion P D H (by unfold surgeryEpochStart; positivity) C

end PoincareMT.Proofs.M46
