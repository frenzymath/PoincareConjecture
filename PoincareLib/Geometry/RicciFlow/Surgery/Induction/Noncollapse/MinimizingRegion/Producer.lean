import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.MinimizingRegion.Configuration
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.Configuration
import PoincareLib.Geometry.RicciFlow.Curvature.Construction

/-!
# The minimizing-region producer on the selected surgery history

Proposition 16.4, p. 369. The actual M33 history contains the complete
required closed strip. M14 supplies one geometry conclusion and one
exponential family on that same history. The scalar continuity and
comparison endpoints substitute directly into the pinned producer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.Proofs.M46

/-- The generic minimizing-region assembly applies to the actual
included M33 history without extending it across its terminal time.
Source: Proposition 16.4, p. 369. -/
theorem actualHistory_minimizingRegion_of_slice_comparison
    (P : M46Predecessors.{u}) {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (D : NoncollapseTest F O) (H : HalfRadiusHistory D) {start : ℝ} (hstart : 0 ≤ start)
    (C : ActionConfinement H.spacetime.geometry.toLGeometry D.time start
      ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val)
    (hcontinuous : ∀ a c : ℝ, 0 < a → c ^ 2 ≤ D.time - start →
      ContinuousOn (cappedSliceAction H.spacetime.geometry.toLGeometry D.time
        ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val
        C.barrier) (Icc a c))
    (hbound : ∀ b : ℝ, 0 < b → b ^ 2 ≤ D.time - start →
      cappedSliceAction H.spacetime.geometry.toLGeometry D.time
        ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val
        C.barrier b ≤ 3 * b) :
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
  exact minimizingRegion_nonempty_of_slice_comparison ricciFlowCurvatureTheory.{0}
    P.m12 LG E C hstrip hcontinuous hbound

/-- The two scalar proof endpoints substitute into the literal
`MinimizingRegionProducer`; no additional premise enters the public M46
statement. Source: Proposition 16.4, p. 369 and pp. 389-391. -/
theorem minimizingRegionProducer_of_slice_comparison
    (P : M46Predecessors.{u}) {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) (rNext cutoff rho : ℝ)
    (hcontinuous : ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
      ObservedInputs p rNext cutoff F O →
      ∀ (D : NoncollapseTest F O) (H : HalfRadiusHistory D),
        surgeryEpochStart p.i ≤ D.time → rho ≤ D.radius →
        ∀ C : ActionConfinement H.spacetime.geometry.toLGeometry
          D.time (surgeryEpochStart (p.i - 1))
          ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val,
          C.barrier = actionBudget p → ∀ a c : ℝ,
          0 < a → c ^ 2 ≤ D.time - surgeryEpochStart (p.i - 1) →
          ContinuousOn (cappedSliceAction H.spacetime.geometry.toLGeometry D.time
            ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val
            C.barrier) (Icc a c))
    (hbound : ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
      ObservedInputs p rNext cutoff F O →
      ∀ (D : NoncollapseTest F O) (H : HalfRadiusHistory D),
        surgeryEpochStart p.i ≤ D.time → rho ≤ D.radius →
        ∀ C : ActionConfinement H.spacetime.geometry.toLGeometry
          D.time (surgeryEpochStart (p.i - 1))
          ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val,
          C.barrier = actionBudget p → ∀ b : ℝ,
          0 < b → b ^ 2 ≤ D.time - surgeryEpochStart (p.i - 1) →
          cappedSliceAction H.spacetime.geometry.toLGeometry D.time
            ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val
            C.barrier b ≤ 3 * b) :
    MinimizingRegionProducer.{u} p rNext cutoff rho := by
  intro F O inputs D H htime hr C hbarrier
  apply actualHistory_minimizingRegion_of_slice_comparison P D H
    (by unfold surgeryEpochStart; positivity) C
  · exact hcontinuous F O inputs D H htime hr C hbarrier
  · exact hbound F O inputs D H htime hr C hbarrier

end PoincareMT.Proofs.M46
