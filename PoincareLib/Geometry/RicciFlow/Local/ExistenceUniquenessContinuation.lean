import PoincareLib.Geometry.RicciFlow.Local.Continuation.EndpointMetric
import PoincareLib.Geometry.RicciFlow.Local.Continuation.Gluing
/- Adapted from Mapher `PoincareMT/Proofs/M03.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Geometry.RicciFlow.Local.Theory
import PoincareLib.Geometry.RicciFlow.Local.ShortTime
import PoincareLib.Geometry.RicciFlow.Local.Connection.NativeTime
import PoincareLib.Geometry.RicciFlow.Local.Curvature.Energy.CurvatureRateAlgebra
import PoincareLib.Geometry.RicciFlow.Local.Metric.MetricDifferenceEnergyRate
import PoincareLib.Geometry.RicciFlow.Local.Connection.RateRicciSmoothness

/-!
# Continuation and assembly of the local Ricci-flow milestone

Continuation follows Morgan-Tian, Proposition 4.12, printed p. 68:
curvature control constructs a smooth positive endpoint metric, and a
short-time restart glues smoothly to the old flow. The imported M03 proof
tree now closes the five earlier component admissions; its helper semantics
remain separately marked for independent review.
-/

/-! M03 is the numbered review and proof entry point. -/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]

/-- Continue a compact flow under its original uniform curvature bound. -/
theorem ricciFlowContinuation : RicciFlowContinuation n M := by
  intro T hT F hbound
  obtain ⟨C, hC⟩ := hbound
  obtain ⟨gT, _, _, hjets⟩ :=
    RicciFlow.Local.exists_ricciFlow_endpoint_metric_of_curvature_bound hT F hC
  obtain ⟨δ, hδ, R, hR⟩ := shortTimeRicciFlowExistence gT
  obtain ⟨G, hG⟩ := RicciFlow.Local.exists_ricciFlow_time_translate hδ R T
  have hGT : G.metric T = gT := by rw [hG T, sub_self, hR]
  obtain ⟨H, hHF, _⟩ :=
    RicciFlow.Local.exists_ricciFlow_gluing_of_uniform_metric_jets hT hδ F G (by
      intro x0
      dsimp only
      intro q K hK hKU i j
      rw [hGT]
      exact (hjets (T / 2) (by linarith) (by linarith) x0 q K hK hKU).2 i j)
  exact ⟨T + δ, by linarith, H, hHF⟩

/-- M03: on a compact Hausdorff second-countable smooth n-manifold without boundary,
every smooth metric starts a Ricci flow for some positive lifetime. Flows with
the same metric at their included least time zero agree on their common domain.
A flow on [0,T), with finite positive T and one bound on its evolving full
curvature tensor norm uniform in space and time, extends beyond T and agrees
with the original metrics at every old time.

Sources: Morgan-Tian Theorem 3.11, pp. 39-40; Proposition 4.12, p. 68;
smooth restart gluing uses Proposition 3.12, p. 40. Correct the DeTurck
pullback generator to -W composed with phi, as recorded in
`reviews/errata/2026-09-12-deturck-pullback.md` (MT-DETURCK-PULLBACK-SIGN).
The component proofs and internal estimates belong to `Proofs/M03/` and
this file; the later M04 theorem is not an input. -/
theorem ricciFlowLocalTheory : RicciFlowLocalTheory n M := by
  exact ⟨shortTimeRicciFlowExistence, ricciFlowUniqueness, ricciFlowContinuation⟩

end PoincareMT
