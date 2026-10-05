import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Extension.Theory
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Extension.Distance
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Extension.Branches.Construction
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Extension.Gluing
/-!
# SurgeryComparison comparison-map proof entry

The separating branch construction and constant-tail gluing give one
continuous extension. Compact regular metric convergence gives its late
near-unit distance bounds for the actual parent and child metrics.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-
Morgan--Tian Proposition 15.12 (printed p. 365) and Claim 18.22
(p. 433), with the local collapse of Claim 13.1/Theorem 13.2
(pp. 331--334). Uniformly in the standard metric and flow, choose a positive
epsilon threshold. For each strongly admissible nonempty event with strict
delta/height bounds, separating surgery spheres, a selected M38 topology
witness and actual parent/child metrics, construct one continuous comparison
map. It agrees with retention on the full nonempty inherited open region,
preserves the limit metric there, has open retained target image, and sends
the complement into the actual closed caps. For each eta > 0, this same map
is globally (1 + eta)-Lipschitz at every sufficiently late pre-time. MetricSurgery's
constant collapse tail extends over each discarded branch; its static
distance estimate and compact regular metric convergence give the bound.
This exports the near-unit consequence used by Claim 18.22. The stronger
exact-unit legacy clause remains unresolved, as recorded in
`reviews/errata/2026-09-18-m39-comparison-provenance.md`; the full derivation
is `reviews/contracts/2026-09-18-m39-repair-contract.md`.
SurgeryComparison.Transport owns controlled smoothing, degree, homotopy and pi3 transport. Remark
15.13 explains the separating-sphere restriction.
-/
theorem repairedComparisonMap : RepairedComparisonMapTheory.{u} := by
  refine ⟨⟨1, zero_lt_one, ?_⟩⟩
  intro g₀ D _hε
  refine ⟨{ comparison := ?_ }⟩
  intro T hT hNonempty I _hdelta _hheight
  obtain ⟨B⟩ := SurgeryComparison.comparisonBranches_nonempty I
  obtain ⟨G⟩ := SurgeryComparison.comparisonExtension_of_branches I B
  exact ⟨SurgeryComparison.comparisonConclusionOfExtension I G⟩

end PoincareMT
