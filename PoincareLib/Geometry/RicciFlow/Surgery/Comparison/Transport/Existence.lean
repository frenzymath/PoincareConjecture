import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Transport.Theory
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Transport.Construction
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.BasedApproximation
/-!
# SurgeryComparison.Transport comparison-map homotopy proof entry

The numbered proof file assembles the topology and quantitative smoothing
of the literal comparison selected by the supplied SurgeryComparison data.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/--
Morgan--Tian Proposition 15.12 (printed p. 365), the cap-image comparison
on p. 428, and the Poincare-specific transport discussion on pp. 430--431
support the near-unit map used in Claim 18.22 (p. 433). Given arbitrary
Poincare.Topology and SurgeryComparison services, choose a positive bound on terminal accuracy
before the standard metric and flow. For each flow satisfying that bound
and each realized SurgeryComparison provider, take any nonempty separating event with
strict delta/height bounds, closed simply connected parent and child
components, the actual retained region and a parent integral orientation.
Equip the exact selected SurgeryComparison comparison map with a child orientation,
degree one, a homotopy equivalence whose forward map is that comparison,
and bijectivity of its actual based pi3 map. For every positive eta, all
sufficiently late pre-times admit smooth (1 + eta)-Lipschitz approximants
with the exact target basepoint, the same based pi3 map and the same degree.

Poincare.Topology supplies orientability, CW and homotopy-three-sphere data. The local
degree computation, map-level homology/homotopy naturality and Whitehead
argument remain internal SurgeryComparison.Transport work. Quantitative smoothing and exact-point
correction also belong here; C0 smooth approximation alone is insufficient.
The complete derivation is `reviews/contracts/2026-09-18-m40-full-contract.md`.
The returned subtype retains the actual SurgeryComparison map for M57 and the width
argument. No Poincare endpoint is an input or output. The unused legacy
comparison admission was retired; see
`reviews/declarations/2026-09-18-m39-retirement-validation.md`. The stronger
exact-unit source assertion and the general non-simply-connected branch
remain unclaimed by this theorem.
-/
theorem repairedComparisonHomotopy : RepairedComparisonHomotopyTheory.{u} := by
  constructor
  intro P G39
  obtain ⟨epsilon, hepsilon, _⟩ := G39.comparison
  refine ⟨epsilon, hepsilon, ?_⟩
  intro g₀ D _ K _
  refine ⟨{ transport := ?_ }⟩
  intro T hT _ input hdelta hh
  let Q := Classical.choice
    (K.comparison T hT input.toRepairedComparisonMapInput hdelta hh)
  exact ⟨⟨SurgeryComparison.Transport.comparisonHomotopyConclusion P Q
    (SurgeryComparison.Transport.comparison_smooth_approximants Q), rfl⟩⟩

end PoincareMT
