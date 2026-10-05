import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SurgeryTopology
import PoincareLib.Topology.Manifold.Surgery.Event.Event.EventTopology

open scoped PoincareMT.M38ReviewedAccuracy
/-!
# M38 local surgery topology proof entry

The event producers construct the actual finite connected-sum witnesses
uniformly for every admissible raw flow, parametrically in the supplied
Appendix A neck/cap theory.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-
Morgan--Tian Proposition 15.3 (printed pp. 357--358) reconstructs the
pre-surgery slice at a singular time from the actual post-surgery slice,
finitely many two-sphere bundles over the circle, and closed positive-curvature
spaceforms, using connected-sum operations.  M38 applies this local statement
to each nonempty and whole-slice-vanishing event of the supplied raw flow. The
nonempty output includes one cap correspondence for the selected conclusion;
the vanishing output contains no survivor pieces.  No endpoint identification
or global finite-flow assembly is assumed here.  The source correction record
is `reviews/errata/2026-09-10-surgery-extinction-audit.md`; the
`MT-NECK-SEPARATION` convention is recorded in
`reviews/errata/2026-09-10-analytic-outline-audit.md`: separating central
spheres use the tube case, while nonseparating spheres use the
S²-bundle-over-S¹ case.
-/
/-- Given an Appendix A neck/cap theory, choose a positive topology threshold
below its epsilon threshold. Every admissible raw surgery flow with doubled
epsilon below this bound admits the actual event-indexed finite connected-sum
reconstruction, with cap correspondence in the nonempty branch and no
survivors in the vanishing branch. Source: Morgan--Tian Proposition 15.3,
pp. 357--358; the separating-neck correction is cited above. -/
theorem rawLocalSurgeryTopology : RawLocalSurgeryTopologyTheory.{u} :=
  ⟨M38.exists_raw_local_surgery_topology_data⟩

/-- Checked specialization of the raw M38 result to the legacy repaired API. -/
theorem repairedLocalSurgeryTopology : RepairedLocalSurgeryTopologyTheory.{u} := by
  refine ⟨?_⟩
  intro N
  obtain ⟨epsilon₀, hpositive, hthreshold, hraw⟩ := rawLocalSurgeryTopology.topology N
  exact ⟨epsilon₀, hpositive, hthreshold,
    fun D hadmissible hepsilon => hraw D.flow hadmissible hepsilon⟩
end PoincareMT
