import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Providers
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Assembly
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Flow.UnitLifetime

/-!
# M34 standard-cap existence proof entry

The conditional theorem owns the single cap-existence admission and applies
its full predecessor implication. The closed public theorem supplies those
earlier services. Supporting objects are declared in
`Definitions/M34StandardCapExistence.lean`; later collaborators edit this
file and optional `Proofs/M34/` helpers.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

/-- M34: a complete standard initial metric on R^3 exists. Every supplied
standard initial metric admits one selected maximal Ricci flow with that
exact initial metric and connection, lifetime one, complete time slices,
nonnegative sectional curvature on [0,1), strictly positive sectional
curvature on (0,1), and invariance under the actual standard SO(3) action.
Its initial metric has positive scalar lower and upper bounds, finite core
volume, and uniform bounds on every covariant curvature derivative.

For every epsilon > 0 and 0 <= t0 < 1, outside one compact set the flow has
cylindrical patches, each fixed throughout [0,t0], intrinsically
epsilon-close to 2*(1-t)*g_unit_S2 + dz^2 through order floor(1/epsilon).
There are positive r0 and kappa, independent of the tested time, center and
radius, giving kappa-noncollapse at each 0 < r <= r0 with r^2 <= t whenever
the full curvature is bounded by r^(-2) on its actual past parabolic ball.

Sources: Morgan-Tian Definition 12.1, Lemmas 12.2-12.3 and Theorem 12.5,
pp. 293-297; Lemma 12.6, Proposition 12.7, Corollaries 12.8/12.12 and
Proposition 12.13, pp. 297-306; the required portion of Theorem 12.28,
pp. 323-324, and Theorem 12.29/Claim 12.30, pp. 324-325. Use the corrections
and complete derivation in `reviews/contracts/2026-09-17-m34-full-contract.md`.

The actual M03/M04/M07, M08-M10, M12-M15, M22, M27 and M30 services are
inputs. The compact-double initial endpoint, noncompact restart, complete
maximum principles, splitting and rotation-field argument are internal
M34 obligations. M15 uses a fixed positive early slice so that ordinary
M14 capture is applied strictly inside its complete time window. No M31,
M32, M33 or M35 conclusion is assumed; lifetime one is proved here. -/
theorem repairedStandardCapExistence_of_predecessors
    (P : M34StandardCapPredecessors) : RepairedStandardCapExistenceTheory := by
  exact M34.repairedStandardCapExistenceTheory_of_lifetime_ge_one P
    (fun _ F => M34.standardFlow_lifetime_ge_one P F)

/-- Apply the complete M34 construction with the actual earlier services.
The standard metric and every cap-flow conclusion remain outputs. -/
theorem repairedStandardCapExistence : RepairedStandardCapExistenceTheory :=
  repairedStandardCapExistence_of_predecessors m34StandardCapPredecessorsFromMilestones

end PoincareMT
