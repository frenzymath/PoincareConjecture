import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.PersistenceTheory
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scales
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cutoff.Assembly

/-!
# M44 surgery-cap persistence

Natural-language theorem: given the M34 standard-cap existence, M35
standard-cap uniqueness/comparison, and M36 metric-surgery theories, every
standard initial metric admits a cap-persistence package. Proposition 16.5
then supplies one positive cutoff for each admissible parameter configuration;
at every eligible surgery cap, either a standard-flow comparison cylinder
exists on the assigned interval or a later surgery removes the corresponding
ball. Canonicality, pinching and fixed-scale conditions are primitive
hypotheses of the operation. The cutoff is chosen before the actual flow,
observation, event and cap; it depends on the fixed setup, rNext, A, eta
and theta. Forward scalar estimates on the tracked region are derived inside
M44 using a stopped cylindrical collar and the cap's absolute evolution bound.
The actual radius profile is only bounded below by rNext on the overlap.
The metric comparison pulls both tangent slots through the initial chart
and the evolving cylinder, with the cylinder's single h⁻² normalization.

Source: Morgan--Tian, Proposition 16.5, printed pp. 370--371; Claim 16.6,
Corollary 16.7, Lemma 16.8 and Corollary 16.9, pp. 371--373; Claim 16.10,
pp. 374--375. Definition 9.72(8), p. 231, gives an absolute scalar
rate, hence the forward bound for Lemma 11.2 derived and reviewed in
`reviews/contracts/2026-09-18-m44-cap-local-contract.md` and its independent
geometry and analysis reviews. It asserts no whole-flow absolute rate.

The theorem consumes an explicit `M44CapPersistencePredecessors` record.
Its M04 curvature and M13 ordinary-rescaling services are applied by the
checked supplier in `Proofs/M44/Providers.lean`. Restrict to a fixed physical
open collar buffer and normalize before applying M04's initial estimates
with all-point bounds on that carrier. The Ricci and connection equations
turn those estimates into a coordinate C2 time modulus, preserving the
collar's strict margin. All compactness, exact-ball, stopping, every-fixed-
radius survival and partial-limit work remains owned here.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- The supplied predecessor services and M34/M35/M36 packages give
the exact cutoff-first alternative of Proposition 16.5, pp. 370-375. -/
theorem repairedCapPersistence
    (P : M44CapPersistencePredecessors.{u}) :
    RepairedCapPersistenceTheory.{u} :=
  ⟨M44.exists_repaired_cap_persistence_data P⟩

end PoincareMT
