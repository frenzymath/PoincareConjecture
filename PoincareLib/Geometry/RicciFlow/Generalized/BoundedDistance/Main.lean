import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Compatibility
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.BoundedDistanceInputs
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Exclusion
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SameTime

open scoped PoincareMT.BoundedDistanceSource
/-!
# M28 bounded curvature at bounded distance

The actual counterexample sources produce the retained spatial limit,
positive recut and scalar-normalized backward limit. Their common source
distances give the local cone contradiction. The compact-path transfer
then supplies the unchanged dense-time estimate. Source: Morgan--Tian
Theorem 10.2, pp. 245-265; M28 derivations 07, 08 and 161e.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-
For a universal epsilon0 chosen small enough that the Appendix-A inputs and
Proposition 2.19 apply at 2 epsilon, and for every 0 < epsilon <= epsilon0,
every C > 0 and every A >= 0, choose positive D₀,D after epsilon, C and A
and before the generalized flow.
For every generalized flow satisfying the weak Hamilton--Ivey inequalities
(10.1), canonical control above four times the base scalar
on the tested slice suffices for the bound on its ball of radius `A R^(-1/2)`
when the base scalar is at least D₀. A second estimate at the same universal
epsilon0 allows whole controlled slices arbitrarily close from the left to
every earlier included time, including the tested time. This strengthens
Morgan--Tian Theorem 10.2, printed p. 245, using its proof: Claims 10.3--10.6
choose same-slice certificates, Claim 10.10 uses their strong-neck cylinders,
and Claim 10.11 retains whole-flow weak pinching. Nonnegative curvature
satisfies these inequalities on any time interval because its negative
curvature part vanishes. Transporting a compact path to
one good time and re-basing at scalar exactly twice the original base scalar
gives the dense-time estimate. The derivation, threshold margins and relative
endpoint convention are in
`reviews/contracts/2026-09-18-regular-time-canonical-boundary-round1.md`.
The original earlier-time estimate is a checked corollary. The generalized canonical
alternatives use `SingularRoundComponent` and the reviewed Appendix-A
cap/neck certificates; no legacy S^3-only round model is used.
-/
/-- Uniform bounded curvature at bounded distance, with both the
same-time and left-dense-time canonical-neighborhood hypotheses.
The actual source/cone contradiction supplies the universal threshold.
Source: MT Theorem 10.2, pp. 245-265; derivations 07, 08 and 161e. -/
theorem m28BoundedDistance (P : M28BoundedDistancePredecessors.{u}) :
    RepairedBoundedDistanceTheory.{u} := by
  obtain ⟨epsilon0, hpositive, hsmall, hexclude⟩ :=
    M28.exists_actual_counterexample_exclusion_accuracy P.m04 (Classical.choice P.m25)
  exact M28.theory_of_counterexample_exclusion P.m04 hpositive hsmall hexclude

end PoincareMT
