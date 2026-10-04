import PoincareLib.Topology.Manifold.Poincare.Final.Statement
import PoincareLib.Topology.Manifold.Poincare.Final.Providers

/-!
# M90 proof entry

The first theorem is the closed field-copy adapter. The second applies the
actual milestone suppliers and produces both endpoints without any input
service. It adds no admission to the milestone skeleton.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Copy the two concrete M80 endpoints into the final conclusion. This is
logical packaging of the unchanged `PoincareMT.Statement` propositions. -/
theorem m90FinalAssembly : M90FinalAssemblyStatement.{u} := by
  intro A
  exact ⟨{ smooth := A.smooth, topological := A.topological }⟩

/-- M90: the actual numbered milestones supply smooth and topological
Poincare with their original Mathlib-only hypotheses and no input service.
M01/M02/M83 provide initial data, M71 gives extinction of one calibrated
flow, M72--M75 reconstruct that same flow, and M76--M80 supply the topological
passage and endpoint package. Sources: Morgan--Tian Corollary 0.2(a),
Corollary 15.4(2), pp. 358-359, and Theorem 18.1, p. 415; compatible
smoothing is the separately reviewed M76 obligation. No endpoint admission
is introduced by this checked assembly. -/
theorem m90FinalAssemblyFromMilestones : M90CompleteAssemblyStatement.{u} := by
  obtain ⟨A⟩ := m90EndpointPackageFromMilestones.{u}
  exact m90FinalAssembly A

end PoincareMT
