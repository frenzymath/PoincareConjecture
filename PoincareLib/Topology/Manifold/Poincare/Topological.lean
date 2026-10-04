import PoincareLib.Topology.Manifold.Poincare.Topological.Statement

/-! Adapted from Mapher `PoincareMT/Proofs/M79.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

/-!
# M79 proof entry

This is an admission-free universal wrapper around the concrete predecessor
services.  M75 remains the mathematical endpoint producer; M79 only applies
it through M76--M78 and exposes the primitive topological proposition.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

/-- M79: the actual M76 smoothing, M77 hypothesis transport, smooth Poincare
and M78 composition services imply `TopologicalPoincare` for every original
compact simply connected topological three-manifold. Source: Morgan--Tian
Corollary 0.2(a) through Hamilton Theorem 2(1), p. 64, and Cairns Theorem III,
p. 797, as supplied by M76. No smoothness of the original atlas is assumed
and this universal application adds no admission. -/
theorem m79TopologicalPoincare : M79TopologicalPoincareStatement.{u} := by
  intro h76 h77 h75 h78 M _ _ _ _ _ _
  let P : SmoothingBridgeInput (M := M) :=
    { connected := isConnected_univ
      nonempty := Set.univ_nonempty }
  rcases h76 M P with ⟨S⟩
  rcases h77 M P S with ⟨T⟩
  rcases h78 M P S T h75 with ⟨C⟩
  exact ⟨C.identification⟩

end PoincareMT
