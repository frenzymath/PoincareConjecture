import PoincareLib.Topology.Homotopy.Sphere.ThreeSphere

/-! Adapted from Mapher `PoincareMT/Statement.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

/-!
# Poincare endpoint propositions

The smooth conclusion is Morgan-Tian Corollary 0.2(a). The topological
conclusion has no smoothness assumption. These declarations specify the
targets; they do not prove either proposition. See reviews/contracts/endpoint-v1.md.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- Smooth Poincare, Morgan-Tian Corollary 0.2(a). -/
def SmoothPoincare : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [CompactSpace M] [SimplyConnectedSpace M],
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) M ThreeSphere ∞)

/-- Topological Poincare, without any smooth structure assumption. -/
def TopologicalPoincare : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M], Nonempty (M ≃ₜ ThreeSphere)

end PoincareMT
