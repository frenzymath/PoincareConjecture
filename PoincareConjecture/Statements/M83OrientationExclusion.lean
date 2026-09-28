import PoincareConjecture.Definitions.Ch01.Topology
import PoincareConjecture.Definitions.Ch17.GlobalSurgery













set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture



def M83OrientationExclusionStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M],
    OrientationCompatibleAtlas M → NoTrivialNormalProjectivePlane (M := M)

end PoincareConjecture
