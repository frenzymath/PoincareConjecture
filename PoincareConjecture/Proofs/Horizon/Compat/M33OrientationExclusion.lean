import PoincareConjecture.Definitions.Ch17.GlobalSurgery
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Atlas.OpenEmbedding
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Atlas.LocalOrientation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Nonorientable

set_option autoImplicit false
open scoped Manifold ContDiff Topology
universe u
namespace PoincareConjecture

theorem m33OrientationExclusion
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (A : OrientationCompatibleAtlas M) :
    NoTrivialNormalProjectivePlane (M := M) := by
  rintro ⟨f, hf⟩
  let X := RealProjectiveTwo × Poincare.Topology.Orientation.ProjectivePlane.NormalInterval
  let : Nonempty X := Nonempty.map Poincare.Topology.Orientation.ProjectivePlane.projectivePlaneCover inferInstance
  let : T2Space X := hf.isEmbedding.t2Space
  let : SecondCountableTopology X := hf.isEmbedding.secondCountableTopology
  let P := Poincare.Topology.Orientation.ProjectivePlane.positiveThreeAtlasOpenEmbedding f hf
    (Poincare.Topology.positiveThreeAtlasOfSigned M A)
  let : ChartedSpace (EuclideanSpace Real (Fin 3)) X := P.charts
  let : LocallyCompactSpace X :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace Real (Fin 3)) X
  obtain ⟨O⟩ := Poincare.Topology.Orientation.ProjectivePlane.exists_localOrientation_of_positiveThreeAtlas P
  exact Poincare.Topology.Orientation.ProjectivePlane.projectivePlaneThickening_not_orientable O

end PoincareConjecture
