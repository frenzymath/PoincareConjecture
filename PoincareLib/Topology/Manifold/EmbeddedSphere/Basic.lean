import PoincareLib.Topology.Manifold.NeckCap.Separation
import Mathlib.Topology.Homotopy.Basic

/-!
# M53 repaired sphere-separation data

The input records a smooth embedded, null-homotopic two-sphere in a compact
connected smooth three-manifold.  The output records the source separation
implication for that primitive sphere object.  Actual surgery-event transport
is a later adapter and is not bundled into this generic topological node.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/- A primitive null-homotopy interface for a sphere map.  The continuity
   witness is explicit so later proofs need not reconstruct a ContinuousMap. -/
def IsNullHomotopicSphere {M : Type u} [TopologicalSpace M]
    (sphere : UnitTwoSphere → M) : Prop :=
  ∃ hcontinuous : Continuous sphere, ∃ x₀ : M,
    ContinuousMap.Homotopic
      ({ toFun := sphere, continuous_toFun := hcontinuous } :
        ContinuousMap UnitTwoSphere M)
      (ContinuousMap.const UnitTwoSphere x₀)

structure SmoothEmbeddedNullHomotopicSphere
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] where
  sphere : UnitTwoSphere → M
  smooth_embedding :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ sphere
  null_homotopic : IsNullHomotopicSphere sphere

structure RepairedSphereSeparationData
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] where
  /-- Every smooth embedded null-homotopic sphere separates, stated with
      primitive map and property hypotheses. -/
  separating : ∀ (S : SmoothEmbeddedNullHomotopicSphere (M := M)),
    SeparatingSphere (Set.range S.sphere)

end PoincareMT
