import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Topology.Homotopy.Basic










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



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


  separating : ∀ (S : SmoothEmbeddedNullHomotopicSphere (M := M)),
    SeparatingSphere (Set.range S.sphere)

end PoincareConjecture
