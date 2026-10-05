import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Transport.Theory
import PoincareLib.Topology.Manifold.EmbeddedSphere.Basic
import PoincareLib.Topology.Manifold.Smoothing.Imports.Topology.SphereConnectivity
import PoincareLib.Topology.Manifold.Smoothing.Imports.Topology.SphereDiskExtension

/-!
# Free null-homotopies on the Poincare components

Morgan--Tian, pp. 430-431, applies Proposition 15.12 to null-homotopic
surgery spheres. The supplied M02 homotopy-three-sphere conclusion and its
checked cube/sphere quotient bridge give the needed free null-homotopy.
-/

set_option autoImplicit false

open scoped Manifold ContDiff ContinuousMap

universe u

namespace PoincareMT

/-- The M02 homotopy-three-sphere conclusion makes every continuous two-sphere
freely null-homotopic, as used before Proposition 18.18, pp. 430-431. -/
theorem m57FreeSphereNullHomotopy
    (P02 : RepairedClosedTopologyProvider.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [SimplyConnectedSpace M] (f : UnitTwoSphere → M) (hf : Continuous f) :
    IsNullHomotopicSphere f := by
  obtain ⟨O⟩ := P02 (M := M)
  obtain ⟨e⟩ := O.homotopy_three_sphere
  let F : ContinuousMap UnitTwoSphere M := ⟨f, hf⟩
  have hpi (y : ThreeSphere) : Subsingleton (HomotopyGroup.Pi 2 ThreeSphere y) :=
    Proofs.M02.sphere_homotopyGroup_subsingleton_of_dim_lt (N := Fin 2) (by simp) y
  have hnull := Proofs.M02.Topology.sphere_map_nullhomotopic_of_pi_trivial
    1 hpi (e.toFun.comp F)
  obtain ⟨y, hy⟩ := hnull.comp_right e.invFun
  refine ⟨hf, y, ?_⟩
  exact (ContinuousMap.Homotopic.comp e.left_inv.symm (.refl F)).trans hy

end PoincareMT
