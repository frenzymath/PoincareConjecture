import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.OriginalBallTopology
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.Mathlib.CubePrismBoundary
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Polyhedra.Mathlib.PolyhedralPLInverse

/-!
# The whole marked boundary of an actual PL ball is a PL sphere

Restrict the original cube parametrization to the complete cube sphere.
Its finite triangulation supplies the original-atlas PL certificate.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.ChartwisePLBall

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {D S : Set X}

theorem nonempty_boundarySphere (b : ChartwisePLBall e D S) :
    Nonempty (ChartwisePLSphere e S) := by
  obtain ⟨K, hK, hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  exact ⟨{
    parametrization := b.parametrization.restrictSubsets sphere_subset_closedBall
      b.boundary_subset (fun x => (b.boundary_eq x).symm)
    map := b.map
    map_eq := fun x => b.map_eq ⟨x, sphere_subset_closedBall x.property⟩
    piecewiseAffine := hKs ▸ b.piecewiseAffine.restrict_finite K hK
      (hKs.subset.trans sphere_subset_closedBall)
  }⟩

end PoincareMT.M76.ChartwisePLBall
