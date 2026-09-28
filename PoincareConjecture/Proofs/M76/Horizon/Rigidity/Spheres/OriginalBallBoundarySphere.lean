import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse








set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.ChartwisePLBall

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

end PoincareConjecture.M76.ChartwisePLBall
