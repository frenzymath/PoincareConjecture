import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M02.SphereConnectivity
import PoincareConjecture.Proofs.M02.Topology.SphereDiskExtension









set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.simplyConnectedSpace
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) : SimplyConnectedSpace S := by
  let c : V3 ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let H := PoincareConjecture.Proofs.M02.Topology.unitSphereHomeomorph c
  let : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    PoincareConjecture.Proofs.M02.sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)
  exact (s.parametrization.symm.trans H).toHomotopyEquiv.simplyConnectedSpace

end PoincareConjecture.M76
