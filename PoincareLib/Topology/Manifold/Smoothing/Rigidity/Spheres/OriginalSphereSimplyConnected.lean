import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonGeometricInputs
import PoincareLib.Topology.Manifold.Smoothing.Imports.Topology.SphereConnectivity
import PoincareLib.Topology.Manifold.Smoothing.Imports.Topology.SphereDiskExtension

/-!
# Simple connectedness of the complete original PL sphere

Transport the known Euclidean sphere result through the radial norm
change and the complete original sphere parametrization. This rules
out an essential rim on a spherical component of a compressed phase.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.simplyConnectedSpace
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) : SimplyConnectedSpace S := by
  let c : V3 ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let H := PoincareMT.Proofs.M02.Topology.unitSphereHomeomorph c
  let : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    PoincareMT.Proofs.M02.sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)
  exact (s.parametrization.symm.trans H).toHomotopyEquiv.simplyConnectedSpace

end PoincareMT.M76
