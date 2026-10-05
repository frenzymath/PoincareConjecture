import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.Mathlib.ConnectedClosedRegion
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonGeometricInputs
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connectedness from the original complete sphere parameter

The actual three-dimensional cube sphere supplies a connected whole
frontier. In a connected ambient space this gives connectedness of
the same compact cut, without an interior-connectedness claim. See045.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {S K : Set X}

/-- The frozen whole sphere parameter proves actual connectedness
and nonemptiness of its complete original carrier. See045, section1. -/
theorem ChartwisePLSphere.isConnected (s : ChartwisePLSphere e S) : IsConnected S := by
  have hdim : 1 < Module.finrank ℝ V3 := by simp
  have hrank : 1 < Module.rank ℝ V3 := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hdim
  have hunit := isConnected_sphere hrank (0 : V3) zero_le_one
  exact isConnected_iff_connectedSpace.mpr
    (s.parametrization.connectedSpace_iff.mp (isConnected_iff_connectedSpace.mp hunit))

/-- The compact original region with the given complete frontier
sphere is connected in the original preconnected ambient space.
See045, section1. -/
theorem ChartwisePLSphere.isConnected_region [T2Space X] [PreconnectedSpace X]
    (s : ChartwisePLSphere e (frontier K)) (hK : IsCompact K) : IsConnected K :=
  hK.isClosed.isConnected_of_isConnected_frontier s.isConnected

end PoincareMT.M76
