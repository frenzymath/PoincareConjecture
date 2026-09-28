import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ConnectedClosedRegion
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {S K : Set X}

theorem ChartwisePLSphere.isConnected (s : ChartwisePLSphere e S) : IsConnected S := by
  have hdim : 1 < Module.finrank ℝ V3 := by simp
  have hrank : 1 < Module.rank ℝ V3 := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hdim
  have hunit := isConnected_sphere hrank (0 : V3) zero_le_one
  exact isConnected_iff_connectedSpace.mpr
    (s.parametrization.connectedSpace_iff.mp (isConnected_iff_connectedSpace.mp hunit))

theorem ChartwisePLSphere.isConnected_region [T2Space X] [PreconnectedSpace X]
    (s : ChartwisePLSphere e (frontier K)) (hK : IsCompact K) : IsConnected K :=
  hK.isClosed.isConnected_of_isConnected_frontier s.isConnected

end PoincareConjecture.M76
