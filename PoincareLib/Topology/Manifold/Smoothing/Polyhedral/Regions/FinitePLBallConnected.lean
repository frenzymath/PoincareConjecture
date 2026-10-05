import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallTopology

/-!
# Connectedness of finite PL ball carriers

The convex ball model supplies connectedness in the actual
ambient subspace topology. See Hudson 1969, pp. 15--19,
Alexander 1924, pp. 7--8 and M76 derivation 234.
-/

set_option autoImplicit false

open Set

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A finite PL ball carrier is connected, including in model
dimension zero. See Hudson pp. 15--19 and derivation 234. -/
theorem IsFinitePLBallPair.isConnected {d b : Set X}
    (hd : IsFinitePLBallPair E d b) : IsConnected d := by
  obtain ⟨_, C, _, hcv, hne, e, _, _⟩ := hd
  exact isConnected_iff_connectedSpace.mpr
    (e.connectedSpace_iff.mpr
      (isConnected_iff_connectedSpace.mp (hcv.isConnected (hne.mono interior_subset))))

end Set
