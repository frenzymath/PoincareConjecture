import PoincareLib.Topology.Manifold.ConnectedSum.Reconstruction
import PoincareLib.Topology.Homotopy.Groups.SimplyConnected

/-!
# Simple connectedness of the reconstructed time-zero slice

The initial identification in the global-flow certificate transports the
ambient simply connectedness assumption to the exact slice used by the M72
assembly.  This is the M71 transport argument with the irrelevant compactness
assumption removed.

Source: Morgan--Tian Theorem 15.9, pp. 363--364, and the time-zero branch of
Theorem 18.1, pp. 415 and 431--432.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

/-- M52's initial identification transports the ambient simply connectedness
assumption to the time-zero slice used by the M72 ledger. Source:
Morgan--Tian Theorem 15.9, pp. 363--364. -/
theorem m73_sliceZero_simplyConnected
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N) :
    SimplyConnectedSpace (I.global.certificate.flow.slice 0).carrier := by
  let e := I.global.certificate.initial_identification.toHomeomorph.symm
  exact e.toHomotopyEquiv.simplyConnectedSpace

end PoincareMT
