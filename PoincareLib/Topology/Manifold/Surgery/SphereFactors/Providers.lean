import PoincareLib.Topology.Manifold.Surgery.Reconstruction.Main
import PoincareLib.Topology.Manifold.Surgery.SphereFactors.Main

/-!
# M73 application to the actual M72 output

Choose the reconstruction returned by M72 and classify precisely its indexed
factors. The checked application introduces no further admission.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

/-- Apply the M72 finite reconstruction and M73 factor classification to the
actual input. Source: Morgan--Tian Corollary 15.4(2), pp. 358--359, using
the checked M72 reconstruction theorem. -/
theorem m73SphereFactors_from_M72
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    {N : NormalizedInitialMetric (M := M)} (I : M72ReconstructionInput N) :
    ∃ C : M72ReconstructionConclusion I, Nonempty (M73SphereFactorConclusion I C) := by
  obtain ⟨C⟩ := m72FiniteReconstruction I
  exact ⟨C, m73SphereFactors I C⟩

end PoincareMT
