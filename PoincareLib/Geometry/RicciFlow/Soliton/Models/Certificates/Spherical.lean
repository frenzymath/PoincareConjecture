import PoincareLib.Geometry.RicciFlow.Soliton.Models.Certificates.Defs
import PoincareLib.Geometry.RicciFlow.Soliton.Models.Spherical.Certificate

/-!
# The spherical branch of refined model certificates

The compact-round input produces the spherical constructor of the frozen
parent conclusion on the same flow.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- Apply the spherical producer to the compact-round branch of M24. -/
theorem repairedModelCertificateTheory_compactRound
    {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}
    (C : CompactRoundShrinkingModel G) :
    RepairedModelCertificateTheory (M24ModelInput.compactRound C) := by
  obtain ⟨certificate⟩ := exists_sphericalSpaceFormCertificate C
  exact ⟨⟨.sphericalSpaceForm certificate, trivial⟩⟩

end PoincareMT
