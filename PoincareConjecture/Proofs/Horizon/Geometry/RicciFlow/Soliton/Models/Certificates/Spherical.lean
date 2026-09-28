import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Certificates.Defs
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Spherical.Certificate

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem repairedModelCertificateTheory_compactRound
    {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}
    (C : CompactRoundShrinkingModel G) :
    RepairedModelCertificateTheory (M24ModelInput.compactRound C) := by
  obtain ⟨certificate⟩ := exists_sphericalSpaceFormCertificate C
  exact ⟨⟨.sphericalSpaceForm certificate, trivial⟩⟩

end PoincareConjecture
