import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Certificates.Spherical
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Certificates.QuotientTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Involution.NormalForm

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem horizon_m24ModelCertificates
    {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S}
    (input : M24ModelInput G) :
    RepairedModelCertificateTheory input := by
  cases input with
  | compactRound C => exact repairedModelCertificateTheory_compactRound C
  | sphereLine model => exact ⟨⟨.sphereLine model, rfl⟩⟩
  | quotientSphereLine q =>
    obtain ⟨transport⟩ := exists_quotientFlowTransport q
    exact ⟨exists_refinedQuotientCertificate q transport⟩

end PoincareConjecture
