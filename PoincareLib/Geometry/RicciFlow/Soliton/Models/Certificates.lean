import PoincareLib.Geometry.RicciFlow.Soliton.Models.Certificates.Spherical
import PoincareLib.Geometry.RicciFlow.Soliton.Models.Certificates.QuotientTransport
import PoincareLib.Geometry.RicciFlow.Soliton.Models.Involution.NormalForm

/-!
# Refined certificates for shrinking-soliton models

Each supplied model is refined on the same flow. The compact-round branch
uses a finite free spherical quotient; the product branch is retained; the
quotient branch receives its constructed normal form and curvature transports.
Morgan--Tian, Theorems 1.11 and 9.42, pp. 8-9 and 206-208, and
Proposition 9.58, pp. 220-221.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- Refine the supplied model without changing its flow or quotient. -/
theorem m24ModelCertificates
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

end PoincareMT
