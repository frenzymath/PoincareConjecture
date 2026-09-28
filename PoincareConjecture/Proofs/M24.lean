import PoincareConjecture.Statements.M24ModelCertificates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Certificates

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem m24ModelCertificates
    {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S}
    (input : M24ModelInput G) :
    RepairedModelCertificateTheory input := by
  exact horizon_m24ModelCertificates input

theorem m24ModelCertificateTheory
    {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S}
    (input : M24ModelInput G) :
    RepairedModelCertificateTheory input :=
  m24ModelCertificates input

end PoincareConjecture
