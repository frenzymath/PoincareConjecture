import PoincareConjecture.Definitions.M24ModelCertificates

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

structure RepairedModelCertificateTheory
    {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S}
    (input : M24ModelInput G) : Prop where
  certificate : ∃ c : RepairedKappaModelCertificate G,
    M24CertificateMatches input c

end PoincareConjecture
