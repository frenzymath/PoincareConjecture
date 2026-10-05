import PoincareLib.Geometry.RicciFlow.Soliton.Models.Refined

/-!
# Refining the supplied shrinking-flow model

The declaration body is unchanged from Mapher
`PoincareMT/Statements/M24ModelCertificates.lean` at
`49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
Morgan--Tian, Theorem 9.42, pp. 206-208.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- Refine one actual model, preserving its flow and exact product/quotient. -/
structure RepairedModelCertificateTheory
    {S : GradientShrinkingSolitonData 3 M}
    {G : ShrinkingSolitonFlow S}
    (input : M24ModelInput G) : Prop where
  certificate : ∃ c : RepairedKappaModelCertificate G,
    M24CertificateMatches input c

end PoincareMT
