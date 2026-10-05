import PoincareLib.Geometry.RicciFlow.Soliton.Models.Cylinder

/-!
# Three-dimensional shrinking-soliton alternatives

Ported from Mapher `Definitions/M20ThreeDimensionalClassification.lean` at
`49331b7d7ecad38f53e4300c3b35d6a84b2cc648`, with declarations unchanged.
Morgan--Tian, Theorem 9.42, pp. 206-208. The quotient alternative retains
the free involution without an orientation restriction.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- A 3D shrinking-soliton model certificate from the Theorem 9.42 ledger. -/
inductive ThreeDimensionalSolitonModel
    (S : GradientShrinkingSolitonData 3 M)
    (G : ShrinkingSolitonFlow S) : Type (u + 2) where
  | compactRound : CompactRoundShrinkingModel G →
      ThreeDimensionalSolitonModel S G
  | sphereLine : SphereLineProductCertificate G →
      ThreeDimensionalSolitonModel S G
  | quotientSphereLine : QuotientSphereLineCertificate G →
      ThreeDimensionalSolitonModel S G

structure ThreeDimensionalSolitonConclusion
    (S : GradientShrinkingSolitonData 3 M) where
  flow : ShrinkingSolitonFlow S
  model : ThreeDimensionalSolitonModel S flow

structure ThreeDimensionalClassificationData
    (S : GradientShrinkingSolitonData 3 M) where
  conclusion : ThreeDimensionalSolitonConclusion S

end PoincareMT
