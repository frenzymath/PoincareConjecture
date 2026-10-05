import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Certificate
import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional.Classification
import PoincareLib.Geometry.RicciFlow.Local.Theory

/-!
# Three-dimensional shrinking-soliton classification

The predecessor and output declarations are unchanged from Mapher's M20
statement at `49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
Morgan--Tian, Theorem 9.42, pp. 206-208, and Corollaries 9.52-9.54,
pp. 216-218. The proof is assembled in `Classification/Assembly.lean`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

structure ThreeDimensionalClassificationPredecessors : Prop where
  local_flow :
    ∀ (n : ℕ) (N : Type u) [TopologicalSpace N] [T2Space N]
      [SecondCountableTopology N]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
      [IsManifold (𝓡 n) ∞ N] [CompactSpace N],
      RicciFlowLocalTheory n N
  curvature : RicciFlowCurvatureTheory.{u}
  harnack : HarnackAncientTheory.{u}
  pointed_compactness :
    ∀ {n : ℕ} {T' T : ℝ}, T' < 0 → 0 < T →
      ∀ H : PointedRicciFlowCompactnessHypotheses n T' T,
        Nonempty (PointedRicciFlowCompactnessConclusion H)
  m18 : AncientAsymptoticSolitonTheory.{u} 3
  two_dimensional :
    ∀ {N : Type u} [TopologicalSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
      [IsManifold (𝓡 2) ∞ N] [MeasurableSpace N] [BorelSpace N]
      [T2Space N] [T3Space N] [SecondCountableTopology N]
      [ConnectedSpace N],
      TwoDimensionalClassificationTheory (M := N)

structure ThreeDimensionalAsymptoticClassificationTheory
    (K : AncientKappaSolution 3 M) : Prop where
  classify :
    ∀ S : AncientRescalingSequence K,
      ∃ L : AncientAsymptoticSolitonLimitData S,
        ThreeDimensionalAsymptoticClassificationCertificate S L

structure ThreeDimensionalClassificationTheory : Prop where
  classify : ∀ S : GradientShrinkingSolitonData 3 M,
    Nonempty (ThreeDimensionalClassificationData S)
  asymptotic_classify : ∀ K : AncientKappaSolution 3 M,
    Nonempty (ThreeDimensionalAsymptoticClassificationTheory K)

end PoincareMT
