import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional.Models
import PoincareLib.Geometry.RicciFlow.Compactness.Convergence
import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.Theory

/-!
# M19 two-dimensional classification statement

The conclusion keeps the compact-round ancient certificate separate from the
shrinking-soliton model output.  It also records the conversion of each
actual M18 limit into the bounded, self-similar, compact-round flow supplied
by Corollary 9.50.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

structure TwoDimensionalClassificationPredecessors : Prop where
  compactness :
    ∀ {T' T : ℝ}, T' < 0 → 0 < T →
      ∀ H : PointedRicciFlowCompactnessHypotheses 2 T' T,
        Nonempty (PointedRicciFlowCompactnessConclusion H)
  m18 :
    ∀ (K : AncientKappaSolution 2 M) (S : AncientRescalingSequence K),
      AncientAsymptoticSolitonConclusion S

/-! Corollary 9.50 is applied to the actual M18 limit rather than to an
unrelated desired-limit premise. -/
structure TwoDimensionalAsymptoticRoundTheory
    (K : AncientKappaSolution 2 M) : Prop where
  classify :
    ∀ S : AncientRescalingSequence K,
      ∃ L : AncientAsymptoticSolitonLimitData S,
        TwoDimensionalAsymptoticRoundCertificate S L

/-! The M19 2D ancient and shrinking-soliton classification output. -/
structure TwoDimensionalClassificationTheory : Prop where
  asymptotic_round : ∀ K : AncientKappaSolution 2 M,
    Nonempty (TwoDimensionalAsymptoticRoundTheory K)
  shrinking_soliton : ∀ S : GradientShrinkingSolitonData 2 M,
    Nonempty (TwoDimensionalShrinkingSolitonConclusion S)
  ancient_classification : ∀ K : AncientKappaSolution 2 M,
    Nonempty (TwoDimensionalAncientRoundCertificate K)

end PoincareMT
