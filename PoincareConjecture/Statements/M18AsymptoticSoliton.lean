import PoincareConjecture.Definitions.M18AsymptoticSoliton
import PoincareConjecture.Statements.M17BlowupSetup
import PoincareConjecture.Statements.M16StructuralKappa
import PoincareConjecture.Statements.Ch04.Harnack
import PoincareConjecture.Statements.Ch05.Compactness
import PoincareConjecture.Statements.Ch06.LGeometry
import PoincareConjecture.Statements.Ch06.ReducedLength
import PoincareConjecture.Statements.Ch06.ReducedVolume
















set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]


structure AncientAsymptoticSolitonPredecessors
    (K : AncientKappaSolution n M) : Prop where
  structural : AncientKappaStructuralConclusion.{u} n
  harnack : HarnackAncientTheory.{u}
  pointed_compactness :
    ∀ {T' T : ℝ}, T' < 0 → 0 < T →
      ∀ H : PointedRicciFlowCompactnessHypotheses n T' T,
        Nonempty (PointedRicciFlowCompactnessConclusion H)
  l_geometry : ∀ R : ℝ, 0 < R →
    Nonempty (LGeodesicTheory K.flow 0 R)
  reduced_length : ∀ R : ℝ, 0 < R →
    Nonempty (ReducedLengthDifferentialTheory K.flow 0 R)
  reduced_volume : ∀ R : ℝ, 0 < R →
    Nonempty (ReducedVolumeTheory K.flow 0 R)




def AncientAsymptoticSolitonConclusion
    {K : AncientKappaSolution n M} (S : AncientRescalingSequence K) : Prop :=
  Nonempty (AncientAsymptoticSolitonLimitData S)




structure AncientAsymptoticSolitonTheory (n : ℕ) : Prop where
  limits : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) (S : AncientRescalingSequence K),
    AncientAsymptoticSolitonConclusion S

end PoincareConjecture
