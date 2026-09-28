import PoincareConjecture.Definitions.M17BlowupSetup
import PoincareConjecture.Statements.Ch06.ReducedVolume
import PoincareConjecture.Statements.M13Rescaling












set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]




def AncientReducedVolumeMinimumProvider
    (K : AncientKappaSolution n M) : Prop :=
  ∀ R : ℝ, 0 < R → Nonempty (ReducedVolumeTheory K.flow 0 R)


def AncientBlowupSetupConclusion
    (K : AncientKappaSolution n M) (reference : M) (tau : ℕ → ℝ) : Prop :=
  Nonempty (AncientBlowupSetup K reference tau)




structure AncientBlowupSetupTheory (n : ℕ) : Prop where
  setup : ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) (reference : M) (tau : ℕ → ℝ),
    (tau_pos : ∀ k, 0 < tau k) →
    (tau_tendsto : Filter.Tendsto tau Filter.atTop Filter.atTop) →
    AncientBlowupSetupConclusion K reference tau

end PoincareConjecture
