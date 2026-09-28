import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Definitions.Ch04.Pinching


















set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture



def M47PositiveComponentBlowupStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M],
    ∀ T : ℝ, 0 < T → ∀ F : RicciFlow 3 M (Set.Ico 0 T),
      (∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair (F.metric 0) x v w →
          0 < (F.connection 0).sectionalCurvature x v w) →
      (∀ L s : ℝ, s < T → ∃ t ∈ Set.Ioo (max 0 s) T, ∃ x : M,
        L < (F.connection t).curvatureTensorNorm x) →
      ∀ L : ℝ, ∃ s : ℝ, 0 ≤ s ∧ s < T ∧
        ∀ t ∈ Set.Ioo s T, ∀ x : M, L ≤ (F.connection t).scalarCurvature x

end PoincareConjecture
