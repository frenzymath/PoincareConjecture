import PoincareConjecture.Definitions.Ch03.RicciFlow

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable (n : ℕ) (M : Type u) [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def ShortTimeRicciFlowExistence : Prop :=
  ∀ g0 : RiemannianMetric n M,
    ∃ T : ℝ, 0 < T ∧ ∃ F : RicciFlow n M (Set.Ico 0 T), F.metric 0 = g0

def RicciFlowUniqueness : Prop :=
  ∀ (J J' : Set ℝ) (F : RicciFlow n M J) (F' : RicciFlow n M J'),
    IsLeast J 0 → IsLeast J' 0 → F.metric 0 = F'.metric 0 →
      Set.EqOn F.metric F'.metric (J ∩ J')

end PoincareConjecture
