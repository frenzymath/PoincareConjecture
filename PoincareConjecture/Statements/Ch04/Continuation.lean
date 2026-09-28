import PoincareConjecture.Statements.Ch03.ShortTime

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable (n : ℕ) (M : Type u) [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def RicciFlowContinuation : Prop :=
  ∀ T : ℝ, 0 < T → ∀ F : RicciFlow n M (Set.Ico 0 T),
    (∃ C : ℝ, ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      (F.connection t).curvatureTensorNorm x ≤ C) →
    ∃ T' : ℝ, T < T' ∧ ∃ F' : RicciFlow n M (Set.Ico 0 T'),
      Set.EqOn F.metric F'.metric (Set.Ico 0 T)

def RicciFlowLocalTheory : Prop :=
  ShortTimeRicciFlowExistence n M ∧ RicciFlowUniqueness n M ∧
    RicciFlowContinuation n M

end PoincareConjecture
