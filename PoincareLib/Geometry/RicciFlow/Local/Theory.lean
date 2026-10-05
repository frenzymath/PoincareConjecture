import PoincareLib.Geometry.RicciFlow.Basic

/-!
# The compact local Ricci-flow service

Unchanged propositions from Mapher's `Statements/Ch03/ShortTime.lean`
and `Statements/Ch04/Continuation.lean` at
`49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
Morgan--Tian, Theorem 3.11, p. 39, and Proposition 4.12, p. 68.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable (n : ℕ) (M : Type u) [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def ShortTimeRicciFlowExistence : Prop :=
  ∀ g0 : RiemannianMetric n M,
    ∃ T : ℝ, 0 < T ∧ ∃ F : RicciFlow n M (Set.Ico 0 T), F.metric 0 = g0

def RicciFlowUniqueness : Prop :=
  ∀ (J J' : Set ℝ) (F : RicciFlow n M J) (F' : RicciFlow n M J'),
    IsLeast J 0 → IsLeast J' 0 → F.metric 0 = F'.metric 0 →
      Set.EqOn F.metric F'.metric (J ∩ J')

def RicciFlowContinuation : Prop :=
  ∀ T : ℝ, 0 < T → ∀ F : RicciFlow n M (Set.Ico 0 T),
    (∃ C : ℝ, ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      (F.connection t).curvatureTensorNorm x ≤ C) →
    ∃ T' : ℝ, T < T' ∧ ∃ F' : RicciFlow n M (Set.Ico 0 T'),
      Set.EqOn F.metric F'.metric (Set.Ico 0 T)

def RicciFlowLocalTheory : Prop :=
  ShortTimeRicciFlowExistence n M ∧ RicciFlowUniqueness n M ∧
    RicciFlowContinuation n M

end PoincareMT
