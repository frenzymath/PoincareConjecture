import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.LocalCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Small









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientRescalingSequence

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M}

theorem compactnessWindow_curvature_bound (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ t₀ ∈ Icc (compactnessLower j) (compactnessUpper j),
      ∀ t ∈ Icc (compactnessLower j) (compactnessUpper j),
      ∀ x ∈ ((S.rescaling k).flow.metric t₀).ball (S.base k) A,
        ((S.rescaling k).flow.connection t).curvatureTensorNorm x ≤ C := by
  intro A _
  obtain ⟨C, hC, hbound⟩ := S.uniform_curvature_on_two_time_balls P
    (compactnessUpper j) A (by linarith [compactnessUpper_base j]) (compactnessUpper_neg j)
  refine ⟨C, hC.le, Filter.Eventually.of_forall fun k t₀ ht₀ t ht x hx ↦ ?_⟩
  exact (le_abs_self _).trans (hbound k t₀ ht₀.2 t ht.2 x hx)



theorem finiteCompactness (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ) :
    Nonempty (PointedRicciFlowCompactnessConclusion
      (S.smallCompactnessHypotheses j (S.compactnessWindow_curvature_bound P j))) := by
  exact S.smallCompactnessConclusion P j (S.compactnessWindow_curvature_bound P j)

end PoincareConjecture.AncientRescalingSequence
