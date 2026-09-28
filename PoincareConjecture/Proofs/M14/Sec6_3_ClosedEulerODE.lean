import PoincareConjecture.Proofs.M14.Mathlib.ClosedODEUniqueness
import PoincareConjecture.Proofs.M08.ClosedChartCoefficients

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem closedChartEulerPhase_unique {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x₀ : M)
    {a b s₀ : ℝ} (hab : a < b) (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    {f g : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hsrc : ∀ s ∈ Icc a b, (f s).1 ∈ (extChartAt (𝓡 n) x₀).target)
    (hf : ∀ s ∈ Icc a b,
      HasDerivWithinAt f (M08.closedChartEulerPhase F T x₀ (Icc a b) s (f s)) (Icc a b) s)
    (hg : ∀ s ∈ Icc a b,
      HasDerivWithinAt g (M08.closedChartEulerPhase F T x₀ (Icc a b) s (g s)) (Icc a b) s)
    (hs₀ : s₀ ∈ Icc a b) (heq : f s₀ = g s₀) : EqOn f g (Icc a b) := by
  exact closedODE_interval_solution_unique hab
    ((isOpen_extChartAt_target (I := 𝓡 n) x₀).prod isOpen_univ)
    (Function.uncurry (M08.closedChartEulerPhase F T x₀ (Icc a b)))
    (M08.closedChartEulerPhase_contDiffOn F hM04 T x₀ (uniqueDiffOn_Icc hab) htime)
    (fun s hs => ⟨hsrc s hs, mem_univ _⟩) hf hg hs₀ heq

end PoincareConjecture.M14
