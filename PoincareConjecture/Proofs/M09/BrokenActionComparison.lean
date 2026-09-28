import PoincareConjecture.Proofs.M09.SmoothJoinAction

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem minimizing_action_le_broken_square_action {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T τmax : ℝ) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (P : BackwardTimePath F T 0 b) (hmin : IsMinimizingBackwardLPath F T 0 b P)
    (α β : ℝ → M) (D : Set ℝ) (hD : IsOpen D) (hI : Set.Icc 0 (Real.sqrt b) ⊆ D)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α D)
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ β D)
    (c : ℝ) (hc : c ∈ Set.Ioo 0 (Real.sqrt b)) (heq : α c = β c)
    (hleft : α 0 = P.curve 0) (hright : β (Real.sqrt b) = P.curve b) :
    backwardLLength F T 0 b P.curve ≤
      (∫ s in 0..c, squareCurveActionDensity F T α s) +
        ∫ s in c..Real.sqrt b, squareCurveActionDensity F T β s := by
  by_contra h
  let B := (∫ s in 0..c, squareCurveActionDensity F T α s) +
    ∫ s in c..Real.sqrt b, squareCurveActionDensity F T β s
  have hgap : 0 < (backwardLLength F T 0 b P.curve - B) / 2 := by
    dsimp only [B]
    linarith
  obtain ⟨Q, hQ0, hQb, hQa⟩ := exists_backwardPath_smoothJoin_action_le F hM04 T τmax
    hτmax hwindow b hb hmax α β D hD hI hα hβ c hc heq _ hgap
  have hPQ := hmin Q (hQ0.trans hleft) (hQb.trans hright)
  change backwardLLength F T 0 b Q.curve ≤ B +
    (backwardLLength F T 0 b P.curve - B) / 2 at hQa
  change ¬ backwardLLength F T 0 b P.curve ≤ B at h
  linarith

end PoincareConjecture.Proofs.M09
