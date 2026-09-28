import PoincareConjecture.Proofs.M03.Existence.ChartStateSourceSmoothNative
import Mathlib.Analysis.Calculus.ContDiff.RCLike










set_option autoImplicit false

noncomputable section

namespace PoincareConjecture.DeTurckNative

open scoped Matrix.Norms.Elementwise

variable {n : ℕ}

theorem contDiffOn_chartStateSource
    (background : MetricJet2 (n := n))
    (K : Set (ChartState (n := n)))
    (hpos : ∀ p ∈ K, p.1.PosDef) (i j : Fin n) :
    ContDiffOn ℝ 1 (fun p : ChartState (n := n) =>
      chartStateSource background p i j) K := by
  intro p hp
  exact (contDiffAt_chartStateSource background p (hpos p hp) i j).contDiffWithinAt

theorem exists_chartStateSource_lipschitzOnWith
    (background : MetricJet2 (n := n))
    (K : Set (ChartState (n := n)))
    (hconv : Convex ℝ K) (hcompact : IsCompact K)
    (hpos : ∀ p ∈ K, p.1.PosDef) (i j : Fin n) :
    ∃ L : NNReal, LipschitzOnWith L
      (fun p : ChartState (n := n) => chartStateSource background p i j) K := by
  exact (contDiffOn_chartStateSource background K hpos i j).exists_lipschitzOnWith
    one_ne_zero hconv hcompact

end PoincareConjecture.DeTurckNative

end
