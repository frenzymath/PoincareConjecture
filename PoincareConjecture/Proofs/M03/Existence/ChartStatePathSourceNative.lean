import PoincareConjecture.Proofs.M03.Existence.ChartStateBoundsNative
import PoincareConjecture.Proofs.M03.Existence.ChartStateLipschitzNative

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open scoped Matrix.Norms.Elementwise

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ}

theorem continuousOn_chartStateSource_path
    (background : MetricJet2 (n := n))
    {T : ℝ} {q : ℝ → ChartState (n := n)}
    (hq : ContinuousOn q (Set.Ico (0 : ℝ) T))
    (hpos : ∀ t ∈ Set.Ico (0 : ℝ) T, (q t).1.PosDef)
    (i j : Fin n) :
    ContinuousOn
      (fun t => chartStateSource background (q t) i j)
      (Set.Ico (0 : ℝ) T) := by
  intro t ht
  have hsource := continuousAt_chartStateSource background (q t)
    (hpos t ht) i j
  have hcomp := hsource.comp_continuousWithinAt (hq t ht)
  change ContinuousWithinAt ((fun p => chartStateSource background p i j) ∘ q)
    (Set.Ico (0 : ℝ) T) t
  exact hcomp

theorem exists_chartStateSource_path_norm_bound
    (background : MetricJet2 (n := n))
    {T : ℝ} {q : ℝ → ChartState (n := n)}
    (hq : ContinuousOn q (Set.Icc (0 : ℝ) T))
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) T, (q t).1.PosDef)
    (i j : Fin n) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        ‖chartStateSource background (q t) i j‖ ≤ B := by
  have hcompact : IsCompact (q '' Set.Icc (0 : ℝ) T) :=
    isCompact_Icc.image_of_continuousOn hq
  have hpos' : ∀ p ∈ q '' Set.Icc (0 : ℝ) T, p.1.PosDef := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := hp
    exact hpos t ht
  obtain ⟨B, hB, hbound⟩ := exists_chartStateSource_norm_bound
    background (q '' Set.Icc (0 : ℝ) T) hcompact hpos' i j
  refine ⟨B, hB, ?_⟩
  intro t ht
  exact hbound (q t) ⟨t, ht, rfl⟩

theorem exists_chartStateSource_lipschitzOnWith_closedBall
    (background : MetricJet2 (n := n))
    (p : ChartState (n := n)) (r : ℝ)
    (_hr : 0 ≤ r)
    (hpos : ∀ q ∈ Metric.closedBall p r, q.1.PosDef)
    (i j : Fin n) :
    ∃ L : NNReal,
      LipschitzOnWith L
        (fun q : ChartState (n := n) => chartStateSource background q i j)
        (Metric.closedBall p r) := by
  have hcompact : IsCompact (Metric.closedBall p r) :=
    ProperSpace.isCompact_closedBall p r
  have hconv : Convex ℝ (Metric.closedBall p r) :=
    convex_closedBall p r
  exact exists_chartStateSource_lipschitzOnWith background
    (Metric.closedBall p r) hconv hcompact hpos i j

theorem exists_chartStateSource_norm_bound_closedBall
    (background : MetricJet2 (n := n))
    (p : ChartState (n := n)) (r : ℝ)
    (_hr : 0 ≤ r)
    (hpos : ∀ q ∈ Metric.closedBall p r, q.1.PosDef)
    (i j : Fin n) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ q ∈ Metric.closedBall p r,
        ‖chartStateSource background q i j‖ ≤ B := by
  exact exists_chartStateSource_norm_bound background
    (Metric.closedBall p r) (ProperSpace.isCompact_closedBall p r)
    hpos i j

end PoincareConjecture.DeTurckNative

end
