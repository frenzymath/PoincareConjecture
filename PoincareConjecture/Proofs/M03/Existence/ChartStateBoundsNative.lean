import PoincareConjecture.Proofs.M03.Existence.ChartStateContinuity
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Bornology

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ}

theorem exists_chartStateSource_norm_bound
    (background : MetricJet2 (n := n))
    (K : Set (ChartState (n := n)))
    (hK : IsCompact K)
    (hpos : ∀ p ∈ K, p.1.PosDef)
    (i j : Fin n) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ p ∈ K, ‖chartStateSource background p i j‖ ≤ B := by
  have hcont : ContinuousOn
      (fun p : ChartState (n := n) =>
        ‖chartStateSource background p i j‖) K := by
    intro p hp
    exact ((continuousAt_chartStateSource background p (hpos p hp) i j).norm
      ).continuousWithinAt
  have himage : IsCompact
      ((fun p : ChartState (n := n) =>
        ‖chartStateSource background p i j‖) '' K) :=
    hK.image_of_continuousOn hcont
  have hbdd : IsBounded
      ((fun p : ChartState (n := n) =>
        ‖chartStateSource background p i j‖) '' K) :=
    himage.isBounded
  obtain ⟨r, hr⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hbdd
  refine ⟨max r 0, le_max_right _ _, ?_⟩
  intro p hp
  have hpball :
      ‖chartStateSource background p i j‖ ∈ Metric.closedBall (0 : ℝ) r :=
    hr ⟨p, hp, rfl⟩
  have hdist := (Metric.mem_closedBall.mp hpball)
  have hnorm : ‖chartStateSource background p i j‖ ≤ r := by
    simpa only [dist_zero_right, norm_norm] using hdist
  exact hnorm.trans (le_max_left r 0)

end PoincareConjecture.DeTurckNative
