import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

open Set Metric
open scoped NNReal

namespace PoincareConjecture.M10

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_lipschitz_extension_of_concave {f : E → ℝ} {x : E} {r : ℝ}
    (hr : 0 < r) (hf : ContinuousOn f (ball x (4 * r)))
    (hconc : ConcaveOn ℝ (ball x (4 * r)) f) :
    ∃ (L : ℝ≥0) (g : E → ℝ), LipschitzWith L g ∧ EqOn f g (ball x (2 * r)) := by
  have hsub : closedBall x (3 * r) ⊆ ball x (4 * r) :=
    closedBall_subset_ball (by linarith)
  obtain ⟨A, hA⟩ := (isCompact_closedBall x (3 * r)).bddAbove_image
    ((hf.mono hsub).abs)
  have hbound (y : E) (hy : dist y x < 3 * r) : |f y| ≤ A :=
    hA ⟨y, mem_closedBall.mpr hy.le, rfl⟩
  have hconc' : ConcaveOn ℝ (ball x (3 * r)) f :=
    hconc.subset (ball_subset_ball (by linarith)) (convex_ball _ _)
  have hLip := hconc'.lipschitzOnWith_of_abs_le hr hbound
  rw [show 3 * r - r = 2 * r by ring] at hLip
  obtain ⟨g, hg, heq⟩ := hLip.extend_real
  exact ⟨_, g, hg, heq⟩

end PoincareConjecture.M10
