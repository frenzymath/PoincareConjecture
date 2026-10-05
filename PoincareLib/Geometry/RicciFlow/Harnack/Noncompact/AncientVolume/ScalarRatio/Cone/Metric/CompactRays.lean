import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Compactness.Compact

/-!
# Compactness of based minimizing rays

Actual unit-speed rays form a closed subset of a product of compact metric
balls. This pointwise compactness is the compactness input for the unit link
of the asymptotic cone; no cone or quotient compactness is assumed.

Reference: Kleiner--Lott, Theorem 41.2, Case 2, p. 2677, and Appendix G,
p. 2852 (corrected 2013). This elementary compactness step is unnumbered.
-/

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X]

/-- Unit-speed minimizing rays based at a prescribed point, parametrized by
nonnegative real distance. -/
def basedMinimizingRays (p : X) : Set (ℝ≥0 → X) :=
  {γ | γ 0 = p ∧ Isometry γ}

theorem isClosed_basedMinimizingRays (p : X) :
    IsClosed (basedMinimizingRays p) := by
  have h0 : IsClosed {γ : ℝ≥0 → X | γ 0 = p} :=
    isClosed_eq (continuous_apply 0) continuous_const
  have hdist : IsClosed {γ : ℝ≥0 → X | ∀ s t, dist (γ s) (γ t) = dist s t} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun t =>
      isClosed_eq ((continuous_apply s).dist (continuous_apply t)) continuous_const
  simpa only [basedMinimizingRays, isometry_iff_dist_eq, ofPred_and] using h0.inter hdist

/-- Properness gives compactness of all based minimizing rays in the
pointwise topology, including compactness across all nonnegative times. -/
theorem isCompact_basedMinimizingRays [ProperSpace X] (p : X) :
    IsCompact (basedMinimizingRays p) := by
  have hballs : IsCompact (Set.pi univ (fun t : ℝ≥0 => Metric.closedBall p (t : ℝ))) :=
    isCompact_univ_pi fun t : ℝ≥0 => isCompact_closedBall p (t : ℝ)
  apply hballs.of_isClosed_subset (isClosed_basedMinimizingRays p)
  intro γ hγ t _
  rw [Metric.mem_closedBall, ← hγ.1, hγ.2.dist_eq]
  simp

instance basedMinimizingRays_compactSpace [ProperSpace X] (p : X) :
    CompactSpace (basedMinimizingRays p) :=
  isCompact_iff_compactSpace.mp (isCompact_basedMinimizingRays p)

end Poincare.AncientVolume.ScalarRatio
