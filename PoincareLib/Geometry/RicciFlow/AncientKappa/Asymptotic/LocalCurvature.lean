import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.TimeBounds
import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.SpatialCurvature

/-!
# Uniform local curvature of the specified ancient rescalings

The reduced-length time comparison controls the base scalar at one later
time. Integrated Harnack then controls every two-time spatial ball below
the chosen negative time bound. These are the curvature estimates used in
Morgan--Tian, Theorem 9.11, pp. 183-185.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.AncientRescalingSequence

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

/-- Full curvature is bounded uniformly in the sequence on two-time balls
below any fixed negative time sufficiently close to zero. -/
theorem uniform_curvature_on_two_time_balls {K : AncientKappaSolution n M}
    (S : AncientRescalingSequence K) (P : AncientAsymptoticSolitonPredecessors K)
    (a r : ℝ) (ha : -2 ≤ a) (ha0 : a < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ s ≤ a, ∀ t ≤ a,
      ∀ x ∈ ((S.rescaling k).flow.metric s).ball (S.base k) r,
        |((S.rescaling k).flow.connection t).curvatureTensorNorm x| ≤ C := by
  let σ := -a / 2
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσ1 : σ ≤ 1 := by dsimp [σ]; linarith
  let B := 3 * (n : ℝ) / (2 * σ ^ 3)
  let E := Real.exp (r ^ 2 / (2 * (-σ - a)))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : 0 < E := Real.exp_pos _
  refine ⟨B * E + 1, by positivity, ?_⟩
  intro k s hs t ht x hx
  have hbound := (S.rescaling k).curvature_le_scalar_exp_on_two_time_ball P
    hs ht (show a < -σ by dsimp [σ]; linarith) (neg_neg_of_pos hσ) (S.base k) x hx
  have hscalar := S.scalar_at_base_time_le P k σ hσ hσ1
  rw [abs_of_nonneg (show 0 ≤ ((S.rescaling k).flow.connection t).curvatureTensorNorm x
    from Real.sqrt_nonneg _)]
  exact (hbound.trans (mul_le_mul_of_nonneg_right hscalar hE.le)).trans (by linarith)

end PoincareMT.AncientRescalingSequence
