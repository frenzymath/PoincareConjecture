import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeChartCorrection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem m64ChartReadable_local_observed_correction
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e) (p : M) :
    ∃ (U : Set M) (r B : ℝ) (T : E → M), IsOpen U ∧ p ∈ U ∧ 0 < r ∧ 0 ≤ B ∧
      (∀ q ∈ U, T (e q) = q ∧ dist (e q) (e p) < r / 2) ∧
      (∀ y ∈ closedBall (e p) r, ContMDiffAt (𝓡 m) (𝓡 n) 1 T y) ∧
      ∀ y ∈ closedBall (e p) r, ‖fderiv ℝ (e ∘ T) y‖ ≤ B := by
  obtain ⟨U, r, _, T, hU, hp, hr, _, hfix, hT, _⟩ :=
    m64ChartReadable_local_correction g e he hread p
  have hG (y : E) (hy : y ∈ closedBall (e p) r) : ContDiffAt ℝ 1 (e ∘ T) y :=
    contMDiffAt_iff_contDiffAt.mp (he.contMDiffAt.comp y (hT y hy))
  have hc : ContinuousOn (fderiv ℝ (e ∘ T)) (closedBall (e p) r) :=
    fun y hy => ((hG y hy).continuousAt_fderiv (by norm_num)).continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall (e p) r).exists_bound_of_continuousOn hc
  exact ⟨U, r, max B 0, T, hU, hp, hr, le_max_right _ _, hfix, hT,
    fun y hy => (hB y hy).trans (le_max_left _ _)⟩

end PoincareConjecture
