import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Multilinear bounds from the closed unit balls

Normalize each input without excluding zero vectors. This is the scalar
normalization used for the ambient estimates in MT2015Correction
Corollary 0.3, p. 6; see `references/ricci-flow/mapher/curve-evolution/derivations/2026-09-20-pointwise-bounds.md`.
-/

set_option autoImplicit false

open scoped BigOperators

/-- A bound on the product of closed unit balls scales by the product of
input norms, including zero inputs; the normalization for corrected
Corollary 0.3, p. 6. -/
theorem MultilinearMap.norm_le_mul_prod_of_unit_bound
    {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {G : Type*} [SeminormedAddCommGroup G] [NormedSpace ℝ G]
    (A : MultilinearMap ℝ E G) {K : ℝ}
    (hbound : ∀ w, (∀ i, ‖w i‖ ≤ 1) → ‖A w‖ ≤ K) (v : ∀ i, E i) :
    ‖A v‖ ≤ K * ∏ i, ‖v i‖ := by
  let w : ∀ i, E i := fun i => NormedSpace.normalize (v i)
  have hw (i : ι) : ‖w i‖ ≤ 1 := by
    simpa only [w, NormedSpace.normalize, Metric.mem_closedBall, dist_zero_right] using
      inv_norm_smul_mem_unitClosedBall (v i)
  have hv : (fun i => ‖v i‖ • w i) = v := by
    funext i
    exact NormedSpace.norm_smul_normalize (v i)
  have hscale := A.map_smul_univ (fun i => ‖v i‖) w
  rw [hv] at hscale
  have hnonneg : 0 ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  rw [hscale, norm_smul_of_nonneg hnonneg, mul_comm K]
  exact mul_le_mul_of_nonneg_left (hbound w hw) hnonneg
