import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalization
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

set_option autoImplicit false

open Set Metric Filter
open scoped Topology SchwartzMap ContDiff

namespace PoincareConjecture.M65Interior

theorem exists_disk_cutoff {U : Set LoopPlane} (hU : IsOpen U)
    (x : LoopPlane) {R : ℝ} (hR : 0 ≤ R) (hRU : closedBall x R ⊆ U) :
    ∃ θ : 𝓢(LoopPlane, ℝ), HasCompactSupport θ ∧ tsupport θ ⊆ U ∧
      ∀ z ∈ closedBall x R,
        (θ =ᶠ[𝓝 z] fun _ => (1 : ℝ)) ∧ θ z = 1 ∧ fderiv ℝ θ z = 0 := by
  obtain ⟨δ, hδ, hδU⟩ :=
    (isCompact_closedBall x R).exists_cthickening_subset_open hU hRU
  rw [cthickening_closedBall hδ.le hR] at hδU
  let c : ContDiffBump x :=
    { rIn := R + δ / 3
      rOut := R + 2 * δ / 3
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  let θ : 𝓢(LoopPlane, ℝ) := c.hasCompactSupport.toSchwartzMap c.contDiff
  refine ⟨θ, c.hasCompactSupport, ?_, ?_⟩
  · change tsupport c ⊆ U
    rw [c.tsupport_eq]
    apply Subset.trans _ hδU
    exact closedBall_subset_closedBall (by dsimp only [c]; linarith)
  · intro z hz
    have hz' : z ∈ ball x c.rIn := by
      change dist z x < R + δ / 3
      have hzd : dist z x ≤ R := hz
      linarith
    have heq : θ =ᶠ[𝓝 z] fun _ => (1 : ℝ) := c.eventuallyEq_one_of_mem_ball hz'
    refine ⟨heq, heq.eq_of_nhds, ?_⟩
    rw [heq.fderiv_eq, fderiv_const_apply]

end PoincareConjecture.M65Interior
