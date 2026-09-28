import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension



set_option autoImplicit false
open Set Metric Filter
open scoped ContDiff Topology

namespace Poincare.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_global_contDiff_germ_finiteDimension {f : E → F} {U : Set E} {a : E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (ha : a ∈ U) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 a] f := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let χ : ContDiffBump a := {
    rIn := r / 4
    rOut := r / 2
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  have hsupport : tsupport χ ⊆ U := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_ball (by change r / 2 < r; linarith)).trans hrU
  refine ⟨fun x => χ x • f x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact χ.contDiffAt.smul ((hf x hx).contDiffAt (hU.mem_nhds hx))
    · have hn : x ∉ tsupport χ := fun h => hx (hsupport h)
      apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      simp [hy]
  · filter_upwards [ball_mem_nhds a χ.rIn_pos] with x hx
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall hx), one_smul]

end Poincare.Analysis
