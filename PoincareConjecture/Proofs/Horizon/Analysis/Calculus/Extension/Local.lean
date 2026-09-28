import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
open Set Metric Filter
open scoped ContDiff Topology

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_global_contDiff_germ {f : ℝ → E} {U : Set ℝ} {a : ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (ha : a ∈ U) :
    ∃ g : ℝ → E, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 a] f := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let χ : ContDiffBump a := {
    rIn := r / 4
    rOut := r / 2
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  have hsupport : tsupport χ ⊆ U := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_ball (by change r / 2 < r; linarith)).trans hrU
  refine ⟨fun t => χ t • f t, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t ∈ U
    · exact χ.contDiffAt.smul ((hf t ht).contDiffAt (hU.mem_nhds ht))
    · have hn : t ∉ tsupport χ := fun ht' => ht (hsupport ht')
      have heq := notMem_tsupport_iff_eventuallyEq.mp hn
      apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      filter_upwards [heq] with s hs
      simp [hs]
  · filter_upwards [ball_mem_nhds a χ.rIn_pos] with t ht
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall ht), one_smul]

end Poincare.Analysis
