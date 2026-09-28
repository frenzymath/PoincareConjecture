import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchMollificationLimit
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyConvergence
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap

namespace PoincareConjecture.M65Branch





theorem exists_cauchy_schwartz_approximation {h : ℂ → ℂ} {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hh : MemLp h 2 volume)
    (hs : Function.support h ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖h z‖ ≤ B) :
    ∃ f : ℕ → 𝓢(ℂ, ℂ),
      (∀ n, HasCompactSupport (f n : ℂ → ℂ)) ∧
      (∀ n z, ‖f n z‖ ≤ B) ∧
      (∀ n z, ‖cauchyOperator (f n) z‖ ≤ 8 * (R + 1) * B) ∧
      Tendsto (fun n => (f n).toLp 2 volume) atTop (𝓝 (hh.toLp h)) ∧
      TendstoUniformly (fun n => cauchyOperator (f n)) (cauchyOperator h) atTop := by
  obtain ⟨f, hf, hfs, hfb, hconv⟩ := exists_smooth_bounded_approximation hB hh.1 hs hb
  have hfc (n : ℕ) : HasCompactSupport (f n) :=
    (isCompact_closedBall (0 : ℂ) (R + 1)).of_isClosed_subset isClosed_closure
      (closure_minimal (hfs n) isClosed_closedBall)
  let F (n : ℕ) : 𝓢(ℂ, ℂ) := (hfc n).toSchwartzMap (hf n)
  have hgs : Function.support h ⊆ closedBall (0 : ℂ) (R + 1) :=
    hs.trans (closedBall_subset_closedBall (by linarith))
  have hL1 : Tendsto (fun n => ∫ z : ℂ, ‖f n z - h z‖) atTop (𝓝 0) := by
    simpa only [pow_one] using integral_norm_sub_pow_tendsto_of_ae
      (fun n => (hf n).continuous.aestronglyMeasurable) hh.1 hfs hgs hfb hb hconv 1
      (by norm_num)
  have hL2 : Tendsto (fun n => (F n).toLp 2 volume) atTop (𝓝 (hh.toLp h)) :=
    tendsto_toLp_two_of_bound_support (fun n => (F n).memLp 2 volume) hh
      hfs hgs hfb hb hconv
  have hC : TendstoUniformly (fun n => cauchyOperator (F n)) (cauchyOperator h) atTop :=
    tendstoUniformly_cauchyOperator_of_l1 hB
      (fun n => (hf n).continuous.aestronglyMeasurable) hh.1 hfs hgs hfb hb hL1
  refine ⟨F, hfc, hfb, ?_, hL2, hC⟩
  intro n z
  exact norm_cauchyOperator_le_of_bound (by linarith) hB
    (hf n).continuous.aestronglyMeasurable (hfs n) (hfb n) z

end PoincareConjecture.M65Branch
