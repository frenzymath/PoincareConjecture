import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Uniform

set_option autoImplicit false

open Set Filter
open scoped Topology

theorem continuousWithinAt_zero_of_initial_norm_bound
    {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F]
    {f : ℝ × X → F} {g : X → F} {T C : ℝ} {x : X} {K : Set X}
    (hK : K ∈ 𝓝 x) (hg : ContinuousAt g x) (hzero : f (0, x) = g x)
    (hbound : ∀ t ∈ Ico 0 T, ∀ y ∈ K, ‖f (t, y) - g y‖ ≤ C * t) :
    ContinuousWithinAt f (Ico 0 T ×ˢ univ) (0, x) := by
  have hspace : Tendsto (fun p : ℝ × X => p.2)
      (𝓝[Ico 0 T ×ˢ univ] (0, x)) (𝓝 x) :=
    continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have htime : Tendsto (fun p : ℝ × X => C * p.1)
      (𝓝[Ico 0 T ×ˢ univ] (0, x)) (𝓝 0) := by
    have hc : ContinuousAt (fun p : ℝ × X => C * p.1) (0, x) := by fun_prop
    simpa only [mul_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsmall : Tendsto (fun p : ℝ × X => f p - g p.2)
      (𝓝[Ico 0 T ×ˢ univ] (0, x)) (𝓝 0) := by
    apply squeeze_zero_norm' _ htime
    filter_upwards [self_mem_nhdsWithin, hspace.eventually hK] with p hp hpK
    exact hbound p.1 hp.1 p.2 hpK
  have hbase := hg.tendsto.comp hspace
  change Tendsto f (𝓝[Ico 0 T ×ˢ univ] (0, x)) (𝓝 (f (0, x)))
  rw [hzero]
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hsmall.add hbase
