import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations










set_option autoImplicit false

open Set Filter Metric
open scoped ContDiff Topology

namespace PoincareConjecture.M14

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem exists_closedTime_state_extension {C : Set ℝ} {U : Set E} (hU : IsOpen U)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f (C ×ˢ U)) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ r > (0 : ℝ), ∃ g : ℝ × E → F,
      closedBall x₀ r ⊆ U ∧ ContDiffOn ℝ ∞ g (C ×ˢ univ) ∧
        EqOn g f (C ×ˢ closedBall x₀ r) := by
  obtain ⟨e, he, heU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  let χ : ContDiffBump x₀ := {
    rIn := e / 4
    rOut := e / 2
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  let g : ℝ × E → F := fun z => χ z.2 • f z
  have hsupport : tsupport χ ⊆ U := by
    rw [χ.tsupport_eq]
    intro x hx
    apply heU
    have hd : dist x x₀ ≤ e / 2 := hx
    change dist x x₀ < e
    linarith
  have hχ : ContDiff ℝ ∞ (fun z : ℝ × E => χ z.2) := χ.contDiff.comp contDiff_snd
  have hlocal : ContDiffOn ℝ ∞ g (C ×ˢ U) := hχ.contDiffOn.smul hf
  have hg : ContDiffOn ℝ ∞ g (C ×ˢ univ) := by
    intro z hz
    by_cases hx : z.2 ∈ U
    · apply (hlocal z ⟨hz.1, hx⟩).mono_of_mem_nhdsWithin
      have hN : (univ : Set ℝ) ×ˢ U ∈ 𝓝 z :=
        (isOpen_univ.prod hU).mem_nhds ⟨mem_univ _, hx⟩
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hN] with y hy hyU
      exact ⟨hy.1, hyU.2⟩
    · have hnot : z.2 ∉ tsupport χ := fun h => hx (hsupport h)
      have hzero : g =ᶠ[𝓝 z] fun _ => (0 : F) := by
        filter_upwards [continuousAt_snd.tendsto.eventually
          (notMem_tsupport_iff_eventuallyEq.mp hnot)] with y hy
        change χ y.2 • f y = 0
        simp only [hy, Pi.zero_apply, zero_smul]
      exact (contDiffAt_const.congr_of_eventuallyEq hzero).contDiffWithinAt
  refine ⟨e / 4, by positivity, g, ?_, hg, ?_⟩
  · intro x hx
    apply heU
    have hd : dist x x₀ ≤ e / 4 := hx
    change dist x x₀ < e
    linarith
  · intro z hz
    change χ z.2 • f z = f z
    rw [χ.one_of_mem_closedBall hz.2, one_smul]

end PoincareConjecture.M14
