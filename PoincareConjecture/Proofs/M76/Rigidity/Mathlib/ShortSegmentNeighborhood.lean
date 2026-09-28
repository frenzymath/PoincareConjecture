import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false

open Set
open scoped Topology

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X]

theorem ContinuousOn.exists_short_segment_mem_open
    {S : Set E} {f : E → X} (hf : ContinuousOn f S) (hS : Convex ℝ S)
    {b v : E} (hb : b ∈ S) (hv : v ∈ S) {U : Set X}
    (hU : IsOpen U) (hbU : f b ∈ U) :
    ∃ r ∈ Ioo (0 : ℝ) 1, f (AffineMap.lineMap b v r) ∈ U := by
  let c : ℝ → E := AffineMap.lineMap b v
  have hc : Continuous c := AffineMap.lineMap_continuous
  have hmap : MapsTo c (Icc 0 1) S :=
    fun _ hr => hS.segment_subset hb hv (lineMap_mem_segment ℝ b v hr)
  have hfc : ContinuousOn (f ∘ c) (Icc 0 1) := hf.comp hc.continuousOn hmap
  have hbU' : (f ∘ c) 0 ∈ U := by
    simpa only [Function.comp_apply, c, AffineMap.lineMap_apply_zero] using hbU
  have hpre : (f ∘ c) ⁻¹' U ∈ 𝓝[Icc 0 1] (0 : ℝ) :=
    (hfc 0 ⟨le_rfl, zero_le_one⟩).preimage_mem_nhdsWithin (hU.mem_nhds hbU')
  obtain ⟨W, hW, hzeroW, hWU⟩ := mem_nhdsWithin.mp hpre
  have hzero : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨r, hrW, hr⟩ := mem_closure_iff.mp hzero W hW hzeroW
  exact ⟨r, hr, hWU ⟨hrW, hr.1.le, hr.2.le⟩⟩
