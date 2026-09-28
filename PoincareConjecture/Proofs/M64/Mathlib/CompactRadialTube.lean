import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas




set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture





theorem m64_exists_extended_radial_tube
    {E : Type*} [TopologicalSpace E] [SMul ℝ E] [ContinuousSMul ℝ E]
    {O : Set E} (hO : IsOpen O) {v : E}
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ O) :
    ∃ A > (1 : ℝ), ∃ W ∈ 𝓝 v, ∀ w ∈ W, ∀ t ∈ Icc (0 : ℝ) A, t • w ∈ O := by
  have hpre : IsOpen {p : ℝ × E | p.1 • p.2 ∈ O} :=
    hO.preimage (continuous_fst.smul continuous_snd)
  have hsub : Icc (0 : ℝ) 1 ×ˢ ({v} : Set E) ⊆ {p : ℝ × E | p.1 • p.2 ∈ O} := by
    rintro ⟨t, w⟩ ⟨ht, hw⟩
    have hwv : w = v := hw
    change t • w ∈ O
    simpa only [hwv] using hsegment t ht
  obtain ⟨X, W, hX, hW, hIX, hvW, hXW⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hpre hsub
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp
    (hX.mem_nhds (hIX (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)))
  refine ⟨1 + delta / 2, by linarith, W, hW.mem_nhds (hvW (mem_singleton v)), ?_⟩
  intro w hw t ht
  change (t, w) ∈ {p : ℝ × E | p.1 • p.2 ∈ O}
  apply hXW
  refine ⟨?_, hw⟩
  by_cases ht1 : t ≤ 1
  · exact hIX ⟨ht.1, ht1⟩
  · apply hball
    rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr (lt_of_not_ge ht1))]
    linarith [ht.2]

end PoincareConjecture
