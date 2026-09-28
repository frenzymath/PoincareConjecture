import PoincareConjecture.Definitions.Ch11.BlowupLimits
import Mathlib.Topology.MetricSpace.Pseudo.Defs










set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture



theorem GeneralizedRicciFlowData.exists_common_box_lifetime
    (F : GeneralizedRicciFlowData.{u}) (t : ℝ)
    (K : Set (F.slice t).carrier) (hK : IsCompact K) :
    ∃ B : Finset {b : F.box_index // t ∈ (F.box b).interval},
      K ⊆ ⋃ b ∈ B, range ((F.box b.val).forward t b.property) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ F.interval, |s - t| < δ →
        ∀ b ∈ B, s ∈ (F.box b.val).interval := by
  obtain ⟨B, hB⟩ := hK.elim_finite_subcover
    (fun b : {b : F.box_index // t ∈ (F.box b).interval} =>
      range ((F.box b.val).forward t b.property))
    (fun b => ((F.box b.val).forward_openEmbedding t b.property).isOpen_range) (by
      intro x _
      obtain ⟨b, ht, y, hy⟩ := F.box_covers t x
      exact mem_iUnion.mpr ⟨⟨b, ht⟩, y, hy⟩)
  have hcommon : {s : ℝ | ∀ b ∈ B, s ∈ (F.box b.val).interval} ∈
      𝓝[F.interval] t := by
    apply (eventually_all_finset B).mpr
    intro b _
    obtain ⟨V, hV, hI⟩ := (F.box b.val).relatively_open
    have htV : t ∈ V := by
      have ht := b.property
      rw [hI] at ht
      exact ht.2
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hV.mem_nhds htV)] with s hs hsV
    rw [hI]
    exact ⟨hs, hsV⟩
  obtain ⟨δ, hδ, hlocal⟩ := Metric.mem_nhdsWithin_iff.mp hcommon
  refine ⟨B, hB, δ, hδ, fun s hs hst => hlocal ⟨?_, hs⟩⟩
  simpa only [Metric.mem_ball, Real.dist_eq] using hst

end PoincareConjecture
