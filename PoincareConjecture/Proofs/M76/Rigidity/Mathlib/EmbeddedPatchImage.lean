import Mathlib.Topology.OpenPartialHomeomorph.Continuity









set_option autoImplicit false

open Set

namespace Topology.IsEmbedding

variable {E X V : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace V] {S N : Set E} {f : E → X}




theorem exists_open_chart_image_eq_of_patch
    (hf : IsEmbedding (fun z : S => f z))
    (G : OpenPartialHomeomorph X V) (hNS : N ⊆ S)
    (hNG : MapsTo f N G.source)
    (z : S) (W : Set S) (hW : IsOpen W) (hzW : z ∈ W)
    (hWN : Subtype.val '' W ⊆ N) :
    ∃ O : Set V, IsOpen O ∧ G (f z) ∈ O ∧ O ⊆ G.target ∧
      (G '' (f '' S ∩ G.source)) ∩ O = ((G ∘ f) '' N) ∩ O := by
  obtain ⟨U, hU, hWU⟩ := hf.isInducing.image_eq_isOpen_inter_range hW
  let O := G '' (U ∩ G.source)
  have hO : IsOpen O := G.isOpen_image_of_subset_source
    (hU.inter G.open_source) inter_subset_right
  have hfzU : f z ∈ U := (hWU.subset ⟨z, hzW, rfl⟩).1
  have hfzG : f z ∈ G.source := hNG (hWN ⟨z, hzW, rfl⟩)
  refine ⟨O, hO, ⟨f z, ⟨hfzU, hfzG⟩, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact G.map_source hx.2
  · ext y
    constructor
    · rintro ⟨⟨x, ⟨⟨u, hu, hux⟩, hxG⟩, hxy⟩, hyO⟩
      obtain ⟨x', ⟨hx'U, hx'G⟩, hx'y⟩ := hyO
      have hx'x : x' = x := G.injOn hx'G hxG (hx'y.trans hxy.symm)
      have hxU : x ∈ U := hx'x ▸ hx'U
      have hxrange : x ∈ range (fun v : S => f v) := ⟨⟨u, hu⟩, hux⟩
      obtain ⟨w, hw, hwx⟩ := hWU.symm.subset ⟨hxU, hxrange⟩
      refine ⟨⟨w, hWN ⟨w, hw, rfl⟩, ?_⟩, ⟨x', ⟨hx'U, hx'G⟩, hx'y⟩⟩
      exact (congrArg G hwx).trans hxy
    · rintro ⟨⟨u, hu, rfl⟩, hyO⟩
      exact ⟨⟨f u, ⟨mem_image_of_mem f (hNS hu), hNG hu⟩, rfl⟩, hyO⟩

end Topology.IsEmbedding
