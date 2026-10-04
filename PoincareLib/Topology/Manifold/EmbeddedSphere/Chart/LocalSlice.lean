import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Exact local slices for embedded immersions

The chart normal form for an immersion describes one local sheet. A topological
embedding lets us shrink the ambient neighborhood to exclude all other sheets.
This is the local geometric input to the sphere-separation repair for
Morgan--Tian Proposition 15.12 and Remark 15.13, printed p. 365.
See `proof-work/tasks/M53/derivations/01-null-homology-and-local-slices.md`.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

noncomputable section

namespace Manifold.IsImmersionAtOfComplement

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace E' N]
  {n : ℕ∞ω} {f : M → N} {x : M}

/-- In boundaryless chart models, the immersion formula also holds on the
domain chart source. This is the domain-restricted normal form used in
derivation 01 for Morgan--Tian Proposition 15.12, printed p. 365. -/
theorem writtenInCharts_source
    (h : IsImmersionAtOfComplement F 𝓘(𝕜, E) 𝓘(𝕜, E') n f x)
    {z : M} (hz : z ∈ h.domChart.source) :
    h.codChart (f z) = h.equiv (h.domChart z, 0) := by
  have ht : h.domChart z ∈ (h.domChart.extend 𝓘(𝕜, E)).target := by
    simpa [OpenPartialHomeomorph.extend_target] using h.domChart.map_source hz
  have he := h.writtenInCharts ht
  simpa [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    h.domChart.left_inv hz] using he

/-- For an embedded immersion, the entire image is a zero-complement slice
near each image point. The embedding excludes remote sheets; the extra
target restriction makes the reverse implication valid. Source: derivation
01, local step of the repair for Morgan--Tian Proposition 15.12, p. 365. -/
theorem exists_isOpen_range_iff
    (h : IsImmersionAtOfComplement F 𝓘(𝕜, E) 𝓘(𝕜, E') n f x)
    (hf : IsEmbedding f) :
    ∃ V : Set N, IsOpen V ∧ f x ∈ V ∧ V ⊆ h.codChart.source ∧
      ∀ y ∈ V, y ∈ range f ↔ (h.equiv.symm (h.codChart y)).2 = 0 := by
  obtain ⟨W, hW, hpre⟩ := hf.isInducing.isOpen_iff.mp h.domChart.open_source
  let q : N → E := fun y => (h.equiv.symm (h.codChart y)).1
  have hq : ContinuousOn q h.codChart.source :=
    (h.equiv.symm.continuous.comp_continuousOn h.codChart.continuousOn).fst
  let V := W ∩ (h.codChart.source ∩ q ⁻¹' h.domChart.target)
  have hV : IsOpen V :=
    hW.inter (hq.isOpen_inter_preimage h.codChart.open_source h.domChart.open_target)
  have hxW : f x ∈ W := by
    change x ∈ f ⁻¹' W
    rw [hpre]
    exact h.mem_domChart_source
  have hqx : q (f x) = h.domChart x := by
    dsimp [q]
    rw [h.writtenInCharts_source h.mem_domChart_source, h.equiv.symm_apply_apply]
  refine ⟨V, hV, ⟨hxW, h.mem_codChart_source, ?_⟩, fun _ hy => hy.2.1, ?_⟩
  · change q (f x) ∈ h.domChart.target
    rw [hqx]
    exact h.domChart.map_source h.mem_domChart_source
  · intro y hy
    constructor
    · rintro ⟨z, rfl⟩
      have hz : z ∈ h.domChart.source := by
        rw [← hpre]
        exact hy.1
      rw [h.writtenInCharts_source hz, h.equiv.symm_apply_apply]
    · intro hyzero
      have hyt : q y ∈ h.domChart.target := hy.2.2
      have hz : h.domChart.symm (q y) ∈ h.domChart.source :=
        h.domChart.map_target hyt
      refine ⟨h.domChart.symm (q y), ?_⟩
      apply h.codChart.injOn (h.source_subset_preimage_source hz) hy.2.1
      rw [h.writtenInCharts_source hz, h.domChart.right_inv hyt]
      have heq : (q y, (0 : F)) = h.equiv.symm (h.codChart y) := by
        apply Prod.ext
        · rfl
        · exact hyzero.symm
      rw [heq, h.equiv.apply_symm_apply]

end Manifold.IsImmersionAtOfComplement
