import PoincareConjecture.Proofs.M38.CapPatch









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38



theorem singletonPartialSubtype_smooth {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (e : OpenPartialHomeomorph StandardCapSpace M)
    (U : TopologicalSpace.Opens StandardCapSpace) (hU : Nonempty U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hg : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) :
    letI : Nonempty U := hU
    letI := U.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.subtypeRestr hU) (e.subtypeRestr hU).source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.subtypeRestr hU).symm (e.subtypeRestr hU).target := by
  letI : Nonempty U := hU
  letI := U.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let b := U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  constructor
  · change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e ∘ Subtype.val) _
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hf.comp (contMDiff_isOpenEmbedding
      (I := 𝓡 3) (n := ∞) U.isOpen.isOpenEmbedding_subtypeVal).contMDiffOn (fun _ hx => hx)
  · have hrange (y : M) (hy : y ∈ (e.subtypeRestr hU).target) :
        e.symm y ∈ Set.range (Subtype.val : U → StandardCapSpace) := by
      refine ⟨(e.subtypeRestr hU).symm y, ?_⟩
      exact e.subtypeRestr_symm_apply hU hy
    have hs := (contMDiffOn_isOpenEmbedding_symm (I := 𝓡 3) (n := ∞)
      U.isOpen.isOpenEmbedding_subtypeVal).comp
        (hg.mono (e.subtypeRestr_target_subset hU)) hrange
    apply hs.congr
    intro y hy
    apply Subtype.ext
    exact (e.subtypeRestr_symm_apply hU hy).trans
      (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
        (f := (Subtype.val : U → StandardCapSpace))
        (h := U.isOpen.isOpenEmbedding_subtypeVal) (hrange y hy)).symm

namespace EventCapCoordinates

variable {F : SurgeryFlowData.{u}} {T : ℝ} {hT : T ∈ F.surgery_times}
  [Nonempty (F.slice T).carrier] {i : Fin (F.event T hT).cap_count}
  (P : EventCapCoordinates F T hT i)



theorem attachmentChart_symm_apply {y : eventDiscardedOpen F T hT}
    (hy : y ∈ P.attachmentChart.target) :
    (P.attachmentChart.symm y).val = capAttachVector (P.collarInverse y.val) := by
  change ((P.annularChart.subtypeRestr capDoubleBall_nonempty).symm y.val).val = _
  simp only [attachmentChart, OpenPartialHomeomorph.symm_target,
    OpenPartialHomeomorph.subtypeRestr_source, OpenPartialHomeomorph.symm_source,
    Set.mem_preimage] at hy
  exact P.annularChart.subtypeRestr_symm_apply capDoubleBall_nonempty hy



theorem attachmentChart_smooth :
    letI : Nonempty capDoubleBall := capDoubleBall_nonempty
    letI := capDoubleBall.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ P.attachmentChart P.attachmentChart.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ P.attachmentChart.symm P.attachmentChart.target := by
  letI : Nonempty capDoubleBall := capDoubleBall_nonempty
  letI := capDoubleBall.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  constructor
  · have hdom : Set.MapsTo (Subtype.val : capDoubleBall → StandardCapSpace)
        P.attachmentChart.source P.annularChart.source := by
      intro x hx
      rw [P.attachmentChart_source] at hx
      exact ⟨hx, by simpa only [capDoubleBall, TopologicalSpace.Opens.mem_mk,
        Metric.mem_ball, dist_zero_right] using x.property⟩
    have hs := P.annular_map_smooth.comp
      (contMDiff_isOpenEmbedding (I := 𝓡 3) (n := ∞)
        capDoubleBall.isOpen.isOpenEmbedding_subtypeVal).contMDiffOn hdom
    have hcoe : ContMDiffOn (𝓡 3) (𝓡 3) ∞
        (Subtype.val ∘ P.attachmentChart) P.attachmentChart.source :=
      hs.congr (fun x hx => P.attachmentChart_apply
        (by rwa [P.attachmentChart_source] at hx))
    intro x hx
    exact (ContMDiffWithinAt.subtypeVal_comp_iff
      (eventDiscardedOpen F T hT) P.attachmentChart P.attachmentChart.source x).mp (hcoe x hx)
  · have hdom : Set.MapsTo
        (Subtype.val : eventDiscardedOpen F T hT → (F.slice (F.event T hT).tMinus).carrier)
        P.attachmentChart.target P.annularChart.target := by
      intro y hy
      rwa [P.attachmentChart_target] at hy
    have hs := P.annular_inverse_smooth.comp contMDiff_subtype_val.contMDiffOn hdom
    have hrange (y : eventDiscardedOpen F T hT) (hy : y ∈ P.attachmentChart.target) :
        capAttachVector (P.collarInverse y.val) ∈
          Set.range (Subtype.val : capDoubleBall → StandardCapSpace) :=
      ⟨P.attachmentChart.symm y, P.attachmentChart_symm_apply hy⟩
    have hcomp := (contMDiffOn_isOpenEmbedding_symm (I := 𝓡 3) (n := ∞)
      capDoubleBall.isOpen.isOpenEmbedding_subtypeVal).comp hs hrange
    apply hcomp.congr
    intro y hy
    apply Subtype.ext
    exact (P.attachmentChart_symm_apply hy).trans
      (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
        (f := (Subtype.val : capDoubleBall → StandardCapSpace))
        (h := capDoubleBall.isOpen.isOpenEmbedding_subtypeVal) (hrange y hy)).symm

end EventCapCoordinates

end PoincareConjecture.M38
