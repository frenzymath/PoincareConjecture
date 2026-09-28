import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Terminal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.CollarNeighborhood

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

open SaddleLevel

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_terminal_common_outer_collar
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    (i : Fin 3) :
    ∃ rA rM : Real, 1 < rA ∧ 1 < rM ∧
      closedBall 0 rA ⊆ (data.actualDisk i).source ∧
      closedBall 0 rM ⊆ (data.modelDisk i).source ∧
      H '' ((data.toTerminalSaddleGeometry.flatten ∘ g ∘ data.actualDisk i) ''
        (closedBall (0 : E2) rA \ ball 0 1)) ⊆ data.toTerminalSaddleGeometry.modelBand ∧
      (fun x => data.toTerminalSaddleGeometry.flatten
        (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x))) ''
          (closedBall (0 : E2) rM \ ball 0 1) ⊆ data.toTerminalSaddleGeometry.modelBand ∧
      ∃ U : Set E3, IsOpen U ∧
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand ⊆ U ∧
        data.toTerminalSaddleGeometry.modelBand ∩ U ⊆
          H '' ((data.toTerminalSaddleGeometry.flatten ∘ g ∘ data.actualDisk i) ''
            (closedBall (0 : E2) rA \ ball 0 1)) ∧
        data.toTerminalSaddleGeometry.modelBand ∩ U ⊆
          (fun x => data.toTerminalSaddleGeometry.flatten
            (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x))) ''
              (closedBall (0 : E2) rM \ ball 0 1) := by
  obtain ⟨rA, hrA, hAsource, hAband⟩ := exists_actual_terminal_outer_annulus data hg i
  obtain ⟨rM, hrM, hMsource, hMband⟩ := exists_model_terminal_outer_annulus data i
  have hband := terminal_band_image data Φ χ H hH hχ hplanar
  let sA : S2 → E3 := H ∘ data.toTerminalSaddleGeometry.flatten ∘ g
  let sM : S2 → E3 := fun q => data.toTerminalSaddleGeometry.flatten
    (data.toTerminalSaddleGeometry.filledModel q)
  have hAemb : Topology.IsEmbedding sA := H.toHomeomorph.isEmbedding.comp
    (data.toTerminalSaddleGeometry.flatten.toHomeomorph.isEmbedding.comp
      (M.tree.embedding_of_mem_leaves hg).isEmbedding)
  have hMemb : Topology.IsEmbedding sM :=
    data.toTerminalSaddleGeometry.flatten.toHomeomorph.isEmbedding.comp
      (data.toTerminalSaddleGeometry.filledModel.toHomeomorph.isEmbedding.comp
        Topology.IsEmbedding.subtypeVal)
  have hArange : range sA = H '' (data.toTerminalSaddleGeometry.flatten '' range g) := by
    simp only [sA, range_comp]
  have hMrange : range sM = data.toTerminalSaddleGeometry.flatten ''
      (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) := by
    rw [image_image]
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact mem_image_of_mem _ q.property
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  have hAwhole : data.toTerminalSaddleGeometry.modelBand ⊆ range sA := by
    rw [hArange, ← hband]
    apply image_mono
    rw [data.actual_decomposition]
    exact subset_union_left
  have hMwhole : data.toTerminalSaddleGeometry.modelBand ⊆ range sM := by
    rw [hMrange, data.model_decomposition]
    exact subset_union_left
  have hAdis : Disjoint ((sA ∘ data.actualDisk i) '' ball (0 : E2) 1)
      data.toTerminalSaddleGeometry.modelBand := by
    rw [← hband]
    simpa only [sA, image_image, comp_def] using
      disjoint_image_of_injective (f := (H : E3 → E3)) H.injective
        (actual_terminal_cap_interior_disjoint_band data hg i)
  have hMdis : Disjoint ((sM ∘ data.modelDisk i) '' ball (0 : E2) 1)
      data.toTerminalSaddleGeometry.modelBand :=
    model_terminal_cap_interior_disjoint_band data i
  obtain ⟨UA, hUA, hAcircle, hAcover⟩ := exists_band_neighborhood_in_outer_annulus
    hAemb (data.actualDisk i) hrA hAsource hAwhole hAdis
  obtain ⟨UM, hUM, hMcircle, hMcover⟩ := exists_band_neighborhood_in_outer_annulus
    hMemb (data.modelDisk i) hrM hMsource hMwhole hMdis
  have hAcircleEq : (sA ∘ data.actualDisk i) '' sphere (0 : E2) 1 =
      data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand := by
    have h := terminal_cap_band_inter_image data Φ χ H hH hχ hplanar hlabels i
    conv_lhs at h =>
      rw [← hband, ← image_inter (f := (H : E3 → E3)) H.injective, data.actual_boundary]
    simpa only [sA, image_image, comp_def] using h
  have hMcircleEq : (sM ∘ data.modelDisk i) '' sphere (0 : E2) 1 =
      data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand :=
    (data.model_boundary i).symm
  refine ⟨rA, rM, hrA, hrM, hAsource, hMsource, ?_, hMband,
    UA ∩ UM, hUA.inter hUM, ?_, ?_, ?_⟩
  · rw [← hband]
    exact image_mono hAband
  · rw [hAcircleEq] at hAcircle
    rw [hMcircleEq] at hMcircle
    exact subset_inter hAcircle hMcircle
  · intro y hy
    have h := hAcover ⟨hy.1, hy.2.1⟩
    simpa only [sA, image_image, comp_def] using h
  · exact fun y hy => hMcover ⟨hy.1, hy.2.2⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
