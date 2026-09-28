import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Terminal

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

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

theorem isCompact_actual_terminal_cap
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves) (i : Fin 3) :
    IsCompact (data.toTerminalSaddleGeometry.C i) := by
  have hd : IsCompact (data.actualDisk i '' closedBall (0 : E2) 1) :=
    (isCompact_closedBall (0 : E2) 1).image_of_continuousOn
      ((data.actualDisk i).continuousOn.mono (data.actualDisk_source i))
  rw [data.actualDisk_image] at hd
  exact hd.image ((data.toTerminalSaddleGeometry.flatten.contMDiff.continuous).comp
    (M.tree.embedding_of_mem_leaves hg).contMDiff.continuous)

theorem isCompact_model_terminal_cap
    (data : TerminalSaddleData M P p e) (i : Fin 3) :
    IsCompact (data.toTerminalSaddleGeometry.modelCaps i) := by
  have hd : IsCompact (data.modelDisk i '' closedBall (0 : E2) 1) :=
    (isCompact_closedBall (0 : E2) 1).image_of_continuousOn
      ((data.modelDisk i).continuousOn.mono (data.modelDisk_source i))
  rw [data.modelDisk_image] at hd
  exact hd.image ((data.toTerminalSaddleGeometry.flatten.contMDiff.continuous).comp
    (data.toTerminalSaddleGeometry.filledModel.contMDiff.continuous.comp continuous_subtype_val))

theorem exists_terminal_rim_neighborhood_avoiding_other_caps
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
    ∃ N : Set E3, IsOpen N ∧
      data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand ⊆ N ∧
      ∀ j, j ≠ i →
        Disjoint N (H '' data.toTerminalSaddleGeometry.C j) ∧
        Disjoint N (data.toTerminalSaddleGeometry.modelCaps j) := by
  let K : Set E3 := ⋃ j : {j : Fin 3 // j ≠ i},
    (H '' data.toTerminalSaddleGeometry.C j) ∪ data.toTerminalSaddleGeometry.modelCaps j
  have hK : IsClosed K := isClosed_iUnion_of_finite (fun j =>
    (((isCompact_actual_terminal_cap data hg j).image H.contMDiff.continuous).isClosed).union
      (isCompact_model_terminal_cap data j).isClosed)
  refine ⟨Kᶜ, hK.isOpen_compl, ?_, ?_⟩
  · intro z hz hzK
    obtain ⟨j, hj⟩ := mem_iUnion.mp hzK
    rcases hj with hj | hj
    · have hzactual : z ∈ H '' data.toTerminalSaddleGeometry.C i :=
        ((terminal_cap_band_inter_image data Φ χ H hH hχ hplanar hlabels i).symm ▸ hz).1
      exact disjoint_left.mp
        (disjoint_image_of_injective H.injective (data.actual_disjoint j.property.symm))
        hzactual hj
    · exact disjoint_left.mp (data.model_disjoint j.property.symm) hz.1 hj
  · intro j hji
    constructor
    · apply disjoint_left.mpr
      intro z hzN hzj
      exact hzN (mem_iUnion.mpr ⟨⟨j, hji⟩, Or.inl hzj⟩)
    · apply disjoint_left.mpr
      intro z hzN hzj
      exact hzN (mem_iUnion.mpr ⟨⟨j, hji⟩, Or.inr hzj⟩)

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
