import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.SeparatedTransport

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open _root_.PoincareConjecture

namespace M38Schoenflies

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

theorem terminal_surface_germ_of_collar_matching
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (H G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (i : Fin 3)
    (T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hTs : T.source ⊆ (data.actualDisk i).source)
    (hTm : T.target ⊆ (data.modelDisk i).source)
    {O : Set E2} (hO : IsOpen O) (hcO : sphere (0 : E2) 1 ⊆ O)
    (hOT : O ⊆ T.target)
    (hmatch : ∀ y ∈ O,
      G (H (data.toTerminalSaddleGeometry.flatten (g (data.actualDisk i (T.symm y))))) =
        data.toTerminalSaddleGeometry.flatten
          (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y))) :
    ∃ U : Set E3, IsOpen U ∧
      data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand ⊆ U ∧
      (G '' (H '' (data.toTerminalSaddleGeometry.flatten '' range g))) ∩ U =
        (data.toTerminalSaddleGeometry.flatten ''
          (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1)) ∩ U := by
  let s : S2 → E3 := G ∘ H ∘ data.toTerminalSaddleGeometry.flatten ∘ g
  let t : S2 → E3 := fun y => data.toTerminalSaddleGeometry.flatten
    (data.toTerminalSaddleGeometry.filledModel y)
  let m := T.toOpenPartialHomeomorph.symm.trans (data.actualDisk i)
  have hs : Topology.IsEmbedding s := G.toHomeomorph.isEmbedding.comp
    (H.toHomeomorph.isEmbedding.comp
      (data.toTerminalSaddleGeometry.flatten.toHomeomorph.isEmbedding.comp
        (M.tree.embedding_of_mem_leaves hg).isEmbedding))
  have ht : Topology.IsEmbedding t :=
    data.toTerminalSaddleGeometry.flatten.toHomeomorph.isEmbedding.comp
      (data.toTerminalSaddleGeometry.filledModel.toHomeomorph.isEmbedding.comp
        Topology.IsEmbedding.subtypeVal)
  have hOm : O ⊆ m.source := fun y hy => ⟨hOT hy, hTs (T.map_target (hOT hy))⟩
  have heq : EqOn (s ∘ m) (t ∘ data.modelDisk i) O := fun y hy => hmatch y hy
  obtain ⟨U, hU, hOU, hsurface⟩ := exists_common_surface_neighborhood_of_eqOn_charts
    hs ht m (data.modelDisk i) hO hOm (hOT.trans hTm) heq
  have hcU : data.toTerminalSaddleGeometry.modelCaps i ∩
      data.toTerminalSaddleGeometry.modelBand ⊆ U := by
    rw [data.model_boundary i]
    rintro _ ⟨y, hy, rfl⟩
    have hh := hOU (mem_image_of_mem (s ∘ m) (hcO hy))
    rw [heq (hcO hy)] at hh
    exact hh
  have hsr : range s = G '' (H '' (data.toTerminalSaddleGeometry.flatten '' range g)) := by
    simp only [s, range_comp]
  have htr : range t = data.toTerminalSaddleGeometry.flatten ''
      (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) := by
    rw [image_image]
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact mem_image_of_mem _ q.property
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  exact ⟨U, hU, hcU, by rwa [hsr, htr] at hsurface⟩

theorem exists_separated_terminal_surface_germ
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
    ∃ (S U : Set E3), IsCompact S ∧ IsOpen U ∧
      data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand ⊆ U ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ z ∉ S, G z = z) ∧ EqOn G id data.toTerminalSaddleGeometry.modelBand ∧
        (∀ j, j ≠ i → EqOn G id (H '' data.toTerminalSaddleGeometry.C j) ∧
          EqOn G id (data.toTerminalSaddleGeometry.modelCaps j)) ∧
        (G '' (H '' (data.toTerminalSaddleGeometry.flatten '' range g))) ∩ U =
          (data.toTerminalSaddleGeometry.flatten ''
            (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1)) ∩ U := by
  obtain ⟨T, O, S, _, _, hTs, hTm, hO, hcO, _, hOT, hS, _, G, hfix, hband, hother, hmap⟩ :=
    exists_separated_terminal_collar_transport data hg Φ χ H hH hχ hplanar hlabels i
  obtain ⟨U, hU, hcU, heq⟩ := terminal_surface_germ_of_collar_matching data hg H G i
    T hTs hTm hO hcO (subset_closure.trans hOT) (fun y hy => hmap y (subset_closure hy))
  exact ⟨S, U, hS, hU, hcU, G, hfix, hband, hother, heq⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
