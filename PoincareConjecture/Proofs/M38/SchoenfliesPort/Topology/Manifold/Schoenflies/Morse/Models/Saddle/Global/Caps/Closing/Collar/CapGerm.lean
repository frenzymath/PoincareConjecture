import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.SurfaceGerm

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

private theorem cap_inter_eq_of_decomposition
    {X ι : Type*} {S T B U : Set X} {A D : ι → Set X} (i : ι)
    (hS : S = B ∪ ⋃ j, A j) (hT : T = B ∪ ⋃ j, D j)
    (heq : S ∩ U = T ∩ U) (hrim : A i ∩ B = D i ∩ B)
    (hother : ∀ j, j ≠ i → Disjoint U (A j) ∧ Disjoint U (D j)) :
    A i ∩ U = D i ∩ U := by
  ext x
  constructor
  · rintro ⟨hx, hxU⟩
    have hxT : x ∈ T := (heq ▸
      (show x ∈ S ∩ U from ⟨hS ▸ Or.inr (mem_iUnion.mpr ⟨i, hx⟩), hxU⟩)).1
    rcases hT ▸ hxT with hxB | hxD
    · exact ⟨(hrim ▸ (show x ∈ A i ∩ B from ⟨hx, hxB⟩)).1, hxU⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hxD
      by_cases hji : j = i
      · exact ⟨hji ▸ hj, hxU⟩
      · exact False.elim (disjoint_left.mp (hother j hji).2 hxU hj)
  · rintro ⟨hx, hxU⟩
    have hxS : x ∈ S := (heq.symm ▸
      (show x ∈ T ∩ U from ⟨hT ▸ Or.inr (mem_iUnion.mpr ⟨i, hx⟩), hxU⟩)).1
    rcases hS ▸ hxS with hxB | hxA
    · exact ⟨(hrim.symm ▸ (show x ∈ D i ∩ B from ⟨hx, hxB⟩)).1, hxU⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hxA
      by_cases hji : j = i
      · exact ⟨hji ▸ hj, hxU⟩
      · exact False.elim (disjoint_left.mp (hother j hji).1 hxU hj)

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_separated_terminal_cap_germ
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
        (G '' (H '' data.toTerminalSaddleGeometry.C i)) ∩ U =
          data.toTerminalSaddleGeometry.modelCaps i ∩ U ∧
        (G '' (H '' (data.toTerminalSaddleGeometry.flatten '' range g))) ∩ U =
          (data.toTerminalSaddleGeometry.flatten ''
            (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1)) ∩ U := by
  obtain ⟨S, V, hS, hV, hcV, G, hfix, hband, hother, heq⟩ :=
    exists_separated_terminal_surface_germ data hg Φ χ H hH hχ hplanar hlabels i
  obtain ⟨N, hN, hcN, hNother⟩ := exists_terminal_rim_neighborhood_avoiding_other_caps
    data hg Φ χ H hH hχ hplanar hlabels i
  have hGband : G '' data.toTerminalSaddleGeometry.modelBand =
      data.toTerminalSaddleGeometry.modelBand := by
    rw [image_congr hband, image_id]
  have hGother (j : Fin 3) (hji : j ≠ i) :
      G '' (H '' data.toTerminalSaddleGeometry.C j) = H '' data.toTerminalSaddleGeometry.C j := by
    rw [image_congr (hother j hji).1, image_id]
  have hsurface : (G '' (H '' (data.toTerminalSaddleGeometry.flatten '' range g))) ∩ (V ∩ N) =
      (data.toTerminalSaddleGeometry.flatten ''
        (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1)) ∩ (V ∩ N) := by
    rw [← inter_assoc, heq, inter_assoc]
  refine ⟨S, V ∩ N, hS, hV.inter hN, fun y hy => ⟨hcV hy, hcN hy⟩,
    G, hfix, hband, hother, ?_, hsurface⟩
  apply cap_inter_eq_of_decomposition i
    (A := fun j => G '' (H '' data.toTerminalSaddleGeometry.C j))
    (D := data.toTerminalSaddleGeometry.modelCaps) (B := data.toTerminalSaddleGeometry.modelBand)
    (S := G '' (H '' (data.toTerminalSaddleGeometry.flatten '' range g)))
    (T := data.toTerminalSaddleGeometry.flatten ''
      (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1))
  · rw [data.actual_decomposition, image_union, image_iUnion,
      terminal_band_image data Φ χ H hH hχ hplanar, image_union, image_iUnion, hGband]
  · exact data.model_decomposition
  · exact hsurface
  · conv_lhs => rw [← hGband, ← image_inter (f := (G : E3 → E3)) G.injective,
      terminal_cap_band_inter_image data Φ χ H hH hχ hplanar hlabels i]
    rw [image_congr (hband.mono inter_subset_right), image_id]
  · intro j hji
    rw [hGother j hji]
    exact ⟨(hNother j hji).1.mono_left inter_subset_right,
      (hNother j hji).2.mono_left inter_subset_right⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
