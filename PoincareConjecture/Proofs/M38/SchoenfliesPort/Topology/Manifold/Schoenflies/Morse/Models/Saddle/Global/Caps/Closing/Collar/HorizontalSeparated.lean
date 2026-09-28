import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.HorizontalGerm
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.CoreSeparation







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

open SaddleLevel Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}




theorem exists_horizontal_terminal_separation_neighborhood
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
    (i : Fin 3) {N : Set E3} (hN : IsOpen N)
    (hcircleN : (fun y => data.toTerminalSaddleGeometry.filledModel
      (data.modelDisk i y)) '' sphere (0 : E2) 1 ⊆ N) :
    ∃ Q : Set E3, IsOpen Q ∧ Q ⊆ N ∧
      (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
        sphere (0 : E2) 1 ⊆ Q ∧
      (∀ j, j ≠ i →
        Disjoint Q (data.toTerminalSaddleGeometry.flatten.symm ''
          (H '' data.toTerminalSaddleGeometry.C j)) ∧
        Disjoint Q (data.toTerminalSaddleGeometry.flatten.symm ''
          data.toTerminalSaddleGeometry.modelCaps j)) ∧
      ∀ D ∈ data.ends.caps, Disjoint Q (g '' (D.chart '' closedBall (0 : E2) 1)) := by
  obtain ⟨V, hV, hcV, hVother⟩ := exists_terminal_rim_neighborhood_avoiding_other_caps
    data hg Φ χ H hH hχ hplanar hlabels i
  obtain ⟨a, b, ha, hb, hcores⟩ := exists_terminal_slab_avoiding_inserted_caps data hg
  let height := innerSL Real (M.v : E3)
  let Q := N ∩ (data.toTerminalSaddleGeometry.flatten ⁻¹' V) ∩ height ⁻¹' Ioo a b
  have hQ : IsOpen Q :=
    (hN.inter (hV.preimage data.toTerminalSaddleGeometry.flatten.continuous)).inter
      (isOpen_Ioo.preimage height.continuous)
  have hcQ : (fun y => data.toTerminalSaddleGeometry.filledModel
      (data.modelDisk i y)) '' sphere (0 : E2) 1 ⊆ Q := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨hcircleN (mem_image_of_mem _ hy), ?_⟩, ?_⟩
    · apply hcV
      rw [data.model_boundary i]
      exact mem_image_of_mem _ hy
    · have hcuts : data.ends.lowerCut < data.ends.upperCut := by
        rw [data.lowerCut_eq, data.upperCut_eq]
        linarith [data.eta_pos]
      rcases terminal_model_domain_boundary data i with hl | hu
      · change inner Real (M.v : E3)
          (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ∈ Ioo a b
        have heq : inner Real (M.v : E3)
          (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) =
            data.ends.lowerCut := hl.2 y hy
        rw [heq]
        exact ⟨ha, hcuts.trans hb⟩
      · change inner Real (M.v : E3)
          (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ∈ Ioo a b
        have heq : inner Real (M.v : E3)
          (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) =
            data.ends.upperCut := hu.2 y hy
        rw [heq]
        exact ⟨ha.trans hcuts, hb⟩
  refine ⟨Q, hQ, fun y hy => hy.1.1, hcQ, ?_, ?_⟩
  · intro j hji
    constructor
    · apply disjoint_left.mpr
      rintro z hz ⟨x, hx, rfl⟩
      have hzV := hz.1.2
      change data.toTerminalSaddleGeometry.flatten
        (data.toTerminalSaddleGeometry.flatten.symm x) ∈ V at hzV
      rw [Diffeomorph.apply_symm_apply] at hzV
      exact disjoint_left.mp (hVother j hji).1 hzV hx
    · apply disjoint_left.mpr
      rintro z hz ⟨x, hx, rfl⟩
      have hzV := hz.1.2
      change data.toTerminalSaddleGeometry.flatten
        (data.toTerminalSaddleGeometry.flatten.symm x) ∈ V at hzV
      rw [Diffeomorph.apply_symm_apply] at hzV
      exact disjoint_left.mp (hVother j hji).2 hzV hx
  · intro D hD
    apply disjoint_left.mpr
    rintro z hz ⟨q, hq, rfl⟩
    have hh : a < inner Real (M.v : E3) (g q) ∧ inner Real (M.v : E3) (g q) < b := hz.2
    rcases hcores D hD q hq with hl | hu <;> linarith




theorem exists_separated_horizontal_terminal_surface_germ_within
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
    (i : Fin 3) {N : Set E3} (hN : IsOpen N)
    (hcircleN : (fun y => data.toTerminalSaddleGeometry.filledModel
      (data.modelDisk i y)) '' sphere (0 : E2) 1 ⊆ N) :
    ∃ (S U : Set E3), IsCompact S ∧ S ⊆ N ∧ IsOpen U ∧ U ⊆ N ∧
      (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
        sphere (0 : E2) 1 ⊆ U ∧
      (∀ j, j ≠ i →
        Disjoint U (data.toTerminalSaddleGeometry.flatten.symm ''
          (H '' data.toTerminalSaddleGeometry.C j)) ∧
        Disjoint U (data.toTerminalSaddleGeometry.flatten.symm ''
          data.toTerminalSaddleGeometry.modelCaps j)) ∧
      (∀ D ∈ data.ends.caps, Disjoint S (g '' (D.chart '' closedBall (0 : E2) 1))) ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ z ∉ S, G z = z) ∧
        (∀ z, inner Real (M.v : E3) (G z) = inner Real (M.v : E3) z) ∧
        EqOn G id (data.toTerminalSaddleGeometry.flatten ⁻¹'
          data.toTerminalSaddleGeometry.modelBand) ∧
        (∀ D ∈ data.ends.caps, EqOn (G ∘ g) g (D.chart '' closedBall (0 : E2) 1)) ∧
        (∀ j, j ≠ i →
          EqOn G id (data.toTerminalSaddleGeometry.flatten.symm ''
            (H '' data.toTerminalSaddleGeometry.C j)) ∧
          EqOn G id (data.toTerminalSaddleGeometry.flatten.symm ''
            data.toTerminalSaddleGeometry.modelCaps j)) ∧
        (G '' (data.toTerminalSaddleGeometry.flatten.symm ''
          (H '' (data.toTerminalSaddleGeometry.flatten '' range g)))) ∩ U =
          (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U := by
  obtain ⟨Q, hQ, hQN, hcQ, hQother, hQcores⟩ :=
    exists_horizontal_terminal_separation_neighborhood data hg Φ χ H hH hχ hplanar hlabels i
      hN hcircleN
  obtain ⟨S, V, hS, hSQ, hV, hcV, G, hfix, hheight, hband, heq⟩ :=
    exists_relative_horizontal_terminal_surface_germ_within
      data hg Φ χ H hH hχ hplanar hlabels i hQ hcQ
  refine ⟨S, V ∩ Q, hS, hSQ.trans hQN, hV.inter hQ,
    inter_subset_right.trans hQN, fun z hz => ⟨hcV hz, hcQ hz⟩, ?_, ?_,
    G, hfix, hheight, hband, ?_, ?_, ?_⟩
  · intro j hji
    exact ⟨(hQother j hji).1.mono_left inter_subset_right,
      (hQother j hji).2.mono_left inter_subset_right⟩
  · intro D hD
    exact (hQcores D hD).mono_left hSQ
  · intro D hD q hq
    exact hfix (g q) (fun hs => disjoint_left.mp (hQcores D hD)
      (hSQ hs) (mem_image_of_mem g hq))
  · intro j hji
    constructor
    · intro z hz
      exact hfix z (fun hs => disjoint_left.mp (hQother j hji).1 (hSQ hs) hz)
    · intro z hz
      exact hfix z (fun hs => disjoint_left.mp (hQother j hji).2 (hSQ hs) hz)
  · rw [← inter_assoc, heq, inter_assoc]

private theorem cap_germ_of_decompositions
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




theorem exists_separated_horizontal_terminal_cap_germ_within
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
    (i : Fin 3) {N : Set E3} (hN : IsOpen N)
    (hcircleN : (fun y => data.toTerminalSaddleGeometry.filledModel
      (data.modelDisk i y)) '' sphere (0 : E2) 1 ⊆ N) :
    ∃ (S U : Set E3), IsCompact S ∧ S ⊆ N ∧ IsOpen U ∧ U ⊆ N ∧
      (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
        sphere (0 : E2) 1 ⊆ U ∧
      (∀ D ∈ data.ends.caps, Disjoint S (g '' (D.chart '' closedBall (0 : E2) 1))) ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ z ∉ S, G z = z) ∧
        (∀ z, inner Real (M.v : E3) (G z) = inner Real (M.v : E3) z) ∧
        EqOn G id (data.toTerminalSaddleGeometry.flatten ⁻¹'
          data.toTerminalSaddleGeometry.modelBand) ∧
        (∀ D ∈ data.ends.caps, EqOn (G ∘ g) g (D.chart '' closedBall (0 : E2) 1)) ∧
        (∀ j, j ≠ i →
          EqOn G id (data.toTerminalSaddleGeometry.flatten.symm ''
            (H '' data.toTerminalSaddleGeometry.C j)) ∧
          EqOn G id (data.toTerminalSaddleGeometry.flatten.symm ''
            data.toTerminalSaddleGeometry.modelCaps j)) ∧
        (G '' (data.toTerminalSaddleGeometry.flatten.symm ''
          (H '' data.toTerminalSaddleGeometry.C i))) ∩ U =
          (data.toTerminalSaddleGeometry.flatten.symm ''
            data.toTerminalSaddleGeometry.modelCaps i) ∩ U ∧
        (G '' (data.toTerminalSaddleGeometry.flatten.symm ''
          (H '' (data.toTerminalSaddleGeometry.flatten '' range g)))) ∩ U =
          (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U := by
  obtain ⟨S, U, hS, hSN, hU, hUN, hcU, hUother, hScore, G,
      hfix, hheight, hband, hcore, hother, hsurface⟩ :=
    exists_separated_horizontal_terminal_surface_germ_within
      data hg Φ χ H hH hχ hplanar hlabels i hN hcircleN
  let J := data.toTerminalSaddleGeometry.flatten.symm
  let W := J '' data.toTerminalSaddleGeometry.modelBand
  have hWpre : W = data.toTerminalSaddleGeometry.flatten ⁻¹'
      data.toTerminalSaddleGeometry.modelBand := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change data.toTerminalSaddleGeometry.flatten
        (data.toTerminalSaddleGeometry.flatten.symm y) ∈
          data.toTerminalSaddleGeometry.modelBand
      rwa [Diffeomorph.apply_symm_apply]
    · intro hx
      exact ⟨data.toTerminalSaddleGeometry.flatten x, hx,
        data.toTerminalSaddleGeometry.flatten.symm_apply_apply x⟩
  have hGW : EqOn G id W := hWpre ▸ hband
  have hGband : G '' W = W := by rw [image_congr hGW, image_id]
  have hGother (j : Fin 3) (hji : j ≠ i) :
      G '' (J '' (H '' data.toTerminalSaddleGeometry.C j)) =
        J '' (H '' data.toTerminalSaddleGeometry.C j) := by
    rw [image_congr (hother j hji).1, image_id]
  have hcancel (X : Set E3) : J '' (data.toTerminalSaddleGeometry.flatten '' X) = X := by
    rw [image_image]
    change (fun x => data.toTerminalSaddleGeometry.flatten.symm
      (data.toTerminalSaddleGeometry.flatten x)) '' X = X
    simp only [Diffeomorph.symm_apply_apply, image_id']
  refine ⟨S, U, hS, hSN, hU, hUN, hcU, hScore,
    G, hfix, hheight, hband, hcore, hother, ?_, hsurface⟩
  apply cap_germ_of_decompositions i
    (A := fun j => G '' (J '' (H '' data.toTerminalSaddleGeometry.C j)))
    (D := fun j => J '' data.toTerminalSaddleGeometry.modelCaps j) (B := W)
    (S := G '' (J '' (H '' (data.toTerminalSaddleGeometry.flatten '' range g))))
    (T := data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1)
  · rw [data.actual_decomposition, image_union, image_iUnion,
      terminal_band_image data Φ χ H hH hχ hplanar, image_union, image_iUnion,
      image_union, image_iUnion, hGband]
  · rw [← hcancel (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1),
      data.model_decomposition, image_union, image_iUnion]
  · exact hsurface
  · have hrim : (J '' (H '' data.toTerminalSaddleGeometry.C i)) ∩ W =
        (J '' data.toTerminalSaddleGeometry.modelCaps i) ∩ W := by
      change (J '' (H '' data.toTerminalSaddleGeometry.C i)) ∩
        (J '' data.toTerminalSaddleGeometry.modelBand) =
          (J '' data.toTerminalSaddleGeometry.modelCaps i) ∩
            (J '' data.toTerminalSaddleGeometry.modelBand)
      rw [← image_inter (f := (J : E3 → E3)) J.injective,
        terminal_cap_band_inter_image data Φ χ H hH hχ hplanar hlabels i,
        image_inter (f := (J : E3 → E3)) J.injective]
    calc
      (G '' (J '' (H '' data.toTerminalSaddleGeometry.C i))) ∩ W =
          G '' ((J '' (H '' data.toTerminalSaddleGeometry.C i)) ∩ W) := by
            rw [image_inter (f := (G : E3 → E3)) G.injective, hGband]
      _ = G '' ((J '' data.toTerminalSaddleGeometry.modelCaps i) ∩ W) := congrArg _ hrim
      _ = (J '' data.toTerminalSaddleGeometry.modelCaps i) ∩ W := by
        rw [image_congr (hGW.mono inter_subset_right), image_id]
  · intro j hji
    rw [hGother j hji]
    exact hUother j hji

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
