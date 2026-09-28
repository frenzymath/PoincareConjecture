import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.MarkedEquivalence
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.SupportedEquivalence
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Range
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Side

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
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

open Reverse

theorem exists_supported_nested_boundary_replacement
    (B L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hnest : L '' closedBall (0 : E3) 1 ⊆ B '' closedBall (0 : E3) 1)
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {r : Real} (hr : 1 < r)
    (hB : g '' closedBall (0 : E2) r ⊆ B '' sphere (0 : E3) 1)
    (hL : g '' closedBall (0 : E2) r ⊆ L '' sphere (0 : E3) 1)
    {C : Set E3} (hC : IsClosed C)
    (hBC : (B '' closedBall (0 : E3) 1) ∩ C ⊆
      g '' closedBall (0 : E2) 1) :
    ∃ (K W : Set E3), IsCompact K ∧ K ⊆ Cᶜ ∧ IsOpen W ∧
      C ∪ (g '' closedBall (0 : E2) 1) ⊆ W ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, F y = y) ∧ (∀ y ∈ W, F y = y) ∧
        F '' (B '' closedBall (0 : E3) 1) = L '' closedBall (0 : E3) 1 ∧
        F '' ((B '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1)) =
          (L '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1) := by
  have hrpos : 0 < r := zero_lt_one.trans hr
  obtain ⟨p, hp, _⟩ := hB (mem_image_of_mem g (mem_closedBall_self hrpos.le))
  obtain ⟨D, hDB, hDfix⟩ := exists_ball_equivalence_fixing_common_disk
    B L g hg hgi hgd hrpos hB hL ⟨p, hp⟩
  obtain ⟨K, hK, hKC, hKdisk, F, hFfix, hFB⟩ :=
    exists_supported_nested_ball_equivalence B D (hDB ▸ hnest) g hg hgi hgd hr hB
      hDfix hC.isOpen_compl (fun y hy hyC => hy.2 (hBC ⟨hy.1, hyC⟩)) ⟨p, hp⟩
  have hFL : F '' (B '' closedBall (0 : E3) 1) = L '' closedBall (0 : E3) 1 :=
    hFB.trans hDB
  refine ⟨K, Kᶜ, hK, hKC, hK.isClosed.isOpen_compl, ?_, F, hFfix,
    (fun y hy => hFfix y hy), hFL, ?_⟩
  · rintro y (hy | hy) hyK
    · exact hKC hyK hy
    · exact disjoint_left.mp hKdisk hyK hy
  · have hFD : F '' (g '' ball (0 : E2) 1) = g '' ball (0 : E2) 1 := by
      calc
        _ = id '' (g '' ball (0 : E2) 1) := image_congr (fun y hy =>
          hFfix y (fun hyK => disjoint_left.mp hKdisk hyK
            (image_mono ball_subset_closedBall hy)))
        _ = _ := image_id _
    calc
      F '' ((B '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1)) =
          (F '' (B '' sphere (0 : E3) 1)) \ (F '' (g '' ball (0 : E2) 1)) :=
        image_sdiff F.injective _ _
      _ = (L '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1) := by
        rw [image_filled_sphere_of_image_filled_ball F B L hFL, hFD]

theorem exists_supported_boundary_replacement_of_local_inclusion
    (B L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {r : Real} (hr : 1 < r)
    (hB : g '' closedBall (0 : E2) r ⊆ B '' sphere (0 : E3) 1)
    (hL : g '' closedBall (0 : E2) r ⊆ L '' sphere (0 : E3) 1)
    {V C : Set E3} (hV : IsOpen V) (hCV : g '' closedBall (0 : E2) r ⊆ V)
    (hside : (L '' closedBall (0 : E3) 1) ∩ V ⊆ B '' closedBall (0 : E3) 1)
    (hC : IsClosed C)
    (hBC : (B '' closedBall (0 : E3) 1) ∩ C ⊆ g '' closedBall (0 : E2) 1)
    (hLC : (L '' closedBall (0 : E3) 1) ∩ C ⊆ g '' closedBall (0 : E2) 1) :
    ∃ (K W : Set E3), IsCompact K ∧ K ⊆ Cᶜ ∧ IsOpen W ∧
      C ∪ (g '' closedBall (0 : E2) 1) ⊆ W ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, G y = y) ∧ (∀ y ∈ W, G y = y) ∧
        G '' (B '' closedBall (0 : E3) 1) = L '' closedBall (0 : E3) 1 ∧
        G '' ((B '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1)) =
          (L '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1) := by
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hsmall : g '' closedBall (0 : E2) 1 ⊆ g '' closedBall (0 : E2) r :=
    image_mono (closedBall_subset_closedBall hr.le)
  obtain ⟨p, hp, _⟩ := hL (mem_image_of_mem g (mem_closedBall_self hrpos.le))
  obtain ⟨m, hmi, hml, _, hmrange⟩ :=
    exists_ambient_disk_marking_at_radius L g hg hgi hgd hrpos hL ⟨p, hp⟩
  obtain ⟨J, hJ, hJC, hJdisk, H, hHfix, hHsmall⟩ :=
    Rounding.exists_marked_ball_compression_away_disk L m hmi hml V Cᶜ hV
      hC.isOpen_compl (hmrange.symm ▸ hCV) (by
        rw [hmrange]
        exact fun y hy hyC => hy.2 (hsmall (hLC ⟨hy.1, hyC⟩)))
  have hJmark : Disjoint J (g '' closedBall (0 : E2) r) := hmrange ▸ hJdisk
  have hHmark (y : E3) (hy : y ∈ g '' closedBall (0 : E2) r) : H y = y :=
    hHfix y (fun hyJ => disjoint_left.mp hJmark hyJ hy)
  let L' := L.trans H
  have hL'ball : L' '' closedBall (0 : E3) 1 = H '' (L '' closedBall (0 : E3) 1) :=
    image_comp H L _
  have hnest : L' '' closedBall (0 : E3) 1 ⊆ B '' closedBall (0 : E3) 1 := by
    rw [hL'ball]
    exact hHsmall.trans hside
  have hL'mark : g '' closedBall (0 : E2) r ⊆ L' '' sphere (0 : E3) 1 := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hL hy
    refine ⟨x, hx, ?_⟩
    change H (L x) = y
    rw [hxy, hHmark y hy]
  obtain ⟨K, W, hK, hKC, hW, hCW, F, hFfix, hFW, hFB, _⟩ :=
    exists_supported_nested_boundary_replacement B L' hnest g hg hgi hgd hr
      hB hL'mark hC hBC
  have hHinv (y : E3) (hy : y ∉ J) : H.symm y = y := by
    apply H.injective
    change H (H.symm y) = H y
    rw [H.apply_symm_apply, hHfix y hy]
  have hWCJ : C ∪ (g '' closedBall (0 : E2) 1) ⊆ W ∩ Jᶜ := by
    intro y hy
    refine ⟨hCW hy, ?_⟩
    rcases hy with hy | hy
    · exact fun hyJ => hJC hyJ hy
    · exact fun hyJ => disjoint_left.mp hJmark hyJ (hsmall hy)
  let G := F.trans H.symm
  have hGW (y : E3) (hy : y ∈ W ∩ Jᶜ) : G y = y := by
    change H.symm (F y) = y
    rw [hFW y hy.1, hHinv y hy.2]
  have hGB : G '' (B '' closedBall (0 : E3) 1) = L '' closedBall (0 : E3) 1 := by
    change (H.symm ∘ F) '' (B '' closedBall (0 : E3) 1) = _
    rw [image_comp, hFB, hL'ball, image_image]
    simp only [H.symm_apply_apply, image_id']
  refine ⟨K ∪ J, W ∩ Jᶜ, hK.union hJ, union_subset hKC hJC,
    hW.inter hJ.isClosed.isOpen_compl, hWCJ, G, ?_, hGW, hGB, ?_⟩
  · intro y hy
    change H.symm (F y) = y
    rw [hFfix y (fun hyK => hy (Or.inl hyK)),
      hHinv y (fun hyJ => hy (Or.inr hyJ))]
  · have hGD : G '' (g '' ball (0 : E2) 1) = g '' ball (0 : E2) 1 := by
      calc
        _ = id '' (g '' ball (0 : E2) 1) := image_congr (fun y hy =>
          hGW y (hWCJ (Or.inr (image_mono ball_subset_closedBall hy))))
        _ = _ := image_id _
    calc
      G '' ((B '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1)) =
          (G '' (B '' sphere (0 : E3) 1)) \ (G '' (g '' ball (0 : E2) 1)) :=
        image_sdiff G.injective _ _
      _ = (L '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1) := by
        rw [image_filled_sphere_of_image_filled_ball G B L hGB, hGD]

theorem exists_supported_boundary_replacement_of_shared_exterior
    (B L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {r : Real} (hr : 1 < r)
    (hB : g '' closedBall (0 : E2) r ⊆ B '' sphere (0 : E3) 1)
    (hL : g '' closedBall (0 : E2) r ⊆ L '' sphere (0 : E3) 1)
    {X : Set E3} (happroach : g '' closedBall (0 : E2) r ⊆ closure X)
    (hXB : X ⊆ (B '' closedBall (0 : E3) 1)ᶜ)
    (hXL : X ⊆ (L '' closedBall (0 : E3) 1)ᶜ)
    {C : Set E3} (hC : IsClosed C)
    (hBC : (B '' closedBall (0 : E3) 1) ∩ C ⊆ g '' closedBall (0 : E2) 1)
    (hLC : (L '' closedBall (0 : E3) 1) ∩ C ⊆ g '' closedBall (0 : E2) 1) :
    ∃ (K W : Set E3), IsCompact K ∧ K ⊆ Cᶜ ∧ IsOpen W ∧
      C ∪ (g '' closedBall (0 : E2) 1) ⊆ W ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, G y = y) ∧ (∀ y ∈ W, G y = y) ∧
        G '' (B '' closedBall (0 : E3) 1) = L '' closedBall (0 : E3) 1 ∧
        G '' ((B '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1)) =
          (L '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1) := by
  obtain ⟨s, hs, hsr⟩ := exists_between hr
  have hsmall : g '' closedBall (0 : E2) s ⊆ g '' closedBall (0 : E2) r :=
    image_mono (closedBall_subset_closedBall hsr.le)
  obtain ⟨V, hV, hDV, hside⟩ := exists_local_inclusion_of_shared_exterior B L
    g hg hgi hgd (zero_lt_one.trans hr) hsr hB hL (hsmall.trans happroach) hXB hXL
  exact exists_supported_boundary_replacement_of_local_inclusion B L g hg hgi hgd hs
    (hsmall.trans hB) (hsmall.trans hL) hV hDV hside hC hBC hLC

end Poincare.Manifold.Schoenflies.Saddle.Caps

end

end M38Schoenflies
