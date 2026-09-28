import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.CommonExterior
import Mathlib.Analysis.Normed.Module.Ball.Pointwise



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)



theorem exists_smaller_enlarged_marking_in_open
    {g : E2 → E3} (hg : Continuous g) {r : Real} (hr : 1 < r)
    {U : Set E3} (hU : IsOpen U) (hgU : g '' closedBall (0 : E2) 1 ⊆ U) :
    ∃ s : Real, 1 < s ∧ s < r ∧ g '' closedBall (0 : E2) s ⊆ U := by
  have hunit : closedBall (0 : E2) 1 ⊆ g ⁻¹' U ∩ ball 0 r := by
    intro x hx
    exact ⟨hgU (mem_image_of_mem g hx), closedBall_subset_ball hr hx⟩
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall (0 : E2) 1).exists_cthickening_subset_open
    ((hU.preimage hg).inter isOpen_ball) hunit
  rw [cthickening_closedBall hδ.le (by norm_num : (0 : Real) ≤ 1)] at hsub
  let s := 1 + min δ (r - 1) / 2
  have hs : 1 < s := by dsimp [s]; linarith [lt_min hδ (sub_pos.mpr hr)]
  have hsr : s < r := by dsimp [s]; linarith [min_le_right δ (r - 1)]
  have hsδ : s ≤ δ + 1 := by dsimp [s]; linarith [min_le_left δ (r - 1)]
  exact ⟨s, hs, hsr, fun _ hy => by
    obtain ⟨x, hx, rfl⟩ := hy
    exact (hsub (closedBall_subset_closedBall hsδ hx)).1⟩

private theorem disjoint_boundary_of_nested_or_disjoint
    (B I : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hposition : I '' closedBall (0 : E3) 1 ⊆ B '' ball (0 : E3) 1 ∨
      Disjoint (I '' closedBall (0 : E3) 1) (B '' closedBall (0 : E3) 1)) :
    Disjoint (I '' closedBall (0 : E3) 1) (B '' sphere (0 : E3) 1) := by
  rcases hposition with hn | hd
  · apply disjoint_left.mpr
    intro y hy hys
    obtain ⟨x, hx, heq⟩ := hn hy
    obtain ⟨z, hz, heqz⟩ := hys
    have h := B.injective (heq.trans heqz.symm)
    subst z
    exact (mem_ball_zero_iff.mp hx).ne (mem_sphere_zero_iff_norm.mp hz)
  · exact hd.mono_right (image_mono sphere_subset_closedBall)





theorem exists_supported_moving_pair_replacement
    (B₀ B₁ L₀ L₁ F₀ F₁ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hF₀ball : F₀ '' (B₀ '' closedBall (0 : E3) 1) = L₀ '' closedBall (0 : E3) 1)
    (hF₁ball : F₁ '' (B₁ '' closedBall (0 : E3) 1) = L₁ '' closedBall (0 : E3) 1)
    (hF₀compact : ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, F₀ y = y)
    {U C : Set E3} (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    (hF₀ : EqOn F₀ id U) (hF₁ : EqOn F₁ id U)
    (hsource : B₁ '' closedBall (0 : E3) 1 ⊆ B₀ '' ball (0 : E3) 1 ∨
      Disjoint (B₁ '' closedBall (0 : E3) 1) (B₀ '' closedBall (0 : E3) 1))
    (htarget : L₁ '' closedBall (0 : E3) 1 ⊆ L₀ '' ball (0 : E3) 1 ∨
      Disjoint (L₁ '' closedBall (0 : E3) 1) (L₀ '' closedBall (0 : E3) 1))
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {r : Real} (hr : 1 < r)
    (hB : g '' closedBall (0 : E2) r ⊆ B₁ '' sphere (0 : E3) 1)
    (hL : g '' closedBall (0 : E2) r ⊆ L₁ '' sphere (0 : E3) 1)
    (hgU : g '' closedBall (0 : E2) 1 ⊆ U)
    (hBC : (B₁ '' closedBall (0 : E3) 1) ∩ C ⊆ g '' closedBall (0 : E2) 1)
    (hLC : (L₁ '' closedBall (0 : E3) 1) ∩ C ⊆ g '' closedBall (0 : E2) 1) :
    ∃ (K : Set E3) (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      IsCompact K ∧ K ⊆ (C ∪ (L₀ '' sphere (0 : E3) 1))ᶜ ∧
      (∀ y ∉ K, G y = y) ∧
      EqOn G id (C ∪ (L₀ '' sphere (0 : E3) 1) ∪ (g '' closedBall (0 : E2) 1)) ∧
      G '' (F₀ '' (B₁ '' closedBall (0 : E3) 1)) = L₁ '' closedBall (0 : E3) 1 ∧
      G '' (F₀ '' ((B₁ '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1))) =
        (L₁ '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1) ∧
      (∃ J : Set E3, IsCompact J ∧ ∀ y ∉ J, (F₀.trans G) y = y) ∧
      EqOn (F₀.trans G) id C ∧
      (F₀.trans G) '' (B₀ '' sphere (0 : E3) 1) = L₀ '' sphere (0 : E3) 1 := by
  obtain ⟨s, hs, hsr, hsU⟩ := exists_smaller_enlarged_marking_in_open hg.continuous hr hU hgU
  have hsmall : g '' closedBall (0 : E2) s ⊆ g '' closedBall (0 : E2) r :=
    image_mono (closedBall_subset_closedBall hsr.le)
  let B' := B₁.trans F₀
  let H := F₀.symm.trans F₁
  have hB'ball : B' '' closedBall (0 : E3) 1 = F₀ '' (B₁ '' closedBall (0 : E3) 1) :=
    image_comp F₀ B₁ _
  have hB'sphere : B' '' sphere (0 : E3) 1 = F₀ '' (B₁ '' sphere (0 : E3) 1) :=
    image_comp F₀ B₁ _
  have hHball : H '' (B' '' closedBall (0 : E3) 1) = L₁ '' closedBall (0 : E3) 1 := by
    rw [hB'ball]
    change (F₁ ∘ F₀.symm) '' (F₀ '' (B₁ '' closedBall (0 : E3) 1)) = _
    simpa only [image_image, Function.comp_apply, F₀.symm_apply_apply] using hF₁ball
  have hHfix : EqOn H id U := by
    intro y hy
    have hsy : F₀.symm y = y := by
      apply F₀.injective
      change F₀ (F₀.symm y) = F₀ y
      rw [F₀.apply_symm_apply, hF₀ hy, id_eq]
    change F₁ (F₀.symm y) = y
    rw [hsy, hF₁ hy, id_eq]
  have hmark : g '' closedBall (0 : E2) s ⊆ B' '' sphere (0 : E3) 1 := by
    intro y hy
    rw [hB'sphere]
    exact ⟨y, hB (hsmall hy), hF₀ (hsU hy)⟩
  have houter : F₀ '' (B₀ '' sphere (0 : E3) 1) = L₀ '' sphere (0 : E3) 1 :=
    Reverse.image_filled_sphere_of_image_filled_ball F₀ B₀ L₀ hF₀ball
  have hdsource : Disjoint (B' '' closedBall (0 : E3) 1) (L₀ '' sphere (0 : E3) 1) := by
    rw [hB'ball, ← houter]
    exact (disjoint_image_iff F₀.injective).mpr
      (disjoint_boundary_of_nested_or_disjoint B₀ B₁ hsource)
  have hdtarget := disjoint_boundary_of_nested_or_disjoint L₀ L₁ htarget
  have hB'C : (B' '' closedBall (0 : E3) 1) ∩ (C ∪ (L₀ '' sphere (0 : E3) 1)) ⊆
      g '' closedBall (0 : E2) 1 := by
    rintro y ⟨hy, hyC | hyouter⟩
    · rw [hB'ball] at hy
      obtain ⟨x, hx, heq⟩ := hy
      have hxy : x = y := F₀.injective (heq.trans (hF₀ (hCU hyC)).symm)
      exact hBC ⟨hxy ▸ hx, hyC⟩
    · exact (disjoint_left.mp hdsource hy hyouter).elim
  have hL'C : (L₁ '' closedBall (0 : E3) 1) ∩ (C ∪ (L₀ '' sphere (0 : E3) 1)) ⊆
      g '' closedBall (0 : E2) 1 := by
    rintro y ⟨hy, hyC | hyouter⟩
    · exact hLC ⟨hy, hyC⟩
    · exact (disjoint_left.mp hdtarget hy hyouter).elim
  obtain ⟨K, W, hK, hKC, _, hCW, G, hGfix, hGW, hGball, hGcap⟩ :=
    exists_supported_boundary_replacement_of_fixed_neighborhood_matching B' L₁ H hHball
      g hg hgi hgd hs hmark (hsmall.trans hL) hU hHfix hsU
      (hC.union ((isCompact_sphere (0 : E3) 1).image L₀.continuous).isClosed) hB'C hL'C
  have hGid : EqOn G id (C ∪ (L₀ '' sphere (0 : E3) 1) ∪ (g '' closedBall (0 : E2) 1)) :=
    fun _ hy => hGW _ (hCW hy)
  have hFdisk : F₀ '' (g '' ball (0 : E2) 1) = g '' ball (0 : E2) 1 := by
    rw [image_congr (hF₀.mono ((image_mono ball_subset_closedBall).trans hgU)), image_id]
  have hGcap' : G '' (F₀ '' ((B₁ '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1))) =
      (L₁ '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1) := by
    have hFi : Injective (F₀ : E3 → E3) := F₀.injective
    rw [image_sdiff hFi, hFdisk, ← hB'sphere]
    exact hGcap
  refine ⟨K, G, hK, hKC, hGfix, hGid, hB'ball ▸ hGball, hGcap', ?_, ?_, ?_⟩
  · obtain ⟨J, hJ, hFJ⟩ := hF₀compact
    refine ⟨J ∪ K, hJ.union hK, fun y hy => ?_⟩
    change G (F₀ y) = y
    rw [hFJ y (fun h => hy (Or.inl h)), hGfix y (fun h => hy (Or.inr h))]
  · intro y hy
    change G (F₀ y) = y
    rw [hF₀ (hCU hy), id_eq, hGid (Or.inl (Or.inl hy)), id_eq]
  · change (G ∘ F₀) '' (B₀ '' sphere (0 : E3) 1) = _
    rw [image_comp, houter, image_congr (hGid.mono (fun _ hy => Or.inl (Or.inr hy))), image_id]

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
