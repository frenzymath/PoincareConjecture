import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripCutSides
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripHalfDiskComplement

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

private theorem planar_strip_not_in_center_boundary_disk
    {A Q : Set P2} (hA : IsFinitePLBallPair P2 A Q) (c : P2 → P2)
    (hcPL : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcenter : c '' arm 0 ⊆ Q) : ¬ c '' source ⊆ A := by
  intro hsub
  have hstrip : IsFinitePLBallPair P2 source stripRim :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  have himage := hstrip.image hcPL hci
  have hx : ((1 / 2, 0) : P2) ∈ source := by norm_num [source]
  have hxcenter : ((1 / 2, 0) : P2) ∈ arm 0 := by norm_num [arm]
  have hn : c (1 / 2, 0) ∉ c '' stripRim := by
    rintro ⟨z, hz, heq⟩
    have he := hci (hstrip.1 hz) hx heq
    rw [he] at hz
    norm_num [stripRim] at hz
  have hi : c (1 / 2, 0) ∈ interior (c '' source) := by
    rw [himage.interior_eq_sdiff_of_finrank_eq rfl]
    exact ⟨mem_image_of_mem c hx, hn⟩
  have hf : c (1 / 2, 0) ∈ frontier A := by
    rw [hA.frontier_eq_of_finrank_eq rfl]
    exact hcenter (mem_image_of_mem c hxcenter)
  exact hf.2 (interior_mono hsub hi)

theorem exists_opposite_strip_sides_of_center_trace
    {A B QA QB : Set P2}
    (hA : IsFinitePLBallPair P2 A QA) (hB : IsFinitePLBallPair P2 B QB)
    (c : P2 → P2) (hcPL : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcAB : c '' source ⊆ A ∪ B)
    (htrace : (c '' source) ∩ (A ∩ B) = c '' arm 0)
    (hcenterA : c '' arm 0 ⊆ QA) (hcenterB : c '' arm 0 ⊆ QB) :
    ∃ positive : Bool, c '' halfSource positive ⊆ A ∧
      c '' halfSource (!positive) ⊆ B := by
  let L := Icc (0 : ℝ) 1 ×ˢ Ico (-1 : ℝ) 0
  let U := Icc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1
  have hLS : L ⊆ source := fun _ hx ↦ ⟨hx.1, hx.2.1, hx.2.2.le.trans (by norm_num)⟩
  have hUS : U ⊆ source := fun _ hx ↦ ⟨hx.1, le_trans (by norm_num) hx.2.1.le, hx.2.2⟩
  have hcenterS : arm 0 ⊆ source :=
    (arm_zero_subset_halfSource false).trans (halfSource_subset_source false)
  have hLdis : Disjoint (c '' L) (A ∩ B) := by
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ hAB
    obtain ⟨y, hy, heq⟩ := htrace.subset ⟨mem_image_of_mem c (hLS hx), hAB⟩
    have hxy := hci (hcenterS hy) (hLS hx) heq
    have hx0 : x.2 = 0 := hxy ▸ hy.2
    exact (ne_of_lt hx.2.2) hx0
  have hUdis : Disjoint (c '' U) (A ∩ B) := by
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ hAB
    obtain ⟨y, hy, heq⟩ := htrace.subset ⟨mem_image_of_mem c (hUS hx), hAB⟩
    have hxy := hci (hcenterS hy) (hUS hx) heq
    have hx0 : x.2 = 0 := hxy ▸ hy.2
    exact (ne_of_gt hx.2.1) hx0
  have hLside := isPreconnected_subset_one_cut_piece
    (((convex_Icc (0 : ℝ) 1).prod (convex_Ico (-1 : ℝ) 0)).isPreconnected.image
      c (hcPL.continuousOn.mono hLS)) hA.isCompact.isClosed hB.isCompact.isClosed
      ((image_mono hLS).trans hcAB) rfl hLdis
  have hUside := isPreconnected_subset_one_cut_piece
    (((convex_Icc (0 : ℝ) 1).prod (convex_Ioc (0 : ℝ) 1)).isPreconnected.image
      c (hcPL.continuousOn.mono hUS)) hA.isCompact.isClosed hB.isCompact.isClosed
      ((image_mono hUS).trans hcAB) rfl hUdis
  have hwhole {T : Set P2} (hL : c '' L ⊆ T) (hU : c '' U ⊆ T)
      (hC : c '' arm 0 ⊆ T) : c '' source ⊆ T := by
    rintro z ⟨x, hx, rfl⟩
    rcases lt_trichotomy x.2 0 with hneg | hzero | hpos
    · exact hL ⟨x, ⟨hx.1, hx.2.1, hneg⟩, rfl⟩
    · exact hC ⟨x, ⟨hx.1, hzero⟩, rfl⟩
    · exact hU ⟨x, ⟨hx.1, hpos, hx.2.2⟩, rfl⟩
  have hLclosed {T : Set P2} (hL : c '' L ⊆ T) (hC : c '' arm 0 ⊆ T) :
      c '' halfSource false ⊆ T := by
    rintro z ⟨x, hx, rfl⟩
    rcases hx.2.2.eq_or_lt with hzero | hneg
    · exact hC ⟨x, ⟨hx.1, hzero⟩, rfl⟩
    · exact hL ⟨x, ⟨hx.1, hx.2.1, hneg⟩, rfl⟩
  have hUclosed {T : Set P2} (hU : c '' U ⊆ T) (hC : c '' arm 0 ⊆ T) :
      c '' halfSource true ⊆ T := by
    rintro z ⟨x, hx, rfl⟩
    rcases hx.2.1.eq_or_lt with hzero | hpos
    · exact hC ⟨x, ⟨hx.1, hzero.symm⟩, rfl⟩
    · exact hU ⟨x, ⟨hx.1, hpos, hx.2.2⟩, rfl⟩
  have hCA := hcenterA.trans hA.1
  have hCB := hcenterB.trans hB.1
  rcases hLside with hLA | hLB <;> rcases hUside with hUA | hUB
  · exact False.elim (planar_strip_not_in_center_boundary_disk hA c hcPL hci
      hcenterA (hwhole hLA hUA hCA))
  · exact ⟨false, hLclosed hLA hCA, hUclosed hUB hCB⟩
  · exact ⟨true, hUclosed hUA hCA, hLclosed hLB hCB⟩
  · exact False.elim (planar_strip_not_in_center_boundary_disk hB c hcPL hci
      hcenterB (hwhole hLB hUB hCB))

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
