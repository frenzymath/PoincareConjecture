import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripCutSides

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
local notation "P2" => (ℝ × ℝ)

private theorem strip_center_mem_interior_image
    {c : P2 → P2} (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source) :
    c (1/2,0) ∈ interior (c '' source) := by
  have hstrip : IsFinitePLBallPair P2 source stripRim :=
    (isFinitePLBallPair_Icc (show (0:ℝ)<1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (-1:ℝ)<1 by norm_num))
  have hpair := hstrip.image hc hci
  rw [hpair.interior_eq_sdiff_of_finrank_eq rfl]
  refine ⟨⟨(1/2,0),by norm_num [source],rfl⟩,?_⟩
  rintro ⟨p,hp,hpeq⟩
  have hpx := hci (hstrip.1 hp) (by norm_num [source]) hpeq
  rw [hpx] at hp
  norm_num [stripRim] at hp

private theorem strip_not_contained_in_center_boundary_planar_disk
    {A Q : Set P2} (hA : IsFinitePLBallPair P2 A Q) (c : P2 → P2)
    (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcenter : c '' arm 0 ⊆ Q) : ¬c '' source ⊆ A := by
  intro hsub
  have hx := interior_mono hsub (strip_center_mem_interior_image hc hci)
  have hq := hcenter (mem_image_of_mem c (by norm_num [arm] : ((1/2,0):P2)∈arm 0))
  rw [hA.interior_eq_sdiff_of_finrank_eq rfl] at hx
  exact hx.2 hq

private theorem strip_not_contained_in_opposite_region
    {A B Q : Set P2} (hA : IsFinitePLBallPair P2 A Q) (c : P2 → P2)
    (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hinter : A ∩ B = c '' arm 0) (hcenter : c '' arm 0 ⊆ Q) :
    ¬c '' source ⊆ B := by
  intro hsub
  have hx := strip_center_mem_interior_image hc hci
  have hq := hcenter (mem_image_of_mem c (by norm_num [arm] : ((1/2,0):P2)∈arm 0))
  have hcl : c (1/2,0) ∈ closure (interior A) :=
    (hA.closure_interior_of_finrank_eq rfl).superset (hA.1 hq)
  obtain ⟨z,hzU,hzA⟩ := mem_closure_iff.mp hcl _ isOpen_interior hx
  have hzq := hcenter (hinter.subset ⟨interior_subset hzA,hsub (interior_subset hzU)⟩)
  exact (hA.interior_eq_sdiff_of_finrank_eq rfl).subset hzA |>.2 hzq

theorem strip_halves_on_opposite_disk_region_sides
    {A B QA : Set P2}
    (hA : IsFinitePLBallPair P2 A QA) (hB : IsClosed B)
    (c : P2 → P2) (hcPL : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcAB : c '' source ⊆ A ∪ B) (hinter : A ∩ B = c '' arm 0)
    (hcenterA : c '' arm 0 ⊆ QA) :
    (c '' (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 0) ⊆ A ∧
      c '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ⊆ B) ∨
    (c '' (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 0) ⊆ B ∧
      c '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ⊆ A) := by
  let L := Icc (0 : ℝ) 1 ×ˢ Ico (-1 : ℝ) 0
  let U := Icc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1
  have hLS : L ⊆ source := fun _ hx => ⟨hx.1, hx.2.1, le_trans hx.2.2.le (by norm_num)⟩
  have hUS : U ⊆ source := fun _ hx => ⟨hx.1, le_trans (by norm_num) hx.2.1.le, hx.2.2⟩
  have hcenterS : arm 0 ⊆ source := by
    rintro x ⟨hx, hx0⟩
    exact ⟨hx, by change x.2 = 0 at hx0; rw [hx0]; norm_num⟩
  have hLdisj : Disjoint (c '' L) (c '' arm 0) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hxy := hci (hcenterS hy) (hLS hx) heq
    have hx0 : x.2 = 0 := hxy ▸ hy.2
    exact (ne_of_lt hx.2.2) hx0
  have hUdisj : Disjoint (c '' U) (c '' arm 0) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hxy := hci (hcenterS hy) (hUS hx) heq
    have hx0 : x.2 = 0 := hxy ▸ hy.2
    exact (ne_of_gt hx.2.1) hx0
  have hLside := isPreconnected_subset_one_cut_piece
    (((convex_Icc (0 : ℝ) 1).prod (convex_Ico (-1 : ℝ) 0)).isPreconnected.image
      c (hcPL.continuousOn.mono hLS)) hA.isCompact.isClosed hB
      ((image_mono hLS).trans hcAB) hinter hLdisj
  have hUside := isPreconnected_subset_one_cut_piece
    (((convex_Icc (0 : ℝ) 1).prod (convex_Ioc (0 : ℝ) 1)).isPreconnected.image
      c (hcPL.continuousOn.mono hUS)) hA.isCompact.isClosed hB
      ((image_mono hUS).trans hcAB) hinter hUdisj
  have hwhole {T : Set P2} (hL : c '' L ⊆ T) (hU : c '' U ⊆ T)
      (hC : c '' arm 0 ⊆ T) : c '' source ⊆ T := by
    rintro z ⟨x, hx, rfl⟩
    rcases lt_trichotomy x.2 0 with hneg | hzero | hpos
    · exact hL ⟨x, ⟨hx.1, hx.2.1, hneg⟩, rfl⟩
    · exact hC ⟨x, ⟨hx.1, hzero⟩, rfl⟩
    · exact hU ⟨x, ⟨hx.1, hpos, hx.2.2⟩, rfl⟩
  have hLclosed {T : Set P2} (hL : c '' L ⊆ T) (hC : c '' arm 0 ⊆ T) :
      c '' (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 0) ⊆ T := by
    rintro z ⟨x, hx, rfl⟩
    rcases hx.2.2.eq_or_lt with hzero | hneg
    · exact hC ⟨x, ⟨hx.1, hzero⟩, rfl⟩
    · exact hL ⟨x, ⟨hx.1, hx.2.1, hneg⟩, rfl⟩
  have hUclosed {T : Set P2} (hU : c '' U ⊆ T) (hC : c '' arm 0 ⊆ T) :
      c '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ⊆ T := by
    rintro z ⟨x, hx, rfl⟩
    rcases hx.2.1.eq_or_lt with hzero | hpos
    · exact hC ⟨x, ⟨hx.1, hzero.symm⟩, rfl⟩
    · exact hU ⟨x, ⟨hx.1, hpos, hx.2.2⟩, rfl⟩
  have hCA := hcenterA.trans hA.1
  have hCB : c '' arm 0 ⊆ B := hinter.symm.subset.trans inter_subset_right
  rcases hLside with hLA | hLB <;> rcases hUside with hUA | hUB
  · exact False.elim (strip_not_contained_in_center_boundary_planar_disk hA c hcPL hci
      hcenterA (hwhole hLA hUA hCA))
  · exact Or.inl ⟨hLclosed hLA hCA, hUclosed hUB hCB⟩
  · exact Or.inr ⟨hLclosed hLB hCB, hUclosed hUA hCA⟩
  · exact False.elim (strip_not_contained_in_opposite_region hA c hcPL hci
      hinter hcenterA (hwhole hLB hUB hCB))

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
