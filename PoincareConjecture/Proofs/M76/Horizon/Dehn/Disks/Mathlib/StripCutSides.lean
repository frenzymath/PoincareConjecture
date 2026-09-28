import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripCenterCuts
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

private theorem nested_disk_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D R A Q : Set E} (hD : IsFinitePLBallPair P2 D R)
    (hA : IsFinitePLBallPair P2 A Q) (hDA : D ⊆ A) : D ∩ Q ⊆ R := by
  obtain ⟨_, B, _, _, _, H, hH, hHQ⟩ := hA
  obtain ⟨f, hf, hHf⟩ := hH
  have hfi : InjOn f A := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hHf ⟨x, hx⟩).trans (hxy.trans (hHf ⟨y, hy⟩).symm))))
  have himage := hD.image_of_subset hf hDA hfi
  have himageB : f '' D ⊆ B := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hHf ⟨x, hDA hx⟩]
    exact (H ⟨x, hDA hx⟩).property
  intro x hx
  by_contra hxR
  have hxnot : f x ∉ f '' R := by
    rintro ⟨y, hy, hyx⟩
    exact hxR ((hfi (hDA (hD.1 hy)) (hDA hx.1) hyx) ▸ hy)
  have hxint : f x ∈ interior B := interior_mono himageB
    ((himage.interior_eq_sdiff_of_finrank_eq rfl).superset
      ⟨mem_image_of_mem f hx.1, hxnot⟩)
  have hxfront := (hHQ ⟨x, hDA hx.1⟩).mp hx.2
  rw [hHf] at hxfront
  exact hxfront.2 hxint

private theorem strip_not_contained_in_center_boundary_disk
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A Q : Set E} (hA : IsFinitePLBallPair P2 A Q) (c : P2 → E)
    (hcPL : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcenter : c '' arm 0 ⊆ Q) : ¬ c '' source ⊆ A := by
  intro hsub
  have hstrip : IsFinitePLBallPair P2 source stripRim :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  have himage := hstrip.image hcPL hci
  have hx : ((1 / 2, 0) : P2) ∈ source := by norm_num [source]
  have hxcenter : ((1 / 2, 0) : P2) ∈ arm 0 := by norm_num [arm]
  have hxr := nested_disk_boundary himage hA hsub
    ⟨mem_image_of_mem c hx, hcenter (mem_image_of_mem c hxcenter)⟩
  obtain ⟨y, hy, heq⟩ := hxr
  have hyx := hci (hstrip.1 hy) hx heq
  rw [hyx] at hy
  norm_num [stripRim] at hy

theorem strip_halves_on_opposite_cut_sides
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B QA QB : Set E}
    (hA : IsFinitePLBallPair P2 A QA) (hB : IsFinitePLBallPair P2 B QB)
    (c : P2 → E) (hcPL : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcAB : c '' source ⊆ A ∪ B) (hinter : A ∩ B = c '' arm 0)
    (hcenterA : c '' arm 0 ⊆ QA) (hcenterB : c '' arm 0 ⊆ QB) :
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
      c (hcPL.continuousOn.mono hLS)) hA.isCompact.isClosed hB.isCompact.isClosed
      ((image_mono hLS).trans hcAB) hinter hLdisj
  have hUside := isPreconnected_subset_one_cut_piece
    (((convex_Icc (0 : ℝ) 1).prod (convex_Ioc (0 : ℝ) 1)).isPreconnected.image
      c (hcPL.continuousOn.mono hUS)) hA.isCompact.isClosed hB.isCompact.isClosed
      ((image_mono hUS).trans hcAB) hinter hUdisj
  have hwhole {T : Set E} (hL : c '' L ⊆ T) (hU : c '' U ⊆ T)
      (hC : c '' arm 0 ⊆ T) : c '' source ⊆ T := by
    rintro z ⟨x, hx, rfl⟩
    rcases lt_trichotomy x.2 0 with hneg | hzero | hpos
    · exact hL ⟨x, ⟨hx.1, hx.2.1, hneg⟩, rfl⟩
    · exact hC ⟨x, ⟨hx.1, hzero⟩, rfl⟩
    · exact hU ⟨x, ⟨hx.1, hpos, hx.2.2⟩, rfl⟩
  have hLclosed {T : Set E} (hL : c '' L ⊆ T) (hC : c '' arm 0 ⊆ T) :
      c '' (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 0) ⊆ T := by
    rintro z ⟨x, hx, rfl⟩
    rcases hx.2.2.eq_or_lt with hzero | hneg
    · exact hC ⟨x, ⟨hx.1, hzero⟩, rfl⟩
    · exact hL ⟨x, ⟨hx.1, hx.2.1, hneg⟩, rfl⟩
  have hUclosed {T : Set E} (hU : c '' U ⊆ T) (hC : c '' arm 0 ⊆ T) :
      c '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ⊆ T := by
    rintro z ⟨x, hx, rfl⟩
    rcases hx.2.1.eq_or_lt with hzero | hpos
    · exact hC ⟨x, ⟨hx.1, hzero.symm⟩, rfl⟩
    · exact hU ⟨x, ⟨hx.1, hpos, hx.2.2⟩, rfl⟩
  have hCA := hcenterA.trans hA.1
  have hCB := hcenterB.trans hB.1
  rcases hLside with hLA | hLB <;> rcases hUside with hUA | hUB
  · exact False.elim (strip_not_contained_in_center_boundary_disk hA c hcPL hci
      hcenterA (hwhole hLA hUA hCA))
  · exact Or.inl ⟨hLclosed hLA hCA, hUclosed hUB hCB⟩
  · exact Or.inr ⟨hLclosed hLB hCB, hUclosed hUA hCA⟩
  · exact False.elim (strip_not_contained_in_center_boundary_disk hB c hcPL hci
      hcenterB (hwhole hLB hUB hCB))

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
