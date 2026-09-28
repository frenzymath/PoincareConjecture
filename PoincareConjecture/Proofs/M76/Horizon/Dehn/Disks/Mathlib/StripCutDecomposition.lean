import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripCutSides
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripHalfDiskComplement

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

theorem exists_strip_cut_decomposition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S Q : Set E} (hS : IsFinitePLBallPair P2 S Q) (c0 c1 : P2 → E)
    (hc0PL : FinitePiecewiseAffineOn c0 source)
    (hc1PL : FinitePiecewiseAffineOn c1 source)
    (hc0i : InjOn c0 source) (hc1i : InjOn c1 source)
    (hc0S : MapsTo c0 source S) (hc1S : MapsTo c1 source S)
    (hc0Q : ∀ x ∈ source, c0 x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1)
    (hc1Q : ∀ x ∈ source, c1 x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1)
    (hdisj : Disjoint (c0 '' source) (c1 '' source)) :
    let W := c0 '' arm 0
    let Z := c1 '' arm 0
    ∃ (A M C : Set E) (s0 s1 : Bool),
      IsFinitePLBallPair P2 A ((A ∩ Q) ∪ W) ∧
      IsFinitePLBallPair P2 M (((M ∩ Q) ∪ W) ∪ Z) ∧
      IsFinitePLBallPair P2 C ((C ∩ Q) ∪ Z) ∧
      (A ∪ M) ∪ C = S ∧ A ∩ M = W ∧ M ∩ C = Z ∧ Disjoint A C ∧
      c0 '' halfSource s0 ⊆ M ∧ c0 '' halfSource (!s0) ⊆ A ∧
      c1 '' halfSource s1 ⊆ M ∧ c1 '' halfSource (!s1) ⊆ C := by
  have hcenterS : arm 0 ⊆ source :=
    (arm_zero_subset_halfSource false).trans (halfSource_subset_source false)
  have hzeroCenter : ((0, 0) : P2) ∈ arm 0 := by norm_num [arm]
  have hzeroSource := hcenterS hzeroCenter
  obtain ⟨hW, ha, hb, hab, hproperW⟩ :=
    strip_center_is_proper_arc c0 hc0PL hc0i hc0S hc0Q
  obtain ⟨hZ, hc, hd, hcd, hproperZ⟩ :=
    strip_center_is_proper_arc c1 hc1PL hc1i hc1S hc1Q
  have hcenters : Disjoint (c0 '' arm 0) (c1 '' arm 0) :=
    hdisj.mono (image_mono hcenterS) (image_mono hcenterS)
  obtain ⟨A, M, C, hA, hM, hC, hcover, hAM, hMC, hAC, hB⟩ :=
    exists_two_proper_arc_cuts_with_union hS hW hZ ha hb hc hd hab hcd
      hcenters hproperW hproperZ
  have hAB : A ∩ (M ∪ C) = c0 '' arm 0 := by
    rw [inter_union_distrib_left, hAM, hAC.inter_eq, union_empty]
  have hcover' : A ∪ (M ∪ C) = S := by rwa [← union_assoc]
  have h0cover : c0 '' source ⊆ A ∪ (M ∪ C) := by
    rw [hcover']
    exact image_subset_iff.mpr hc0S
  have h1cover : c1 '' source ⊆ A ∪ (M ∪ C) := by
    rw [hcover']
    exact image_subset_iff.mpr hc1S
  obtain h0sides := strip_halves_on_opposite_cut_sides hA hB c0 hc0PL hc0i
    h0cover hAB subset_union_right subset_union_right
  obtain ⟨s0, h0middleSide, h0outer⟩ : ∃ s0 : Bool,
      c0 '' halfSource s0 ⊆ M ∪ C ∧ c0 '' halfSource (!s0) ⊆ A := by
    rcases h0sides with ⟨hL, hU⟩ | ⟨hL, hU⟩
    · exact ⟨true, hU, hL⟩
    · exact ⟨false, hL, hU⟩
  have hstrip : IsFinitePLBallPair P2 source stripRim :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  have h1B : c1 '' source ⊆ M ∪ C := by
    have h1connected := hstrip.isConnected.isPreconnected.image c1 hc1PL.continuousOn
    rcases isPreconnected_subset_one_cut_piece h1connected hA.isCompact.isClosed
        hB.isCompact.isClosed h1cover hAB
        (hdisj.symm.mono Subset.rfl (image_mono hcenterS)) with h1A | h1B
    · have hxZ : c1 (0, 0) ∈ c1 '' arm 0 := mem_image_of_mem c1 hzeroCenter
      have hxM : c1 (0, 0) ∈ M := (hMC.symm.subset hxZ).1
      have hxW := hAM.subset ⟨h1A (mem_image_of_mem c1 hzeroSource), hxM⟩
      exact False.elim (Set.disjoint_left.mp hcenters hxW hxZ)
    · exact h1B
  obtain h1sides := strip_halves_on_opposite_cut_sides hM hC c1 hc1PL hc1i
    h1B hMC subset_union_right subset_union_right
  obtain ⟨s1, h1middle, h1outer⟩ : ∃ s1 : Bool,
      c1 '' halfSource s1 ⊆ M ∧ c1 '' halfSource (!s1) ⊆ C := by
    rcases h1sides with ⟨hL, hU⟩ | ⟨hL, hU⟩
    · exact ⟨false, hL, hU⟩
    · exact ⟨true, hU, hL⟩
  have h0middle : c0 '' halfSource s0 ⊆ M := by
    have hhalfConnected : IsPreconnected (halfSource s0) := by
      cases s0
      · exact ((convex_Icc (0 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 0)).isPreconnected
      · exact ((convex_Icc (0 : ℝ) 1).prod (convex_Icc (0 : ℝ) 1)).isPreconnected
    have hconnected := hhalfConnected.image c0
      (hc0PL.continuousOn.mono (halfSource_subset_source s0))
    rcases isPreconnected_subset_one_cut_piece hconnected hM.isCompact.isClosed
        hC.isCompact.isClosed h0middleSide hMC
        (hdisj.mono (image_mono (halfSource_subset_source s0))
          (image_mono hcenterS)) with h0M | h0C
    · exact h0M
    · have hxW := mem_image_of_mem c0 hzeroCenter
      have hxA := (hAM.symm.subset hxW).1
      have hxC := h0C (mem_image_of_mem c0 (arm_zero_subset_halfSource s0 hzeroCenter))
      exact False.elim (Set.disjoint_left.mp hAC hxA hxC)
  exact ⟨A, M, C, s0, s1, hA, hM, hC, hcover, hAM, hMC, hAC,
    h0middle, h0outer, h1middle, h1outer⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
