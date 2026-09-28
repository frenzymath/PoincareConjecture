import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ParentBoundaryRefinement













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology
open Poincare.Topology.Plane.Meshes PoincareConjecture.Topology.Surface

namespace PoincareConjecture





theorem m64Intrinsic_preconnected_subset_segment_convex
    {A : Set AnnulusCoordinates} (hA : IsPreconnected A)
    (p q : AnnulusCoordinates) (hsub : A ⊆ segment ℝ p q) : Convex ℝ A := by
  by_cases hpq : p = q
  · subst q
    rw [segment_same] at hsub
    exact (show A.Subsingleton from fun x hx y hy =>
      (mem_singleton_iff.mp (hsub hx)).trans (mem_singleton_iff.mp (hsub hy)).symm).convex
  let param : AnnulusCoordinates → ℝ := fun x => inner ℝ (q - p) (x - p) / ‖q - p‖ ^ 2
  have hne : ‖q - p‖ ^ 2 ≠ 0 := pow_ne_zero _
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hpq)))
  have hinverse (t : ℝ) : param (AffineMap.lineMap p q t) = t := by
    dsimp only [param]
    rw [AffineMap.lineMap_apply_module]
    have hvec : (1 - t) • p + t • q - p = t • (q - p) := by module
    rw [hvec, inner_smul_right, real_inner_self_eq_norm_sq]
    exact mul_div_cancel_right₀ t hne
  have hleft (x : AnnulusCoordinates) (hx : x ∈ A) :
      AffineMap.lineMap p q (param x) = x := by
    have hxseg := hsub hx
    rw [segment_eq_image_lineMap] at hxseg
    obtain ⟨t, _, rfl⟩ := hxseg
    rw [hinverse]
  have hcontinuous : Continuous param := by
    dsimp only [param]
    fun_prop
  have heq : (AffineMap.lineMap p q) '' (param '' A) = A := by
    rw [image_image]
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      simpa only [Function.comp_apply, hleft z hz] using hz
    · intro x hx
      exact ⟨x, hx, hleft x hx⟩
  rw [← heq]
  exact (hA.image param hcontinuous.continuousOn).convex.affine_image _

private theorem parent_edge_coord_zero
    (b : AffineBasis (Fin 3) ℝ Plane) (i : Fin 3) :
    affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) ⊆ {x | b.coord i x = 0} := by
  rw [affineSegment_eq_segment, segment_eq_image_lineMap]
  rintro x ⟨t, _, rfl⟩
  rw [mem_ofPred_eq, AffineMap.apply_lineMap]
  have h0 : i ≠ i.succAbove 0 := Ne.symm (Fin.succAbove_ne i 0)
  have h1 : i ≠ i.succAbove 1 := Ne.symm (Fin.succAbove_ne i 1)
  simp only [b.coord_apply_ne h0, b.coord_apply_ne h1, AffineMap.lineMap_same_apply]







theorem m64Intrinsic_child_straight_boundary_contact
    (F G : OpenPartialHomeomorph Plane AnnulusCoordinates)
    (b c d : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source)
    (hchild : convexHull ℝ (range c) ⊆ convexHull ℝ (range b))
    (hother : convexHull ℝ (range d) ⊆ G.source)
    (i j : Fin 3) (p q u v : AnnulusCoordinates)
    (hstraight : F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) ⊆ segment ℝ p q)
    (hchord : G '' affineSegment ℝ (d (j.succAbove 0)) (d (j.succAbove 1)) = segment ℝ u v)
    (hleft : (F '' convexHull ℝ (range c)) ∩ (G '' convexHull ℝ (range d)) ⊆
      F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)))
    (hright : (F '' convexHull ℝ (range c)) ∩ (G '' convexHull ℝ (range d)) ⊆
      G '' affineSegment ℝ (d (j.succAbove 0)) (d (j.succAbove 1))) :
    CoordinateTriangleBoundaryIntersection F G c d := by
  let E := affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1))
  let A := F '' (convexHull ℝ (range c) ∩ E)
  have hE : E ⊆ convexHull ℝ (range b) := by
    dsimp only [E]
    rw [affineSegment_eq_segment]
    exact segment_subset_convexHull (mem_range_self _) (mem_range_self _)
  have hEin : E ⊆ F.source := hE.trans hsource
  have hcin : convexHull ℝ (range c) ⊆ F.source := hchild.trans hsource
  have hAconvex : Convex ℝ A := by
    apply m64Intrinsic_preconnected_subset_segment_convex ?_ p q
      ((image_mono inter_subset_right).trans hstraight)
    apply ((convex_convexHull ℝ _).inter ?_).isPreconnected.image F
      (F.continuousOn.mono (inter_subset_left.trans hcin))
    rw [affineSegment_eq_segment]
    exact convex_segment _ _
  have heq : (F '' convexHull ℝ (range c)) ∩ (G '' convexHull ℝ (range d)) =
      A ∩ segment ℝ u v := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨z, hz, hzx⟩ := hx.1
      obtain ⟨w, hw, hwx⟩ := hleft hx
      have hzw : z = w := F.injOn (hcin hz) (hEin hw) (hzx.trans hwx.symm)
      exact ⟨⟨z, ⟨hz, hzw.symm ▸ hw⟩, hzx⟩, hchord ▸ hright hx⟩
    · rintro x ⟨⟨z, hz, rfl⟩, hxchord⟩
      refine ⟨mem_image_of_mem _ hz.1, ?_⟩
      rw [← hchord] at hxchord
      apply image_mono ?_ hxchord
      rw [affineSegment_eq_segment]
      exact segment_subset_convexHull (mem_range_self _) (mem_range_self _)
  have hside : ∀ k : Fin 3, 0 ≤ b.coord i (c k) := by
    intro k
    have h := hchild (subset_convexHull ℝ _ (mem_range_self k))
    rw [b.convexHull_eq_nonneg_coord] at h
    exact h i
  obtain ⟨k, hk⟩ := triangle_inter_zero_subset_edge c (b.coord i) (b.surjective_coord i)
    (Or.inl hside)
  apply CoordinateTriangleBoundaryIntersection.of_isPreconnected_inter F G c d hcin hother
    ?_ k j ?_ hright
  · rw [heq]
    exact (hAconvex.inter (convex_segment _ _)).isPreconnected
  · intro x hx
    obtain ⟨z, hz, hzx⟩ := hx.1
    obtain ⟨w, hw, hwx⟩ := hleft hx
    have hzw : z = w := F.injOn (hcin hz) (hEin hw) (hzx.trans hwx.symm)
    exact ⟨z, hk ⟨hz, parent_edge_coord_zero b i (hzw.symm ▸ hw)⟩, hzx⟩

end PoincareConjecture
