import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ChildBoundaryContacts















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture

private theorem child_parent_frontier
    (F : OpenPartialHomeomorph Plane AnnulusCoordinates)
    (b c : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source)
    (hchild : convexHull ℝ (range c) ⊆ convexHull ℝ (range b)) :
    (F '' convexHull ℝ (range c)) ∩ (F '' frontier (convexHull ℝ (range b))) ⊆
      F '' frontier (convexHull ℝ (range c)) := by
  rintro x ⟨⟨z, hz, hzx⟩, ⟨w, hw, hwx⟩⟩
  have hwsource : w ∈ F.source :=
    hsource (((finite_range b).isCompact_convexHull ℝ).isClosed.frontier_subset hw)
  have hzw := F.injOn (hsource (hchild hz)) hwsource (hzx.trans hwx.symm)
  refine ⟨z, ⟨subset_closure hz, ?_⟩, hzx⟩
  intro hzi
  exact (hzw.symm ▸ hw).2 (interior_mono hchild hzi)

private theorem child_parent_edge
    (F : OpenPartialHomeomorph Plane AnnulusCoordinates)
    (b c : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source)
    (hchild : convexHull ℝ (range c) ⊆ convexHull ℝ (range b)) (i : Fin 3) :
    ∃ k : Fin 3,
      (F '' convexHull ℝ (range c)) ∩
          (F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1))) ⊆
        F '' affineSegment ℝ (c (k.succAbove 0)) (c (k.succAbove 1)) := by
  have hside : ∀ k : Fin 3, 0 ≤ b.coord i (c k) := by
    intro k
    have h := hchild (subset_convexHull ℝ _ (mem_range_self k))
    rw [b.convexHull_eq_nonneg_coord] at h
    exact h i
  have hzero : affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) ⊆
      {z | b.coord i z = 0} := by
    rw [affineSegment_eq_segment, segment_eq_image_lineMap]
    rintro z ⟨t, _, rfl⟩
    rw [mem_ofPred_eq, AffineMap.apply_lineMap]
    simp only [b.coord_apply_ne (Ne.symm (Fin.succAbove_ne i 0)),
      b.coord_apply_ne (Ne.symm (Fin.succAbove_ne i 1)), AffineMap.lineMap_same_apply]
  obtain ⟨k, hk⟩ := triangle_inter_zero_subset_edge c (b.coord i) (b.surjective_coord i)
    (Or.inl hside)
  refine ⟨k, ?_⟩
  rintro x ⟨⟨z, hz, hzx⟩, ⟨w, hw, hwx⟩⟩
  have hzw := F.injOn (hsource (hchild hz))
    (hsource (Euler.coordinate_edge_subset_hull b i hw)) (hzx.trans hwx.symm)
  exact ⟨z, hk ⟨hz, hzero (hzw.symm ▸ hw)⟩, hzx⟩

private theorem subinterval_subset_edge
    (F : OpenPartialHomeomorph Plane AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ Plane) (i : Fin 3)
    {a d : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hd : d ∈ Icc (0 : ℝ) 1) :
    (F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))) '' uIcc a d ⊆
      F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) := by
  rw [image_comp, ← Euler.affineChartSegment_image]
  apply image_mono (image_mono ?_)
  exact fun _ ht => ⟨(le_min ha.1 hd.1).trans ht.1, ht.2.trans (max_le ha.2 hd.2)⟩







theorem m64Intrinsic_canonical_contact_children
    (F G : OpenPartialHomeomorph Plane AnnulusCoordinates)
    (b c d e : AffineBasis (Fin 3) ℝ Plane)
    (hF : convexHull ℝ (range b) ⊆ F.source)
    (hG : convexHull ℝ (range c) ⊆ G.source)
    (hd : convexHull ℝ (range d) ⊆ convexHull ℝ (range b))
    (he : convexHull ℝ (range e) ⊆ convexHull ℝ (range c))
    (hparents : CoordinateTriangleBoundaryIntersection F G b c) :
    CoordinateTriangleBoundaryIntersection F G d e := by
  have hFd : F '' convexHull ℝ (range d) ⊆ F '' convexHull ℝ (range b) := image_mono hd
  have hGe : G '' convexHull ℝ (range e) ⊆ G '' convexHull ℝ (range c) := image_mono he
  have hFdcompact := ((finite_range d).isCompact_convexHull ℝ).image_of_continuousOn
    (F.continuousOn.mono (hd.trans hF))
  have hGecompact := ((finite_range e).isCompact_convexHull ℝ).image_of_continuousOn
    (G.continuousOn.mono (he.trans hG))
  cases hparents with
  | disjoint h =>
    exact CoordinateTriangleBoundaryIntersection.disjoint (h.mono hFd hGe)
  | point q hqF hqG hq =>
    by_cases hne : ((F '' convexHull ℝ (range d)) ∩ (G '' convexHull ℝ (range e))).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hxq := mem_singleton_iff.mp (hq ⟨hFd hx.1, hGe hx.2⟩)
      apply CoordinateTriangleBoundaryIntersection.point q
      · exact child_parent_frontier F b d hF hd ⟨hxq ▸ hx.1, hqF⟩
      · exact child_parent_frontier G c e hG he ⟨hxq ▸ hx.2, hqG⟩
      · exact fun z hz => hq ⟨hFd hz.1, hGe hz.2⟩
    · exact CoordinateTriangleBoundaryIntersection.disjoint
        (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hne))
  | subsegment i j a s a' s' ha hs ha' hs' hparentF hparentG =>
    let H := (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c))
    let A := (F '' convexHull ℝ (range d)) ∩ H
    let B := (G '' convexHull ℝ (range e)) ∩ H
    have hHcompact : IsCompact H :=
      (((finite_range b).isCompact_convexHull ℝ).image_of_continuousOn
        (F.continuousOn.mono hF)).inter
        (((finite_range c).isCompact_convexHull ℝ).image_of_continuousOn
          (G.continuousOn.mono hG))
    have hHedgeF : H ⊆ F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)) := by
      dsimp only [H]
      rw [hparentF]
      exact subinterval_subset_edge F b i ha hs
    have hHedgeG : H ⊆ G '' affineSegment ℝ (c (j.succAbove 0)) (c (j.succAbove 1)) := by
      dsimp only [H]
      rw [hparentG]
      exact subinterval_subset_edge G c j ha' hs'
    have hAconnected : IsPreconnected A := by
      dsimp only [A, H]
      rw [hparentF]
      exact m64Intrinsic_child_parent_subsegment_preconnected F b d hF hd i ha hs
    have hBconnected : IsPreconnected B := by
      dsimp only [B, H]
      rw [hparentG]
      exact m64Intrinsic_child_parent_subsegment_preconnected G c e hG he j ha' hs'
    have hXeq : (F '' convexHull ℝ (range d)) ∩ (G '' convexHull ℝ (range e)) = A ∩ B := by
      ext x
      constructor
      · intro hx
        have hxH : x ∈ H := ⟨hFd hx.1, hGe hx.2⟩
        exact ⟨⟨hx.1, hxH⟩, ⟨hx.2, hxH⟩⟩
      · exact fun hx => ⟨hx.1.1, hx.2.1⟩
    have hconnected : IsPreconnected ((F '' convexHull ℝ (range d)) ∩
        (G '' convexHull ℝ (range e))) := by
      rw [hXeq]
      exact m64Intrinsic_common_coordinate_edge_inter_preconnected F b hF i
        (hFdcompact.inter hHcompact) (hGecompact.inter hHcompact)
        hAconnected hBconnected (inter_subset_right.trans hHedgeF)
        (inter_subset_right.trans hHedgeF)
    obtain ⟨k, hk⟩ := child_parent_edge F b d hF hd i
    obtain ⟨l, hl⟩ := child_parent_edge G c e hG he j
    apply CoordinateTriangleBoundaryIntersection.of_isPreconnected_inter F G d e
      (hd.trans hF) (he.trans hG) hconnected k l
    · exact fun x hx => hk ⟨hx.1, hHedgeF ⟨hFd hx.1, hGe hx.2⟩⟩
    · exact fun x hx => hl ⟨hx.2, hHedgeG ⟨hFd hx.1, hGe hx.2⟩⟩

end PoincareConjecture
