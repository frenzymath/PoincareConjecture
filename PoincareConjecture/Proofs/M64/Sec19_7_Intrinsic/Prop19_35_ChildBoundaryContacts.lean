import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RefinedCapBandContact















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture

private theorem edge_parameter_source
    (F : OpenPartialHomeomorph Plane AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source) (i : Fin 3)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) t ∈ F.source := by
  apply hsource
  apply Euler.coordinate_edge_subset_hull b i
  rw [← Euler.affineChartSegment_image]
  exact mem_image_of_mem _ ht

private theorem edge_parameter_injOn
    (F : OpenPartialHomeomorph Plane AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source) (i : Fin 3) :
    InjOn (F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))) (Icc (0 : ℝ) 1) := by
  intro s hs t ht heq
  have h := F.injOn (edge_parameter_source F b hsource i hs)
    (edge_parameter_source F b hsource i ht) heq
  simp only [Euler.affineChartSegment_eq_lineMap] at h
  apply AffineMap.lineMap_injective ℝ (b.ind.injective.ne ?_) h
  intro hi
  have h01 : (0 : Fin 2) = 1 := Fin.succAbove_right_injective hi
  exact (by decide : (0 : Fin 2) ≠ 1) h01

private theorem edge_parameter_continuousOn
    (F : OpenPartialHomeomorph Plane AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source) (i : Fin 3) :
    ContinuousOn (F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)))
      (Icc (0 : ℝ) 1) := by
  apply F.continuousOn.comp (by unfold affineChartSegment; fun_prop)
  exact fun t ht => edge_parameter_source F b hsource i ht






theorem m64Intrinsic_common_coordinate_edge_inter_preconnected
    (F : OpenPartialHomeomorph Plane AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source) (i : Fin 3)
    {A B : Set AnnulusCoordinates} (hAcompact : IsCompact A) (hBcompact : IsCompact B)
    (hAconnected : IsPreconnected A) (hBconnected : IsPreconnected B)
    (hAedge : A ⊆ F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1)))
    (hBedge : B ⊆ F '' affineSegment ℝ (b (i.succAbove 0)) (b (i.succAbove 1))) :
    IsPreconnected (A ∩ B) := by
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · obtain ⟨a, d, ha, hd, _, hAeq⟩ :=
        exists_coordinate_edge_subinterval F b hsource i hAcompact hAconnected hA hAedge
      obtain ⟨a', d', ha', hd', _, hBeq⟩ :=
        exists_coordinate_edge_subinterval F b hsource i hBcompact hBconnected hB hBedge
      have hsub : Icc a d ⊆ Icc (0 : ℝ) 1 := fun _ ht =>
        ⟨ha.1.trans ht.1, ht.2.trans hd.2⟩
      have hsub' : Icc a' d' ⊆ Icc (0 : ℝ) 1 := fun _ ht =>
        ⟨ha'.1.trans ht.1, ht.2.trans hd'.2⟩
      rw [hAeq, hBeq, ← (edge_parameter_injOn F b hsource i).image_inter hsub hsub']
      exact ((convex_Icc a d).inter (convex_Icc a' d')).isPreconnected.image _
        ((edge_parameter_continuousOn F b hsource i).mono (inter_subset_left.trans hsub))
    · rw [not_nonempty_iff_eq_empty.mp hB, inter_empty]
      exact isPreconnected_empty
  · rw [not_nonempty_iff_eq_empty.mp hA, empty_inter]
    exact isPreconnected_empty






theorem m64Intrinsic_child_parent_subsegment_preconnected
    (F : OpenPartialHomeomorph Plane AnnulusCoordinates)
    (b c : AffineBasis (Fin 3) ℝ Plane)
    (hsource : convexHull ℝ (range b) ⊆ F.source)
    (hchild : convexHull ℝ (range c) ⊆ convexHull ℝ (range b))
    (i : Fin 3) {a d : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hd : d ∈ Icc (0 : ℝ) 1) :
    IsPreconnected ((F '' convexHull ℝ (range c)) ∩
      ((F ∘ affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1))) '' uIcc a d)) := by
  let e : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap (b (i.succAbove 0)) (b (i.succAbove 1))
  have hinterval : uIcc a d ⊆ Icc (0 : ℝ) 1 := fun _ ht =>
    ⟨(le_min ha.1 hd.1).trans ht.1, ht.2.trans (max_le ha.2 hd.2)⟩
  have he : affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) = e :=
    funext (Euler.affineChartSegment_eq_lineMap _ _)
  have hsrc : e '' uIcc a d ⊆ F.source := by
    rintro z ⟨t, ht, rfl⟩
    rw [← he]
    exact edge_parameter_source F b hsource i (hinterval ht)
  rw [he, image_comp, ← F.injOn.image_inter (hchild.trans hsource) hsrc]
  exact ((convex_convexHull ℝ _).inter ((convex_uIcc a d).affine_image e)).isPreconnected.image F
    (F.continuousOn.mono (inter_subset_left.trans (hchild.trans hsource)))

end PoincareConjecture
