import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionBoundary
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapBandGluing

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_shared_edge_image_mem_interior
    (f g : SmoothFace AnnulusCoordinates)
    (C D : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b c : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hC : convexHull ℝ (range b) ⊆ C.source)
    (hD : convexHull ℝ (range c) ⊆ D.source)
    (hf : f.carrier = C '' convexHull ℝ (range b))
    (hg : g.carrier = D '' convexHull ℝ (range c))
    (hfb : ∀ k, (f.boundary k).map = C ∘
      affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)))
    (hgb : ∀ k, (g.boundary k).map = D ∘
      affineChartSegment (c (k.succAbove 0)) (c (k.succAbove 1)))
    (hfront : f.carrier ∩ g.carrier ⊆ frontier f.carrier)
    (k l : Fin 3)
    (himage : (f.boundary k).map '' Icc (0 : ℝ) 1 =
      (g.boundary l).map '' Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (f.boundary k).map t ∈ interior (f.carrier ∪ g.carrier) := by
  classical
  have hinjf := m64Intrinsic_coordinate_face_boundary_injective f C b hC hfb k
  have hinjg := m64Intrinsic_coordinate_face_boundary_injective g D c hD hgb l
  have hqedge : (f.boundary k).map t ∈ (g.boundary l).map '' Icc (0 : ℝ) 1 := by
    rw [← himage]
    exact mem_image_of_mem _ (Ioo_subset_Icc_self ht)
  obtain ⟨s, hs, hsq⟩ := hqedge
  have hends := Euler.equal_coordinate_edge_endpoints_mem C b hC k (g.boundary l) hinjg
    (by rw [← hfb]; exact himage.symm)
  have hnotvertex (v : Fin 3) : (f.boundary k).map t ≠ C (b v) := by
    intro hv
    rw [hfb] at hv
    rcases Euler.coordinate_vertex_on_edge C b hC k v (Ioo_subset_Icc_self ht) hv with h | h
    · exact ht.1.ne' h
    · exact ht.2.ne h
  have hnotends : (f.boundary k).map t ∉ ({C (b (k.succAbove 0)), C (b (k.succAbove 1))} :
      Set AnnulusCoordinates) := by
    rintro (h | h)
    · exact hnotvertex _ h
    · exact hnotvertex _ (mem_singleton_iff.mp h)
  have hsopen : s ∈ Ioo (0 : ℝ) 1 := by
    have hs0 : s ≠ 0 := by
      intro h
      subst s
      exact hnotends (hsq ▸ hends.1)
    have hs1 : s ≠ 1 := by
      intro h
      subst s
      exact hnotends (hsq ▸ hends.2)
    exact ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hs1⟩
  let otherf := ⋃ j : {j : Fin 3 // j ≠ k}, (f.boundary j).map '' Icc (0 : ℝ) 1
  let otherg := ⋃ j : {j : Fin 3 // j ≠ l}, (g.boundary j).map '' Icc (0 : ℝ) 1
  have hcompactf : IsCompact otherf := isCompact_iUnion (fun j =>
    isCompact_Icc.image_of_continuousOn (f.boundary j).smooth.continuousOn)
  have hcompactg : IsCompact otherg := isCompact_iUnion (fun j =>
    isCompact_Icc.image_of_continuousOn (g.boundary j).smooth.continuousOn)
  have hnot : (f.boundary k).map t ∉ otherf ∪ otherg := by
    rintro (hfother | hgother)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hfother
      exact coordinate_triangle_boundary_avoids_other_edges f C b hC hfb (Ne.symm j.2) ht hj
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hgother
      rw [← hsq] at hj
      exact coordinate_triangle_boundary_avoids_other_edges g D c hD hgb (Ne.symm j.2) hsopen hj
  have hfreg : closure (interior f.carrier) = f.carrier := by
    rw [hf]
    exact coordinate_triangle_closure_interior C b hC
  have hgreg : closure (interior g.carrier) = g.carrier := by
    rw [hg]
    exact coordinate_triangle_closure_interior D c hD
  apply (f.boundary k).mem_interior_union_of_local_frontiers (0 : AnnulusCoordinates)
    hinjf (by intro z _; simp) (f.interior_boundary_image k) f.isClosed_carrier g.isClosed_carrier
    hfreg hgreg (f.disjoint_interiors_of_inter_subset_frontier g hfront) ht
    (f.isClosed_carrier.frontier_subset
      (f.boundary_image_subset_frontier k (mem_image_of_mem _ (Ioo_subset_Icc_self ht))))
    (hsq ▸ g.isClosed_carrier.frontier_subset
      (g.boundary_image_subset_frontier l (mem_image_of_mem _ hs)))
    ((hcompactf.union hcompactg).isClosed.isOpen_compl.mem_nhds hnot)
  · rintro q ⟨hqN, hq⟩
    rw [f.boundary_carrier] at hq
    obtain ⟨j, hj⟩ := mem_iUnion.mp hq
    by_cases hjk : j = k
    · simpa only [hjk] using hj
    · exact False.elim (hqN (Or.inl (mem_iUnion.mpr ⟨⟨j, hjk⟩, hj⟩)))
  · rintro q ⟨hqN, hq⟩
    rw [g.boundary_carrier] at hq
    obtain ⟨j, hj⟩ := mem_iUnion.mp hq
    by_cases hjl : j = l
    · subst j
      exact himage.symm ▸ hj
    · exact False.elim (hqN (Or.inr (mem_iUnion.mpr ⟨⟨j, hjl⟩, hj⟩)))

theorem m64Intrinsic_paired_side_subset_region_interior
    {I : Type*} (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hfront : ∀ i j, i ≠ j → (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    (p q : I × Fin 3) (hpq : p ≠ q)
    (hpair : faceBoundaryIndex face p.1 p.2 = faceBoundaryIndex face q.1 q.2) :
    ((face p.1).boundary p.2).map '' Ioo (0 : ℝ) 1 ⊆
      interior (⋃ i, (face i).carrier) := by
  have hij : p.1 ≠ q.1 := by
    intro h
    apply hpq
    apply Prod.ext h
    apply Euler.coordinate_faceBoundaryIndex_injective face F b hsource hboundary q.1
    simpa only [h] using hpair
  rintro z ⟨t, ht, rfl⟩
  apply interior_mono (show (face p.1).carrier ∪ (face q.1).carrier ⊆ ⋃ i, (face i).carrier from
    union_subset (subset_iUnion (fun i => (face i).carrier) p.1)
      (subset_iUnion (fun i => (face i).carrier) q.1))
  exact m64Intrinsic_shared_edge_image_mem_interior (face p.1) (face q.1)
    (F p.1) (F q.1) (b p.1) (b q.1) (hsource p.1) (hsource q.1)
    (hcarrier p.1) (hcarrier q.1) (hboundary p.1) (hboundary q.1) (hfront _ _ hij)
    p.2 q.2 ((faceBoundaryIndex_eq_iff face _ _ _ _).mp hpair) ht

end PoincareConjecture
