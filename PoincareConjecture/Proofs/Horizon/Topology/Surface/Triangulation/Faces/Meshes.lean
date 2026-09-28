


import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.Subdivision.Lines
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.BoundaryMaps
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Topology









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface


noncomputable def meshTriangleBasis (mesh : TriangleMesh) (t : mesh.Triangle) :
    AffineBasis (Fin 3) ℝ Plane :=
  affineBasisOfTriangle (mesh.position ∘ mesh.orderedVertex t)
    (mesh.orderedVertex_affineIndependent t)

theorem range_meshTriangleBasis (mesh : TriangleMesh) (t : mesh.Triangle) :
    range (meshTriangleBasis mesh t) = mesh.position '' (t.1 : Set mesh.Vertex) := by
  change range (mesh.position ∘ mesh.orderedVertex t) = _
  rw [range_comp, mesh.range_orderedVertex t]

theorem meshTriangleBasis_sources_cover (mesh : TriangleMesh) :
    (⋃ t : mesh.Triangle, convexHull ℝ (range (meshTriangleBasis mesh t))) =
      mesh.toPlaneComplex.support := by
  rw [mesh.toPlaneComplex_support]
  simp only [range_meshTriangleBasis]
  ext z
  simp only [mem_iUnion]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t.1, t.2, ht⟩
  · rintro ⟨t, ht, hz⟩
    exact ⟨⟨t, ht⟩, hz⟩

theorem meshTriangleBasis_subset_support (mesh : TriangleMesh) (t : mesh.Triangle) :
    convexHull ℝ (range (meshTriangleBasis mesh t)) ⊆ mesh.toPlaneComplex.support := by
  rw [← meshTriangleBasis_sources_cover]
  exact subset_iUnion (fun u : mesh.Triangle => convexHull ℝ (range (meshTriangleBasis mesh u))) t

private theorem mesh_oppositeEdgePoints_hull (mesh : TriangleMesh)
    (t : mesh.Triangle) (k : Fin 3) :
    convexHull ℝ (mesh.oppositeEdgePoints t k : Set Plane) =
      affineSegment ℝ (meshTriangleBasis mesh t (k.succAbove 0))
        (meshTriangleBasis mesh t (k.succAbove 1)) := by
  have hi : (Finset.univ.erase k : Finset (Fin 3)) =
      {k.succAbove 0, k.succAbove 1} := by
    fin_cases k <;> decide
  simp only [TriangleMesh.oppositeEdgePoints, hi, Finset.image_insert,
    Finset.image_singleton, Finset.coe_insert, Finset.coe_singleton, convexHull_pair,
    affineSegment_eq_segment]
  rfl



theorem meshTriangleBasis_pair_intersections (mesh : TriangleMesh)
    (s t : mesh.Triangle) (hst : s ≠ t) :
    (∃ k l : Fin 3,
      convexHull ℝ (range (meshTriangleBasis mesh s)) ∩
        convexHull ℝ (range (meshTriangleBasis mesh t)) =
        affineSegment ℝ (meshTriangleBasis mesh s (k.succAbove 0))
          (meshTriangleBasis mesh s (k.succAbove 1)) ∧
      affineSegment ℝ (meshTriangleBasis mesh s (k.succAbove 0))
          (meshTriangleBasis mesh s (k.succAbove 1)) =
        affineSegment ℝ (meshTriangleBasis mesh t (l.succAbove 0))
          (meshTriangleBasis mesh t (l.succAbove 1))) ∨
    ∃ v ∈ s.1,
      convexHull ℝ (range (meshTriangleBasis mesh s)) ∩
        convexHull ℝ (range (meshTriangleBasis mesh t)) ⊆ {mesh.position v} := by
  classical
  rw [range_meshTriangleBasis, range_meshTriangleBasis,
    mesh.triangle_inter s.1 s.2 t.1 t.2]
  have hle : (s.1 ∩ t.1).card ≤ 3 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (mesh.card_triangle s.1 s.2).le
  have hne : (s.1 ∩ t.1).card ≠ 3 := by
    intro h
    have hs : s.1 ∩ t.1 = s.1 := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by rw [mesh.card_triangle s.1 s.2, h])
    have ht : s.1 ∩ t.1 = t.1 := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_right (by rw [mesh.card_triangle t.1 t.2, h])
    exact hst (Subtype.ext (hs.symm.trans ht))
  have hcases : (s.1 ∩ t.1).card = 0 ∨ (s.1 ∩ t.1).card = 1 ∨
      (s.1 ∩ t.1).card = 2 := by omega
  rcases hcases with hc | hc | hc
  · right
    refine ⟨mesh.orderedVertex s 0, mesh.orderedVertex_mem s 0, ?_⟩
    simp [Finset.card_eq_zero.mp hc]
  · right
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
    refine ⟨v, ?_, by simp [hv]⟩
    exact (Finset.mem_inter.mp (show v ∈ s.1 ∩ t.1 by rw [hv]; simp)).1
  · left
    obtain ⟨k, hk⟩ := mesh.exists_oppositeEdgePoints_eq s Finset.inter_subset_left hc
    obtain ⟨l, hl⟩ := mesh.exists_oppositeEdgePoints_eq t Finset.inter_subset_right hc
    have hs : convexHull ℝ (mesh.position '' ((s.1 ∩ t.1 : Finset mesh.Vertex) : Set mesh.Vertex)) =
        affineSegment ℝ (meshTriangleBasis mesh s (k.succAbove 0))
          (meshTriangleBasis mesh s (k.succAbove 1)) := by
      rw [← Finset.coe_image, ← hk]
      exact mesh_oppositeEdgePoints_hull mesh s k
    have ht : convexHull ℝ (mesh.position '' ((s.1 ∩ t.1 : Finset mesh.Vertex) : Set mesh.Vertex)) =
        affineSegment ℝ (meshTriangleBasis mesh t (l.succAbove 0))
          (meshTriangleBasis mesh t (l.succAbove 1)) := by
      rw [← Finset.coe_image, ← hl]
      exact mesh_oppositeEdgePoints_hull mesh t l
    exact ⟨k, l, hs, hs.symm.trans ht⟩

private theorem mesh_segment_image (a b : Plane) :
    affineChartSegment a b '' Icc (0 : ℝ) 1 = affineSegment ℝ a b := by
  unfold affineSegment
  congr 1
  funext t
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M]



theorem exists_smoothFaces_of_triangleMesh (mesh : TriangleMesh)
    (F : OpenPartialHomeomorph Plane M)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsub : mesh.toPlaneComplex.support ⊆ F.source) (p : M)
    (hchart : F '' mesh.toPlaneComplex.support ⊆ (chartAt Plane p).source) :
    ∃ face : mesh.Triangle → SmoothFace M,
      (∀ t, (face t).map = F) ∧
      (∀ t, (face t).source = convexHull ℝ (range (meshTriangleBasis mesh t))) ∧
      (∀ t, (face t).carrier = F '' convexHull ℝ (range (meshTriangleBasis mesh t))) ∧
      (∀ t, InjOn (face t).map (face t).source) ∧
      (∀ t k, ((face t).boundary k).map = F ∘
        affineChartSegment (meshTriangleBasis mesh t (k.succAbove 0))
          (meshTriangleBasis mesh t (k.succAbove 1))) ∧
      (∀ t k, InjOn ((face t).boundary k).map (Icc (0 : ℝ) 1)) ∧
      (⋃ t, (face t).carrier) = F '' mesh.toPlaneComplex.support ∧
      (∀ s t, s ≠ t →
        (∃ k l : Fin 3,
          (face s).carrier ∩ (face t).carrier = ((face s).boundary k).map '' Icc (0 : ℝ) 1 ∧
          ((face s).boundary k).map '' Icc (0 : ℝ) 1 =
            ((face t).boundary l).map '' Icc (0 : ℝ) 1) ∨
        ∃ v : mesh.Vertex,
          (face s).carrier ∩ (face t).carrier ⊆ {F (mesh.position v)}) ∧
      (∀ s t, s ≠ t → (face s).carrier ∩ (face t).carrier ⊆ frontier (face s).carrier) := by
  have htriangle (t : mesh.Triangle) :
      convexHull ℝ (range (meshTriangleBasis mesh t)) ⊆ F.source :=
    (meshTriangleBasis_subset_support mesh t).trans hsub
  choose face hmap hsource hcarrier hinj hboundary using fun t =>
    exists_smoothFace_of_smooth_coordinates F hF hFinv (meshTriangleBasis mesh t)
      (htriangle t) p ((image_mono (meshTriangleBasis_subset_support mesh t)).trans hchart)
  have hboundaryImage (t : mesh.Triangle) (k : Fin 3) :
      ((face t).boundary k).map '' Icc (0 : ℝ) 1 =
        F '' affineSegment ℝ (meshTriangleBasis mesh t (k.succAbove 0))
          (meshTriangleBasis mesh t (k.succAbove 1)) := by
    rw [hboundary, ← mesh_segment_image, image_image]
    rfl
  have hvertexfront (t : mesh.Triangle) (j : Fin 3) :
      F (meshTriangleBasis mesh t j) ∈ frontier (face t).carrier := by
    rw [(face t).boundary_carrier]
    fin_cases j
    · refine mem_iUnion.mpr ⟨1, 0, by simp, ?_⟩
      simp [hboundary, affineChartSegment]
    · refine mem_iUnion.mpr ⟨0, 0, by simp, ?_⟩
      simp [hboundary, affineChartSegment]
    · refine mem_iUnion.mpr ⟨0, 1, by simp, ?_⟩
      simp [hboundary, affineChartSegment]
  refine ⟨face, hmap, hsource, hcarrier, hinj, hboundary, ?_, ?_, ?_, ?_⟩
  · intro t k u hu v hv huv
    let a := meshTriangleBasis mesh t (k.succAbove 0)
    let b := meshTriangleBasis mesh t (k.succAbove 1)
    have hseg (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) : affineChartSegment a b w ∈ F.source := by
      apply htriangle t
      apply segment_subset_convexHull (mem_range_self (k.succAbove 0))
        (mem_range_self (k.succAbove 1))
      rw [← affineSegment_eq_segment, ← mesh_segment_image]
      exact mem_image_of_mem _ hw
    have hab : b - a ≠ 0 := by
      intro h
      have he := (meshTriangleBasis mesh t).ind.injective (sub_eq_zero.mp h)
      have h10 : (1 : Fin 2) = 0 := Fin.succAbove_right_injective he
      norm_num at h10
    rw [hboundary t k] at huv
    have heq := F.injOn (hseg u hu) (hseg v hv) huv
    exact smul_left_injective ℝ hab (add_left_cancel heq)
  · simp only [hcarrier, ← image_iUnion, meshTriangleBasis_sources_cover]
  · intro s t hst
    rw [hcarrier, hcarrier, ← F.injOn.image_inter (htriangle s) (htriangle t)]
    rcases meshTriangleBasis_pair_intersections mesh s t hst with ⟨k, l, hk, hl⟩ | ⟨v, _, hv⟩
    · exact Or.inl ⟨k, l, by rw [hk, hboundaryImage], by rw [hboundaryImage, hboundaryImage, hl]⟩
    · right
      refine ⟨v, ?_⟩
      rintro z ⟨w, hw, rfl⟩
      rw [mem_singleton_iff.mp (hv hw)]
      exact mem_singleton _
  · intro s t hst z hz
    rw [hcarrier, hcarrier, ← F.injOn.image_inter (htriangle s) (htriangle t)] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rcases meshTriangleBasis_pair_intersections mesh s t hst with ⟨k, l, hk, _⟩ |
      ⟨v, hvs, hv⟩
    · apply (face s).boundary_image_subset_frontier k
      rw [hboundaryImage]
      exact ⟨w, hk ▸ hw, rfl⟩
    · rw [mem_singleton_iff.mp (hv hw)]
      obtain ⟨j, hj⟩ : v ∈ range (mesh.orderedVertex s) := by
        rw [mesh.range_orderedVertex]
        exact hvs
      rw [← hj]
      exact hvertexfront s j



theorem exists_normalized_smoothFaces_of_triangleMesh (mesh : TriangleMesh)
    (F : OpenPartialHomeomorph Plane M)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsub : mesh.toPlaneComplex.support ⊆ F.source) (p : M)
    (hchart : F '' mesh.toPlaneComplex.support ⊆ (chartAt Plane p).source) :
    ∃ face : mesh.Triangle → SmoothFace M,
      (∀ t, (face t).map = F) ∧
      (∀ t, (face t).source = convexHull ℝ (range (meshTriangleBasis mesh t))) ∧
      (∀ t, (face t).carrier = F '' convexHull ℝ (range (meshTriangleBasis mesh t))) ∧
      (∀ t, InjOn (face t).map (face t).source) ∧
      (∀ t k, ((face t).boundary k).map '' Icc (0 : ℝ) 1 =
        F '' affineSegment ℝ (meshTriangleBasis mesh t (k.succAbove 0))
          (meshTriangleBasis mesh t (k.succAbove 1))) ∧
      (∀ t k, InjOn ((face t).boundary k).map (Icc (0 : ℝ) 1)) ∧
      (⋃ t, (face t).carrier) = F '' mesh.toPlaneComplex.support ∧
      (∀ s t, s ≠ t →
        (∃ k l : Fin 3,
          (face s).carrier ∩ (face t).carrier = ((face s).boundary k).map '' Icc (0 : ℝ) 1 ∧
          (face s).boundary k = (face t).boundary l) ∨
        ∃ v : mesh.Vertex,
          (face s).carrier ∩ (face t).carrier ⊆ {F (mesh.position v)}) ∧
      (∀ s t, s ≠ t → (face s).carrier ∩ (face t).carrier ⊆ frontier (face s).carrier) := by
  obtain ⟨face, hmap, hsource, hcarrier, hinj, hboundary, hedgeinj, hcover, hinter, hfrontier⟩ :=
    exists_smoothFaces_of_triangleMesh mesh F hF hFinv hsub p hchart
  refine ⟨normalizeFaceBoundary face, hmap, hsource, hcarrier, hinj, ?_, ?_, hcover, ?_, hfrontier⟩
  · intro t k
    rw [normalizeFaceBoundary_boundary, faceBoundaryEdge_image, hboundary,
      ← mesh_segment_image, image_image]
    rfl
  · intro t k
    exact hedgeinj (faceBoundaryIndex face t k).out.1 (faceBoundaryIndex face t k).out.2
  · intro s t hst
    rcases hinter s t hst with ⟨k, l, hk, hl⟩ | ⟨v, hv⟩
    · left
      refine ⟨k, l, ?_, normalizeFaceBoundary_shared_edge face s t k l hl⟩
      simpa only [normalizeFaceBoundary_carrier, normalizeFaceBoundary_boundary,
        faceBoundaryEdge_image] using hk
    · exact Or.inr ⟨v, hv⟩

end PoincareConjecture.Topology.Surface
