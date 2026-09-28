import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SubdivisionFans
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ExposedEdgeVertices
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.MeshFamilySeparation
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Gluing.Subsegments














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture

section Family

variable {I : Type*}
  (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
  (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
  (S : I → Finset AnnulusCoordinates)
  (R : ∀ i, SmoothTriangleBoundarySubdivisionWithRefinement (F i) (b i) (S i))
  (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
  (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
  (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
  (hcompat : ∀ (a d : (i : I) × (R i).mesh.Triangle), a ≠ d →
    (((∃ k l : Fin 3, ((R a.1).face a.2).carrier ∩ ((R d.1).face d.2).carrier =
          (((R a.1).face a.2).boundary k).map '' Icc (0 : ℝ) 1 ∧
        (((R a.1).face a.2).boundary k).map '' Icc (0 : ℝ) 1 =
          (((R d.1).face d.2).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ v : Fin 3, ((R a.1).face a.2).carrier ∩ ((R d.1).face d.2).carrier ⊆
        {F a.1 (meshTriangleBasis (R a.1).mesh a.2 v)}) ∧
    ((R a.1).face a.2).carrier ∩ ((R d.1).face d.2).carrier ⊆
      frontier ((R a.1).face a.2).carrier))

include hsource hcompat

private theorem regional_parent_vertex_used
    (q : Euler.CoordinateVertex (fun a : (i : I) × (R i).mesh.Triangle => F a.1)
      (fun a => meshTriangleBasis (R a.1).mesh a.2)) (i : I)
    (hq : q.1 ∈ F i '' convexHull ℝ (range (b i))) :
    ∃ (t : (R i).mesh.Triangle) (v : (R i).mesh.Vertex),
      v ∈ t.1 ∧ F i ((R i).mesh.position v) = q.1 := by
  apply coordinate_mesh_family_vertex_is_used
    (fun j => (R j).mesh) F (fun a => (R a.1).face a.2)
    (fun j => by rw [(R j).support]; exact hsource j)
    (fun a => (R a.1).carrier_eq a.2) (fun a => (R a.1).boundary_map a.2)
    (fun a => (R a.1).boundary_injective a.2) (fun a d h => (hcompat a d h).1) q i
  rwa [(R i).support]






theorem m64Intrinsic_regional_parent_intersection_frontier (i j : I) (hij : i ≠ j) :
    (F i '' convexHull ℝ (range (b i))) ∩ (F j '' convexHull ℝ (range (b j))) ⊆
      frontier (F i '' convexHull ℝ (range (b i))) := by
  rintro q ⟨hqi, hqj⟩
  refine ⟨subset_closure hqi, ?_⟩
  intro hqint
  have hnot := coordinate_mesh_family_not_mem_of_interior_subfamily
    (fun k => (R k).mesh) F (fun a => (R a.1).face a.2)
    (fun k => by rw [(R k).support]; exact hsource k)
    (fun a => (R a.1).carrier_eq a.2) (fun a d h => (hcompat a d h).2)
    (fun _ : Unit => i) j (fun _ => hij.symm)
    (q := q)
  simp only [iUnion_const, (R i).support, (R j).support] at hnot
  exact hnot hqint hqj

include hF hFi

open Classical in





theorem m64Intrinsic_regional_parent_contribution
    (g : RiemannianMetric 2 AnnulusCoordinates)
    (q : Euler.CoordinateVertex (fun a : (i : I) × (R i).mesh.Triangle => F a.1)
      (fun a => meshTriangleBasis (R a.1).mesh a.2)) (i : I) :
    meshVertexAngleContribution g (F i) (R i).mesh q.1 =
      if q.1 ∈ F i '' convexHull ℝ (range (b i)) then
        if q.1 ∈ F i '' interior (convexHull ℝ (range (b i))) then 2 * Real.pi else
          if q.1 ∈ F i '' range (b i) then
            ∑ k : Fin 3, if F i (b i k) = q.1 then
              coordinateTriangleAngle g (F i) (b i) k else 0
          else Real.pi
      else 0 := by
  classical
  by_cases hq : q.1 ∈ F i '' convexHull ℝ (range (b i))
  · rw [if_pos hq]
    exact m64Intrinsic_subdivision_used_vertex_contribution g (F i) (b i) (S i) (R i)
      (hF i) (hFi i) (hsource i) (regional_parent_vertex_used F b S R hsource hcompat q i hq)
  · rw [if_neg hq]
    apply meshVertexAngleContribution_eq_zero_of_not_mem_support
    rwa [(R i).support]






theorem m64Intrinsic_regional_parent_interior_fan
    [Fintype I]
    (g : RiemannianMetric 2 AnnulusCoordinates)
    (q : Euler.CoordinateVertex (fun a : (i : I) × (R i).mesh.Triangle => F a.1)
      (fun a => meshTriangleBasis (R a.1).mesh a.2)) (i : I)
    (hq : q.1 ∈ F i '' interior (convexHull ℝ (range (b i)))) :
    coordinateVertexAngleContribution g
      (fun a : (i : I) × (R i).mesh.Triangle => F a.1)
      (fun a => meshTriangleBasis (R a.1).mesh a.2) q.1 = 2 * Real.pi := by
  classical
  have hqparent : q.1 ∈ F i '' convexHull ℝ (range (b i)) := image_mono interior_subset hq
  have hqint : q.1 ∈ interior (F i '' (R i).mesh.toPlaneComplex.support) := by
    rw [(R i).support, interior_smooth_coordinate_image _ (hsource i)]
    exact hq
  have hother (j : I) (hji : j ≠ i) :
      q.1 ∉ F j '' (R j).mesh.toPlaneComplex.support := by
    apply coordinate_mesh_family_not_mem_of_interior_subfamily (fun k => (R k).mesh) F
      (fun a => (R a.1).face a.2)
      (fun k => by rw [(R k).support]; exact hsource k)
      (fun a => (R a.1).carrier_eq a.2) (fun a d h => (hcompat a d h).2)
      (fun _ : Unit => i) j (fun _ => hji)
    simpa only [iUnion_const] using hqint
  rw [coordinateVertexAngleContribution_mesh_family]
  rw [Finset.sum_eq_single i]
  · exact m64Intrinsic_subdivision_interior_fan g (F i) (b i) (S i) (R i)
      (hF i) (hFi i) (hsource i)
      (regional_parent_vertex_used F b S R hsource hcompat q i hqparent) hq
  · intro j _ hji
    exact meshVertexAngleContribution_eq_zero_of_not_mem_support g (F j) (R j).mesh (hother j hji)
  · simp





theorem m64Intrinsic_regional_parent_open_edge_fan
    (g : RiemannianMetric 2 AnnulusCoordinates)
    (q : Euler.CoordinateVertex (fun a : (i : I) × (R i).mesh.Triangle => F a.1)
      (fun a => meshTriangleBasis (R a.1).mesh a.2)) (i : I) (k : Fin 3)
    (hq : q.1 ∈ F i '' openSegment ℝ (b i (k.succAbove 0)) (b i (k.succAbove 1))) :
    meshVertexAngleContribution g (F i) (R i).mesh q.1 = Real.pi := by
  have hqparent : q.1 ∈ F i '' convexHull ℝ (range (b i)) := by
    apply image_mono _ hq
    exact (openSegment_subset_segment ℝ _ _).trans
      (segment_subset_convexHull (mem_range_self _) (mem_range_self _))
  exact m64Intrinsic_subdivision_open_edge_fan g (F i) (b i) (S i) (R i)
    (hF i) (hFi i) (hsource i)
    (regional_parent_vertex_used F b S R hsource hcompat q i hqparent) k hq






theorem m64Intrinsic_regional_parent_pair_fan [Fintype I]
    (g : RiemannianMetric 2 AnnulusCoordinates)
    (q : Euler.CoordinateVertex (fun a : (i : I) × (R i).mesh.Triangle => F a.1)
      (fun a => meshTriangleBasis (R a.1).mesh a.2)) (i j : I) (hij : i ≠ j)
    (ki kj : Fin 3)
    (hqi : q.1 ∈ F i '' openSegment ℝ (b i (ki.succAbove 0)) (b i (ki.succAbove 1)))
    (hqj : q.1 ∈ F j '' openSegment ℝ (b j (kj.succAbove 0)) (b j (kj.succAbove 1)))
    (hqint : q.1 ∈ interior ((F i '' convexHull ℝ (range (b i))) ∪
      (F j '' convexHull ℝ (range (b j))))) :
    coordinateVertexAngleContribution g
      (fun a : (i : I) × (R i).mesh.Triangle => F a.1)
      (fun a => meshTriangleBasis (R a.1).mesh a.2) q.1 = 2 * Real.pi := by
  classical
  have hother (k : I) (hki : k ≠ i) (hkj : k ≠ j) :
      q.1 ∉ F k '' (R k).mesh.toPlaneComplex.support := by
    apply coordinate_mesh_family_not_mem_of_interior_subfamily (fun n => (R n).mesh) F
      (fun a => (R a.1).face a.2)
      (fun n => by rw [(R n).support]; exact hsource n)
      (fun a => (R a.1).carrier_eq a.2) (fun a d h => (hcompat a d h).2)
      (fun c : Bool => if c then i else j) k (by intro c; cases c <;> simp [hki, hkj])
    have hunion : (⋃ c : Bool,
        F (if c then i else j) '' (R (if c then i else j)).mesh.toPlaneComplex.support) =
        (F i '' convexHull ℝ (range (b i))) ∪ (F j '' convexHull ℝ (range (b j))) := by
      ext z
      constructor
      · rintro hz
        obtain ⟨c, hc⟩ := mem_iUnion.mp hz
        cases c
        · change z ∈ F j '' (R j).mesh.toPlaneComplex.support at hc
          rw [(R j).support] at hc
          exact Or.inr hc
        · change z ∈ F i '' (R i).mesh.toPlaneComplex.support at hc
          rw [(R i).support] at hc
          exact Or.inl hc
      · rintro (hi | hj)
        · refine mem_iUnion.mpr ⟨true, ?_⟩
          change z ∈ F i '' (R i).mesh.toPlaneComplex.support
          rwa [(R i).support]
        · refine mem_iUnion.mpr ⟨false, ?_⟩
          change z ∈ F j '' (R j).mesh.toPlaneComplex.support
          rwa [(R j).support]
    rwa [hunion]
  rw [coordinateVertexAngleContribution_mesh_family]
  have hsum : (∑ k, meshVertexAngleContribution g (F k) (R k).mesh q.1) =
      ∑ k ∈ ({i, j} : Finset I), meshVertexAngleContribution g (F k) (R k).mesh q.1 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    have hki : k ≠ i := fun h => hk (by simp [h])
    have hkj : k ≠ j := fun h => hk (by simp [h])
    exact meshVertexAngleContribution_eq_zero_of_not_mem_support g (F k) (R k).mesh
      (hother k hki hkj)
  rw [hsum]
  simp only [Finset.sum_pair hij,
    m64Intrinsic_regional_parent_open_edge_fan F b S R hF hFi hsource hcompat g q i ki hqi,
    m64Intrinsic_regional_parent_open_edge_fan F b S R hF hFi hsource hcompat g q j kj hqj]
  ring






theorem m64Intrinsic_regional_shared_subsegment_fan [Fintype I]
    (g : RiemannianMetric 2 AnnulusCoordinates)
    (q : Euler.CoordinateVertex (fun a : (i : I) × (R i).mesh.Triangle => F a.1)
      (fun a => meshTriangleBasis (R a.1).mesh a.2)) (i j : I) (hij : i ≠ j)
    (ki kj : Fin 3) {a d a' d' t s : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hd : d ∈ Icc (0 : ℝ) 1)
    (ha' : a' ∈ Icc (0 : ℝ) 1) (hd' : d' ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Ioo a d) (hs : s ∈ Ioo a' d')
    (hqi : F i (affineChartSegment (b i (ki.succAbove 0)) (b i (ki.succAbove 1)) t) = q.1)
    (hqj : F j (affineChartSegment (b j (kj.succAbove 0)) (b j (kj.succAbove 1)) s) = q.1)
    (hshared : (F i ∘ affineChartSegment (b i (ki.succAbove 0))
        (b i (ki.succAbove 1))) '' Icc a d =
      (F j ∘ affineChartSegment (b j (kj.succAbove 0))
        (b j (kj.succAbove 1))) '' Icc a' d') :
    coordinateVertexAngleContribution g
      (fun a : (i : I) × (R i).mesh.Triangle => F a.1)
      (fun a => meshTriangleBasis (R a.1).mesh a.2) q.1 = 2 * Real.pi := by
  classical
  choose face hmap hsrc hcarrier hinj hboundary using fun p : I =>
    exists_smoothFace_of_smooth_coordinates (F p) (hF p) (hFi p) (b p) (hsource p)
      (0 : AnnulusCoordinates) (by intro z _; simp)
  have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans_lt ht.1, ht.2.trans_le hd.2⟩
  have hs01 : s ∈ Ioo (0 : ℝ) 1 := ⟨ha'.1.trans_lt hs.1, hs.2.trans_le hd'.2⟩
  apply m64Intrinsic_regional_parent_pair_fan F b S R hF hFi hsource hcompat
    g q i j hij ki kj
  · refine ⟨_, ?_, hqi⟩
    simpa only [Euler.affineChartSegment_eq_lineMap] using
      lineMap_mem_openSegment ℝ (b i (ki.succAbove 0)) (b i (ki.succAbove 1)) ht01
  · refine ⟨_, ?_, hqj⟩
    simpa only [Euler.affineChartSegment_eq_lineMap] using
      lineMap_mem_openSegment ℝ (b j (kj.succAbove 0)) (b j (kj.succAbove 1)) hs01
  · have hfront : (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier := by
      rw [hcarrier, hcarrier]
      exact m64Intrinsic_regional_parent_intersection_frontier F b S R hsource hcompat i j hij
    have hint := mem_interior_union_of_coordinate_triangles_shared_subsegment
      (face i) (face j) (F i) (F j) (b i) (b j) (hsource i) (hsource j)
      (hcarrier i) (hcarrier j) (hboundary i) (hboundary j) hfront ki kj
      (m64Intrinsic_coordinate_boundary_injective face F b hsource hboundary i ki)
      (m64Intrinsic_coordinate_boundary_injective face F b hsource hboundary j kj)
      ha hd ha' hd' ht hs
      (by simpa only [hboundary, Function.comp_apply] using hqi.trans hqj.symm)
      (by simpa only [hboundary] using hshared)
    simpa only [hcarrier, hboundary, Function.comp_apply, hqi] using hint

end Family
end PoincareConjecture
