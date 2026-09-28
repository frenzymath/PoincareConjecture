import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapCoreMatching












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes

namespace PoincareConjecture

private theorem region_segment_image (p q : AnnulusCoordinates) :
    affineChartSegment p q '' Icc (0 : ℝ) 1 = affineSegment ℝ p q := by
  unfold affineSegment
  congr 1
  funext t
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

private theorem region_vertex_frontier (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates) :
    range b ⊆ frontier (convexHull ℝ (range b)) := by
  rintro z ⟨i, rfl⟩
  rw [frontier_convexHull_affineBasis_fin3_segments]
  have hedge (k : Fin 3) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)) t ∈
        ⋃ j : Fin 3, affineSegment ℝ (b (j.succAbove 0)) (b (j.succAbove 1)) := by
    apply mem_iUnion.mpr
    refine ⟨k, ?_⟩
    rw [← region_segment_image]
    exact mem_image_of_mem _ ht
  fin_cases i
  · simpa [affineChartSegment] using hedge 1 0 (by simp)
  · simpa [affineChartSegment] using hedge 0 0 (by simp)
  · simpa [affineChartSegment] using hedge 0 1 (by simp)

private theorem region_subdivision_intersections
    {F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates}
    {b : AffineBasis (Fin 3) ℝ AnnulusCoordinates} {S : Finset AnnulusCoordinates}
    (R : SmoothTriangleBoundarySubdivision F b S) (t u : R.mesh.Triangle) (htu : t ≠ u) :
    (∃ k l : Fin 3, (R.face t).carrier ∩ (R.face u).carrier =
        ((R.face t).boundary k).map '' Icc (0 : ℝ) 1 ∧
      ((R.face t).boundary k).map '' Icc (0 : ℝ) 1 =
        ((R.face u).boundary l).map '' Icc (0 : ℝ) 1) ∨
    ∃ v : Fin 3, (R.face t).carrier ∩ (R.face u).carrier ⊆
      {F (meshTriangleBasis R.mesh t v)} := by
  have hedge (s : R.mesh.Triangle) (k : Fin 3) :
      ((R.face s).boundary k).map '' Icc (0 : ℝ) 1 =
        F '' affineSegment ℝ (meshTriangleBasis R.mesh s (k.succAbove 0))
          (meshTriangleBasis R.mesh s (k.succAbove 1)) := by
    rw [R.boundary_map, image_comp, region_segment_image]
  rw [R.carrier_eq, R.carrier_eq, ← F.injOn.image_inter (R.source_subset t) (R.source_subset u)]
  rcases meshTriangleBasis_pair_intersections R.mesh t u htu with ⟨k, l, hk, hl⟩ | ⟨v, hvt, hv⟩
  · exact Or.inl ⟨k, l, by rw [hk, hedge], by rw [hedge, hedge, hl]⟩
  · obtain ⟨j, hj⟩ : v ∈ range (R.mesh.orderedVertex t) := by
      rw [R.mesh.range_orderedVertex]
      exact hvt
    refine Or.inr ⟨j, ?_⟩
    rintro q ⟨z, hz, rfl⟩
    rw [mem_singleton_iff.mp (hv hz), ← hj]
    exact mem_singleton _







theorem m64Intrinsic_exists_compatible_region_refinement
    {I : Type*} [Finite I]
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hparents : ∀ i j, i ≠ j → CoordinateTriangleBoundaryIntersection (F i) (F j) (b i) (b j)) :
    ∃ (S : I → Finset AnnulusCoordinates)
      (R : ∀ i, SmoothTriangleBoundarySubdivisionWithRefinement (F i) (b i) (S i)),
      (∀ (a d : (i : I) × (R i).mesh.Triangle), a ≠ d →
        (((∃ k l : Fin 3, ((R a.1).face a.2).carrier ∩ ((R d.1).face d.2).carrier =
              (((R a.1).face a.2).boundary k).map '' Icc (0 : ℝ) 1 ∧
            (((R a.1).face a.2).boundary k).map '' Icc (0 : ℝ) 1 =
              (((R d.1).face d.2).boundary l).map '' Icc (0 : ℝ) 1) ∨
          ∃ v : Fin 3, ((R a.1).face a.2).carrier ∩ ((R d.1).face d.2).carrier ⊆
            {F a.1 (meshTriangleBasis (R a.1).mesh a.2 v)}) ∧
        ((R a.1).face a.2).carrier ∩ ((R d.1).face d.2).carrier ⊆
          frontier ((R a.1).face a.2).carrier)) ∧
      (⋃ a : (i : I) × (R i).mesh.Triangle, ((R a.1).face a.2).carrier) =
        ⋃ i, F i '' convexHull ℝ (range (b i)) := by
  classical
  let J := {ij : I × I // ij.1 ≠ ij.2}
  choose P hP using fun ij : J => (hparents ij.1.1 ij.1.2 ij.2).exists_marks
  let V : Set AnnulusCoordinates :=
    (⋃ i, F i '' range (b i)) ∪ ⋃ ij : J, (P ij : Set AnnulusCoordinates)
  have hV : V.Finite :=
    (finite_iUnion (fun i => (finite_range (b i)).image (F i))).union
      (finite_iUnion (fun ij => (P ij).finite_toSet))
  let allmarks := hV.toFinset
  let S (i : I) := allmarks.filter
    (fun q => q ∈ F i '' frontier (convexHull ℝ (range (b i))))
  have hS (i : I) : (S i : Set AnnulusCoordinates) ⊆
      F i '' frontier (convexHull ℝ (range (b i))) :=
    fun _ hq => (Finset.mem_filter.mp hq).2
  have hvertices (i : I) : F i '' range (b i) ⊆ (S i : Set AnnulusCoordinates) := by
    intro q hq
    refine Finset.mem_filter.mpr ⟨?_, image_mono (region_vertex_frontier (b i)) hq⟩
    exact (Set.Finite.mem_toFinset hV).mpr (Or.inl (mem_iUnion.mpr ⟨i, hq⟩))
  have hpairmarks (ij : J) : (P ij : Set AnnulusCoordinates) ⊆ S ij.1.1 ∧
      (P ij : Set AnnulusCoordinates) ⊆ S ij.1.2 := by
    have hglobal {q : AnnulusCoordinates} (hq : q ∈ (P ij : Set AnnulusCoordinates)) :
        q ∈ allmarks := (Set.Finite.mem_toFinset hV).mpr (Or.inr (mem_iUnion.mpr ⟨ij, hq⟩))
    exact ⟨fun _ hq => Finset.mem_filter.mpr ⟨hglobal hq, ((hP ij).1 hq).1⟩,
      fun _ hq => Finset.mem_filter.mpr ⟨hglobal hq, ((hP ij).1 hq).2⟩⟩
  have hfrontsub (i : I) : F i '' frontier (convexHull ℝ (range (b i))) ⊆
      F i '' convexHull ℝ (range (b i)) :=
    image_mono ((finite_range (b i)).isCompact_convexHull ℝ).isClosed.frontier_subset
  have hsync (i j : I) (hij : i ≠ j) :
      (S i : Set AnnulusCoordinates) ∩ (F j '' convexHull ℝ (range (b j))) =
        (S j : Set AnnulusCoordinates) ∩ (F i '' convexHull ℝ (range (b i))) := by
    ext q
    constructor
    · rintro ⟨hqi, hqj⟩
      have hqKi := hfrontsub i (hS i hqi)
      exact ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hqi).1,
        ((hparents i j hij).subset_frontiers ⟨hqKi, hqj⟩).2⟩, hqKi⟩
    · rintro ⟨hqj, hqi⟩
      have hqKj := hfrontsub j (hS j hqj)
      exact ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hqj).1,
        ((hparents i j hij).subset_frontiers ⟨hqi, hqKj⟩).1⟩, hqKj⟩
  choose R _ using fun i => exists_smoothTriangleBoundarySubdivision_with_refinement
    (F i) (hF i) (hFi i) (b i) (hsource i) (S i) (hS i) (hvertices i)
    (0 : AnnulusCoordinates) (by simp)
  refine ⟨S, R, ?_, ?_⟩
  · rintro ⟨i, t⟩ ⟨j, u⟩ had
    by_cases hij : i = j
    · subst j
      have htu : t ≠ u := fun h => had (h ▸ rfl)
      exact ⟨region_subdivision_intersections (R i).toSmoothTriangleBoundarySubdivision t u htu,
        (R i).intersection_frontier t u htu⟩
    · let ij : J := ⟨(i, j), hij⟩
      have h := (hP ij).2 (S i) (S j) (hpairmarks ij).1 (hpairmarks ij).2
        (R i).toSmoothTriangleBoundarySubdivision (R j).toSmoothTriangleBoundarySubdivision
        (hsync i j hij) t u
      exact ⟨h.1, h.2.trans inter_subset_left⟩
  · ext q
    constructor
    · intro hq
      obtain ⟨a, ha⟩ := mem_iUnion.mp hq
      apply mem_iUnion.mpr
      refine ⟨a.1, ?_⟩
      rw [← (R a.1).cover]
      exact mem_iUnion.mpr ⟨a.2, ha⟩
    · intro hq
      obtain ⟨i, hi⟩ := mem_iUnion.mp hq
      rw [← (R i).cover] at hi
      obtain ⟨t, ht⟩ := mem_iUnion.mp hi
      exact mem_iUnion.mpr ⟨⟨i, t⟩, ht⟩

end PoincareConjecture
