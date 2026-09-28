


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Decomposition
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Topology
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.PolygonalDomains









set_option autoImplicit false

open Set Classical
open scoped Manifold ContDiff Topology

namespace Poincare.Topology

universe u v

variable {X : Type u} [TopologicalSpace X] {U K A : Set X}



theorem closure_diff_disjoint_of_local_cover
    (hcover : ∀ p ∈ closure U ∩ K,
      ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ∩ closure U ⊆ A) :
    Disjoint (closure (U \ A)) K := by
  apply disjoint_left.mpr
  intro p hp hpK
  obtain ⟨V, hV, hpV, hVA⟩ := hcover p ⟨closure_mono sdiff_subset hp, hpK⟩
  obtain ⟨q, hqV, hq⟩ := mem_closure_iff.mp hp V hV hpV
  exact hq.2 (hVA ⟨hqV, subset_closure hq.1⟩)



theorem closure_diff_subset_of_local_frontier_cover (hU : IsOpen U)
    (hfront : frontier U ⊆ K)
    (hcover : ∀ p ∈ closure U ∩ K,
      ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ∩ closure U ⊆ A) :
    closure (U \ A) ⊆ U := by
  intro p hp
  have hpc : p ∈ closure U := closure_mono sdiff_subset hp
  by_contra hpU
  apply disjoint_left.mp (closure_diff_disjoint_of_local_cover hcover) hp
  apply hfront
  rw [hU.frontier_eq]
  exact ⟨hpc, hpU⟩


theorem closure_diff_inter_subset_frontier (hAU : A ⊆ K) :
    closure (U \ K) ∩ A ⊆ frontier A := by
  rintro p ⟨hp, hpA⟩
  refine ⟨subset_closure hpA, ?_⟩
  intro hpint
  obtain ⟨q, hqint, hq⟩ := mem_closure_iff.mp hp (interior A) isOpen_interior hpint
  exact hq.2 (hAU (interior_subset hqint))


theorem frontier_diff_iUnion_subset_of_local_cover
    {I : Type v} [Finite I] (pieces interfaces : I → Set X)
    (hU : IsOpen U) (hclosed : ∀ i, IsClosed (pieces i))
    (hfront : frontier U ⊆ K)
    (hpieces : ∀ i, frontier (pieces i) ⊆ K ∪ interfaces i)
    (hcover : ∀ p ∈ closure U ∩ K,
      ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ∩ closure U ⊆ ⋃ i, pieces i) :
    frontier (U \ ⋃ i, pieces i) ⊆ ⋃ i, interfaces i := by
  have hopen : IsOpen (U \ ⋃ i, pieces i) :=
    hU.sdiff (isClosed_iUnion_of_finite hclosed)
  have hsubset := closure_diff_subset_of_local_frontier_cover hU hfront hcover
  have hdisjoint := closure_diff_disjoint_of_local_cover hcover
  intro p hp
  have hpcl := frontier_subset_closure hp
  have hpU := hsubset hpcl
  have hpnotK : p ∉ K := fun hpK => disjoint_left.mp hdisjoint hpcl hpK
  have hpin : p ∈ ⋃ i, pieces i := by
    by_contra hpout
    exact hp.2 (hopen.interior_eq.symm ▸ And.intro hpU hpout)
  obtain ⟨i, hpi⟩ := mem_iUnion.mp hpin
  have hpfront : p ∈ frontier (pieces i) :=
    closure_diff_inter_subset_frontier (subset_iUnion pieces i) ⟨hpcl, hpi⟩
  exact mem_iUnion.mpr ⟨i, (hpieces i hpfront).resolve_left hpnotK⟩



theorem closure_eq_iUnion_union_closure_diff
    {I : Type v} [Finite I] (pieces : I → Set X)
    (hclosed : ∀ i, IsClosed (pieces i)) (hsub : ∀ i, pieces i ⊆ closure U) :
    closure U = (⋃ i, pieces i) ∪ closure (U \ ⋃ i, pieces i) := by
  apply subset_antisymm
  · apply closure_minimal ?_
      ((isClosed_iUnion_of_finite hclosed).union isClosed_closure)
    intro p hp
    by_cases hpin : p ∈ ⋃ i, pieces i
    · exact Or.inl hpin
    · exact Or.inr (subset_closure ⟨hp, hpin⟩)
  · exact union_subset (iUnion_subset hsub) (closure_mono sdiff_subset)

end Poincare.Topology

namespace PoincareConjecture.Topology.Surface

universe u v

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

omit [T2Space M] [IsManifold (𝓡 2) ∞ M] in



theorem exists_exact_polygonal_remainder_mesh_with_refinement
    {I : Type v} [Finite I] (p : M) {U K : Set M}
    (hU : IsOpen U) (hcompact : IsCompact (closure U))
    (hsource : closure U ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source)
    (pieces : I → Set M) (hclosed : ∀ i, IsClosed (pieces i))
    (hsub : ∀ i, pieces i ⊆ closure U) (hfront : frontier U ⊆ K)
    (lines : List (Poincare.Topology.Plane.Meshes.Plane →ᵃ[ℝ] ℝ))
    (hsurj : ∀ l ∈ lines, Function.Surjective l)
    (hpieces : ∀ i, frontier (pieces i) ⊆ K ∪
      (chartAt (EuclideanSpace ℝ (Fin 2)) p) ⁻¹' (⋃ l ∈ lines, {z | l z = 0}))
    (hcover : ∀ q ∈ closure U ∩ K,
      ∃ V : Set M, IsOpen V ∧ q ∈ V ∧ V ∩ closure U ⊆ ⋃ i, pieces i) :
    ∃ T : Poincare.Topology.Plane.Meshes.TriangleMesh,
      T.toPlaneComplex.support =
        closure ((chartAt (EuclideanSpace ℝ (Fin 2)) p) '' (U \ ⋃ i, pieces i)) ∧
      T.toPlaneComplex.support ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).target ∧
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm '' T.toPlaneComplex.support =
        closure (U \ ⋃ i, pieces i) ∧
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm '' T.toPlaneComplex.support ⊆ U ∧
      closure U = (⋃ i, pieces i) ∪
        ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm '' T.toPlaneComplex.support) ∧
      (∀ i, ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm '' T.toPlaneComplex.support) ∩ pieces i ⊆
        frontier (pieces i) ∩
          (chartAt (EuclideanSpace ℝ (Fin 2)) p) ⁻¹' (⋃ l ∈ lines, {z | l z = 0})) ∧
      ∃ (b : AffineBasis (Fin 3) ℝ (Poincare.Topology.Plane.Meshes.Plane))
        (refinement_lines : List (Poincare.Topology.Plane.Meshes.Plane →ᵃ[ℝ] ℝ))
        (P : Finset ((Poincare.Topology.Plane.Meshes.TriangleMesh.single b b.ind).refineByLines
          refinement_lines).Vertex → Prop),
        T = ((Poincare.Topology.Plane.Meshes.TriangleMesh.single b b.ind).refineByLines
          refinement_lines).restrictTriangles P ∧
        T.toPlaneComplex.support ⊆ interior (convexHull ℝ (range b)) := by
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) p
  let C := U \ ⋃ i, pieces i
  have hCopen : IsOpen C := hU.sdiff (isClosed_iUnion_of_finite hclosed)
  have hCU : closure C ⊆ U :=
    Poincare.Topology.closure_diff_subset_of_local_frontier_cover hU hfront hcover
  have hCclosure : closure C ⊆ closure U := closure_mono sdiff_subset
  have hCcompact : IsCompact (closure C) :=
    hcompact.of_isClosed_subset isClosed_closure hCclosure
  have hCsource : closure C ⊆ e.source := hCclosure.trans hsource
  have hCfront : frontier C ⊆ e ⁻¹' (⋃ l ∈ lines, {z | l z = 0}) := by
    have hf := Poincare.Topology.frontier_diff_iUnion_subset_of_local_cover pieces
      (fun _ => e ⁻¹' (⋃ l ∈ lines, {z | l z = 0})) hU hclosed hfront hpieces hcover
    intro q hq
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hf hq)
    exact hi
  have hopen : IsOpen (e '' C) :=
    e.isOpen_image_of_subset_source hCopen (subset_closure.trans hCsource)
  have hbounded : Bornology.IsBounded (e '' C) :=
    (hCcompact.image_of_continuousOn (e.continuousOn.mono hCsource)).isBounded.subset
      (image_mono subset_closure)
  have hfrontier : frontier (e '' C) ⊆ ⋃ l ∈ lines, {z | l z = 0} := by
    rw [← chart_image_frontier_of_isCompact_closure p hCcompact hCsource]
    rintro z ⟨q, hq, rfl⟩
    exact hCfront hq
  obtain ⟨T, hT, b, P, hmesh, hinterior⟩ :=
    Poincare.Topology.Plane.Meshes.exists_triangleMesh_of_frontier_in_finitely_many_lines_with_refinement
      hopen hbounded lines hsurj hfrontier
  have hclosure : e '' closure C = closure (e '' C) :=
    image_closure_of_isCompact hCcompact (e.continuousOn.mono hCsource)
  have htarget : T.toPlaneComplex.support ⊆ e.target := by
    rw [hT, ← hclosure]
    rintro z ⟨q, hq, rfl⟩
    exact e.map_source (hCsource hq)
  have hback : e.symm '' T.toPlaneComplex.support = closure C := by
    rw [hT, ← hclosure, image_image]
    apply subset_antisymm
    · rintro q ⟨z, hz, rfl⟩
      simpa only [e.left_inv (hCsource hz)] using hz
    · intro q hq
      exact ⟨q, hq, e.left_inv (hCsource hq)⟩
  refine ⟨T, hT, htarget, hback, hback ▸ hCU, ?_, ?_, b, lines, P, hmesh, hinterior⟩
  · rw [hback]
    exact Poincare.Topology.closure_eq_iUnion_union_closure_diff pieces hclosed hsub
  · intro i q hq
    rw [hback] at hq
    have hqi := Poincare.Topology.closure_diff_inter_subset_frontier
      (subset_iUnion pieces i) hq
    refine ⟨hqi, (hpieces i hqi).resolve_left ?_⟩
    exact fun hqK => disjoint_left.mp
      (Poincare.Topology.closure_diff_disjoint_of_local_cover hcover) hq.1 hqK

omit [T2Space M] [IsManifold (𝓡 2) ∞ M] in

theorem exists_exact_polygonal_remainder_mesh
    {I : Type v} [Finite I] (p : M) {U K : Set M}
    (hU : IsOpen U) (hcompact : IsCompact (closure U))
    (hsource : closure U ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source)
    (pieces : I → Set M) (hclosed : ∀ i, IsClosed (pieces i))
    (hsub : ∀ i, pieces i ⊆ closure U) (hfront : frontier U ⊆ K)
    (lines : List (Poincare.Topology.Plane.Meshes.Plane →ᵃ[ℝ] ℝ))
    (hsurj : ∀ l ∈ lines, Function.Surjective l)
    (hpieces : ∀ i, frontier (pieces i) ⊆ K ∪
      (chartAt (EuclideanSpace ℝ (Fin 2)) p) ⁻¹' (⋃ l ∈ lines, {z | l z = 0}))
    (hcover : ∀ q ∈ closure U ∩ K,
      ∃ V : Set M, IsOpen V ∧ q ∈ V ∧ V ∩ closure U ⊆ ⋃ i, pieces i) :
    ∃ T : Poincare.Topology.Plane.Meshes.TriangleMesh,
      T.toPlaneComplex.support =
        closure ((chartAt (EuclideanSpace ℝ (Fin 2)) p) '' (U \ ⋃ i, pieces i)) ∧
      T.toPlaneComplex.support ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).target ∧
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm '' T.toPlaneComplex.support =
        closure (U \ ⋃ i, pieces i) ∧
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm '' T.toPlaneComplex.support ⊆ U ∧
      closure U = (⋃ i, pieces i) ∪
        ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm '' T.toPlaneComplex.support) ∧
      ∀ i, ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm '' T.toPlaneComplex.support) ∩ pieces i ⊆
        frontier (pieces i) ∩
          (chartAt (EuclideanSpace ℝ (Fin 2)) p) ⁻¹' (⋃ l ∈ lines, {z | l z = 0}) := by
  obtain ⟨T, hs, ht, hb, hu, hc, hf, _⟩ :=
    exists_exact_polygonal_remainder_mesh_with_refinement p hU hcompact hsource pieces
      hclosed hsub hfront lines hsurj hpieces hcover
  exact ⟨T, hs, ht, hb, hu, hc, hf⟩

namespace FiniteChartRegionDecomposition




theorem exists_exact_region_remainder_mesh
    (D : FiniteChartRegionDecomposition (M := M)) {I : Type v} [Finite I]
    (x : D.regions) (p : M)
    (hsource : closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ x) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).source)
    (face : I → SmoothFace M)
    (hsub : ∀ i, (face i).carrier ⊆
      closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ x))
    (lines : List (Poincare.Topology.Plane.Meshes.Plane →ᵃ[ℝ] ℝ))
    (hsurj : ∀ l ∈ lines, Function.Surjective l)
    (hfront : ∀ i, frontier (face i).carrier ⊆ chartDiskBoundaryUnion D.centers D.radius ∪
      (chartAt (EuclideanSpace ℝ (Fin 2)) p) ⁻¹' (⋃ l ∈ lines, {z | l z = 0}))
    (hcover : ∀ q ∈
        closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ x) ∩
          chartDiskBoundaryUnion D.centers D.radius,
      ∃ V : Set M, IsOpen V ∧ q ∈ V ∧
        V ∩ closure (connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ x) ⊆
          ⋃ i, (face i).carrier) :
    let U := connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ x
    ∃ T : Poincare.Topology.Plane.Meshes.TriangleMesh,
      T.toPlaneComplex.support =
        closure ((chartAt (EuclideanSpace ℝ (Fin 2)) p) '' (U \ ⋃ i, (face i).carrier)) ∧
      T.toPlaneComplex.support ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).target ∧
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm '' T.toPlaneComplex.support =
        closure (U \ ⋃ i, (face i).carrier) ∧
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm '' T.toPlaneComplex.support ⊆ U ∧
      closure U = (⋃ i, (face i).carrier) ∪
        ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm '' T.toPlaneComplex.support) ∧
      ∀ i, ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm '' T.toPlaneComplex.support) ∩
          (face i).carrier ⊆ frontier (face i).carrier ∩
        (chartAt (EuclideanSpace ℝ (Fin 2)) p) ⁻¹' (⋃ l ∈ lines, {z | l z = 0}) := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) M
  obtain ⟨_, _, _, _, hcompact, _⟩ := D.region_containment x (D.regions_outside x x.property)
  exact exists_exact_polygonal_remainder_mesh p
    (isClosed_chartDiskBoundaryUnion D.centers D.radius).isOpen_compl.connectedComponentIn
    hcompact hsource (fun i => (face i).carrier) (fun i => (face i).isClosed_carrier) hsub
    (Poincare.Topology.frontier_connectedComponentIn_compl_subset
      (isClosed_chartDiskBoundaryUnion D.centers D.radius) x) lines hsurj hfront hcover

end FiniteChartRegionDecomposition

end PoincareConjecture.Topology.Surface
