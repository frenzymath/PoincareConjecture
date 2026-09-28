


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.Frontier









set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface
namespace ChartCircleArrangementVertexPatch.VertexCapFaces

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {r : M → ℝ} {p : M} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → M} (B : VertexCapFaces P x)


theorem carrier_diff_interior_union_subset_chord (i : Bool × Bool) :
    (B.face i).carrier \ interior (⋃ j, (B.face j).carrier) ⊆
      ((B.face i).boundary 0).map '' Icc (0 : ℝ) 1 := by
  rintro q ⟨hq, hnot⟩
  have hfront : q ∈ frontier (B.face i).carrier :=
    ⟨subset_closure hq, fun h => hnot (interior_mono (subset_iUnion _ i) h)⟩
  rw [(B.face i).boundary_carrier] at hfront
  obtain ⟨k, t, ht, rfl⟩ := mem_iUnion.mp hfront
  fin_cases k
  · exact ⟨t, ht, rfl⟩
  · by_cases hzero : t = 0
    · subst t
      have heq : ((B.face i).boundary 1).map 0 = p := by
        rw [B.second_map i 0 (by simp)]
        simpa [Prod.zero_eq_mk] using P.sectorCoordinates_zero i
      exact False.elim (hnot (heq.symm ▸ B.center_mem_interior_union))
    by_cases hone : t = 1
    · subst t
      refine ⟨1, by simp, ?_⟩
      change ((B.face i).boundary 0).map 1 = ((B.face i).boundary 1).map 1
      rw [B.boundary_map i 0, B.boundary_map i 1]
      simp [affineChartSegment, Fin.succAbove]
    exact False.elim (hnot (B.second_boundary_mem_interior_union i
      ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), lt_of_le_of_ne ht.2 hone⟩))
  · by_cases hzero : t = 0
    · subst t
      have heq : ((B.face i).boundary 2).map 0 = p := by
        rw [B.first_map i 0 (by simp)]
        simpa [Prod.zero_eq_mk] using P.sectorCoordinates_zero i
      exact False.elim (hnot (heq.symm ▸ B.center_mem_interior_union))
    by_cases hone : t = 1
    · subst t
      refine ⟨0, by simp, ?_⟩
      change ((B.face i).boundary 0).map 0 = ((B.face i).boundary 2).map 1
      rw [B.boundary_map i 0, B.boundary_map i 2]
      simp [affineChartSegment, Fin.succAbove, Fin.lt_def]
    exact False.elim (hnot (B.first_boundary_mem_interior_union i
      ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), lt_of_le_of_ne ht.2 hone⟩))

omit [T2Space M] in

theorem chord_segment_subset_chart_target (i : Bool × Bool) :
    affineSegment ℝ
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (B.scale, 0)))
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (0, B.scale))) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).target := by
  rw [affineSegment_eq_segment, segment_eq_image_lineMap]
  rintro z ⟨t, ht, rfl⟩
  have hsource : ((1 - t) * B.scale, t * B.scale) ∈ (B.planarCoordinates i).source := by
    apply B.planar_source i
    exact ⟨mul_nonneg (sub_nonneg.mpr ht.2) B.scale_pos.le,
      mul_nonneg ht.1 B.scale_pos.le, by nlinarith⟩
  have h := B.planar_target i ((B.planarCoordinates i).map_source hsource)
  rw [B.planar_chord i t, B.planar_first i B.scale (by simp [B.scale_pos.le]),
    B.planar_second i B.scale (by simp [B.scale_pos.le])] at h
  simpa only [AffineMap.lineMap_apply_module] using h

omit [T2Space M] in


theorem chart_chord_image (i : Bool × Bool) :
    chartAt (EuclideanSpace ℝ (Fin 2)) (x i) ''
      (((B.face i).boundary 0).map '' Icc (0 : ℝ) 1) =
    affineSegment ℝ
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (B.scale, 0)))
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (0, B.scale))) := by
  rw [B.chord_image i]
  apply subset_antisymm
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    simpa only [(chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).right_inv
      (B.chord_segment_subset_chart_target i hz)] using hz
  · intro z hz
    exact ⟨_, ⟨z, hz, rfl⟩, (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).right_inv
      (B.chord_segment_subset_chart_target i hz)⟩

omit [T2Space M] in

theorem chord_chart_endpoints_ne (i : Bool × Bool) :
    chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (B.scale, 0)) ≠
      chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (0, B.scale)) := by
  intro h
  have hfirst : (B.scale, 0) ∈ (B.planarCoordinates i).source :=
    B.planar_source i ⟨B.scale_pos.le, le_rfl, by simp⟩
  have hsecond : (0, B.scale) ∈ (B.planarCoordinates i).source :=
    B.planar_source i ⟨le_rfl, B.scale_pos.le, by simp⟩
  have heq : B.planarCoordinates i (B.scale, 0) = B.planarCoordinates i (0, B.scale) := by
    rw [B.planar_first i B.scale (by simp [B.scale_pos.le]),
      B.planar_second i B.scale (by simp [B.scale_pos.le])]
    exact h
  exact B.scale_pos.ne' (congrArg Prod.fst ((B.planarCoordinates i).injOn hfirst hsecond heq))

omit [T2Space M] in


theorem chart_chord_subset_affine_line (i : Bool × Bool) :
    chartAt (EuclideanSpace ℝ (Fin 2)) (x i) ''
      (((B.face i).boundary 0).map '' Icc (0 : ℝ) 1) ⊆
    (affineSpan ℝ
      {chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (B.scale, 0)),
        chartAt (EuclideanSpace ℝ (Fin 2)) (x i) (P.sectorCoordinates i (0, B.scale))} :
        Set (EuclideanSpace ℝ (Fin 2))) := by
  rw [B.chart_chord_image i]
  exact affineSegment_subset_affineSpan ℝ _ _

end ChartCircleArrangementVertexPatch.VertexCapFaces

namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  (D : FiniteChartRegionDecomposition (M := M))
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M)}
  {x : D.vertices → Bool × Bool → M}
  (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
  (region : D.vertices → Bool × Bool → D.regions)




theorem frontier_vertexCapsInRegion_inter_cap_subset
    (hregion : ∀ p i, ((B p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    (R : D.regions) (p : D.vertices) (i : Bool × Bool) :
    frontier (D.vertexCapsInRegion B region R) ∩ ((B p).face i).carrier ⊆
      chartDiskBoundaryUnion D.centers D.radius ∪
        (((B p).face i).boundary 0).map '' Icc (0 : ℝ) 1 := by
  have hselected := D.frontier_assigned_pieces_subset
    (fun a : D.vertices × (Bool × Bool) => region a.1 a.2)
    (fun a => ((B a.1).face a.2).carrier)
    (fun a => ((B a.1).face a.2).isClosed_carrier) (fun a => hregion a.1 a.2) R
  rintro q ⟨hq, hcap⟩
  by_cases hK : q ∈ chartDiskBoundaryUnion D.centers D.radius
  · exact Or.inl hK
  have htotal := (hselected hq).resolve_left hK
  refine Or.inr ((B p).carrier_diff_interior_union_subset_chord i ⟨hcap, ?_⟩)
  intro hlocal
  apply htotal.2
  exact interior_mono (iUnion_subset (fun j => subset_iUnion
    (fun a : D.vertices × (Bool × Bool) => ((B a.1).face a.2).carrier) (p, j))) hlocal



theorem inter_cap_subset_chord_of_disjoint_vertexCapsInRegion_interior
    (hregion : ∀ p i, ((B p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    {R : D.regions} {p : D.vertices} {i : Bool × Bool} (hassign : region p i = R)
    {A : Set M} (hA : Disjoint A (interior (D.vertexCapsInRegion B region R)))
    (hK : Disjoint A (chartDiskBoundaryUnion D.centers D.radius)) :
    A ∩ ((B p).face i).carrier ⊆ (((B p).face i).boundary 0).map '' Icc (0 : ℝ) 1 := by
  rintro q ⟨hqA, hcap⟩
  have hselected : q ∈ D.vertexCapsInRegion B region R :=
    mem_iUnion.mpr ⟨⟨(p, i), hassign⟩, hcap⟩
  have hfront : q ∈ frontier (D.vertexCapsInRegion B region R) :=
    ⟨subset_closure hselected, fun h => disjoint_left.mp hA hqA h⟩
  exact (D.frontier_vertexCapsInRegion_inter_cap_subset B region hregion R p i
    ⟨hfront, hcap⟩).resolve_left (fun h => disjoint_left.mp hK hqA h)



theorem inter_cap_subset_chord_of_disjoint_collar_interior
    (hregion : ∀ p i, ((B p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    {R : D.regions} {p : D.vertices} {i : Bool × Bool} (hassign : region p i = R)
    {A C : Set M} (hC : D.vertexCapsInRegion B region R ⊆ C)
    (hA : Disjoint A (interior C))
    (hK : Disjoint A (chartDiskBoundaryUnion D.centers D.radius)) :
    A ∩ ((B p).face i).carrier ⊆ (((B p).face i).boundary 0).map '' Icc (0 : ℝ) 1 :=
  D.inter_cap_subset_chord_of_disjoint_vertexCapsInRegion_interior B region hregion hassign
    (hA.mono_right (interior_mono hC)) hK



theorem chart_inter_cap_subset_segment_of_disjoint_collar_interior
    (hregion : ∀ p i, ((B p).face i).carrier ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    {R : D.regions} {p : D.vertices} {i : Bool × Bool} (hassign : region p i = R)
    {A C : Set M} (hC : D.vertexCapsInRegion B region R ⊆ C)
    (hA : Disjoint A (interior C))
    (hK : Disjoint A (chartDiskBoundaryUnion D.centers D.radius)) :
    chartAt (EuclideanSpace ℝ (Fin 2)) (x p i) '' (A ∩ ((B p).face i).carrier) ⊆
      affineSegment ℝ
        (chartAt (EuclideanSpace ℝ (Fin 2)) (x p i)
          ((P p).sectorCoordinates i ((B p).scale, 0)))
        (chartAt (EuclideanSpace ℝ (Fin 2)) (x p i)
          ((P p).sectorCoordinates i (0, (B p).scale))) := by
  rw [← (B p).chart_chord_image i]
  exact image_mono (D.inter_cap_subset_chord_of_disjoint_collar_interior B region
    hregion hassign hC hA hK)

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
