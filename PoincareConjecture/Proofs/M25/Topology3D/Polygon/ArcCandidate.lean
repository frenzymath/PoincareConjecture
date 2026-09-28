import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcTriangle
import PoincareConjecture.Proofs.M25.Topology3D.Plane.OppositeCoordinate
import PoincareConjecture.Proofs.M25.Topology3D.Plane.PairCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SegmentSubdivision











set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  {p : Polygon E (n + 2)}



theorem IsSimplePolygonalArc.linearIndependent_of_not_admissible
    (hp : IsSimplePolygonalArc p) (k : Fin (n + 2))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1))
    (hnot : ¬ IsAdmissibleArcVertex p k) :
    LinearIndependent ℝ
      ![p ((finRotate (n + 2)).symm k) - p k, p (finRotate (n + 2) k) - p k] := by
  obtain ⟨i, j, hik, hjk, hip, hjs, hij⟩ := exists_arc_incident_edge_indices k hk0 hkl
  have hpk : (finRotate (n + 2)).symm k ≠ k := by
    rw [← hip, ← hik]
    intro h
    have hv := congrArg Fin.val h
    change i.val = i.val + 1 at hv
    omega
  have hsk : finRotate (n + 2) k ≠ k := by
    rw [← hjs, ← hjk]
    intro h
    have hv := congrArg Fin.val h
    change j.val + 1 = j.val at hv
    omega
  have hps : (finRotate (n + 2)).symm k ≠ finRotate (n + 2) k := by
    intro h
    rw [← hip, ← hjs] at h
    have hv := congrArg Fin.val h
    have hk := congrArg Fin.val (hik.trans hjk.symm)
    change i.val = j.val + 1 at hv
    change i.val + 1 = j.val at hk
    omega
  have hinter : segment ℝ (p k) (p ((finRotate (n + 2)).symm k)) ∩
      segment ℝ (p k) (p (finRotate (n + 2) k)) ⊆ {p k} := by
    rintro x ⟨hx, hy⟩
    have hxi : x ∈ p.edgeSet ℝ i.castSucc := by
      rw [polygon_arcEdge_eq_segment, hip, hik, segment_symm]
      exact hx
    have hxj : x ∈ p.edgeSet ℝ j.castSucc := by
      rw [polygon_arcEdge_eq_segment, hjk, hjs]
      exact hy
    have hh := hp.edges_inter i j hij ⟨hxi, hxj⟩
    rw [hip, hik, hjk, hjs] at hh
    rcases hh.1 with hprev | hk
    · rcases hh.2 with hk | hnext
      · exact hk
      · exact (hps (hp.vertices_injective (hprev.symm.trans hnext))).elim
    · exact hk
  have hnotRay := not_sameRay_sub_of_segments_inter_subset_singleton
    (fun h => hpk (hp.vertices_injective h))
    (fun h => hsk (hp.vertices_injective h)) hinter
  by_contra hli
  have hopp := (sameRay_or_sameRay_neg_iff_not_linearIndependent.mpr hli).resolve_left hnotRay
  have hmem : p k ∈ segment ℝ (p ((finRotate (n + 2)).symm k))
      (p (finRotate (n + 2) k)) := by
    apply mem_segment_iff_sameRay.mpr
    simpa only [neg_sub] using sameRay_neg_swap.mpr hopp
  have hT : polygonVertexTriangle p k ⊆
      segment ℝ (p ((finRotate (n + 2)).symm k)) (p (finRotate (n + 2) k)) := by
    apply convexHull_min
    · rintro x (rfl | rfl | rfl)
      · exact hmem
      · exact left_mem_segment ℝ _ _
      · exact right_mem_segment ℝ _ _
    · exact convex_segment (𝕜 := ℝ) _ _
  apply hnot
  refine ⟨hk0, hkl, subset_antisymm ?_
    (polygonArcIncidentEdges_subset_triangle_inter_boundary p k hk0 hkl)⟩
  intro x hx
  rw [(segment_split_at_point hmem).1]
  exact hT hx.1



theorem internal_of_mem_vertexTriangle_of_endpoint_extrema
    (p : Polygon E (n + 2)) (k : Fin (n + 2))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1)) (X : E →ₗ[ℝ] ℝ)
    (hLR : X (p 0) < X (p (Fin.last (n + 1))))
    (hX : ∀ i, i ≠ 0 → i ≠ Fin.last (n + 1) →
      X (p 0) < X (p i) ∧ X (p i) < X (p (Fin.last (n + 1))))
    (j : Fin (n + 2)) (_hjk : j ≠ k) (hjp : j ≠ (finRotate (n + 2)).symm k)
    (hjs : j ≠ finRotate (n + 2) k) (hjT : p j ∈ polygonVertexTriangle p k) :
    j ≠ 0 ∧ j ≠ Fin.last (n + 1) := by
  have hleft (i : Fin (n + 2)) (hi : i ≠ 0) : X (p 0) < X (p i) := by
    by_cases hil : i = Fin.last (n + 1)
    · simpa only [hil] using hLR
    · exact (hX i hi hil).1
  have hright (i : Fin (n + 2)) (hi : i ≠ Fin.last (n + 1)) :
      X (p i) < X (p (Fin.last (n + 1))) := by
    by_cases hi0 : i = 0
    · simpa only [hi0] using hLR
    · exact (hX i hi0 hi).2
  constructor
  · intro hj0
    have hp0 : (finRotate (n + 2)).symm k ≠ 0 := fun h => hjp (hj0.trans h.symm)
    have hs0 : finRotate (n + 2) k ≠ 0 := fun h => hjs (hj0.trans h.symm)
    have hT : polygonVertexTriangle p k ⊆ {x | X (p 0) < X x} := by
      apply convexHull_min
      · rintro x (rfl | rfl | rfl)
        · exact hleft k hk0
        · exact hleft _ hp0
        · exact hleft _ hs0
      · exact convex_halfSpace_gt (X.isLinearMap_of_compatibleSMul ℝ) _
    have hh := hT hjT
    change X (p 0) < X (p j) at hh
    rw [hj0] at hh
    exact (lt_irrefl _ hh)
  · intro hjl
    have hpl : (finRotate (n + 2)).symm k ≠ Fin.last (n + 1) :=
      fun h => hjp (hjl.trans h.symm)
    have hsl : finRotate (n + 2) k ≠ Fin.last (n + 1) :=
      fun h => hjs (hjl.trans h.symm)
    have hT : polygonVertexTriangle p k ⊆ {x | X x < X (p (Fin.last (n + 1)))} := by
      apply convexHull_min
      · rintro x (rfl | rfl | rfl)
        · exact hright k hkl
        · exact hright _ hpl
        · exact hright _ hsl
      · exact convex_halfSpace_lt (X.isLinearMap_of_compatibleSMul ℝ) _
    have hh := hT hjT
    change X (p j) < X (p (Fin.last (n + 1))) at hh
    rw [hjl] at hh
    exact (lt_irrefl _ hh)



theorem IsSimplePolygonalArc.exists_internal_minimal_triangle_vertex
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 2)
    (hp : IsSimplePolygonalArc p) (k : Fin (n + 2))
    (hk0 : k ≠ 0) (hkl : k ≠ Fin.last (n + 1))
    (hnot : ¬ IsAdmissibleArcVertex p k) (X : E →ₗ[ℝ] ℝ)
    (hLR : X (p 0) < X (p (Fin.last (n + 1))))
    (hX : ∀ i, i ≠ 0 → i ≠ Fin.last (n + 1) →
      X (p 0) < X (p i) ∧ X (p i) < X (p (Fin.last (n + 1)))) :
    ∃ (f : E ≃ᴬ[ℝ] (ℝ × ℝ)) (j : Fin (n + 2)),
      f (p k) = (0, 0) ∧ f (p ((finRotate (n + 2)).symm k)) = (1, 0) ∧
      f (p (finRotate (n + 2) k)) = (0, 1) ∧ j ≠ 0 ∧ j ≠ Fin.last (n + 1) ∧
      j ≠ k ∧ j ≠ (finRotate (n + 2)).symm k ∧ j ≠ finRotate (n + 2) k ∧
      f (p j) ∈ unitTriangle ∧ 0 < (f (p j)).1 ∧ 0 < (f (p j)).2 ∧
      (∀ l, l ≠ k → l ≠ (finRotate (n + 2)).symm k →
        l ≠ finRotate (n + 2) k → f (p l) ∈ unitTriangle →
          (f (p j)).1 + (f (p j)).2 ≤ (f (p l)).1 + (f (p l)).2) ∧
      Disjoint (openSegment ℝ (p k) (p j)) (polygonArcBoundary p) := by
  obtain ⟨f, hfk, hfp, hfs⟩ := exists_continuousAffineEquiv_map_triangle hdim
    (hp.linearIndependent_of_not_admissible k hk0 hkl hnot)
  obtain ⟨j, hjk, hjp, hjs, hjT, hjx, hjy, hmin, hvis⟩ :=
    hp.exists_minimal_triangle_vertex_of_not_admissible k hk0 hkl f hfk hfp hfs hnot
  have hnorm : f '' polygonVertexTriangle p k = unitTriangle := by
    have him := f.toAffineEquiv.toAffineMap.image_convexHull
      {p k, p ((finRotate (n + 2)).symm k), p (finRotate (n + 2) k)}
    change f '' polygonVertexTriangle p k =
      convexHull ℝ (f '' {p k, p ((finRotate (n + 2)).symm k),
        p (finRotate (n + 2) k)}) at him
    rw [him, image_insert_eq, image_insert_eq, image_singleton, hfk, hfp, hfs,
      ← unitTriangle_eq_convexHull]
  have hjTri : p j ∈ polygonVertexTriangle p k := by
    obtain ⟨x, hx, heq⟩ := hnorm.symm ▸ hjT
    exact f.injective heq ▸ hx
  have hint := internal_of_mem_vertexTriangle_of_endpoint_extrema
    p k hk0 hkl X hLR hX j hjk hjp hjs hjTri
  exact ⟨f, j, hfk, hfp, hfs, hint.1, hint.2, hjk, hjp, hjs, hjT, hjx, hjy, hmin, hvis⟩

end PoincareConjecture.M25.Topology3D
