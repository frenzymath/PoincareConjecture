import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.RefinedFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.BoundaryFans
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Gluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Classical
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.ObliqueBandFaces

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {F : OpenPartialHomeomorph Plane S}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

omit [T2Space S] in
theorem coordinates_symm_endpointEdge (right : Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    collarParameterEquiv (B.coordinates.symm ((B.endpointEdge right).map t)) =
      (if right then 1 else 0, t * B.height (if right then 1 else 0)) := by
  have he : (B.endpointEdge right).map t = B.coordinates
      (collarParameterEquiv.symm (if right then 1 else 0,
        t * B.height (if right then 1 else 0))) := B.endpointEdge_map right t
  have hb : collarParameterEquiv.symm (if right then 1 else 0,
      t * B.height (if right then 1 else 0)) ∈ B.band := by
    rw [B.band_eq_subgraph]
    simp only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply]
    have hr : (if right then 1 else 0 : ℝ) ∈ Icc (0 : ℝ) 1 := by cases right <;> simp
    exact ⟨hr, mul_nonneg ht.1 (B.height_pos hr).le,
      (mul_le_mul_of_nonneg_right ht.2 (B.height_pos hr).le).trans_eq (one_mul _)⟩
  rw [he, B.coordinates.left_inv (B.band_subset_source hb), collarParameterEquiv.apply_symm_apply]

omit [T2Space S] in

theorem open_endpointEdge_ne_vertex (right : Bool) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (v : Fin (B.interface.count + 1) × Bool) :
    (B.endpointEdge right).map t ≠ B.vertex v := by
  intro he
  have hcoord := congrArg (fun q => collarParameterEquiv (B.coordinates.symm q)) he
  rw [B.coordinates_symm_endpointEdge right (Ioo_subset_Icc_self ht), B.coordinates_symm_vertex] at hcoord
  have hx := congrArg Prod.fst hcoord
  have hy := congrArg Prod.snd hcoord
  cases right
  · simp only [Bool.false_eq_true, ↓reduceIte] at hx hy
    have hv : v.1 = 0 := B.cut_strictMono.injective (by simpa only [B.cut_first] using hx.symm)
    have hheight : B.interface.height v.1 = B.height 0 := by
      rw [hv, B.interface.height_first, B.height_zero]
    rw [hheight] at hy
    have hh := B.height_pos (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    cases hvb : v.2 <;> simp only [hvb, Bool.false_eq_true, ↓reduceIte] at hy <;> nlinarith [ht.1, ht.2]
  · simp only [↓reduceIte] at hx hy
    have hv : v.1 = Fin.last B.interface.count := B.cut_strictMono.injective
      (by simpa only [B.cut_last] using hx.symm)
    have hheight : B.interface.height v.1 = B.height 1 := by
      rw [hv, B.interface.height_last, B.height_one]
    rw [hheight] at hy
    have hh := B.height_pos (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    cases hvb : v.2 <;> simp only [hvb, Bool.false_eq_true, ↓reduceIte] at hy <;> nlinarith [ht.1, ht.2]

theorem open_endpointEdge_mem_face_iff (right : Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (p : Fin B.interface.count × Bool) :
    (B.endpointEdge right).map t ∈ (B.face p).carrier ↔
      p = if right then (B.lastCell, false) else (B.firstCell, true) := by
  constructor
  · intro hp
    have hparam := (B.pair p.1).parameter_mem hp
    rw [B.coordinates_symm_endpointEdge right (Ioo_subset_Icc_self ht)] at hparam
    rcases p with ⟨i, s⟩
    cases right
    · have hi : i = B.firstCell := by
        apply Fin.ext
        have hc : B.cut i.castSucc = B.cut 0 := by
          rw [B.cut_first]
          exact le_antisymm hparam.1.1 (by
            simpa only [B.cut_first] using B.cut_strictMono.monotone (Fin.zero_le i.castSucc))
        have hh := congrArg Fin.val (B.cut_strictMono.injective hc)
        exact hh
      subst i
      cases s
      · apply False.elim (B.open_endpointEdge_ne_vertex false ht (0, false) ?_)
        exact (B.pair B.firstCell).lower_left_vertex hp (by
          rw [B.coordinates_symm_endpointEdge false (Ioo_subset_Icc_self ht)]
          exact B.cut_first.symm)
      · rfl
    · have hi : i = B.lastCell := by
        apply Fin.ext
        have hc : B.cut i.succ = B.cut (Fin.last B.interface.count) := by
          rw [B.cut_last]
          exact le_antisymm (by
            simpa only [B.cut_last] using B.cut_strictMono.monotone (Fin.le_last i.succ)) hparam.1.2
        have hv := congrArg Fin.val (B.cut_strictMono.injective hc)
        simp only [Fin.val_succ, Fin.val_last] at hv
        change i.val = B.interface.count - 1
        omega
      subst i
      cases s
      · rfl
      · apply False.elim (B.open_endpointEdge_ne_vertex true ht (B.lastCell.succ, true) ?_)
        have hx : (collarParameterEquiv (B.coordinates.symm ((B.endpointEdge true).map t))).1 =
            B.cut B.lastCell.succ := by
          rw [B.coordinates_symm_endpointEdge true (Ioo_subset_Icc_self ht)]
          have he : B.lastCell.succ = Fin.last B.interface.count := by
            apply Fin.ext
            have hn := B.interface.count_pos
            simp only [lastCell, Fin.val_succ, Fin.val_last]
            omega
          exact (congrArg B.cut he |>.trans B.cut_last).symm
        simpa only [vertex, ↓reduceIte, (B.upperGraph_endpoints B.lastCell).2] using
          (B.pair B.lastCell).upper_right_vertex hp hx
  · rintro rfl
    cases right
    · exact (B.pair B.firstCell).upper.isClosed_carrier.frontier_subset
        ((B.pair B.firstCell).upper.boundary_image_subset_frontier 2
          ⟨t, Ioo_subset_Icc_self ht, rfl⟩)
    · exact (B.pair B.lastCell).lower.isClosed_carrier.frontier_subset
        ((B.pair B.lastCell).lower.boundary_image_subset_frontier 0
          ⟨t, Ioo_subset_Icc_self ht, rfl⟩)

theorem open_endpoint_refined_vertex_fan
    (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (lines : (Fin B.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    (right : Bool) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hused : ∀ p, (B.endpointEdge right).map t ∈ (B.face p).carrier →
      ∃ (u : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).Triangle)
        (v : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).Vertex),
        v ∈ u.1 ∧ B.faceCoordinates p
          (((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).position v) =
            (B.endpointEdge right).map t) :
    (∑ p : Fin B.interface.count × Bool,
      meshVertexAngleContribution g (B.faceCoordinates p)
        ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p))
        ((B.endpointEdge right).map t)) = Real.pi := by
  let p : Fin B.interface.count × Bool :=
    if right then (B.lastCell, false) else (B.firstCell, true)
  have hp : (B.endpointEdge right).map t ∈ (B.face p).carrier :=
    (B.open_endpointEdge_mem_face_iff right ht p).mpr rfl
  rw [Finset.sum_eq_single p]
  · obtain ⟨u, v, hv, heq⟩ := hused p hp
    rw [← heq]
    apply single_refineByLines_new_boundary_vertex_fan g (B.faceCoordinates p)
      (B.faceBasis p) (lines p) (B.smooth_faceCoordinates hF p)
      (B.smooth_faceCoordinates_symm hFi p) (B.face_triangle_subset_source p) u v hv
    · intro hi
      have hopen := (B.faceCoordinates p).isOpen_image_of_subset_source isOpen_interior
        ((interior_subset (s := convexHull ℝ (range (B.faceBasis p)))).trans
          (B.face_triangle_subset_source p))
      have hface : B.faceCoordinates p
          (((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).position v) ∈
          interior (B.face p).carrier := by
        apply hopen.subset_interior_iff.mpr _ (mem_image_of_mem _ hi)
        rw [B.face_carrier_eq_coordinates]
        exact image_mono interior_subset
      have hband := interior_mono (subset_iUnion (fun p => (B.face p).carrier) p) hface
      exact (B.endpointEdge_subset_frontier right ⟨t, Ioo_subset_Icc_self ht, rfl⟩).2 (heq ▸ hband)
    · rintro ⟨k, hk⟩
      exact B.open_endpointEdge_ne_vertex right ht (B.cornerVertexIndex p k)
        (heq.symm.trans ((congrArg (B.faceCoordinates p) hk).symm.trans (B.face_corner_eq_vertex p k)))
  · intro r _ hr
    exact B.refined_contribution_eq_zero_of_not_mem_carrier g r (lines r)
      ((B.open_endpointEdge_mem_face_iff right ht r).not.mpr hr)
  · simp

end PoincareConjecture.Topology.Surface.ObliqueBandFaces
