import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.RefinedFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.BoundaryFans








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Classical
open scoped Manifold ContDiff Bundle Matrix
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface.ObliqueBandFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {F : OpenPartialHomeomorph Plane S}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

private theorem face_hull_subset_rectangle (p : Fin B.interface.count × Bool) {w : Plane}
    (hw : w ∈ convexHull ℝ (range (B.faceBasis p))) :
    w 0 ∈ Icc (B.cut p.1.castSucc) (B.cut p.1.succ) ∧ w 1 ∈ Icc (0 : ℝ) 1 := by
  change w ∈ {z : Plane | z 0 ∈ Icc (B.cut p.1.castSucc) (B.cut p.1.succ) ∧
    z 1 ∈ Icc (0 : ℝ) 1}
  rw [← rectangle_triangle_union (B.cut_strictMono Fin.castSucc_lt_succ) zero_lt_one]
  rcases p with ⟨i, s⟩
  cases s
  · exact Or.inl hw
  · exact Or.inr hw

private theorem upper_graph_mem_source {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    collarParameterEquiv.symm (t, B.height t) ∈ B.coordinates.source := by
  apply B.band_subset_source
  rw [B.band_eq_subgraph]
  simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply, Prod.fst, Prod.snd] using
    And.intro ht (And.intro (B.height_pos ht).le (le_refl (B.height t)))



theorem face_preimage_upper_graph (p : Fin B.interface.count × Bool) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {w : Plane}
    (hw : w ∈ convexHull ℝ (range (B.faceBasis p)))
    (heq : B.faceCoordinates p w = B.coordinates (collarParameterEquiv.symm (t, B.height t))) :
    w = collarParameterEquiv.symm (t, 1) := by
  have hrect := B.face_hull_subset_rectangle p hw
  have hsource : collarParameterEquiv.symm
      (graphStripMap (fun _ => 0) (B.upperGraph p.1) (collarParameterEquiv w)) ∈
      B.coordinates.source := (B.face_triangle_subset_source p hw).2
  have hp := collarParameterEquiv.symm.injective
    (B.coordinates.injOn hsource (B.upper_graph_mem_source ht) heq)
  have hx : w 0 = t := congrArg Prod.fst hp
  have hy : w 1 * B.upperGraph p.1 (w 0) = B.height t := by
    have h : 0 + w 1 * (B.upperGraph p.1 (w 0) - 0) = B.height t := congrArg Prod.snd hp
    simpa only [sub_zero, zero_add] using h
  have hinterval : t ∈ Icc (B.cut p.1.castSucc) (B.cut p.1.succ) := hx ▸ hrect.1
  rw [hx, ← B.height_eq_upperGraph hinterval] at hy
  have hy1 : w 1 = 1 := by nlinarith [B.height_pos ht]
  ext k
  fin_cases k <;> simp [collarParameterEquiv, hx, hy1]

private theorem face_upper_graph_map (i : Fin B.interface.count) {t : ℝ}
    (ht : t ∈ Icc (B.cut i.castSucc) (B.cut i.succ)) :
    B.faceCoordinates (i, true) (collarParameterEquiv.symm (t, 1)) =
      B.coordinates (collarParameterEquiv.symm (t, B.height t)) := by
  change B.coordinates (collarParameterEquiv.symm
    (graphStripMap (fun _ => 0) (B.upperGraph i)
      (collarParameterEquiv (collarParameterEquiv.symm (t, 1))))) = _
  simp [graphStripMap, B.height_eq_upperGraph ht]

private theorem upper_axis_mem_hull (i : Fin B.interface.count) {t : ℝ}
    (ht : t ∈ Icc (B.cut i.castSucc) (B.cut i.succ)) :
    collarParameterEquiv.symm (t, 1) ∈ convexHull ℝ (range (B.faceBasis (i, true))) := by
  rw [show B.faceBasis (i, true) = rectangleUpperBasis
    (B.cut_strictMono Fin.castSucc_lt_succ) zero_lt_one from rfl,
    mem_rectangleUpperBasis_convexHull]
  simp only [collarParameterEquiv, sub_zero, div_one]
  exact ⟨div_nonneg (sub_nonneg.mpr ht.1)
      (sub_pos.mpr (B.cut_strictMono Fin.castSucc_lt_succ)).le,
    (div_le_one (sub_pos.mpr (B.cut_strictMono Fin.castSucc_lt_succ))).mpr
      (sub_le_sub_right ht.2 _), le_rfl⟩

private theorem cell_eq_of_open_interval {i j : Fin B.interface.count} {t : ℝ}
    (hi : t ∈ Ioo (B.cut i.castSucc) (B.cut i.succ))
    (hj : t ∈ Icc (B.cut j.castSucc) (B.cut j.succ)) : j = i := by
  rcases lt_trichotomy j i with hji | hji | hij
  · have hle : j.succ ≤ i.castSucc := hji
    exact False.elim (not_lt_of_ge (hj.2.trans (B.cut_strictMono.monotone hle)) hi.1)
  · exact hji
  · have hle : i.succ ≤ j.castSucc := hij
    exact False.elim (not_lt_of_ge ((B.cut_strictMono.monotone hle).trans hj.1) hi.2)



theorem upper_graph_mem_face_carrier_iff (i : Fin B.interface.count) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hi : t ∈ Ioo (B.cut i.castSucc) (B.cut i.succ))
    (p : Fin B.interface.count × Bool) :
    B.coordinates (collarParameterEquiv.symm (t, B.height t)) ∈ (B.face p).carrier ↔
      p = (i, true) := by
  constructor
  · rw [B.face_carrier_eq_coordinates]
    rintro ⟨w, hw, heq⟩
    have hpos := B.face_preimage_upper_graph p ht hw heq
    rw [hpos] at hw
    have hr := B.face_hull_subset_rectangle p hw
    have hcell : p.1 = i := B.cell_eq_of_open_interval hi hr.1
    rcases p with ⟨j, s⟩
    dsimp at hcell
    subst j
    cases s
    · have hh := (mem_rectangleLowerBasis_convexHull
        (B.cut_strictMono (Fin.castSucc_lt_succ (i := i))) zero_lt_one
        (collarParameterEquiv.symm (t, 1))).mp hw
      have hlt : (t - B.cut i.castSucc) / (B.cut i.succ - B.cut i.castSucc) < 1 :=
        (div_lt_one (sub_pos.mpr (B.cut_strictMono Fin.castSucc_lt_succ))).mpr
          (sub_lt_sub_right hi.2 _)
      have hle : 1 ≤ (t - B.cut i.castSucc) / (B.cut i.succ - B.cut i.castSucc) := by
        simpa [collarParameterEquiv] using hh.2.1
      exact False.elim (not_lt_of_ge hle hlt)
    · rfl
  · rintro rfl
    rw [B.face_carrier_eq_coordinates]
    exact ⟨collarParameterEquiv.symm (t, 1), B.upper_axis_mem_hull i ⟨hi.1.le, hi.2.le⟩,
      B.face_upper_graph_map i ⟨hi.1.le, hi.2.le⟩⟩



theorem upper_axis_mem_open_edge (i : Fin B.interface.count) {t : ℝ}
    (hi : t ∈ Ioo (B.cut i.castSucc) (B.cut i.succ)) :
    collarParameterEquiv.symm (t, 1) ∈ openSegment ℝ
      (B.faceBasis (i, true) 1) (B.faceBasis (i, true) 2) := by
  rw [openSegment_eq_image_lineMap]
  let s := (t - B.cut i.castSucc) / (B.cut i.succ - B.cut i.castSucc)
  have hd : 0 < B.cut i.succ - B.cut i.castSucc :=
    sub_pos.mpr (B.cut_strictMono Fin.castSucc_lt_succ)
  have hs : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr hi.1) hd,
      (div_lt_one hd).mpr (sub_lt_sub_right hi.2 _)⟩
  refine ⟨s, hs, ?_⟩
  have he : s * (B.cut i.succ - B.cut i.castSucc) = t - B.cut i.castSucc :=
    div_mul_cancel₀ _ hd.ne'
  ext k
  fin_cases k <;>
    simp [faceBasis, SmoothGraphBandPair.faceBasis, AffineMap.lineMap_apply,
      vsub_eq_sub, vadd_eq_add, collarParameterEquiv]
  linarith

private theorem refined_vertex_mem_face_hull (p : Fin B.interface.count × Bool)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (u : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines lines).Triangle)
    (x : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines lines).Vertex)
    (hx : x ∈ u.1) :
    ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines lines).position x ∈
      convexHull ℝ (range (B.faceBasis p)) := by
  let M := (TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines lines
  have hr : M.position x ∈ range (meshTriangleBasis M u) := by
    rw [range_meshTriangleBasis]
    exact ⟨x, hx, rfl⟩
  have hs := meshTriangleBasis_subset_support M u (subset_convexHull ℝ _ hr)
  simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using hs



theorem upper_graph_refined_vertex_fan (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (lines : (Fin B.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    (i : Fin B.interface.count) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hi : t ∈ Ioo (B.cut i.castSucc) (B.cut i.succ))
    (hused : ∃ (p : Fin B.interface.count × Bool)
      (u : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).Triangle)
      (x : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).Vertex),
      x ∈ u.1 ∧ B.faceCoordinates p
        (((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).position x) =
          B.coordinates (collarParameterEquiv.symm (t, B.height t))) :
    (∑ p : Fin B.interface.count × Bool,
      meshVertexAngleContribution g (B.faceCoordinates p)
        ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p))
        (B.coordinates (collarParameterEquiv.symm (t, B.height t)))) = Real.pi := by
  obtain ⟨p, u, x, hx, hpoint⟩ := hused
  have hxhull := B.refined_vertex_mem_face_hull p (lines p) u x hx
  have hcarrier : B.coordinates (collarParameterEquiv.symm (t, B.height t)) ∈ (B.face p).carrier := by
    rw [B.face_carrier_eq_coordinates]
    exact ⟨_, hxhull, hpoint⟩
  have hp := (B.upper_graph_mem_face_carrier_iff i ht hi p).mp hcarrier
  subst p
  have hxaxis := B.face_preimage_upper_graph (i, true) ht hxhull hpoint
  have hfan := single_refineByLines_open_edge_vertex_fan g (B.faceCoordinates (i, true))
    (B.faceBasis (i, true)) (lines (i, true)) 0
    (B.smooth_faceCoordinates hF (i, true)) (B.smooth_faceCoordinates_symm hFi (i, true))
    (B.face_triangle_subset_source (i, true)) u x hx
    (by rw [hxaxis]; exact B.upper_axis_mem_open_edge i hi)
  rw [hpoint] at hfan
  calc
    _ = meshVertexAngleContribution g (B.faceCoordinates (i, true))
        ((TriangleMesh.single (B.faceBasis (i, true))
          (B.faceBasis (i, true)).ind).refineByLines (lines (i, true)))
        (B.coordinates (collarParameterEquiv.symm (t, B.height t))) := by
      apply Finset.sum_eq_single (i, true)
      · intro p _ hp
        exact B.refined_contribution_eq_zero_of_not_mem_carrier g p (lines p)
          ((B.upper_graph_mem_face_carrier_iff i ht hi p).not.mpr hp)
      · simp
    _ = Real.pi := hfan



theorem polygonal_top_refined_vertex_fan (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (lines : (Fin B.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    {q : S} (hq : q ∈ B.polygonalTop)
    (hqvertex : ∀ k : Fin (B.interface.count + 1), q ≠ B.vertex (k, true))
    (hused : ∃ (p : Fin B.interface.count × Bool)
      (u : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).Triangle)
      (x : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).Vertex),
      x ∈ u.1 ∧ B.faceCoordinates p
        (((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).position x) = q) :
    (∑ p : Fin B.interface.count × Bool,
      meshVertexAngleContribution g (B.faceCoordinates p)
        ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)) q) =
      Real.pi := by
  rw [← B.height_graph_image] at hq
  obtain ⟨t, ht, hpoint⟩ := hq
  dsimp only at hpoint
  have hcover := ht
  rw [← B.cut_interval_cover] at hcover
  obtain ⟨i, hi⟩ := mem_iUnion.mp hcover
  have hleft : B.cut i.castSucc ≠ t := by
    intro heq
    apply hqvertex i.castSucc
    rw [← hpoint, ← heq, B.height_eq_upperGraph (heq.symm ▸ hi), (B.upperGraph_endpoints i).1]
    rfl
  have hright : t ≠ B.cut i.succ := by
    intro heq
    apply hqvertex i.succ
    rw [← hpoint, heq, B.height_eq_upperGraph (heq ▸ hi), (B.upperGraph_endpoints i).2]
    rfl
  have hio : t ∈ Ioo (B.cut i.castSucc) (B.cut i.succ) :=
    ⟨lt_of_le_of_ne hi.1 hleft, lt_of_le_of_ne hi.2 hright⟩
  rw [← hpoint] at hused ⊢
  exact B.upper_graph_refined_vertex_fan g hF hFi lines i ht hio hused



theorem upper_graph_actual_mesh_vertex_fan (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (M : (Fin B.interface.count × Bool) → TriangleMesh)
    (lines : (Fin B.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    (hM : ∀ p, M p = (TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p))
    (i : Fin B.interface.count) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hi : t ∈ Ioo (B.cut i.castSucc) (B.cut i.succ)) (q : S)
    (hq : B.coordinates (collarParameterEquiv.symm (t, B.height t)) = q)
    (hused : ∃ (p : Fin B.interface.count × Bool) (u : (M p).Triangle) (x : (M p).Vertex),
      x ∈ u.1 ∧ B.faceCoordinates p ((M p).position x) = q) :
    (∑ p, meshVertexAngleContribution g (B.faceCoordinates p) (M p) q) = Real.pi := by
  have heq : M = fun p =>
      (TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p) := funext hM
  subst M
  subst q
  exact B.upper_graph_refined_vertex_fan g hF hFi lines i ht hi hused

end PoincareConjecture.Topology.Surface.ObliqueBandFaces
