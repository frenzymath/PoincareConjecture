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



theorem face_preimage_lower_axis (p : Fin B.interface.count × Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) {w : Plane}
    (hw : w ∈ convexHull ℝ (range (B.faceBasis p)))
    (heq : B.faceCoordinates p w = B.coordinates (collarParameterEquiv.symm (t, 0))) :
    w = collarParameterEquiv.symm (t, 0) := by
  have hrect := B.face_hull_subset_rectangle p hw
  have hsource : collarParameterEquiv.symm
      (graphStripMap (fun _ => 0) (B.upperGraph p.1) (collarParameterEquiv w)) ∈
      B.coordinates.source := (B.face_triangle_subset_source p hw).2
  have hp := collarParameterEquiv.symm.injective
    (B.coordinates.injOn hsource (B.axis_mem_lowerParameterNeighborhood ht).1 heq)
  have hx : w 0 = t := congrArg Prod.fst hp
  have hy : w 1 * B.upperGraph p.1 (w 0) = 0 := by
    have h : 0 + w 1 * (B.upperGraph p.1 (w 0) - 0) = 0 := congrArg Prod.snd hp
    simpa only [sub_zero, zero_add] using h
  have hy0 : w 1 = 0 := (mul_eq_zero.mp hy).resolve_right
    ((B.pair p.1).gap (w 0) hrect.1).ne'
  ext k
  fin_cases k <;> simp [collarParameterEquiv, hx, hy0]

private theorem face_lower_axis_map (i : Fin B.interface.count) (t : ℝ) :
    B.faceCoordinates (i, false) (collarParameterEquiv.symm (t, 0)) =
      B.coordinates (collarParameterEquiv.symm (t, 0)) := by
  change B.coordinates (collarParameterEquiv.symm
    (graphStripMap (fun _ => 0) (B.upperGraph i)
      (collarParameterEquiv (collarParameterEquiv.symm (t, 0))))) = _
  simp [graphStripMap]

private theorem lower_axis_mem_hull (i : Fin B.interface.count) {t : ℝ}
    (ht : t ∈ Icc (B.cut i.castSucc) (B.cut i.succ)) :
    collarParameterEquiv.symm (t, 0) ∈ convexHull ℝ (range (B.faceBasis (i, false))) := by
  rw [show B.faceBasis (i, false) = rectangleLowerBasis
    (B.cut_strictMono Fin.castSucc_lt_succ) zero_lt_one from rfl,
    mem_rectangleLowerBasis_convexHull]
  simp only [collarParameterEquiv, sub_zero, div_one]
  refine ⟨le_rfl, div_nonneg (sub_nonneg.mpr ht.1)
    (sub_pos.mpr (B.cut_strictMono Fin.castSucc_lt_succ)).le, ?_⟩
  exact (div_le_one (sub_pos.mpr (B.cut_strictMono Fin.castSucc_lt_succ))).mpr
    (sub_le_sub_right ht.2 _)

private theorem cell_eq_of_open_interval {i j : Fin B.interface.count} {t : ℝ}
    (hi : t ∈ Ioo (B.cut i.castSucc) (B.cut i.succ))
    (hj : t ∈ Icc (B.cut j.castSucc) (B.cut j.succ)) : j = i := by
  rcases lt_trichotomy j i with hji | hji | hij
  · have hle : j.succ ≤ i.castSucc := hji
    exact False.elim (not_lt_of_ge (hj.2.trans (B.cut_strictMono.monotone hle)) hi.1)
  · exact hji
  · have hle : i.succ ≤ j.castSucc := hij
    exact False.elim (not_lt_of_ge ((B.cut_strictMono.monotone hle).trans hj.1) hi.2)



theorem lower_axis_mem_face_carrier_iff (i : Fin B.interface.count) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (hi : t ∈ Ioo (B.cut i.castSucc) (B.cut i.succ))
    (p : Fin B.interface.count × Bool) :
    B.coordinates (collarParameterEquiv.symm (t, 0)) ∈ (B.face p).carrier ↔ p = (i, false) := by
  constructor
  · rw [B.face_carrier_eq_coordinates]
    rintro ⟨w, hw, heq⟩
    have hpos := B.face_preimage_lower_axis p ht hw heq
    rw [hpos] at hw
    have hr := B.face_hull_subset_rectangle p hw
    have hcell : p.1 = i := B.cell_eq_of_open_interval hi hr.1
    rcases p with ⟨j, s⟩
    dsimp at hcell
    subst j
    cases s
    · rfl
    · have hh := (mem_rectangleUpperBasis_convexHull
        (B.cut_strictMono (Fin.castSucc_lt_succ (i := i))) zero_lt_one
        (collarParameterEquiv.symm (t, 0))).mp hw
      have hpos : 0 < (t - B.cut i.castSucc) / (B.cut i.succ - B.cut i.castSucc) :=
        div_pos (sub_pos.mpr hi.1) (sub_pos.mpr (B.cut_strictMono Fin.castSucc_lt_succ))
      have hle : (t - B.cut i.castSucc) / (B.cut i.succ - B.cut i.castSucc) ≤ 0 := by
        simpa [collarParameterEquiv] using hh.2.1
      exact False.elim (not_lt_of_ge hle hpos)
  · rintro rfl
    rw [B.face_carrier_eq_coordinates]
    exact ⟨collarParameterEquiv.symm (t, 0), B.lower_axis_mem_hull i ⟨hi.1.le, hi.2.le⟩,
      B.face_lower_axis_map i t⟩



theorem lower_axis_mem_open_edge (i : Fin B.interface.count) {t : ℝ}
    (hi : t ∈ Ioo (B.cut i.castSucc) (B.cut i.succ)) :
    collarParameterEquiv.symm (t, 0) ∈ openSegment ℝ
      (B.faceBasis (i, false) 0) (B.faceBasis (i, false) 1) := by
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




theorem lower_axis_refined_vertex_fan (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (lines : (Fin B.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hused : ∃ (p : Fin B.interface.count × Bool)
      (u : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).Triangle)
      (x : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).Vertex),
      x ∈ u.1 ∧ B.faceCoordinates p
        (((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).position x) =
          B.coordinates (collarParameterEquiv.symm (t, 0))) :
    (∑ p : Fin B.interface.count × Bool,
      meshVertexAngleContribution g (B.faceCoordinates p)
        ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p))
        (B.coordinates (collarParameterEquiv.symm (t, 0)))) = Real.pi := by
  by_cases hcut : ∃ k : Fin (B.interface.count + 1), B.cut k = t
  · obtain ⟨k, hk⟩ := hcut
    have hkpos : 0 < k.val := by
      have h : (0 : Fin (B.interface.count + 1)) < k := B.cut_strictMono.lt_iff_lt.mp
        (by simpa only [B.cut_first, hk] using ht.1)
      exact h
    have hklt : k.val < B.interface.count := by
      have h : k < Fin.last B.interface.count := B.cut_strictMono.lt_iff_lt.mp
        (by simpa only [B.cut_last, hk] using ht.2)
      exact h
    let i : Fin B.interface.count := ⟨k.val - 1, by omega⟩
    let j : Fin B.interface.count := ⟨k.val, hklt⟩
    have hi : i.succ = k := by
      apply Fin.ext
      simp only [i, Fin.val_succ]
      omega
    have hj : j.castSucc = k := Fin.ext rfl
    have hp : B.coordinates (collarParameterEquiv.symm (t, 0)) = B.vertex (i.succ, false) := by
      simp only [vertex, Bool.false_eq_true, if_false, hi, hk]
    rw [hp]
    exact B.internal_bottom_refined_vertex_fan g hF hFi lines i j (hi.trans hj.symm)
  · have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    rw [← B.cut_interval_cover] at htcc
    obtain ⟨i, hi⟩ := mem_iUnion.mp htcc
    have hio : t ∈ Ioo (B.cut i.castSucc) (B.cut i.succ) :=
      ⟨lt_of_le_of_ne hi.1 (fun h => hcut ⟨i.castSucc, h⟩),
        lt_of_le_of_ne hi.2 (fun h => hcut ⟨i.succ, h.symm⟩)⟩
    obtain ⟨p, u, x, hx, hpoint⟩ := hused
    have hxhull := B.refined_vertex_mem_face_hull p (lines p) u x hx
    have hcarrier : B.coordinates (collarParameterEquiv.symm (t, 0)) ∈ (B.face p).carrier := by
      rw [B.face_carrier_eq_coordinates]
      exact ⟨_, hxhull, hpoint⟩
    have hp := (B.lower_axis_mem_face_carrier_iff i ht hio p).mp hcarrier
    subst p
    have hxaxis := B.face_preimage_lower_axis (i, false) ht hxhull hpoint
    have hfan := single_refineByLines_open_edge_vertex_fan g (B.faceCoordinates (i, false))
      (B.faceBasis (i, false)) (lines (i, false)) 2
      (B.smooth_faceCoordinates hF (i, false)) (B.smooth_faceCoordinates_symm hFi (i, false))
      (B.face_triangle_subset_source (i, false)) u x hx
      (by rw [hxaxis]; exact B.lower_axis_mem_open_edge i hio)
    rw [hpoint] at hfan
    calc
      _ = meshVertexAngleContribution g (B.faceCoordinates (i, false))
          ((TriangleMesh.single (B.faceBasis (i, false))
            (B.faceBasis (i, false)).ind).refineByLines (lines (i, false)))
          (B.coordinates (collarParameterEquiv.symm (t, 0))) := by
        apply Finset.sum_eq_single (i, false)
        · intro p _ hp
          exact B.refined_contribution_eq_zero_of_not_mem_carrier g p (lines p)
            ((B.lower_axis_mem_face_carrier_iff i ht hio p).not.mpr hp)
        · simp
      _ = Real.pi := hfan



theorem lower_arc_refined_vertex_fan (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (lines : (Fin B.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ))
    {q : S} (hq : q ∈ B.lowerArc)
    (hq0 : q ≠ B.vertex (0, false))
    (hq1 : q ≠ B.vertex (Fin.last B.interface.count, false))
    (hused : ∃ (p : Fin B.interface.count × Bool)
      (u : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).Triangle)
      (x : ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).Vertex),
      x ∈ u.1 ∧ B.faceCoordinates p
        (((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)).position x) = q) :
    (∑ p : Fin B.interface.count × Bool,
      meshVertexAngleContribution g (B.faceCoordinates p)
        ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p)) q) =
      Real.pi := by
  obtain ⟨x, hx, hxq⟩ := hq
  have hab : a < b := by
    simpa only [B.cuts.A_zero, B.cuts.B_zero] using B.cuts.separated 0
      (show (0 : ℝ) ∈ Ioo (-B.cuts.radius) B.cuts.radius from
        ⟨by linarith [B.cuts.radius_pos], B.cuts.radius_pos⟩)
  let t := (x - a) / (b - a)
  have htcc : t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hab).le,
      (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right hx.2 a)⟩
  have htval : a + t * (b - a) = x := by
    dsimp only [t]
    rw [div_mul_cancel₀ _ (sub_pos.mpr hab).ne']
    ring
  have hpoint : B.coordinates (collarParameterEquiv.symm (t, 0)) = q := by
    rw [B.coordinates_bottom, htval]
    exact hxq
  have ht0 : t ≠ 0 := by
    intro heq
    apply hq0
    rw [← hpoint, heq]
    simp [vertex, B.cut_first]
  have ht1 : t ≠ 1 := by
    intro heq
    apply hq1
    rw [← hpoint, heq]
    simp [vertex, B.cut_last]
  have ht : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne htcc.1 ht0.symm, lt_of_le_of_ne htcc.2 ht1⟩
  rw [← hpoint] at hused ⊢
  exact B.lower_axis_refined_vertex_fan g hF hFi lines ht hused

end PoincareConjecture.Topology.Surface.ObliqueBandFaces
