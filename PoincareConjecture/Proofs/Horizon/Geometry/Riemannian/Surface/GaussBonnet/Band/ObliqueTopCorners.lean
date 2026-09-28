import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.ObliqueFans

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Classical
open scoped Manifold ContDiff Bundle Matrix
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.ObliqueBandFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

private theorem right_cut_map (i : Fin B.interface.count) (t : ℝ) :
    B.faceCoordinates (i, false)
      (AffineMap.lineMap (B.faceBasis (i, false) 1) (B.faceBasis (i, false) 2) t) =
      B.coordinates (collarParameterEquiv.symm
        (B.cut i.succ, t * B.interface.height i.succ)) := by
  have h := (B.pair i).right_chart_map
    (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).parameter.open_target
    contDiffOn_const
    ((B.interface.pieceCoordinates B.open_domain B.smooth_lower i).smooth_upperGraph
      B.smooth_lower) t
  rw [coordinateTriangle_chord_map, (B.pair i).right_edge] at h
  change B.faceCoordinates (i, false)
      (AffineMap.lineMap (B.faceBasis (i, false) 1) (B.faceBasis (i, false) 2) t) =
    B.coordinates (collarParameterEquiv.symm
      (B.cut i.succ, 0 + t * (B.upperGraph i (B.cut i.succ) - 0))) at h
  simpa only [sub_zero, zero_add, (B.upperGraph_endpoints i).2] using h

private theorem left_cut_map (i : Fin B.interface.count) (t : ℝ) :
    B.faceCoordinates (i, true)
      (AffineMap.lineMap (B.faceBasis (i, true) 0) (B.faceBasis (i, true) 1) t) =
      B.coordinates (collarParameterEquiv.symm
        (B.cut i.castSucc, t * B.interface.height i.castSucc)) := by
  have h := (B.pair i).left_chart_map
    (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).parameter.open_target
    contDiffOn_const
    ((B.interface.pieceCoordinates B.open_domain B.smooth_lower i).smooth_upperGraph
      B.smooth_lower) t
  rw [coordinateTriangle_first_map, (B.pair i).left_edge] at h
  change B.faceCoordinates (i, true)
      (AffineMap.lineMap (B.faceBasis (i, true) 0) (B.faceBasis (i, true) 1) t) =
    B.coordinates (collarParameterEquiv.symm
      (B.cut i.castSucc, 0 + t * (B.upperGraph i (B.cut i.castSucc) - 0))) at h
  simpa only [sub_zero, zero_add, (B.upperGraph_endpoints i).1] using h

theorem adjacent_top_vertices
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    B.faceCoordinates (i, false) (B.faceBasis (i, false) 2) = B.vertex (i.succ, true) ∧
      B.faceCoordinates (i, true) (B.faceBasis (i, true) 2) = B.vertex (i.succ, true) ∧
      B.faceCoordinates (j, true) (B.faceBasis (j, true) 1) = B.vertex (i.succ, true) := by
  simp [B.face_corner_eq_vertex, cornerVertexIndex, hij]

theorem adjacent_top_downward_velocity
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    coordinateTriangleVelocity (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 2 1 =
      coordinateTriangleVelocity (B.faceCoordinates (j, true)) (B.faceBasis (j, true)) 1 0 := by
  have hmap (t : ℝ) :
      B.faceCoordinates (i, false)
        (AffineMap.lineMap (B.faceBasis (i, false) 2) (B.faceBasis (i, false) 1) t) =
      B.faceCoordinates (j, true)
        (AffineMap.lineMap (B.faceBasis (j, true) 1) (B.faceBasis (j, true) 0) t) := by
    rw [← AffineMap.lineMap_apply_one_sub, B.right_cut_map,
      ← AffineMap.lineMap_apply_one_sub, B.left_cut_map, hij]
  unfold coordinateTriangleVelocity
  rw [funext hmap]
  rfl

noncomputable def topOutwardRay (i : Fin B.interface.count) :
    TangentSpace (𝓡 2) (B.vertex (i.succ, true)) :=
  -coordinateTriangleVelocity (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 2 1

noncomputable def topLeftChord (i : Fin B.interface.count) :
    TangentSpace (𝓡 2) (B.vertex (i.succ, true)) :=
  coordinateTriangleVelocity (B.faceCoordinates (i, true)) (B.faceBasis (i, true)) 2 1

noncomputable def topRightChord (j : Fin B.interface.count) :
    TangentSpace (𝓡 2) (B.vertex (j.castSucc, true)) :=
  coordinateTriangleVelocity (B.faceCoordinates (j, true)) (B.faceBasis (j, true)) 1 2

theorem topOutwardRay_ne_zero
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target) (i : Fin B.interface.count) :
    B.topOutwardRay i ≠ 0 := by
  exact neg_ne_zero.mpr (coordinateTriangleVelocity_ne_zero
    (B.faceCoordinates (i, false)) (B.faceBasis (i, false))
    (B.smooth_faceCoordinates hF (i, false)) (B.smooth_faceCoordinates_symm hFi (i, false))
    (B.face_triangle_subset_source (i, false)) (i := 2) (j := 1) (by decide))

theorem topOutwardRay_eq_cut_velocity
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source) (i : Fin B.interface.count) :
    B.topOutwardRay i = mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
      (fun t : ℝ => B.coordinates (collarParameterEquiv.symm
        (B.cut i.succ, t * B.interface.height i.succ))) 1 1 := by
  let γ := fun t : ℝ => B.faceCoordinates (i, false)
    (AffineMap.lineMap (B.faceBasis (i, false) 1) (B.faceBasis (i, false) 2) t)
  have hsource : AffineMap.lineMap (B.faceBasis (i, false) 1)
      (B.faceBasis (i, false) 2) (1 : ℝ) ∈ (B.faceCoordinates (i, false)).source := by
    simpa using B.face_triangle_subset_source (i, false)
      (subset_convexHull ℝ _ (mem_range_self 2))
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ 1 :=
    (((B.smooth_faceCoordinates hF (i, false)).contMDiffAt
      ((B.faceCoordinates (i, false)).open_source.mem_nhds hsource)).comp 1
      (AffineMap.contDiff_lineMap _ _).contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hφ : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
  have h := LeviCivitaData.mfderiv_curve_reparam (φ := fun t : ℝ => 1 - t)
    (by simpa using hγ) hφ
  have hcurve : γ ∘ (fun t : ℝ => 1 - t) = fun t : ℝ =>
      B.faceCoordinates (i, false)
        (AffineMap.lineMap (B.faceBasis (i, false) 2) (B.faceBasis (i, false) 1) t) := by
    funext t
    exact congrArg (B.faceCoordinates (i, false)) (AffineMap.lineMap_apply_one_sub _ _ t)
  dsimp only [TangentSpace] at h ⊢
  rw [hcurve] at h
  simp only [neg_smul, one_smul] at h
  have hpoint := congrArg (fun t : ℝ =>
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1 : EuclideanSpace ℝ (Fin 2))) (sub_zero (1 : ℝ))
  have h' := h.trans (congrArg Neg.neg hpoint)
  change -coordinateTriangleVelocity (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 2 1 = _
  change coordinateTriangleVelocity (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 2 1 =
    -mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ 1 1 at h'
  rw [h', neg_neg]
  exact congrArg (fun f : ℝ → S =>
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) f 1 1 : EuclideanSpace ℝ (Fin 2))) (funext (B.right_cut_map i))

theorem internal_top_corner_fan (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    coordinateTriangleAngle g (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 2 +
      coordinateTriangleAngle g (B.faceCoordinates (i, true)) (B.faceBasis (i, true)) 2 +
      coordinateTriangleAngle g (B.faceCoordinates (j, true)) (B.faceBasis (j, true)) 1 +
      g.cornerAngle (B.vertex (i.succ, true)) (B.topOutwardRay i) (B.topLeftChord i) +
      g.cornerAngle (B.vertex (i.succ, true)) (B.topOutwardRay i) (B.topRightChord j) =
      2 * Real.pi := by
  have hsplit := (B.pair i).cornerAngle_split_two
    (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).parameter.open_target
    contDiffOn_const
    ((B.interface.pieceCoordinates B.open_domain B.smooth_lower i).smooth_upperGraph B.smooth_lower)
    (smooth_obliqueSurfaceCoordinates F hF B.cuts B.open_domain B.smooth_lower)
    (smooth_obliqueSurfaceCoordinates_symm F hFi B.cuts B.open_domain B.smooth_lower)
    (fun _ ht => (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).parameter_mem_target ht) g
  change coordinateTriangleAngle g (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 2 +
      coordinateTriangleAngle g (B.faceCoordinates (i, true)) (B.faceBasis (i, true)) 2 =
    g.cornerAngle (B.faceCoordinates (i, false) (B.faceBasis (i, false) 2))
      (coordinateTriangleVelocity (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 2 1)
      (coordinateTriangleVelocity (B.faceCoordinates (i, true)) (B.faceBasis (i, true)) 2 1) at hsplit
  rw [hsplit]
  change _ + g.cornerAngle (B.faceCoordinates (j, true) (B.faceBasis (j, true) 1))
      (coordinateTriangleVelocity (B.faceCoordinates (j, true)) (B.faceBasis (j, true)) 1 0)
      (coordinateTriangleVelocity (B.faceCoordinates (j, true)) (B.faceBasis (j, true)) 1 2) + _ + _ = _
  dsimp only [topOutwardRay, topLeftChord, topRightChord, TangentSpace]
  rw [(B.adjacent_top_vertices i j hij).1, (B.adjacent_top_vertices i j hij).2.2,
    ← B.adjacent_top_downward_velocity i j hij, g.cornerAngle_neg_left, g.cornerAngle_neg_left]
  ring

theorem sum_corner_weights_internal_top
    (w : (Fin B.interface.count × Bool) → Fin 3 → ℝ)
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    (∑ p : Fin B.interface.count × Bool, ∑ k : Fin 3,
      if B.faceCoordinates p (B.faceBasis p k) = B.vertex (i.succ, true)
      then w p k else 0) = w (i, false) 2 + w (i, true) 2 + w (j, true) 1 := by
  have hstart (m : Fin B.interface.count) : m.castSucc = i.succ ↔ m = j := by
    rw [hij]
    exact Fin.castSucc_inj
  simp_rw [B.face_corner_eq_vertex_iff]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, cornerVertexIndex]
  simp only [Fin.reduceEq, if_true, if_false, Bool.false_eq_true, Prod.mk.injEq,
    and_true, and_false, hstart, Fin.succ_inj, add_zero, zero_add]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem internal_top_vertex_fan (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    (∑ p : Fin B.interface.count × Bool, ∑ k : Fin 3,
      if B.faceCoordinates p (B.faceBasis p k) = B.vertex (i.succ, true)
      then coordinateTriangleAngle g (B.faceCoordinates p) (B.faceBasis p) k else 0) +
      g.cornerAngle (B.vertex (i.succ, true)) (B.topOutwardRay i) (B.topLeftChord i) +
      g.cornerAngle (B.vertex (i.succ, true)) (B.topOutwardRay i) (B.topRightChord j) =
      2 * Real.pi := by
  rw [B.sum_corner_weights_internal_top
    (fun p k => coordinateTriangleAngle g (B.faceCoordinates p) (B.faceBasis p) k) i j hij]
  exact B.internal_top_corner_fan g hF hFi i j hij

end PoincareConjecture.Topology.Surface.ObliqueBandFaces
