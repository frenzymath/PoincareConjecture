import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.Corners
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.Boundary








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set VectorField
open scoped Manifold ContDiff Bundle Matrix
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.ObliqueBandFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)
  (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
  (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)

private theorem bottom_map (i : Fin B.interface.count) (t : ℝ) :
    B.faceCoordinates (i, false)
      (AffineMap.lineMap (B.faceBasis (i, false) 0) (B.faceBasis (i, false) 1) t) =
      B.coordinates (collarParameterEquiv.symm
        (B.cut i.castSucc + t * (B.cut i.succ - B.cut i.castSucc), 0)) := by
  have h := (B.pair i).lower_chart_map
    (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).parameter.open_target
    contDiffOn_const
    ((B.interface.pieceCoordinates B.open_domain B.smooth_lower i).smooth_upperGraph
      B.smooth_lower) t
  rw [coordinateTriangle_first_map, (B.pair i).lower_edge] at h
  exact h

private theorem left_map (i : Fin B.interface.count) (t : ℝ) :
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

private theorem right_map (i : Fin B.interface.count) (t : ℝ) :
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

private theorem bottom_source (i : Fin B.interface.count) {t : ℝ}
    (ht : t ∈ Icc (B.cut i.castSucc) (B.cut i.succ)) :
    collarParameterEquiv.symm (t, 0) ∈ B.coordinates.source := by
  apply (B.pair i).band_subset_source
  change (collarParameterEquiv (collarParameterEquiv.symm (t, 0))).1 ∈
      Icc (B.cut i.castSucc) (B.cut i.succ) ∧
    0 ≤ (collarParameterEquiv (collarParameterEquiv.symm (t, 0))).2 ∧
    (collarParameterEquiv (collarParameterEquiv.symm (t, 0))).2 ≤ B.upperGraph i
      (collarParameterEquiv (collarParameterEquiv.symm (t, 0))).1
  simpa only [collarParameterEquiv.apply_symm_apply] using
    And.intro ht (And.intro (le_refl (0 : ℝ)) ((B.pair i).gap t ht).le)

include hF in
private theorem bottom_smooth (i : Fin B.interface.count) {t : ℝ}
    (ht : t ∈ Icc (B.cut i.castSucc) (B.cut i.succ)) :
    MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2)
      (fun s : ℝ => B.coordinates (collarParameterEquiv.symm (s, 0))) t := by
  have hC := smooth_obliqueSurfaceCoordinates F hF B.cuts B.open_domain B.smooth_lower
  have hline : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞
      (fun s : ℝ => collarParameterEquiv.symm (s, 0)) t :=
    (collarParameterEquiv.symm.contDiff.comp (contDiff_id.prodMk contDiff_const)).contDiffAt.contMDiffAt
  exact ((hC.contMDiffAt (B.coordinates.open_source.mem_nhds (B.bottom_source i ht))).comp t
    hline).mdifferentiableAt (by simp)

include hF in
private theorem bottom_velocity_zero (i : Fin B.interface.count) :
    coordinateTriangleVelocity (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 0 1 =
      (B.cut i.succ - B.cut i.castSucc) •
        mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
          (fun s : ℝ => B.coordinates (collarParameterEquiv.symm (s, 0))) (B.cut i.castSucc) 1 := by
  let φ := fun t : ℝ => B.cut i.castSucc + t * (B.cut i.succ - B.cut i.castSucc)
  have hφ : HasDerivAt φ (B.cut i.succ - B.cut i.castSucc) 0 := by
    simpa only [φ, id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const
      (B.cut i.succ - B.cut i.castSucc)).const_add (B.cut i.castSucc)
  have hγ := B.bottom_smooth hF i (left_mem_Icc.mpr (B.cut_strictMono Fin.castSucc_lt_succ).le)
  have hγ' : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2)
      (fun s : ℝ => B.coordinates (collarParameterEquiv.symm (s, 0))) (φ 0) := by
    simpa only [φ, zero_mul, add_zero] using hγ
  unfold coordinateTriangleVelocity
  rw [funext (B.bottom_map i)]
  have h := LeviCivitaData.mfderiv_curve_reparam hγ' hφ
  dsimp only [TangentSpace] at h ⊢
  rw [show φ 0 = B.cut i.castSucc by simp [φ]] at h
  exact h

include hF in
private theorem bottom_velocity_one (i : Fin B.interface.count) :
    coordinateTriangleVelocity (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 1 0 =
      (B.cut i.castSucc - B.cut i.succ) •
        mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
          (fun s : ℝ => B.coordinates (collarParameterEquiv.symm (s, 0))) (B.cut i.succ) 1 := by
  let φ := fun t : ℝ => B.cut i.succ + t * (B.cut i.castSucc - B.cut i.succ)
  have hφ : HasDerivAt φ (B.cut i.castSucc - B.cut i.succ) 0 := by
    simpa only [φ, id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const
      (B.cut i.castSucc - B.cut i.succ)).const_add (B.cut i.succ)
  have hγ := B.bottom_smooth hF i (right_mem_Icc.mpr (B.cut_strictMono Fin.castSucc_lt_succ).le)
  have hγ' : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2)
      (fun s : ℝ => B.coordinates (collarParameterEquiv.symm (s, 0))) (φ 0) := by
    simpa only [φ, zero_mul, add_zero] using hγ
  have hmap (t : ℝ) : B.faceCoordinates (i, false)
      (AffineMap.lineMap (B.faceBasis (i, false) 1) (B.faceBasis (i, false) 0) t) =
      B.coordinates (collarParameterEquiv.symm (φ t, 0)) := by
    rw [← AffineMap.lineMap_apply_one_sub, B.bottom_map]
    congr 3
    dsimp only [φ]
    ring
  unfold coordinateTriangleVelocity
  rw [funext hmap]
  have h := LeviCivitaData.mfderiv_curve_reparam hγ' hφ
  dsimp only [TangentSpace] at h ⊢
  rw [show φ 0 = B.cut i.succ by simp [φ]] at h
  exact h



theorem adjacent_bottom_upward_velocity
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    coordinateTriangleVelocity (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 1 2 =
      coordinateTriangleVelocity (B.faceCoordinates (j, true)) (B.faceBasis (j, true)) 0 1 := by
  unfold coordinateTriangleVelocity
  rw [funext (B.right_map i), funext (B.left_map j), hij]
  rfl



theorem adjacent_bottom_vertices
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    B.faceCoordinates (i, false) (B.faceBasis (i, false) 1) = B.vertex (i.succ, false) ∧
      B.faceCoordinates (j, false) (B.faceBasis (j, false) 0) = B.vertex (i.succ, false) ∧
      B.faceCoordinates (j, true) (B.faceBasis (j, true) 0) = B.vertex (i.succ, false) := by
  have hi : B.faceCoordinates (i, false) (B.faceBasis (i, false) 1) =
      B.vertex (i.succ, false) := by
    simpa only [vertex, Bool.false_eq_true, if_false, AffineMap.lineMap_apply_one,
      one_mul, add_sub_cancel] using B.bottom_map i 1
  have hj : B.faceCoordinates (j, false) (B.faceBasis (j, false) 0) =
      B.vertex (i.succ, false) := by
    simpa only [vertex, Bool.false_eq_true, if_false, AffineMap.lineMap_apply_zero,
      zero_mul, add_zero, hij] using B.bottom_map j 0
  exact ⟨hi, hj, hj⟩

include hF hFi in


theorem internal_bottom_corner_fan (g : RiemannianMetric 2 S)
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    coordinateTriangleAngle g (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 1 +
      coordinateTriangleAngle g (B.faceCoordinates (j, false)) (B.faceBasis (j, false)) 0 +
      coordinateTriangleAngle g (B.faceCoordinates (j, true)) (B.faceBasis (j, true)) 0 =
      Real.pi := by
  have hsplit := (B.pair j).cornerAngle_split_zero
    (B.interface.pieceCoordinates B.open_domain B.smooth_lower j).parameter.open_target
    contDiffOn_const
    ((B.interface.pieceCoordinates B.open_domain B.smooth_lower j).smooth_upperGraph B.smooth_lower)
    (smooth_obliqueSurfaceCoordinates F hF B.cuts B.open_domain B.smooth_lower)
    (smooth_obliqueSurfaceCoordinates_symm F hFi B.cuts B.open_domain B.smooth_lower)
    (fun _ ht => (B.interface.pieceCoordinates B.open_domain B.smooth_lower j).parameter_mem_target ht) g
  change coordinateTriangleAngle g (B.faceCoordinates (j, false)) (B.faceBasis (j, false)) 0 +
      coordinateTriangleAngle g (B.faceCoordinates (j, true)) (B.faceBasis (j, true)) 0 =
    g.cornerAngle (B.faceCoordinates (j, false) (B.faceBasis (j, false) 0))
      (coordinateTriangleVelocity (B.faceCoordinates (j, false)) (B.faceBasis (j, false)) 0 1)
      (coordinateTriangleVelocity (B.faceCoordinates (j, true)) (B.faceBasis (j, true)) 0 1) at hsplit
  have hp (k : Fin B.interface.count) :
      B.faceCoordinates (k, false) (B.faceBasis (k, false) 0) =
        B.coordinates (collarParameterEquiv.symm (B.cut k.castSucc, 0)) := by
    simpa only [AffineMap.lineMap_apply_zero, zero_mul, add_zero] using B.bottom_map k 0
  have hq : B.faceCoordinates (i, false) (B.faceBasis (i, false) 1) =
      B.coordinates (collarParameterEquiv.symm (B.cut i.succ, 0)) := by
    simpa only [AffineMap.lineMap_apply_one, one_mul, add_sub_cancel] using B.bottom_map i 1
  have hposi : 0 < B.cut i.succ - B.cut i.castSucc := sub_pos.mpr (B.cut_strictMono Fin.castSucc_lt_succ)
  have hposj : 0 < B.cut j.succ - B.cut j.castSucc := sub_pos.mpr (B.cut_strictMono Fin.castSucc_lt_succ)
  rw [add_assoc, hsplit]
  change g.cornerAngle _
      (coordinateTriangleVelocity (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 1 0)
      (coordinateTriangleVelocity (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 1 2) + _ = _
  rw [B.bottom_velocity_one hF, B.bottom_velocity_zero hF, B.adjacent_bottom_upward_velocity i j hij,
    hq, hij]
  rw [hp j]
  rw [show B.cut i.castSucc - B.cut j.castSucc = -(B.cut i.succ - B.cut i.castSucc) by rw [hij]; ring]
  rw [neg_smul, ← smul_neg, g.cornerAngle_smul_pos_left _ _ _ hposi,
    g.cornerAngle_smul_pos_left _ _ _ hposj, g.cornerAngle_neg_left]
  ring

end PoincareConjecture.Topology.Surface.ObliqueBandFaces
