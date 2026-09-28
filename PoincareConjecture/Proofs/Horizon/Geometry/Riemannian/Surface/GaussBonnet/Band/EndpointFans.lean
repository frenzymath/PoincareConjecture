import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.RefinedFans









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Classical
open scoped Manifold ContDiff Bundle Matrix
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.ObliqueBandFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {F : OpenPartialHomeomorph Plane S}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

private theorem lastCell_succ : B.lastCell.succ = Fin.last B.interface.count := by
  apply Fin.ext
  have hn := B.interface.count_pos
  simp only [lastCell, Fin.val_succ, Fin.val_last]
  omega



theorem sum_corner_weights_first
    (w : (Fin B.interface.count × Bool) → Fin 3 → ℝ) (top : Bool) :
    (∑ p : Fin B.interface.count × Bool, ∑ k : Fin 3,
      if B.faceCoordinates p (B.faceBasis p k) = B.vertex (0, top)
      then w p k else 0) =
      if top then w (B.firstCell, true) 1
      else w (B.firstCell, false) 0 + w (B.firstCell, true) 0 := by
  have hstart (m : Fin B.interface.count) : m.castSucc = 0 ↔ m = B.firstCell := by
    change m.castSucc = B.firstCell.castSucc ↔ m = B.firstCell
    exact Fin.castSucc_inj
  simp_rw [B.face_corner_eq_vertex_iff]
  cases top <;>
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, cornerVertexIndex,
      Fin.reduceEq, if_true, if_false, Bool.false_eq_true, Prod.mk.injEq,
      and_true, and_false, Bool.true_eq_false, hstart, Fin.succ_ne_zero,
      add_zero, zero_add, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, Finset.sum_const_zero]
  ring


theorem sum_corner_weights_last
    (w : (Fin B.interface.count × Bool) → Fin 3 → ℝ) (top : Bool) :
    (∑ p : Fin B.interface.count × Bool, ∑ k : Fin 3,
      if B.faceCoordinates p (B.faceBasis p k) = B.vertex (Fin.last B.interface.count, top)
      then w p k else 0) =
      if top then w (B.lastCell, false) 2 + w (B.lastCell, true) 2
      else w (B.lastCell, false) 1 := by
  have hend (m : Fin B.interface.count) :
      m.succ = Fin.last B.interface.count ↔ m = B.lastCell := by
    rw [← B.lastCell_succ]
    exact Fin.succ_inj
  simp_rw [B.face_corner_eq_vertex_iff]
  cases top <;>
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_three, cornerVertexIndex,
      Fin.reduceEq, if_true, if_false, Bool.false_eq_true, Prod.mk.injEq,
      and_true, and_false, Bool.true_eq_false, hend, Fin.castSucc_ne_last,
      add_zero, zero_add, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, Finset.sum_const_zero]
  ring


theorem cell_bottom_corner_sum (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target) (i : Fin B.interface.count) :
    coordinateTriangleAngle g (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 0 +
      coordinateTriangleAngle g (B.faceCoordinates (i, true)) (B.faceBasis (i, true)) 0 =
      g.cornerAngle (B.faceCoordinates (i, false) (B.faceBasis (i, false) 0))
        (coordinateTriangleVelocity (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 0 1)
        (coordinateTriangleVelocity (B.faceCoordinates (i, true)) (B.faceBasis (i, true)) 0 1) :=
  (B.pair i).cornerAngle_split_zero
    (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).parameter.open_target
    contDiffOn_const
    ((B.interface.pieceCoordinates B.open_domain B.smooth_lower i).smooth_upperGraph B.smooth_lower)
    (smooth_obliqueSurfaceCoordinates F hF B.cuts B.open_domain B.smooth_lower)
    (smooth_obliqueSurfaceCoordinates_symm F hFi B.cuts B.open_domain B.smooth_lower)
    (fun _ ht => (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).parameter_mem_target ht) g



theorem cell_top_corner_sum (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target) (i : Fin B.interface.count) :
    coordinateTriangleAngle g (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 2 +
      coordinateTriangleAngle g (B.faceCoordinates (i, true)) (B.faceBasis (i, true)) 2 =
      g.cornerAngle (B.faceCoordinates (i, false) (B.faceBasis (i, false) 2))
        (coordinateTriangleVelocity (B.faceCoordinates (i, true)) (B.faceBasis (i, true)) 2 1)
        (coordinateTriangleVelocity (B.faceCoordinates (i, false)) (B.faceBasis (i, false)) 2 1) := by
  rw [g.cornerAngle_comm]
  exact (B.pair i).cornerAngle_split_two
    (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).parameter.open_target
    contDiffOn_const
    ((B.interface.pieceCoordinates B.open_domain B.smooth_lower i).smooth_upperGraph B.smooth_lower)
    (smooth_obliqueSurfaceCoordinates F hF B.cuts B.open_domain B.smooth_lower)
    (smooth_obliqueSurfaceCoordinates_symm F hFi B.cuts B.open_domain B.smooth_lower)
    (fun _ ht => (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).parameter_mem_target ht) g



theorem first_bottom_refined_vertex_fan (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (lines : (Fin B.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ p : Fin B.interface.count × Bool,
      meshVertexAngleContribution g (B.faceCoordinates p)
        ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p))
        (B.vertex (0, false))) =
      g.cornerAngle (B.vertex (0, false))
        (coordinateTriangleVelocity (B.faceCoordinates (B.firstCell, false))
          (B.faceBasis (B.firstCell, false)) 0 1)
        (coordinateTriangleVelocity (B.faceCoordinates (B.firstCell, true))
          (B.faceBasis (B.firstCell, true)) 0 1) := by
  rw [B.sum_refined_vertex_contributions g hF hFi lines, B.sum_corner_weights_first]
  have h := B.cell_bottom_corner_sum g hF hFi B.firstCell
  rw [B.face_corner_eq_vertex] at h
  simpa [cornerVertexIndex, firstCell] using h



theorem last_bottom_refined_vertex_fan (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (lines : (Fin B.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ p : Fin B.interface.count × Bool,
      meshVertexAngleContribution g (B.faceCoordinates p)
        ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p))
        (B.vertex (Fin.last B.interface.count, false))) =
      g.cornerAngle (B.vertex (Fin.last B.interface.count, false))
        (coordinateTriangleVelocity (B.faceCoordinates (B.lastCell, false))
          (B.faceBasis (B.lastCell, false)) 1 0)
        (coordinateTriangleVelocity (B.faceCoordinates (B.lastCell, false))
          (B.faceBasis (B.lastCell, false)) 1 2) := by
  rw [B.sum_refined_vertex_contributions g hF hFi lines, B.sum_corner_weights_last]
  change g.cornerAngle (B.faceCoordinates (B.lastCell, false) (B.faceBasis (B.lastCell, false) 1))
      (coordinateTriangleVelocity _ _ 1 0) (coordinateTriangleVelocity _ _ 1 2) = _
  have hp : B.faceCoordinates (B.lastCell, false) (B.faceBasis (B.lastCell, false) 1) =
      B.vertex (Fin.last B.interface.count, false) := by
    rw [B.face_corner_eq_vertex]
    change B.vertex (B.lastCell.succ, false) = _
    rw [B.lastCell_succ]
  rw [hp]



theorem first_top_refined_vertex_fan (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (lines : (Fin B.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ p : Fin B.interface.count × Bool,
      meshVertexAngleContribution g (B.faceCoordinates p)
        ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p))
        (B.vertex (0, true))) =
      g.cornerAngle (B.vertex (0, true))
        (coordinateTriangleVelocity (B.faceCoordinates (B.firstCell, true))
          (B.faceBasis (B.firstCell, true)) 1 2)
        (coordinateTriangleVelocity (B.faceCoordinates (B.firstCell, true))
          (B.faceBasis (B.firstCell, true)) 1 0) := by
  rw [B.sum_refined_vertex_contributions g hF hFi lines, B.sum_corner_weights_first]
  change g.cornerAngle (B.faceCoordinates (B.firstCell, true) (B.faceBasis (B.firstCell, true) 1))
      (coordinateTriangleVelocity _ _ 1 0) (coordinateTriangleVelocity _ _ 1 2) = _
  have hp : B.faceCoordinates (B.firstCell, true) (B.faceBasis (B.firstCell, true) 1) =
      B.vertex (0, true) := by
    rw [B.face_corner_eq_vertex]
    rfl
  rw [hp]
  exact g.cornerAngle_comm _ _ _



theorem last_top_refined_vertex_fan (g : RiemannianMetric 2 S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (lines : (Fin B.interface.count × Bool) → List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ p : Fin B.interface.count × Bool,
      meshVertexAngleContribution g (B.faceCoordinates p)
        ((TriangleMesh.single (B.faceBasis p) (B.faceBasis p).ind).refineByLines (lines p))
        (B.vertex (Fin.last B.interface.count, true))) =
      g.cornerAngle (B.vertex (Fin.last B.interface.count, true))
        (coordinateTriangleVelocity (B.faceCoordinates (B.lastCell, true))
          (B.faceBasis (B.lastCell, true)) 2 1)
        (coordinateTriangleVelocity (B.faceCoordinates (B.lastCell, false))
          (B.faceBasis (B.lastCell, false)) 2 1) := by
  rw [B.sum_refined_vertex_contributions g hF hFi lines, B.sum_corner_weights_last]
  have h := B.cell_top_corner_sum g hF hFi B.lastCell
  have hp : B.faceCoordinates (B.lastCell, false) (B.faceBasis (B.lastCell, false) 2) =
      B.vertex (Fin.last B.interface.count, true) := by
    rw [B.face_corner_eq_vertex]
    change B.vertex (B.lastCell.succ, true) = _
    rw [B.lastCell_succ]
  rw [hp] at h
  exact h

end PoincareConjecture.Topology.Surface.ObliqueBandFaces
