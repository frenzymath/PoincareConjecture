import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.OriginalCorners

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)

noncomputable def firstOuterTip (i : Bool) : S :=
  B.coordinates (i, true) (rightTriangleBasis B.scale_pos 1)

noncomputable def secondOuterTip (i : Bool) : S :=
  B.coordinates (true, i) (rightTriangleBasis B.scale_pos 2)

private theorem boundary_reversed_map (i : Bool × Bool) (k : Fin 3) (t : ℝ) :
    ((B.face i).boundary k).map (1 - t) =
      B.coordinates i (AffineMap.lineMap (rightTriangleBasis B.scale_pos (k.succAbove 1))
        (rightTriangleBasis B.scale_pos (k.succAbove 0)) t) := by
  rw [B.boundary_map]
  change B.coordinates i (affineChartSegment _ _ (1 - t)) = _
  rw [← AffineMap.lineMap_apply_one_sub]
  congr 1
  simp only [affineChartSegment, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]

private theorem reversed_radial_velocity_eq {i j : Bool × Bool} (k : Fin 3)
    (h : EqOn ((B.face i).boundary k).map ((B.face j).boundary k).map (Icc (0 : ℝ) 1)) :
    coordinateTriangleVelocity (B.coordinates i) (rightTriangleBasis B.scale_pos)
        (k.succAbove 1) (k.succAbove 0) =
      coordinateTriangleVelocity (B.coordinates j) (rightTriangleBasis B.scale_pos)
        (k.succAbove 1) (k.succAbove 0) := by
  rw [coordinateTriangleVelocity_eq_mfderivWithin _ _ (B.coordinates_smooth i)
    (B.triangle_subset_source i),
    coordinateTriangleVelocity_eq_mfderivWithin _ _ (B.coordinates_smooth j)
      (B.triangle_subset_source j)]
  apply congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) => L 1)
  apply mfderivWithin_congr_of_mem
  · intro t ht
    rw [← B.boundary_reversed_map, ← B.boundary_reversed_map]
    exact h ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · simp

theorem coordinate_first_outer_tip (i : Bool) (j : Bool) :
    B.coordinates (i, j) (rightTriangleBasis B.scale_pos 1) = B.firstOuterTip i := by
  have h := B.first_boundary_agreement (i := (i, j)) (j := (i, true)) rfl
    (show (1 : ℝ) ∈ Icc 0 1 by simp)
  rw [B.boundary_map, B.boundary_map] at h
  simpa [affineChartSegment, firstOuterTip, Fin.succAbove, Fin.lt_def] using h

theorem coordinate_second_outer_tip (i : Bool) (j : Bool) :
    B.coordinates (j, i) (rightTriangleBasis B.scale_pos 2) = B.secondOuterTip i := by
  have h := B.second_boundary_agreement (i := (j, i)) (j := (true, i)) rfl
    (show (1 : ℝ) ∈ Icc 0 1 by simp)
  rw [B.boundary_map, B.boundary_map] at h
  simpa [affineChartSegment, secondOuterTip] using h

theorem first_outer_inward_velocity_eq (i : Bool) (j : Bool) :
    coordinateTriangleVelocity (B.coordinates (i, j)) (rightTriangleBasis B.scale_pos) 1 0 =
      coordinateTriangleVelocity (B.coordinates (i, true)) (rightTriangleBasis B.scale_pos) 1 0 :=
  B.reversed_radial_velocity_eq 2 (B.first_boundary_agreement rfl)

theorem second_outer_inward_velocity_eq (i : Bool) (j : Bool) :
    coordinateTriangleVelocity (B.coordinates (j, i)) (rightTriangleBasis B.scale_pos) 2 0 =
      coordinateTriangleVelocity (B.coordinates (true, i)) (rightTriangleBasis B.scale_pos) 2 0 :=
  B.reversed_radial_velocity_eq 1 (B.second_boundary_agreement rfl)

noncomputable def firstOuterSpoke (i : Bool) : TangentSpace (𝓡 2) (B.firstOuterTip i) :=
  -coordinateTriangleVelocity (B.coordinates (i, true)) (rightTriangleBasis B.scale_pos) 1 0

noncomputable def secondOuterSpoke (i : Bool) : TangentSpace (𝓡 2) (B.secondOuterTip i) :=
  -coordinateTriangleVelocity (B.coordinates (true, i)) (rightTriangleBasis B.scale_pos) 2 0

noncomputable def firstOuterChord (i j : Bool) : TangentSpace (𝓡 2) (B.firstOuterTip i) :=
  coordinateTriangleVelocity (B.coordinates (i, j)) (rightTriangleBasis B.scale_pos) 1 2

noncomputable def secondOuterChord (i j : Bool) : TangentSpace (𝓡 2) (B.secondOuterTip i) :=
  coordinateTriangleVelocity (B.coordinates (j, i)) (rightTriangleBasis B.scale_pos) 2 1

private theorem reverse_velocity_eq_neg_endpoint (i : Bool × Bool) (k : Fin 3)
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) ((B.face i).boundary k).map 1) :
    coordinateTriangleVelocity (B.coordinates i) (rightTriangleBasis B.scale_pos)
        (k.succAbove 1) (k.succAbove 0) =
      -mfderiv 𝓘(ℝ, ℝ) (𝓡 2) ((B.face i).boundary k).map 1 1 := by
  have hphi : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
  have h := LeviCivitaData.mfderiv_curve_reparam (φ := fun t : ℝ => 1 - t)
    (by simpa using hgamma) hphi
  have hcurve : ((B.face i).boundary k).map ∘ (fun t : ℝ => 1 - t) =
      fun t : ℝ => B.coordinates i (AffineMap.lineMap
        (rightTriangleBasis B.scale_pos (k.succAbove 1))
        (rightTriangleBasis B.scale_pos (k.succAbove 0)) t) := by
    funext t
    exact B.boundary_reversed_map i k t
  dsimp only [TangentSpace] at h ⊢
  rw [hcurve] at h
  have hpoint := congrArg (fun t : ℝ =>
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) ((B.face i).boundary k).map t 1 : EuclideanSpace ℝ (Fin 2)))
    (sub_zero (1 : ℝ))
  have h' := h.trans (congrArg (fun v : EuclideanSpace ℝ (Fin 2) => (-1 : ℝ) • v) hpoint)
  unfold coordinateTriangleVelocity
  convert h' using 1 <;> first | rfl | simp only [neg_smul, one_smul]
  congr 2

theorem firstOuterSpoke_eq_boundary_velocity (i : Bool) :
    B.firstOuterSpoke i = mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
      ((B.face (i, true)).boundary 2).map 1 1 := by
  have h := B.reverse_velocity_eq_neg_endpoint (i, true) 2
    ((B.first_chart_velocity (i, true) (by simp : (1 : ℝ) ∈ Icc 0 1)).1.mdifferentiableAt (by simp))
  change coordinateTriangleVelocity (B.coordinates (i, true))
    (rightTriangleBasis B.scale_pos) 1 0 = _ at h
  rw [firstOuterSpoke, h, neg_neg]

theorem secondOuterSpoke_eq_boundary_velocity (i : Bool) :
    B.secondOuterSpoke i = mfderiv 𝓘(ℝ, ℝ) (𝓡 2)
      ((B.face (true, i)).boundary 1).map 1 1 := by
  have h := B.reverse_velocity_eq_neg_endpoint (true, i) 1
    ((B.second_chart_velocity (true, i) (by simp : (1 : ℝ) ∈ Icc 0 1)).1.mdifferentiableAt (by simp))
  change coordinateTriangleVelocity (B.coordinates (true, i))
    (rightTriangleBasis B.scale_pos) 2 0 = _ at h
  rw [secondOuterSpoke, h, neg_neg]

theorem first_outer_corner_supplement (g : RiemannianMetric 2 S) (i j : Bool) :
    coordinateTriangleAngle g (B.coordinates (i, j)) (rightTriangleBasis B.scale_pos) 1 +
      g.cornerAngle (B.firstOuterTip i) (B.firstOuterSpoke i) (B.firstOuterChord i j) =
        Real.pi := by
  unfold coordinateTriangleAngle firstOuterSpoke firstOuterChord
  change g.cornerAngle (B.coordinates (i, j) (rightTriangleBasis B.scale_pos 1))
      (coordinateTriangleVelocity (B.coordinates (i, j)) (rightTriangleBasis B.scale_pos) 1 0)
      (coordinateTriangleVelocity (B.coordinates (i, j)) (rightTriangleBasis B.scale_pos) 1 2) + _ = _
  dsimp only [TangentSpace]
  rw [B.coordinate_first_outer_tip, B.first_outer_inward_velocity_eq,
    g.cornerAngle_neg_left]
  ring

theorem second_outer_corner_supplement (g : RiemannianMetric 2 S) (i j : Bool) :
    coordinateTriangleAngle g (B.coordinates (j, i)) (rightTriangleBasis B.scale_pos) 2 +
      g.cornerAngle (B.secondOuterTip i) (B.secondOuterSpoke i) (B.secondOuterChord i j) =
        Real.pi := by
  unfold coordinateTriangleAngle secondOuterSpoke secondOuterChord
  change g.cornerAngle (B.coordinates (j, i) (rightTriangleBasis B.scale_pos 2))
      (coordinateTriangleVelocity (B.coordinates (j, i)) (rightTriangleBasis B.scale_pos) 2 0)
      (coordinateTriangleVelocity (B.coordinates (j, i)) (rightTriangleBasis B.scale_pos) 2 1) + _ = _
  dsimp only [TangentSpace]
  rw [B.coordinate_second_outer_tip, B.second_outer_inward_velocity_eq,
    g.cornerAngle_neg_left]
  ring

theorem first_outer_corner_pair (g : RiemannianMetric 2 S) (i : Bool) :
    (∑ j : Bool, coordinateTriangleAngle g (B.coordinates (i, j))
      (rightTriangleBasis B.scale_pos) 1) +
    (∑ j : Bool, g.cornerAngle (B.firstOuterTip i)
      (B.firstOuterSpoke i) (B.firstOuterChord i j)) = 2 * Real.pi := by
  rw [← Finset.sum_add_distrib]
  simp_rw [B.first_outer_corner_supplement]
  simp [two_mul]

theorem second_outer_corner_pair (g : RiemannianMetric 2 S) (i : Bool) :
    (∑ j : Bool, coordinateTriangleAngle g (B.coordinates (j, i))
      (rightTriangleBasis B.scale_pos) 2) +
    (∑ j : Bool, g.cornerAngle (B.secondOuterTip i)
      (B.secondOuterSpoke i) (B.secondOuterChord i j)) = 2 * Real.pi := by
  rw [← Finset.sum_add_distrib]
  simp_rw [B.second_outer_corner_supplement]
  simp [two_mul]

theorem first_outer_refined_corner_pair (g : RiemannianMetric 2 S) (i : Bool)
    (lines : Bool → List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ j : Bool, meshVertexAngleContribution g (B.coordinates (i, j))
      ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines j)) (B.firstOuterTip i)) +
    (∑ j : Bool, g.cornerAngle (B.firstOuterTip i)
      (B.firstOuterSpoke i) (B.firstOuterChord i j)) = 2 * Real.pi := by
  have h (j : Bool) := single_refineByLines_original_corner g (B.coordinates (i, j))
    (rightTriangleBasis B.scale_pos) (lines j) (B.coordinates_smooth (i, j))
    (B.coordinates_smooth_symm (i, j)) (B.triangle_subset_source (i, j)) 1
  simp only [B.coordinate_first_outer_tip] at h
  simp_rw [h]
  exact B.first_outer_corner_pair g i

theorem second_outer_refined_corner_pair (g : RiemannianMetric 2 S) (i : Bool)
    (lines : Bool → List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ j : Bool, meshVertexAngleContribution g (B.coordinates (j, i))
      ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines j)) (B.secondOuterTip i)) +
    (∑ j : Bool, g.cornerAngle (B.secondOuterTip i)
      (B.secondOuterSpoke i) (B.secondOuterChord i j)) = 2 * Real.pi := by
  have h (j : Bool) := single_refineByLines_original_corner g (B.coordinates (j, i))
    (rightTriangleBasis B.scale_pos) (lines j) (B.coordinates_smooth (j, i))
    (B.coordinates_smooth_symm (j, i)) (B.triangle_subset_source (j, i)) 2
  simp only [B.coordinate_second_outer_tip] at h
  simp_rw [h]
  exact B.second_outer_corner_pair g i

end PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces
