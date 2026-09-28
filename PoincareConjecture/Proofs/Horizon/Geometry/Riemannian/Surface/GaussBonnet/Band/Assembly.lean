import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.Corners
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.Cancellation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CoordinateFormula
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Area.Triangulation







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory VectorField
open scoped Manifold ContDiff Bundle Interval Matrix
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.SmoothGraphBandPair

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  [MeasurableSpace S] [BorelSpace S] [T3Space S]
  {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S}
  {lo hi : ℝ → ℝ} {a b : ℝ} {hab : a < b}
  (B : SmoothGraphBandPair F lo hi hab) {g : RiemannianMetric 2 S}

theorem integral_band_eq_sum_faces (D : LeviCivitaData g) :
    (∫ y in F '' coordinateGraphBand lo hi a b, D.scalarCurvature y ∂g.volumeMeasure) =
      ∑ i : Bool, ∫ y in (B.face i).carrier, D.scalarCurvature y ∂g.volumeMeasure := by
  have hdisjoint : AEDisjoint g.volumeMeasure B.lower.carrier B.upper.carrier := by
    change g.volumeMeasure (B.lower.carrier ∩ B.upper.carrier) = 0
    rw [B.diagonal_inter]
    exact (B.lower.boundary 1).volumeMeasure_image_eq_zero g
  rw [← B.cover, setIntegral_union₀ hdisjoint
    B.upper.isCompact_carrier.measurableSet.nullMeasurableSet
    (D.continuous_scalarCurvature.continuousOn.integrableOn_compact B.lower.isCompact_carrier)
    (D.continuous_scalarCurvature.continuousOn.integrableOn_compact B.upper.isCompact_carrier)]
  simp only [Fintype.sum_bool, face]
  ring

variable {U : Set ℝ} (hU : IsOpen U)
  (hlo : ContDiffOn ℝ ∞ lo U) (hhi : ContDiffOn ℝ ∞ hi U)
  (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
  (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)

omit [MeasurableSpace S] [BorelSpace S] [T3Space S] in

noncomputable def alignedFrame (g : RiemannianMetric 2 S) (i : Bool) :
    RiemannianMetric.AlignedChartFrame g
      (coordinateTriangleChart (B.faceCoordinates hU hlo hhi) (B.faceBasis i)) :=
  g.alignedChartFrame _
    (coordinateTriangleChart_smooth _ _ (B.smooth_faceCoordinates_symm hU hlo hhi hFi))
    (coordinateTriangleChart_smooth_symm _ _ (B.smooth_faceCoordinates hU hlo hhi hF))

omit [MeasurableSpace S] [BorelSpace S] [T3Space S] in


noncomputable def outerCornerSum (g : RiemannianMetric 2 S) : ℝ :=
  let C := B.faceCoordinates hU hlo hhi
  g.cornerAngle (C !₂[a, 0])
      (coordinateTriangleVelocity C (B.faceBasis false) 0 1)
      (coordinateTriangleVelocity C (B.faceBasis true) 0 1) +
    coordinateTriangleAngle g C (B.faceBasis false) 1 +
    coordinateTriangleAngle g C (B.faceBasis true) 1 +
    g.cornerAngle (C !₂[b, 1])
      (coordinateTriangleVelocity C (B.faceBasis false) 2 1)
      (coordinateTriangleVelocity C (B.faceBasis true) 2 1)

include hF hFi in
omit [MeasurableSpace S] [BorelSpace S] [T3Space S] in
theorem sum_face_angles_eq_outerCornerSum (hI : Icc a b ⊆ U) :
    (∑ i : Bool, ∑ k : Fin 3,
      coordinateTriangleAngle g (B.faceCoordinates hU hlo hhi) (B.faceBasis i) k) =
        B.outerCornerSum hU hlo hhi g := by
  have h0 := B.cornerAngle_split_zero hU hlo hhi hF hFi hI g
  have h2 := B.cornerAngle_split_two hU hlo hhi hF hFi hI g
  dsimp only at h0 h2
  simp only [Fintype.sum_bool, Fin.sum_univ_three, outerCornerSum]
  linarith only [h0, h2]




theorem gaussBonnet_band (hI : Icc a b ⊆ U) (D : LeviCivitaData g) :
    let C := B.faceCoordinates hU hlo hhi
    let e := fun i => coordinateTriangleChart C (B.faceBasis i)
    let Q := B.alignedFrame hU hlo hhi hF hFi g
    let X := fun i => mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (e i) (fun _ => (1, 0))
    let V := fun i => mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (e i) (fun _ => (-1, 1))
    let W := fun i y => (Real.sqrt (g.inner y (V i y) (V i y)))⁻¹ • V i y
    (∫ y in F '' coordinateGraphBand lo hi a b, D.scalarCurvature y ∂g.volumeMeasure) +
      2 * (∑ i : Bool, (
        (∫ t in (0 : ℝ)..1,
          D.surfaceTurningForm (Q i).first (Q i).second (Q i).first (X i) ((e i).symm (t, 0))) +
        (∫ t in (0 : ℝ)..1,
          D.surfaceTurningForm (Q i).first (Q i).second (W i) (V i) ((e i).symm (1 - t, t))))) +
      2 * (4 * Real.pi - B.outerCornerSum hU hlo hhi g) = 4 * Real.pi := by
  dsimp only
  let C := B.faceCoordinates hU hlo hhi
  let e := fun i => coordinateTriangleChart C (B.faceBasis i)
  let Q := B.alignedFrame hU hlo hhi hF hFi g
  let X := fun i => mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (e i) (fun _ => (1, 0))
  let V := fun i => mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (e i) (fun _ => (-1, 1))
  let W := fun i y => (Real.sqrt (g.inner y (V i y) (V i y)))⁻¹ • V i y
  let H (i : Bool) := (∫ t in (0 : ℝ)..1,
    D.surfaceTurningForm (Q i).first (Q i).second (Q i).first (X i) ((e i).symm (t, 0))) +
    (∫ t in (0 : ℝ)..1,
      D.surfaceTurningForm (Q i).first (Q i).second (W i) (V i) ((e i).symm (1 - t, t)))
  let J (i : Bool) := ∫ t in (0 : ℝ)..1,
    D.surfaceTurningForm (Q i).first (Q i).second
      (coordinateTriangleSecondUnitField g C (B.faceBasis i))
      (coordinateTriangleSecondField C (B.faceBasis i)) ((e i).symm (0, t))
  let I (i : Bool) := ∫ y in (B.face i).carrier, D.scalarCurvature y ∂g.volumeMeasure
  let A (i : Bool) (k : Fin 3) := coordinateTriangleAngle g C (B.faceBasis i) k
  have hface (i : Bool) : I i + 2 * (H i - J i) +
      2 * (3 * Real.pi - (∑ k : Fin 3, A i k)) = 4 * Real.pi := by
    have h := D.gaussBonnet_coordinateTriangle_of_frame C (B.faceBasis i)
      (B.smooth_faceCoordinates hU hlo hhi hF) (B.smooth_faceCoordinates_symm hU hlo hhi hFi)
      (B.face_triangle_subset_source hU hlo hhi hI i) (Q i)
    dsimp only at h
    rw [← B.face_carrier_eq_coordinates hU hlo hhi i, Finset.sum_sub_distrib] at h
    dsimp only [I, H, J, A, X, V, W, e]
    unfold coordinateTriangleSecondUnitField coordinateTriangleSecondField
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat] using h
  have hJ : J false + J true = 0 := by
    have h := integral_rectangle_diagonal_pair_eq_zero C
      (B.smooth_faceCoordinates hU hlo hhi hF) (B.smooth_faceCoordinates_symm hU hlo hhi hFi)
      hab zero_lt_one (B.rectangle_subset_faceCoordinates_source hU hlo hhi hI)
      D (Q false) (Q true)
    dsimp only [J, e]
    simp only [coordinateTriangle_second_map]
    exact h
  have hA := B.sum_face_angles_eq_outerCornerSum hU hlo hhi hF hFi (g := g) hI
  change (∑ i : Bool, ∑ k : Fin 3, A i k) = B.outerCornerSum hU hlo hhi g at hA
  rw [B.integral_band_eq_sum_faces D]
  change (∑ i : Bool, I i) + 2 * (∑ i : Bool, H i) +
    2 * (4 * Real.pi - B.outerCornerSum hU hlo hhi g) = 4 * Real.pi
  simp only [Fintype.sum_bool] at hA ⊢
  linarith only [hface false, hface true, hJ, hA]

end PoincareConjecture.Topology.Surface.SmoothGraphBandPair
