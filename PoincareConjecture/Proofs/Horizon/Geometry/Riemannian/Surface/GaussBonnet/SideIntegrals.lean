import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.SideReindex
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.SideReversal
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.Boundary







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField MeasureTheory
open scoped Manifold ContDiff Bundle Topology Interval

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]


noncomputable def coordinateTriangleTurningIntegral
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b)) (i j : Fin 3) : ℝ :=
  ∫ t in (0 : ℝ)..1, D.surfaceTurningForm Q.first Q.second
    (coordinateTriangleSideUnitField g F b i j) (coordinateTriangleSideField F b i j)
    (F (AffineMap.lineMap (b i) (b j) t))

theorem coordinateTriangleTurningIntegral_reindex
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (r : Equiv.Perm (Fin 3))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b))
    (R : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F (b.reindex r)))
    {i j : Fin 3} (hij : i ≠ j) :
    coordinateTriangleTurningIntegral D F (b.reindex r) R i j =
      trianglePermutationOrientation r * coordinateTriangleTurningIntegral D F b Q
        (r.symm i) (r.symm j) :=
  integral_coordinateTriangle_side_reindex D F b r hF hFi hb Q R hij

theorem coordinateTriangleTurningIntegral_swap
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b))
    {i j : Fin 3} (hij : i ≠ j) :
    coordinateTriangleTurningIntegral D F b Q j i =
      -coordinateTriangleTurningIntegral D F b Q i j :=
  integral_coordinateTriangle_side_swap D F b hF hFi hb Q.first Q.second hij


theorem coordinateTriangleSideUnitField_first_eq
    {g : RiemannianMetric 2 S}
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b))
    {x : S} (hx : x ∈ F.target) : coordinateTriangleSideUnitField g F b 0 1 x = Q.first x := by
  have hx' : x ∈ (coordinateTriangleChart F b).source := by
    rwa [coordinateTriangleChart_source]
  have hv : standardTriangleVertex 1 - standardTriangleVertex 0 = ((1, 0) : ℝ × ℝ) := by
    simp [standardTriangleVertex]
  simpa only [coordinateTriangleSideUnitField, coordinateTriangleSideField, hv] using
    (Q.aligned x hx').symm



theorem coordinateTriangleTurningIntegral_first
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b)) :
    coordinateTriangleTurningIntegral D F b Q 0 1 =
      ∫ t in (0 : ℝ)..1, D.surfaceTurningForm Q.first Q.second Q.first
        (mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (coordinateTriangleChart F b) (fun _ => (1, 0)))
        ((coordinateTriangleChart F b).symm (t, 0)) := by
  let γ := fun t : ℝ => F (AffineMap.lineMap (b 0) (b 1) t)
  have htarget (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ F.target :=
    F.map_source (hb ((convex_convexHull ℝ (range b)).lineMap_mem
      (subset_convexHull ℝ _ (mem_range_self 0)) (subset_convexHull ℝ _ (mem_range_self 1)) ht))
  have hQ : ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% Q.first) F.target := by
    simpa only [coordinateTriangleChart_source] using Q.smooth_first
  have hv : standardTriangleVertex 1 - standardTriangleVertex 0 = ((1, 0) : ℝ × ℝ) := by
    simp [standardTriangleVertex]
  unfold coordinateTriangleTurningIntegral
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro t ht
  dsimp only
  rw [coordinateTriangle_first_map]
  have hcurve := coordinateTriangle_side_velocity F b hF hFi hb 0 1 (Ioo_subset_Icc_self ht)
  have hlocal : ∀ᶠ s in 𝓝 t, coordinateTriangleSideUnitField g F b 0 1 (γ s) = Q.first (γ s) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact coordinateTriangleSideUnitField_first_eq F b Q (htarget s (Ioo_subset_Icc_self hs))
  have h := D.surfaceTurningForm_eq_of_eventuallyEq_along_curve
    (hcurve.1.mdifferentiableAt (by simp)) Q.first Q.second
    (((coordinateTriangleSideUnitField_smooth g F b hF hFi (i := 0) (j := 1)
      (by decide)).contMDiffAt (F.open_target.mem_nhds
        (htarget t (Ioo_subset_Icc_self ht)))).mdifferentiableAt (by simp))
    ((hQ.contMDiffAt (F.open_target.mem_nhds
      (htarget t (Ioo_subset_Icc_self ht)))).mdifferentiableAt (by simp))
    hlocal hcurve.2.symm hcurve.2.symm
  have hX : coordinateTriangleSideField F b 0 1 =
      mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (coordinateTriangleChart F b) (fun _ => (1, 0)) := by
    funext x
    simp only [coordinateTriangleSideField, hv]
  rw [← hX]
  exact h

variable [MeasurableSpace S] [BorelSpace S] [T3Space S]



theorem gaussBonnet_coordinateTriangle_side_integrals
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b)) :
    (∫ x in F '' convexHull ℝ (range b), D.scalarCurvature x ∂g.volumeMeasure) +
      2 * (∑ i : Fin 3, coordinateTriangleTurningIntegral D F b Q i (i + 1)) +
      2 * (∑ i : Fin 3, (Real.pi - coordinateTriangleAngle g F b i)) = 4 * Real.pi := by
  have h := D.gaussBonnet_coordinateTriangle_of_frame F b hF hFi hb Q
  have hs := coordinateTriangleTurningIntegral_swap D F b hF hFi hb Q
    (i := 0) (j := 2) (by decide)
  rw [Fin.sum_univ_three]
  change (∫ x in F '' convexHull ℝ (range b), D.scalarCurvature x ∂g.volumeMeasure) +
    2 * (coordinateTriangleTurningIntegral D F b Q 0 1 +
      coordinateTriangleTurningIntegral D F b Q 1 2 +
      coordinateTriangleTurningIntegral D F b Q 2 0) + _ = _
  rw [hs, coordinateTriangleTurningIntegral_first D F b hF hFi hb Q]
  have hv12 : standardTriangleVertex 2 - standardTriangleVertex 1 = ((-1, 1) : ℝ × ℝ) := by
    simp [standardTriangleVertex]
  have hv02 : standardTriangleVertex 2 - standardTriangleVertex 0 = ((0, 1) : ℝ × ℝ) := by
    simp [standardTriangleVertex]
  let e := coordinateTriangleChart F b
  let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
  let V := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (-1, 1))
  let T := fun x => (Real.sqrt (g.inner x (Y x) (Y x)))⁻¹ • Y x
  let W := fun x => (Real.sqrt (g.inner x (V x) (V x)))⁻¹ • V x
  have hY : coordinateTriangleSideField F b 0 2 = Y := by
    funext x
    simp only [coordinateTriangleSideField, hv02, Y, e]
  have hV : coordinateTriangleSideField F b 1 2 = V := by
    funext x
    simp only [coordinateTriangleSideField, hv12, V, e]
  have hT : coordinateTriangleSideUnitField g F b 0 2 = T := by
    funext x
    simp only [coordinateTriangleSideUnitField, hY, T]
  have hW : coordinateTriangleSideUnitField g F b 1 2 = W := by
    funext x
    simp only [coordinateTriangleSideUnitField, hV, W]
  unfold coordinateTriangleTurningIntegral
  rw [hY, hV, hT, hW]
  simp only [coordinateTriangle_chord_map, coordinateTriangle_second_map] at h
  simpa only [sub_eq_add_neg] using h

end PoincareConjecture.Topology.Surface
