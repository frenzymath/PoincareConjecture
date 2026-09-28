import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CoordinateTriangle
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.FanAngles

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set VectorField
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

noncomputable def coordinateTriangleVelocity
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (i j : Fin 3) :
    TangentSpace (𝓡 2) (F (b i)) :=
  mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun t : ℝ => F (AffineMap.lineMap (b i) (b j) t)) 0 1

noncomputable def coordinateTriangleAngle (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (i : Fin 3) : ℝ :=
  g.cornerAngle (F (b i))
    (coordinateTriangleVelocity F b i (i.succAbove 0))
    (coordinateTriangleVelocity F b i (i.succAbove 1))

omit [IsManifold (𝓡 2) ∞ S] in

theorem coordinateTriangleVelocity_eq_differential
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hsource : convexHull ℝ (range b) ⊆ F.source) (i j : Fin 3) :
    coordinateTriangleVelocity F b i j =
      mfderiv (𝓡 2) (𝓡 2) F (b i) (b j - b i) := by
  have hi : b i ∈ F.source := hsource (subset_convexHull ℝ (range b) (mem_range_self i))
  have hFi := (hF.contMDiffAt (F.open_source.mem_nhds hi)).mdifferentiableAt (by simp)
  have hd : HasDerivAt (fun t : ℝ => AffineMap.lineMap (b i) (b j) t) (b j - b i) 0 := by
    simpa only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, one_smul, id_eq]
      using ((hasDerivAt_id (0 : ℝ)).smul_const (b j - b i)).add_const (b i)
  have h := congrArg (fun L => L 1) (mfderiv_comp (0 : ℝ)
    (by simpa using hFi) hd.differentiableAt.mdifferentiableAt)
  dsimp only [TangentSpace] at h ⊢
  simp only [ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
  rw [AffineMap.lineMap_apply_zero] at h
  exact h

omit [IsManifold (𝓡 2) ∞ S] in
theorem coordinateTriangleVelocity_eq_mfderivWithin
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hsource : convexHull ℝ (range b) ⊆ F.source) (i j : Fin 3) :
    coordinateTriangleVelocity F b i j =
      mfderivWithin 𝓘(ℝ, ℝ) (𝓡 2)
        (fun t : ℝ => F (AffineMap.lineMap (b i) (b j) t)) (Icc (0 : ℝ) 1) 0 1 := by
  have hi : AffineMap.lineMap (b i) (b j) (0 : ℝ) ∈ F.source := by
    simpa using hsource (subset_convexHull ℝ (range b) (mem_range_self i))
  have hcurve := (hF.contMDiffAt (F.open_source.mem_nhds hi)).comp 0
    (AffineMap.contDiff_lineMap (b i) (b j)).contMDiff.contMDiffAt
  change ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞
    (fun t : ℝ => F (AffineMap.lineMap (b i) (b j) t)) 0 at hcurve
  dsimp only [TangentSpace]
  rw [mfderivWithin_eq_mfderiv
    ((uniqueDiffOn_Icc zero_lt_one 0 (by simp)).uniqueMDiffWithinAt)
    (hcurve.mdifferentiableAt (by simp))]
  rfl

omit [IsManifold (𝓡 2) ∞ S] in
theorem coordinateTriangleVelocity_eq_chartField
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : convexHull ℝ (range b) ⊆ F.source) (i j : Fin 3) :
    coordinateTriangleVelocity F b i j =
      mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (coordinateTriangleChart F b)
        (fun _ => standardTriangleVertex j - standardTriangleVertex i) (F (b i)) := by
  let e := coordinateTriangleChart F b
  have hi : standardTriangleVertex i ∈ e.target := by
    apply coordinateTriangleChart_target F b hsource
    fin_cases i <;> norm_num [standardTriangleVertex]
  have h := (LeviCivitaData.mfderiv_chart_line e
    (coordinateTriangleChart_smooth F b hFi)
    (coordinateTriangleChart_smooth_symm F b hF)
    (standardTriangleVertex i) (standardTriangleVertex j - standardTriangleVertex i)
    (t := 0) (by simpa using hi)).2
  have hcurve : (fun t : ℝ => e.symm (standardTriangleVertex i +
      t • (standardTriangleVertex j - standardTriangleVertex i))) =
      fun t : ℝ => F (AffineMap.lineMap (b i) (b j) t) := by
    funext t
    rw [show standardTriangleVertex i + t •
        (standardTriangleVertex j - standardTriangleVertex i) =
        AffineMap.lineMap (standardTriangleVertex i) (standardTriangleVertex j) t by
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      abel]
    exact coordinateTriangleChart_side F b i j t
  dsimp only [TangentSpace] at h ⊢
  rw [hcurve] at h
  have hz : standardTriangleVertex i +
      (0 : ℝ) • (standardTriangleVertex j - standardTriangleVertex i) =
      standardTriangleVertex i := by simp
  rw [hz] at h
  change coordinateTriangleVelocity F b i j =
    mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (coordinateTriangleChart F b)
      (fun _ => standardTriangleVertex j - standardTriangleVertex i)
      ((coordinateTriangleChart F b).symm (standardTriangleVertex i)) at h
  rw [coordinateTriangleChart_vertex] at h
  exact h

omit [IsManifold (𝓡 2) ∞ S] in
theorem coordinateTriangleVelocity_ne_zero
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : convexHull ℝ (range b) ⊆ F.source) {i j : Fin 3} (hij : i ≠ j) :
    coordinateTriangleVelocity F b i j ≠ 0 := by
  rw [coordinateTriangleVelocity_eq_chartField F b hF hFi hsource]
  apply LeviCivitaData.chartField_ne_zero (coordinateTriangleChart F b)
    (coordinateTriangleChart_smooth F b hFi)
    (coordinateTriangleChart_smooth_symm F b hF)
  · intro hzero
    have hv := sub_eq_zero.mp hzero
    have hbij := congrArg (triangleParameterEquiv b) hv
    rw [triangleParameterEquiv_vertex, triangleParameterEquiv_vertex] at hbij
    exact hij (b.ind.injective hbij).symm
  · rw [← coordinateTriangleChart_vertex F b i]
    apply (coordinateTriangleChart F b).map_target
    apply coordinateTriangleChart_target F b hsource
    fin_cases i <;> norm_num [standardTriangleVertex]

theorem sum_coordinateTriangleAngle_eq_chartFields (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : convexHull ℝ (range b) ⊆ F.source) :
    let e := coordinateTriangleChart F b
    let X := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (1, 0))
    let Y := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (0, 1))
    let V := mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) e (fun _ => (-1, 1))
    (∑ i : Fin 3, coordinateTriangleAngle g F b i) =
      g.cornerAngle (F (b 0)) (X (F (b 0))) (Y (F (b 0))) +
      g.cornerAngle (F (b 1)) (-X (F (b 1))) (V (F (b 1))) +
      g.cornerAngle (F (b 2)) (-Y (F (b 2))) (-V (F (b 2))) := by
  dsimp only
  simp only [coordinateTriangleAngle, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change g.cornerAngle (F (b 0)) (coordinateTriangleVelocity F b 0 1)
      (coordinateTriangleVelocity F b 0 2) +
    (g.cornerAngle (F (b 1)) (coordinateTriangleVelocity F b 1 0)
      (coordinateTriangleVelocity F b 1 2) +
    g.cornerAngle (F (b 2)) (coordinateTriangleVelocity F b 2 0)
      (coordinateTriangleVelocity F b 2 1)) = _
  simp only [coordinateTriangleVelocity_eq_chartField F b hF hFi hsource]
  change g.cornerAngle (F (b 0))
      ((mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (coordinateTriangleChart F b) (F (b 0))).inverse
        ((1, 0) - (0, 0)))
      ((mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (coordinateTriangleChart F b) (F (b 0))).inverse
        ((0, 1) - (0, 0))) +
    (g.cornerAngle (F (b 1))
      ((mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (coordinateTriangleChart F b) (F (b 1))).inverse
        ((0, 0) - (1, 0)))
      ((mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (coordinateTriangleChart F b) (F (b 1))).inverse
        ((0, 1) - (1, 0))) +
    g.cornerAngle (F (b 2))
      ((mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (coordinateTriangleChart F b) (F (b 2))).inverse
        ((0, 0) - (0, 1)))
      ((mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (coordinateTriangleChart F b) (F (b 2))).inverse
        ((1, 0) - (0, 1)))) = _
  rw [show ((0, 1) : ℝ × ℝ) - (1, 0) = (-1, 1) by ext <;> norm_num,
    show ((1, 0) : ℝ × ℝ) - (0, 1) = -(-1, 1) by ext <;> norm_num]
  simp only [show ((0, 0) : ℝ × ℝ) = 0 from rfl, sub_zero, zero_sub, map_neg,
    mpullback, add_assoc]

end PoincareConjecture.Topology.Surface
