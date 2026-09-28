import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.FramePermutation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.Locality







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology Interval

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]


noncomputable def coordinateTriangleSideField
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (i j : Fin 3)
    (x : S) : TangentSpace (𝓡 2) x :=
  mpullback (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (coordinateTriangleChart F b)
    (fun _ => standardTriangleVertex j - standardTriangleVertex i) x


noncomputable def coordinateTriangleSideUnitField (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (i j : Fin 3)
    (x : S) : TangentSpace (𝓡 2) x :=
  (Real.sqrt (g.inner x (coordinateTriangleSideField F b i j x)
    (coordinateTriangleSideField F b i j x)))⁻¹ • coordinateTriangleSideField F b i j x


theorem coordinateTriangleSideUnitField_smooth (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {i j : Fin 3} (hij : i ≠ j) :
    ContMDiffOn (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (T% (coordinateTriangleSideUnitField g F b i j)) F.target := by
  have hv : standardTriangleVertex j - standardTriangleVertex i ≠ 0 := by
    intro hzero
    have heq := congrArg (triangleParameterEquiv b) (sub_eq_zero.mp hzero)
    rw [triangleParameterEquiv_vertex, triangleParameterEquiv_vertex] at heq
    exact hij (b.ind.injective heq).symm
  have h := (LeviCivitaData.normalized_chartField_properties g (coordinateTriangleChart F b)
    (coordinateTriangleChart_smooth F b hFi) (coordinateTriangleChart_smooth_symm F b hF) hv).1
  simpa only [coordinateTriangleSideUnitField, coordinateTriangleSideField,
    coordinateTriangleChart_source] using h

omit [IsManifold (𝓡 2) ∞ S] in


theorem coordinateTriangle_side_velocity
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source) (i j : Fin 3)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let γ := fun s : ℝ => F (AffineMap.lineMap (b i) (b j) s)
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ t ∧
      mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ t 1 = coordinateTriangleSideField F b i j (γ t) := by
  let e := coordinateTriangleChart F b
  let p := standardTriangleVertex i
  let v := standardTriangleVertex j - standardTriangleVertex i
  have hmap (s : ℝ) : e.symm (p + s • v) = F (AffineMap.lineMap (b i) (b j) s) := by
    have h := coordinateTriangleChart_side F b i j s
    simpa only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm] using h
  have ht' : p + t • v ∈ e.target := by
    change p + t • v ∈ ((triangleParameterEquiv b).toHomeomorph.toOpenPartialHomeomorph.trans F).source
    refine ⟨mem_univ _, hb ?_⟩
    change triangleParameterEquiv b (p + t • v) ∈ convexHull ℝ (range b)
    have h := triangleParameterEquiv_side b i j t
    have heq : p + t • v = AffineMap.lineMap (standardTriangleVertex i) (standardTriangleVertex j) t := by
      simp [p, v, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]
    rw [heq, h]
    exact (convex_convexHull ℝ (range b)).lineMap_mem
      (subset_convexHull ℝ _ (mem_range_self i)) (subset_convexHull ℝ _ (mem_range_self j)) ht
  have h := LeviCivitaData.mfderiv_chart_line e (coordinateTriangleChart_smooth F b hFi)
    (coordinateTriangleChart_smooth_symm F b hF) p v ht'
  have hcurve := funext hmap
  have hpoint := hmap t
  dsimp only [TangentSpace] at h ⊢
  rw [hcurve, hpoint] at h
  exact h

end PoincareConjecture.Topology.Surface
