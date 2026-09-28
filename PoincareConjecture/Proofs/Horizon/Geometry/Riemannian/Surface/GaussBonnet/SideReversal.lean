import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.SideFields







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set VectorField
open scoped Manifold ContDiff Bundle Interval

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

omit [IsManifold (𝓡 2) ∞ S] in
theorem coordinateTriangleSideField_swap
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (i j : Fin 3) :
    coordinateTriangleSideField F b j i = -coordinateTriangleSideField F b i j := by
  funext x
  have hv : standardTriangleVertex i - standardTriangleVertex j =
      -(standardTriangleVertex j - standardTriangleVertex i) := (neg_sub _ _).symm
  simp only [coordinateTriangleSideField, mpullback, Pi.neg_apply]
  rw [hv, map_neg]

theorem coordinateTriangleSideUnitField_swap (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (i j : Fin 3) :
    coordinateTriangleSideUnitField g F b j i = -coordinateTriangleSideUnitField g F b i j := by
  funext x
  simp only [coordinateTriangleSideUnitField, coordinateTriangleSideField_swap F b i j,
    Pi.neg_apply, map_neg, neg_apply, neg_neg, smul_neg]


theorem surfaceTurningForm_coordinate_side_swap
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x)
    {i j : Fin 3} (hij : i ≠ j) {x : S} (hx : x ∈ F.target) :
    D.surfaceTurningForm e₁ e₂ (coordinateTriangleSideUnitField g F b j i)
      (coordinateTriangleSideField F b j i) x =
    -D.surfaceTurningForm e₁ e₂ (coordinateTriangleSideUnitField g F b i j)
      (coordinateTriangleSideField F b i j) x := by
  rw [coordinateTriangleSideUnitField_swap g F b i j, coordinateTriangleSideField_swap F b i j]
  rw [D.surfaceTurningForm_neg_field e₁ e₂ (coordinateTriangleSideUnitField g F b i j)
    (-coordinateTriangleSideField F b i j) x
    (((coordinateTriangleSideUnitField_smooth g F b hF hFi hij).contMDiffAt
      (F.open_target.mem_nhds hx)).mdifferentiableAt (by simp))]
  simp only [LeviCivitaData.surfaceTurningForm, Pi.neg_apply, map_neg, neg_apply]


theorem integral_coordinateTriangle_side_swap
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (e₁ e₂ : (x : S) → TangentSpace (𝓡 2) x) {i j : Fin 3} (hij : i ≠ j) :
    (∫ t in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂
      (coordinateTriangleSideUnitField g F b j i) (coordinateTriangleSideField F b j i)
      (F (AffineMap.lineMap (b j) (b i) t))) =
    -(∫ t in (0 : ℝ)..1, D.surfaceTurningForm e₁ e₂
      (coordinateTriangleSideUnitField g F b i j) (coordinateTriangleSideField F b i j)
      (F (AffineMap.lineMap (b i) (b j) t))) := by
  let k := fun t : ℝ => D.surfaceTurningForm e₁ e₂
    (coordinateTriangleSideUnitField g F b i j) (coordinateTriangleSideField F b i j)
    (F (AffineMap.lineMap (b i) (b j) t))
  calc
    _ = -(∫ t in (0 : ℝ)..1, k (1 - t)) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro t ht
      dsimp only [k]
      rw [AffineMap.lineMap_apply_one_sub]
      apply surfaceTurningForm_coordinate_side_swap D F b hF hFi e₁ e₂ hij
      exact F.map_source (hb ((convex_convexHull ℝ (range b)).lineMap_mem
        (subset_convexHull ℝ _ (mem_range_self j))
        (subset_convexHull ℝ _ (mem_range_self i)) (Ioo_subset_Icc_self ht)))
    _ = _ := congrArg Neg.neg (by
      simpa only [sub_self, sub_zero] using
        (intervalIntegral.integral_comp_sub_left k (a := (0 : ℝ)) (b := 1) 1))

end PoincareConjecture.Topology.Surface
