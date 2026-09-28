import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.SideFields

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology Interval

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

omit [IsManifold (𝓡 2) ∞ S] in

theorem coordinateTriangleSideField_reindex_on_side
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (r : Equiv.Perm (Fin 3))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source) (i j : Fin 3)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let x := F (AffineMap.lineMap (b (r.symm i)) (b (r.symm j)) t)
    coordinateTriangleSideField F (b.reindex r) i j x =
      coordinateTriangleSideField F b (r.symm i) (r.symm j) x := by
  have hbr : convexHull ℝ (range (b.reindex r)) ⊆ F.source := by
    simpa only [AffineBasis.coe_reindex, EquivLike.range_comp] using hb
  exact (coordinateTriangle_side_velocity F (b.reindex r) hF hFi hbr i j ht).2.symm.trans
    (coordinateTriangle_side_velocity F b hF hFi hb (r.symm i) (r.symm j) ht).2

theorem surfaceTurningForm_coordinate_side_reindex
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (r : Equiv.Perm (Fin 3))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b))
    (R : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F (b.reindex r)))
    {i j : Fin 3} (hij : i ≠ j) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    let x := F (AffineMap.lineMap (b (r.symm i)) (b (r.symm j)) t)
    D.surfaceTurningForm R.first R.second
        (coordinateTriangleSideUnitField g F (b.reindex r) i j)
        (coordinateTriangleSideField F (b.reindex r) i j) x =
      trianglePermutationOrientation r * D.surfaceTurningForm Q.first Q.second
        (coordinateTriangleSideUnitField g F b (r.symm i) (r.symm j))
        (coordinateTriangleSideField F b (r.symm i) (r.symm j)) x := by
  let γ := fun s : ℝ => F (AffineMap.lineMap (b (r.symm i)) (b (r.symm j)) s)
  have hbr : convexHull ℝ (range (b.reindex r)) ⊆ F.source := by
    simpa only [AffineBasis.coe_reindex, EquivLike.range_comp] using hb
  have hz : AffineMap.lineMap (b (r.symm i)) (b (r.symm j)) t ∈
      convexHull ℝ (range b) :=
    (convex_convexHull ℝ (range b)).lineMap_mem
      (subset_convexHull ℝ _ (mem_range_self _))
      (subset_convexHull ℝ _ (mem_range_self _)) (Ioo_subset_Icc_self ht)
  have hx : γ t ∈ F.target := F.map_source (hb hz)
  have hγ := coordinateTriangle_side_velocity F b hF hFi hb (r.symm i) (r.symm j)
    (Ioo_subset_Icc_self ht)
  have hγ' := coordinateTriangle_side_velocity F (b.reindex r) hF hFi hbr i j
    (Ioo_subset_Icc_self ht)
  have hlocal : ∀ᶠ s in 𝓝 t,
      coordinateTriangleSideUnitField g F (b.reindex r) i j (γ s) =
        coordinateTriangleSideUnitField g F b (r.symm i) (r.symm j) (γ s) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hfield := coordinateTriangleSideField_reindex_on_side F b r hF hFi hb i j
      (Ioo_subset_Icc_self hs)
    change coordinateTriangleSideField F (b.reindex r) i j (γ s) =
      coordinateTriangleSideField F b (r.symm i) (r.symm j) (γ s) at hfield
    simp only [coordinateTriangleSideUnitField, hfield]
  have hturn := D.surfaceTurningForm_eq_of_eventuallyEq_along_curve
    (hγ.1.mdifferentiableAt (by simp)) Q.first Q.second
    (((coordinateTriangleSideUnitField_smooth g F (b.reindex r) hF hFi hij).contMDiffAt
      (F.open_target.mem_nhds hx)).mdifferentiableAt (by simp))
    (((coordinateTriangleSideUnitField_smooth g F b hF hFi (r.symm.injective.ne hij)).contMDiffAt
      (F.open_target.mem_nhds hx)).mdifferentiableAt (by simp))
    hlocal hγ'.2.symm hγ.2.symm
  have hframe := surfaceTurningForm_coordinate_reindex D F b r hF hFi hb Q R
    (coordinateTriangleSideUnitField g F (b.reindex r) i j)
    (coordinateTriangleSideField F (b.reindex r) i j) hz
  exact hframe.trans (congrArg (trianglePermutationOrientation r * ·) hturn)

theorem integral_coordinateTriangle_side_reindex
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))) (r : Equiv.Perm (Fin 3))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b))
    (R : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F (b.reindex r)))
    {i j : Fin 3} (hij : i ≠ j) :
    (∫ t in (0 : ℝ)..1, D.surfaceTurningForm R.first R.second
      (coordinateTriangleSideUnitField g F (b.reindex r) i j)
      (coordinateTriangleSideField F (b.reindex r) i j)
      (F (AffineMap.lineMap ((b.reindex r) i) ((b.reindex r) j) t))) =
    trianglePermutationOrientation r *
      ∫ t in (0 : ℝ)..1, D.surfaceTurningForm Q.first Q.second
        (coordinateTriangleSideUnitField g F b (r.symm i) (r.symm j))
        (coordinateTriangleSideField F b (r.symm i) (r.symm j))
        (F (AffineMap.lineMap (b (r.symm i)) (b (r.symm j)) t)) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro t ht
  exact surfaceTurningForm_coordinate_side_reindex D F b r hF hFi hb Q R hij ht

end PoincareConjecture.Topology.Surface
