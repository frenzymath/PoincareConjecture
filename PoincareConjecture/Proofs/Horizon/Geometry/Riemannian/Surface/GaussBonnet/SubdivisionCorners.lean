import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.MetricCorners








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Matrix
open Poincare.Topology.Plane.Triangles Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

private theorem splitBasis_independent
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i : Bool) :
    AffineIndependent ℝ (if i then ![b 0, AffineMap.lineMap (b 1) (b 2) t, b 2]
      else ![b 0, b 1, AffineMap.lineMap (b 1) (b 2) t]) := by
  let u : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) := rightTriangleBasis zero_lt_one
  let E := triangleAffineEquiv u b u.ind b.ind
  have href : AffineIndependent ℝ
      (if i then ![u 0, AffineMap.lineMap (u 1) (u 2) t, u 2]
        else ![u 0, u 1, AffineMap.lineMap (u 1) (u 2) t]) := by
    cases i <;> apply affineIndependent_plane_triple_of_det_ne_zero
    · simpa [u, AffineMap.lineMap_apply] using ht.1.ne'
    · simpa [u, AffineMap.lineMap_apply, sub_eq_add_neg, add_comm] using
        (sub_pos.mpr ht.2).ne'
  have h := href.map' E.toAffineMap E.injective
  convert h using 1
  funext k
  cases i <;> fin_cases k <;>
    simp [E]



noncomputable def coordinateSplitBasis
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i : Bool) :
    AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  affineBasisOfTriangle
    (if i then ![b 0, AffineMap.lineMap (b 1) (b 2) t, b 2]
      else ![b 0, b 1, AffineMap.lineMap (b 1) (b 2) t]) (splitBasis_independent b ht i)

@[simp] theorem coordinateSplitBasis_apply
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i : Bool) (k : Fin 3) :
    coordinateSplitBasis b ht i k =
      (if i then ![b 0, AffineMap.lineMap (b 1) (b 2) t, b 2]
        else ![b 0, b 1, AffineMap.lineMap (b 1) (b 2) t]) k := rfl

theorem coordinateSplitBasis_hull_subset
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (i : Bool) :
    convexHull ℝ (range (coordinateSplitBasis b ht i)) ⊆ convexHull ℝ (range b) := by
  apply convexHull_min _ (convex_convexHull ℝ (range b))
  rintro _ ⟨k, rfl⟩
  have hv (j : Fin 3) := subset_convexHull ℝ (range b) (mem_range_self j)
  have hq := (convex_convexHull ℝ (range b)).lineMap_mem (hv 1) (hv 2) (Ioo_subset_Icc_self ht)
  cases i <;> fin_cases k <;> first | exact hv 0 | exact hv 1 | exact hv 2 | exact hq

section GivenBases

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  (g : RiemannianMetric 2 S)
  (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
  (b l r : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
  (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
  (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
  (hb : convexHull ℝ (range b) ⊆ F.source)
  (hl : convexHull ℝ (range l) ⊆ F.source)
  (hr : convexHull ℝ (range r) ⊆ F.source)
  {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
  (hl0 : l 0 = b 0) (hl1 : l 1 = b 1)
  (hl2 : l 2 = AffineMap.lineMap (b 1) (b 2) t)
  (hr0 : r 0 = b 0) (hr1 : r 1 = l 2) (hr2 : r 2 = b 2)

include hF hFi hb hl hr ht hl0 hl1 hl2 hr0 hr1 hr2



theorem coordinateTriangleAngle_split_vertex :
    coordinateTriangleAngle g F l 0 + coordinateTriangleAngle g F r 0 =
      coordinateTriangleAngle g F b 0 := by
  let L := mfderiv (𝓡 2) (𝓡 2) F (b 0)
  have hne := coordinateTriangleVelocity_ne_zero F l hF hFi hl
    (i := 0) (j := 2) (by decide)
  dsimp only [TangentSpace] at hne ⊢
  rw [coordinateTriangleVelocity_eq_differential F l hF hl, hl0, hl2] at hne
  have hv : AffineMap.lineMap (b 1) (b 2) t - b 0 =
      (1 - t) • (b 1 - b 0) + t • (b 2 - b 0) := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  rw [hv, map_add, map_smul, map_smul] at hne
  have hangle := g.cornerAngle_split_of_nonneg_combination (F (b 0))
    (L (b 1 - b 0)) (L (b 2 - b 0)) (sub_nonneg.mpr ht.2.le) ht.1.le hne
  change g.cornerAngle (F (l 0)) (coordinateTriangleVelocity F l 0 1)
      (coordinateTriangleVelocity F l 0 2) +
    g.cornerAngle (F (r 0)) (coordinateTriangleVelocity F r 0 1)
      (coordinateTriangleVelocity F r 0 2) =
    g.cornerAngle (F (b 0)) (coordinateTriangleVelocity F b 0 1)
      (coordinateTriangleVelocity F b 0 2)
  simp only [coordinateTriangleVelocity_eq_differential F l hF hl,
    coordinateTriangleVelocity_eq_differential F r hF hr,
    coordinateTriangleVelocity_eq_differential F b hF hb, hl0, hl1, hr0, hr1, hr2, hl2,
    hv, map_add, map_smul]
  rw [hl0, hr0]
  exact hangle.symm

omit hFi hb in


theorem coordinateTriangleAngle_split_edge :
    coordinateTriangleAngle g F l 2 + coordinateTriangleAngle g F r 1 = Real.pi := by
  let q := l 2
  let L := mfderiv (𝓡 2) (𝓡 2) F q
  have hleft : b 1 - q = -t • (b 2 - b 1) := by
    dsimp only [q]
    rw [hl2]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hright : b 2 - q = (1 - t) • (b 2 - b 1) := by
    dsimp only [q]
    rw [hl2]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  change g.cornerAngle (F (l 2)) (coordinateTriangleVelocity F l 2 0)
      (coordinateTriangleVelocity F l 2 1) +
    g.cornerAngle (F (r 1)) (coordinateTriangleVelocity F r 1 0)
      (coordinateTriangleVelocity F r 1 2) = _
  simp only [coordinateTriangleVelocity_eq_differential F l hF hl,
    coordinateTriangleVelocity_eq_differential F r hF hr, hl0, hl1, hr0, hr1, hr2]
  rw [hr1]
  change g.cornerAngle (F q) (L (b 0 - q)) (L (b 1 - q)) +
    g.cornerAngle (F q) (L (b 0 - q)) (L (b 2 - q)) = _
  rw [hleft, hright, map_smul, map_smul, neg_smul,
    g.cornerAngle_neg_right, g.cornerAngle_smul_pos_right _ _ _ ht.1,
    g.cornerAngle_smul_pos_right _ _ _ (sub_pos.mpr ht.2)]
  ring

end GivenBases

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem coordinateSplitBasis_angles (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (coordinateTriangleAngle g F (coordinateSplitBasis b ht false) 0 +
      coordinateTriangleAngle g F (coordinateSplitBasis b ht true) 0 =
        coordinateTriangleAngle g F b 0) ∧
    (coordinateTriangleAngle g F (coordinateSplitBasis b ht false) 2 +
      coordinateTriangleAngle g F (coordinateSplitBasis b ht true) 1 = Real.pi) := by
  have hl := (coordinateSplitBasis_hull_subset b ht false).trans hb
  have hr := (coordinateSplitBasis_hull_subset b ht true).trans hb
  exact ⟨coordinateTriangleAngle_split_vertex g F b _ _ hF hFi hb hl hr ht
      rfl rfl rfl rfl rfl rfl,
    coordinateTriangleAngle_split_edge g F b _ _ hF hl hr ht rfl rfl rfl rfl rfl rfl⟩



theorem coordinateSplitBasis_endpoint_angles (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    coordinateTriangleAngle g F (coordinateSplitBasis b ht false) 1 =
        coordinateTriangleAngle g F b 1 ∧
      coordinateTriangleAngle g F (coordinateSplitBasis b ht true) 2 =
        coordinateTriangleAngle g F b 2 := by
  have hl := (coordinateSplitBasis_hull_subset b ht false).trans hb
  have hr := (coordinateSplitBasis_hull_subset b ht true).trans hb
  have hv1 : AffineMap.lineMap (b 1) (b 2) t - b 1 = t • (b 2 - b 1) := by
    simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have hv2 : AffineMap.lineMap (b 1) (b 2) t - b 2 = (1 - t) • (b 1 - b 2) := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  constructor
  · change g.cornerAngle (F (b 1))
      (coordinateTriangleVelocity F (coordinateSplitBasis b ht false) 1 0)
      (coordinateTriangleVelocity F (coordinateSplitBasis b ht false) 1 2) =
      g.cornerAngle (F (b 1)) (coordinateTriangleVelocity F b 1 0)
        (coordinateTriangleVelocity F b 1 2)
    simp only [coordinateTriangleVelocity_eq_differential F _ hF hl,
      coordinateTriangleVelocity_eq_differential F b hF hb, coordinateSplitBasis_apply]
    change g.cornerAngle (F (b 1)) (mfderiv (𝓡 2) (𝓡 2) F (b 1) (b 0 - b 1))
      (mfderiv (𝓡 2) (𝓡 2) F (b 1) (AffineMap.lineMap (b 1) (b 2) t - b 1)) = _
    rw [hv1, map_smul, g.cornerAngle_smul_pos_right _ _ _ ht.1]
  · change g.cornerAngle (F (b 2))
      (coordinateTriangleVelocity F (coordinateSplitBasis b ht true) 2 0)
      (coordinateTriangleVelocity F (coordinateSplitBasis b ht true) 2 1) =
      g.cornerAngle (F (b 2)) (coordinateTriangleVelocity F b 2 0)
        (coordinateTriangleVelocity F b 2 1)
    simp only [coordinateTriangleVelocity_eq_differential F _ hF hr,
      coordinateTriangleVelocity_eq_differential F b hF hb, coordinateSplitBasis_apply]
    change g.cornerAngle (F (b 2)) (mfderiv (𝓡 2) (𝓡 2) F (b 2) (b 0 - b 2))
      (mfderiv (𝓡 2) (𝓡 2) F (b 2) (AffineMap.lineMap (b 1) (b 2) t - b 2)) = _
    rw [hv2, map_smul, g.cornerAngle_smul_pos_right _ _ _ (sub_pos.mpr ht.2)]

end PoincareConjecture.Topology.Surface
