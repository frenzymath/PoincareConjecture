import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.AdjacentCancellation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.Cancellation







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set VectorField
open scoped Manifold ContDiff Bundle Interval

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]



theorem chartTriangle_open_image_subset_interior
    (e : OpenPartialHomeomorph S (ℝ × ℝ))
    (ht : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} ⊆ e.target) :
    e.symm '' {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1} ⊆
      interior (e.symm '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}) := by
  have hsub : {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1} ⊆
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} :=
    fun _ h => ⟨h.1.le, h.2.1.le, h.2.2.le⟩
  have hopen : IsOpen {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1} :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))
  exact interior_maximal (image_mono hsub)
    (e.isOpen_image_symm_of_subset_target hopen (hsub.trans ht))



theorem coordinateTriangle_disjoint_open_images
    (F G : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (hc : convexHull ℝ (range c) ⊆ G.source)
    (hdisjoint : Disjoint (interior (F '' convexHull ℝ (range b)))
      (interior (G '' convexHull ℝ (range c)))) :
    Disjoint ((coordinateTriangleChart F b).symm ''
      {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1})
      ((coordinateTriangleChart G c).symm ''
        {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}) := by
  apply hdisjoint.mono
  · simpa only [coordinateTriangleChart_image] using
      chartTriangle_open_image_subset_interior (coordinateTriangleChart F b)
        (coordinateTriangleChart_target F b hb)
  · simpa only [coordinateTriangleChart_image] using
      chartTriangle_open_image_subset_interior (coordinateTriangleChart G c)
        (coordinateTriangleChart_target G c hc)

variable [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem integral_coordinateTriangle_shared_vertical_side_pair_eq_zero
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (F G : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b c : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hG : ContMDiffOn (𝓡 2) (𝓡 2) ∞ G G.source)
    (hGi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ G.symm G.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (hc : convexHull ℝ (range c) ⊆ G.source)
    (Q : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart F b))
    (R : RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart G c))
    (himage : (fun t : ℝ => G (AffineMap.lineMap (c 0) (c 2) t)) '' Icc (0 : ℝ) 1 =
      (fun t : ℝ => F (AffineMap.lineMap (b 0) (b 2) t)) '' Icc (0 : ℝ) 1)
    (hdisjoint : Disjoint (interior (F '' convexHull ℝ (range b)))
      (interior (G '' convexHull ℝ (range c)))) :
    (∫ t in (0 : ℝ)..1, D.surfaceTurningForm R.first R.second
      (coordinateTriangleSecondUnitField g G c) (coordinateTriangleSecondField G c)
      (G (AffineMap.lineMap (c 0) (c 2) t))) +
    (∫ t in (0 : ℝ)..1, D.surfaceTurningForm Q.first Q.second
      (coordinateTriangleSecondUnitField g F b) (coordinateTriangleSecondField F b)
      (F (AffineMap.lineMap (b 0) (b 2) t))) = 0 := by
  have het (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (0, t) ∈ (coordinateTriangleChart F b).target :=
    coordinateTriangleChart_target F b hb (by simpa using And.intro (le_refl (0 : ℝ)) ht)
  have hft (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (0, t) ∈ (coordinateTriangleChart G c).target :=
    coordinateTriangleChart_target G c hc (by simpa using And.intro (le_refl (0 : ℝ)) ht)
  have himage' : (fun t : ℝ => (coordinateTriangleChart G c).symm (0, t)) '' Icc (0 : ℝ) 1 =
      (fun t : ℝ => (coordinateTriangleChart F b).symm (0, t)) '' Icc (0 : ℝ) 1 := by
    simpa only [coordinateTriangle_second_map] using himage
  have h := integral_chartTriangle_shared_side_pair_eq_zero D
    (coordinateTriangleChart F b) (coordinateTriangleChart G c)
    (coordinateTriangleChart_smooth F b hFi) (coordinateTriangleChart_smooth_symm F b hF)
    (coordinateTriangleChart_smooth G c hGi) (coordinateTriangleChart_smooth_symm G c hG)
    Q R het hft himage' (coordinateTriangle_disjoint_open_images F G b c hb hc hdisjoint)
  change (∫ t in (0 : ℝ)..1, D.surfaceTurningForm R.first R.second
      (coordinateTriangleSecondUnitField g G c) (coordinateTriangleSecondField G c)
      ((coordinateTriangleChart G c).symm (0, t))) +
    (∫ t in (0 : ℝ)..1, D.surfaceTurningForm Q.first Q.second
      (coordinateTriangleSecondUnitField g F b) (coordinateTriangleSecondField F b)
      ((coordinateTriangleChart F b).symm (0, t))) = 0 at h
  simpa only [coordinateTriangle_second_map] using h

end PoincareConjecture.Topology.Surface
