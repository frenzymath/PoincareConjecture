import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.BoundarySum









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.Topology.Surface.FiniteSmoothTriangulation

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [T3Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  [IsManifold (𝓡 2) ∞ S] [CompactSpace S]




theorem integral_scalarCurvature_eq_metric_corner_sum
    (T : FiniteSmoothTriangulation (M := S))
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (F : T.faces → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : T.faces → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hF : ∀ f, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F f) (F f).source)
    (hFi : ∀ f, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F f).symm (F f).target)
    (hb : ∀ f, convexHull ℝ (range (b f)) ⊆ (F f).source)
    (hcarrier : ∀ f, (T.face f).carrier = F f '' convexHull ℝ (range (b f)))
    (hside : ∀ f k, ((T.face f).boundary k).map '' Icc (0 : ℝ) 1 =
      F f '' affineSegment ℝ (b f (k.succAbove 0)) (b f (k.succAbove 1))) :
    letI := T.faces_finite
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) =
      2 * (∑ f, ∑ i : Fin 3, coordinateTriangleAngle g (F f) (b f) i) -
        2 * Real.pi * Fintype.card T.faces := by
  let _ := T.faces_finite
  let Q := fun f => g.alignedChartFrame (coordinateTriangleChart (F f) (b f))
    (coordinateTriangleChart_smooth (F f) (b f) (hFi f))
    (coordinateTriangleChart_smooth_symm (F f) (b f) (hF f))
  have hboundary := T.sum_coordinateTurningIntegral_eq_zero D F b hF hFi hb hcarrier hside Q
  have hint : (∑ f, ∫ x in F f '' convexHull ℝ (range (b f)),
      D.scalarCurvature x ∂g.volumeMeasure) = ∫ x, D.scalarCurvature x ∂g.volumeMeasure := by
    rw [T.integral_scalarCurvature_eq_sum_faces g D]
    apply Finset.sum_congr rfl
    intro f _
    rw [hcarrier f]
  have hsum : (∑ f,
      ((∫ x in F f '' convexHull ℝ (range (b f)), D.scalarCurvature x ∂g.volumeMeasure) +
        2 * (∑ i : Fin 3, coordinateTriangleTurningIntegral D (F f) (b f) (Q f) i (i + 1)) +
        2 * (∑ i : Fin 3, (Real.pi - coordinateTriangleAngle g (F f) (b f) i)))) =
      ∑ _f : T.faces, 4 * Real.pi :=
    Finset.sum_congr rfl (fun f _ =>
      gaussBonnet_coordinateTriangle_side_integrals D (F f) (b f) (hF f) (hFi f) (hb f) (Q f))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  rw [hint, hboundary, mul_zero, add_zero] at hsum
  have hcorners : (∑ f, ∑ i : Fin 3, (Real.pi - coordinateTriangleAngle g (F f) (b f) i)) =
      3 * Real.pi * Fintype.card T.faces -
        ∑ f, ∑ i : Fin 3, coordinateTriangleAngle g (F f) (b f) i := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hcorners] at hsum
  linarith

end PoincareConjecture.Topology.Surface.FiniteSmoothTriangulation
