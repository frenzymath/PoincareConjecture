import PoincareConjecture.Proofs.M09.FixedChartIndexCoefficients
import PoincareConjecture.Proofs.M09.FixedChartCurvature
import PoincareConjecture.Proofs.M09.AdaptedIndexTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem squareChartIndexCurvature_on_target {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (y : E) (hy : y ∈ (chartAt E p).target) (u v w : E) :
    (F.connection (T - s ^ 2)).curvature ((chartAt E p).symm y)
        (chartVectorField p u ((chartAt E p).symm y))
        (chartVectorField p v ((chartAt E p).symm y))
        (chartVectorField p w ((chartAt E p).symm y)) =
      chartVectorField p (coordinateIndexCurvature (squareChartMetric F T p) (s, y) u v w)
        ((chartAt E p).symm y) := by
  let C := coordinateConnectionBilinear (squareChartMetric F T p)
  let Ω := Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt E p).target
  have hC : DifferentiableAt ℝ C (s, y) :=
    ((coordinateConnectionBilinear_contDiffOn (squareChartMetric F T p) Ω
      (isOpen_Ioo.prod (chartAt E p).open_target)
      (squareChartMetric_smooth F T b hb hwindow p)
      (fun z hz a ha ↦ squareChartMetric_pos F T p z hz.2 a ha)).contDiffAt
      ((isOpen_Ioo.prod (chartAt E p).open_target).mem_nhds ⟨hs, hy⟩)).differentiableAt
        (by simp)
  have h := squareChartCurvature_on_target F hM04 T b hb hwindow p s hs y hy u v w
  dsimp only [coefficientCurvature] at h
  rw [fderiv_spatialSlice C s y hC] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem squareChartMetric_on_target {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (p : M) (s : ℝ) (y : E) (hy : y ∈ (chartAt E p).target) (v w : E) :
    squareChartMetric F T p (s, y) v w =
      (F.metric (T - s ^ 2)).inner ((chartAt E p).symm y)
        (chartVectorField p v ((chartAt E p).symm y))
        (chartVectorField p w ((chartAt E p).symm y)) := by
  rw [chartVectorField_at_inverse p v y hy, chartVectorField_at_inverse p w y hy]
  rfl

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem squareChartIndexDensity_on_target {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (y : E) (hy : y ∈ (chartAt E p).target) (a v w : E) :
    coordinateIndexDensity (squareChartMetric F T p) (squareChartScalar F T p) (s, y) a v w =
      pointwiseSecondVariationDensity F T ((chartAt E p).symm y) s
        (chartVectorField p a ((chartAt E p).symm y))
        (chartVectorField p v ((chartAt E p).symm y))
        (chartVectorField p w ((chartAt E p).symm y)) := by
  let q := (chartAt E p).symm y
  let D := F.connection (T - s ^ 2)
  have hcurv : squareChartMetric F T p (s, y)
      (coordinateIndexCurvature (squareChartMetric F T p) (s, y) v a v) a =
      D.curvatureTensor q (chartVectorField p v q) (chartVectorField p a q)
        (chartVectorField p a q) (chartVectorField p v q) := by
    rw [squareChartMetric_on_target F T p s y hy,
      ← squareChartIndexCurvature_on_target F hM04 T b hb hwindow p s hs y hy v a v]
    rfl
  unfold coordinateIndexDensity pointwiseSecondVariationDensity
  rw [hcurv, squareChartMetric_on_target F T p s y hy,
    squareChartIndexHessian_on_target F hM04 T b hb hwindow p s hs y hy,
    squareChartTimeCovariant_on_target F hM04 T b hb hwindow p s hs y hy,
    squareChartTimeCovariant_on_target F hM04 T b hb hwindow p s hs y hy]
  ring

end PoincareConjecture.Proofs.M09
