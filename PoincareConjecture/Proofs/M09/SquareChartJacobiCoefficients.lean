import PoincareConjecture.Proofs.M09.SpatialPartial
import PoincareConjecture.Proofs.M09.CenteredHessian
import PoincareConjecture.Proofs.M09.SquareChartConnectionTime

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem squareChartMetric_at_center {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (p : M) (s : ℝ) (v w : E) :
    squareChartMetric F T p (s, (chartAt E p) p) v w =
      (F.metric (T - s ^ 2)).inner p v w := by
  have hy := (chartAt E p).map_source (mem_chart_source E p)
  change (F.metric (T - s ^ 2)).inner ((chartAt E p).symm ((chartAt E p) p))
    (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm ((chartAt E p) p) v)
    (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm ((chartAt E p) p) w) = _
  rw [← chartVectorField_at_inverse p v ((chartAt E p) p) hy,
    ← chartVectorField_at_inverse p w ((chartAt E p) p) hy,
    (chartAt E p).left_inv (mem_chart_source E p), chartVectorField_self, chartVectorField_self]

set_option backward.isDefEq.respectTransparency false in
theorem squareChartScalar_hessian_at_center {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) (v w : E) :
    let C := coordinateConnectionBilinear (squareChartMetric F T p)
    let P : E → E →L[ℝ] ℝ := fun y ↦
      (fderiv ℝ (squareChartScalar F T p) (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)
    let y0 := (chartAt E p) p
    fderiv ℝ P y0 v w - P y0 (C (s, y0) v w) =
      (F.connection (T - s ^ 2)).hessian (F.connection (T - s ^ 2)).scalarCurvature p v w := by
  let Ω := Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt E p).target
  have hΩ : IsOpen Ω := isOpen_Ioo.prod (chartAt E p).open_target
  have hz : (s, (chartAt E p) p) ∈ Ω :=
    ⟨hs, (chartAt E p).map_source (mem_chart_source E p)⟩
  have hR := squareChartScalar_smooth F hM04 T b hb hwindow p
  have hRa := (hR.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp)
  have hi : ContMDiff (𝓡 n) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞
      (fun q : M ↦ (T - s ^ 2, q)) := contMDiff_const.prodMk contMDiff_id
  have hscalar0 := (hM04.scalar_regular n M J F).comp
    (hi.contMDiffOn (s := (chartAt E p).source))
    (fun q _ ↦ ⟨hwindow (squareTime_mem_window T hb hs), Set.mem_univ q⟩)
  have hscalar : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (F.connection (T - s ^ 2)).scalarCurvature (chartAt E p).source := by
    convert! hscalar0 using 1
  dsimp only
  rw [fderiv_spatialPartial_apply _ Ω hΩ hR s _ hz,
    hessian_centeredCoordinates _ _ p hscalar]
  rw [← fderiv_spatialSlice (squareChartScalar F T p) s ((chartAt E p) p) hRa,
    coordinateConnectionBilinear_apply, squareChartConnection_at_center F T b hb hwindow p s hs]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem squareChartMetric_time_covariant_at_center {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) (u v w : E) :
    let C := coordinateConnectionBilinear (squareChartMetric F T p)
    let H : E → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦
      fderiv ℝ (squareChartMetric F T p) (s, y) (1, 0)
    let y0 := (chartAt E p) p
    fderiv ℝ H y0 u v w - H y0 (C (s, y0) u v) w - H y0 v (C (s, y0) u w) =
      4 * s * ricciDerivativePairing (F.connection (T - s ^ 2)) p u v w := by
  dsimp only
  rw [squareChartMetric_time_space_at_center F hM04 T b hb hwindow p s hs,
    squareChartMetric_time_at_center F T b hb hwindow p s hs,
    squareChartMetric_time_at_center F T b hb hwindow p s hs,
    ricciDerivativePairing_centeredCoordinates hM04]
  simp only [coordinateConnectionBilinear_apply,
    squareChartConnection_at_center F T b hb hwindow p s hs]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem squareChartCurvature_bilinear_at_center {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) (u v w : E) :
    let C := coordinateConnectionBilinear (squareChartMetric F T p)
    let z := (s, (chartAt E p) p)
    ((F.connection (T - s ^ 2)).curvature p u v w : E) =
      fderiv ℝ C z (0, u) v w - fderiv ℝ C z (0, v) u w +
        C z u (C z v w) - C z v (C z u w) := by
  let C := coordinateConnectionBilinear (squareChartMetric F T p)
  let Ω := Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt E p).target
  have hΩ : IsOpen Ω := isOpen_Ioo.prod (chartAt E p).open_target
  have hz : (s, (chartAt E p) p) ∈ Ω :=
    ⟨hs, (chartAt E p).map_source (mem_chart_source E p)⟩
  have hC : DifferentiableAt ℝ C (s, (chartAt E p) p) :=
    ((coordinateConnectionBilinear_contDiffOn (squareChartMetric F T p) Ω hΩ
      (squareChartMetric_smooth F T b hb hwindow p)
      (fun z hz a ha ↦ squareChartMetric_pos F T p z hz.2 a ha)).contDiffAt
        (hΩ.mem_nhds hz)).differentiableAt (by simp)
  have h := squareChartCurvature_at_center F hM04 T b hb hwindow p s hs u v w
  change ((F.connection (T - s ^ 2)).curvature p u v w : E) =
    fderiv ℝ (fun y ↦ C (s, y) v w) ((chartAt E p) p) u -
      fderiv ℝ (fun y ↦ C (s, y) u w) ((chartAt E p) p) v +
      C (s, (chartAt E p) p) u (C (s, (chartAt E p) p) v w) -
      C (s, (chartAt E p) p) v (C (s, (chartAt E p) p) u w) at h
  rw [fderiv_spatial_bilinear_apply C s _ u v w hC,
    fderiv_spatial_bilinear_apply C s _ v u w hC] at h
  exact h

end PoincareConjecture.Proofs.M09
