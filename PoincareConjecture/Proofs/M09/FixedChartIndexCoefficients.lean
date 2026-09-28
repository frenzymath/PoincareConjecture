import PoincareConjecture.Proofs.M09.FixedChartHessian
import PoincareConjecture.Proofs.M09.CoordinateIndexDensity
import PoincareConjecture.Proofs.M09.SquareChartJacobiCoefficients
import PoincareConjecture.Proofs.M09.HessianTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem squareChartIndexHessian_on_target {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (y : E) (hy : y ∈ (chartAt E p).target) (v w : E) :
    coordinateIndexHessian (squareChartMetric F T p) (squareChartScalar F T p) (s, y) v w =
      (F.connection (T - s ^ 2)).hessian (F.connection (T - s ^ 2)).scalarCurvature
        ((chartAt E p).symm y) (chartVectorField p v ((chartAt E p).symm y))
        (chartVectorField p w ((chartAt E p).symm y)) := by
  let e := chartAt E p
  let q := e.symm y
  let Ω := Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ e.target
  have hΩ : IsOpen Ω := isOpen_Ioo.prod e.open_target
  have hz : (s, y) ∈ Ω := ⟨hs, hy⟩
  let R := squareChartScalar F T p
  let Q := coordinateScalarPartial R
  let C := coordinateConnectionBilinear (squareChartMetric F T p)
  have hR := squareChartScalar_smooth F hM04 T b hb hwindow p
  have hQ : ContDiffOn ℝ ∞ Q Ω :=
    (hR.fderiv_of_isOpen hΩ (by simp)).clm_comp contDiffOn_const
  have hscalar : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (F.connection (T - s ^ 2)).scalarCurvature e.source :=
    (scalarCurvature_contMDiff hM04 (F.connection (T - s ^ 2))).contMDiffOn
  have hconn (a : E) : (F.connection (T - s ^ 2)).connection (chartVectorField p a) q
      (chartVectorField p v q) = chartVectorField p (C (s, y) v a) q :=
    (squareChartConnection_eq F T b hb hwindow p s hs y hy v a).symm
  have hh := hessian_fixedChart (F.connection (T - s ^ 2))
    (F.connection (T - s ^ 2)).scalarCurvature p q (e.map_target hy) hscalar v w (C (s, y) v) hconn
  dsimp only at hh
  rw [e.right_inv hy] at hh
  let φ : E → ℝ := fun z ↦ R (s, z)
  have hgerm : (fun z ↦ Q (s, z)) =ᶠ[𝓝 y] fderiv ℝ φ := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz'
    exact (fderiv_spatialSlice R s z
      ((hR.contDiffAt (hΩ.mem_nhds ⟨hs, hz'⟩)).differentiableAt (by simp))).symm
  have hQd := (hQ.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp)
  have hsecond : fderiv ℝ Q (s, y) (0, v) w = fderiv ℝ (fderiv ℝ φ) y v w := by
    have h := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ ↦ L v w) hgerm.fderiv_eq
    rw [fderiv_spatialSlice Q s y hQd] at h
    exact h
  change fderiv ℝ Q (s, y) (0, v) w - Q (s, y) (C (s, y) v w) = _
  rw [hsecond, hgerm.eq_of_nhds, hh]
  rfl

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem squareChartTimeCovariant_on_target {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (y : E) (hy : y ∈ (chartAt E p).target) (u v w : E) :
    coordinateTimeCovariant (squareChartMetric F T p) (s, y) u v w =
      4 * s * ricciDerivativePairing (F.connection (T - s ^ 2)) ((chartAt E p).symm y)
        (chartVectorField p u ((chartAt E p).symm y))
        (chartVectorField p v ((chartAt E p).symm y))
        (chartVectorField p w ((chartAt E p).symm y)) := by
  let e := chartAt E p
  let q := e.symm y
  let D := F.connection (T - s ^ 2)
  let Ω := Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ e.target
  have hΩ : IsOpen Ω := isOpen_Ioo.prod e.open_target
  let C := coordinateConnectionBilinear (squareChartMetric F T p)
  let H := coordinateMetricTimePartial (squareChartMetric F T p)
  have hRic := (hM04.tensor_calculus n M (F.metric (T - s ^ 2)) D).2.1
  let B := chartTensorBilinear D.ricciEvaluation hRic p
  have hB := chartTensorBilinear_smooth D.ricciEvaluation hRic p
  have hBs : ContDiffOn ℝ ∞ (fun z ↦ B (e.symm z)) e.target :=
    (hB.comp contMDiffOn_chart_symm (fun z hz ↦ e.map_target hz)).contDiffOn
  have hBsd := (hBs.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have hH : ContDiffOn ℝ ∞ H Ω :=
    ((squareChartMetric_smooth F T b hb hwindow p).fderiv_of_isOpen hΩ
      (by simp)).clm_apply contDiffOn_const
  have hHvalue (z : E) (hz : z ∈ e.target) : H (s, z) = (4 * s) • B (e.symm z) := by
    ext a c
    change H (s, z) a c = (4 * s) * chartTensorBilinear D.ricciEvaluation hRic p (e.symm z) a c
    rw [chartTensorBilinear_apply]
    change fderiv ℝ (squareChartMetric F T p) (s, z) (1, 0) a c =
      (4 * s) * D.ricci (e.symm z) (chartVectorField p a (e.symm z))
        (chartVectorField p c (e.symm z))
    rw [squareChartMetric_time_pairing F T b hb hwindow p s hs z a c hz,
      chartVectorField_at_inverse p a z hz, chartVectorField_at_inverse p c z hz]
  have hHgerm : (fun z ↦ H (s, z)) =ᶠ[𝓝 y] (fun z ↦ (4 * s) • B (e.symm z)) := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact hHvalue z hz
  have hHder : fderiv ℝ H (s, y) (0, u) v w =
      (4 * s) * (fderiv ℝ (fun z ↦ B (e.symm z)) y u v w) := by
    have h := (hBsd.hasFDerivAt.const_smul (4 * s)).fderiv
    change fderiv ℝ (fun z ↦ (4 * s) • B (e.symm z)) y =
      (4 * s) • fderiv ℝ (fun z ↦ B (e.symm z)) y at h
    rw [← hHgerm.fderiv_eq (𝕜 := ℝ), fderiv_spatialSlice H s y
      ((hH.contDiffAt (hΩ.mem_nhds ⟨hs, hy⟩)).differentiableAt (by simp))] at h
    exact congrArg (fun L : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ ↦ L u v w) h
  have hconn (a : E) : D.connection (chartVectorField p a) q (chartVectorField p u q) =
      chartVectorField p (C (s, y) u a) q :=
    (squareChartConnection_eq F T b hb hwindow p s hs y hy u a).symm
  have hcov := covariantTensorDerivative_fixedChart D D.ricciEvaluation hRic p q
    (e.map_target hy) (chartVectorField p u q) (C (s, y) u) hconn v w
  have hchain := mvfderiv_chartVectorField_normed p B y u hy
    ((hB.contMDiffAt (e.open_source.mem_nhds (e.map_target hy))).mdifferentiableAt (by simp))
  change ricciDerivativePairing D q (chartVectorField p u q) (chartVectorField p v q)
      (chartVectorField p w q) = mvfderiv (𝓡 n) B q (chartVectorField p u q) v w -
        B q (C (s, y) u v) w - B q v (C (s, y) u w) at hcov
  rw [hchain] at hcov
  change fderiv ℝ H (s, y) (0, u) v w - H (s, y) (C (s, y) u v) w -
      H (s, y) v (C (s, y) u w) = _
  rw [hHder, hHvalue y hy, hcov]
  simp only [smul_apply, smul_eq_mul]
  ring

end PoincareConjecture.Proofs.M09
