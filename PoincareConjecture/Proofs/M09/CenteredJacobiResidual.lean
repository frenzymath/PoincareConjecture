import PoincareConjecture.Proofs.M09.SquareChartJacobiCoefficients
import PoincareConjecture.Proofs.M09.CoordinateJacobiCommutation
import PoincareConjecture.Proofs.M09.CoordinateEulerLinearization

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem centered_coordinate_jacobi_residual {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (x Y : ℝ → E) (s : ℝ)
    (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hxcenter : x s = (chartAt E p) p)
    (hx : DifferentiableAt ℝ x s) (hx2 : DifferentiableAt ℝ (deriv x) s)
    (hY : DifferentiableAt ℝ Y s) (hY2 : DifferentiableAt ℝ (deriv Y) s)
    (hphase : deriv (deriv x) s =
      (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
        (s, (x s, deriv x s))).2)
    (hlinear : deriv (deriv Y) s =
      (fderiv ℝ (regularizedCoordinatePhase (squareChartMetric F T p)
        (squareChartScalar F T p)) (s, (x s, deriv x s)) (0, (Y s, deriv Y s))).2)
    (W : E) :
    let C := coordinateConnectionBilinear (squareChartMetric F T p)
    let d : ℝ → E := fun r ↦ deriv Y r + C (r, x r) (deriv x r) (Y r)
    let D := F.connection (T - s ^ 2)
    (F.metric (T - s ^ 2)).inner p (deriv d s + C (s, x s) (deriv x s) (d s)) W +
      D.curvatureTensor p (Y s) (deriv x s) W (deriv x s) -
      2 * s * backwardConnectionVariationPairing D p (deriv x s) (Y s) W -
      2 * s ^ 2 * D.hessian D.scalarCurvature p (Y s) W +
      4 * s * ricciDerivativePairing D p (Y s) (deriv x s) W +
      4 * s * D.ricci p (d s) W = 0 := by
  let G := squareChartMetric F T p
  let R := squareChartScalar F T p
  let C := coordinateConnectionBilinear G
  let Ω := Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt E p).target
  have hΩ : IsOpen Ω := isOpen_Ioo.prod (chartAt E p).open_target
  have hz : (s, x s) ∈ Ω := by
    rw [hxcenter]
    exact ⟨hs, (chartAt E p).map_source (mem_chart_source E p)⟩
  have hG := squareChartMetric_smooth F T b hb hwindow p
  have hR := squareChartScalar_smooth F hM04 T b hb hwindow p
  have hpos : ∀ z ∈ Ω, ∀ v : E, v ≠ 0 → 0 < G z v v :=
    fun z hz v hv ↦ squareChartMetric_pos F T p z hz.2 v hv
  have hC : DifferentiableAt ℝ C (s, x s) :=
    ((coordinateConnectionBilinear_contDiffOn G Ω hΩ hG hpos).contDiffAt
      (hΩ.mem_nhds hz)).differentiableAt (by simp)
  have hCs : ∀ᶠ z in 𝓝 (s, x s), ∀ v w, C z v w = C z w v := by
    filter_upwards [hΩ.mem_nhds hz] with z hz'
    exact fun v w ↦ coordinateConnection_symm G z
      ((hG.contDiffAt (hΩ.mem_nhds hz')).differentiableAt (by simp))
      (Eventually.of_forall (fun z v w ↦ squareChartMetric_symm F T p z v w)) v w
  have hcomm := coordinate_jacobi_commutation C x Y s hC hCs hx hx2 hY hY2
  dsimp only at hcomm
  rw [hphase, hlinear] at hcomm
  have hlin := regularizedCoordinatePhase_covariant_linearized_pairing G R Ω hΩ hG hR hpos
    (fun z _ v w ↦ squareChartMetric_symm F T p z v w) s (x s) hz
    (deriv x s) (Y s) (deriv Y s) W
  dsimp only at hlin
  rw [← hcomm, hxcenter] at hlin
  have hcurv := squareChartCurvature_bilinear_at_center F hM04 T b hb hwindow p s hs
    (Y s) (deriv x s) (deriv x s)
  dsimp only at hcurv
  rw [← hcurv] at hlin
  rw [squareChartScalar_hessian_at_center F hM04 T b hb hwindow p s hs,
    squareChartMetric_time_covariant_at_center F hM04 T b hb hwindow p s hs,
    squareChartMetric_time_at_center F T b hb hwindow p s hs] at hlin
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply] at hlin
  rw [squareChartConnection_time_at_center F hM04 T b hb hwindow p s hs] at hlin
  simp only [G, squareChartMetric_at_center] at hlin
  dsimp only
  rw [hxcenter]
  simpa only [LeviCivitaData.curvatureTensor, C, map_add, add_apply,
    inner_add_left, add_assoc] using hlin

end PoincareConjecture.Proofs.M09
