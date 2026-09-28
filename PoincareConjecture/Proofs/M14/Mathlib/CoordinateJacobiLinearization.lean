import PoincareConjecture.Proofs.M14.Mathlib.CoordinateMetricTime
import PoincareConjecture.Proofs.M09.CoordinateJacobiCommutation
import PoincareConjecture.Proofs.M09.CoordinateEulerLinearization
import PoincareConjecture.Proofs.M08.WeightedJacobiCoefficients

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M14

open PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

set_option maxHeartbeats 800000 in

theorem coordinate_linearization_weightedJacobi
    (G : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (R : ℝ × E → ℝ) (U : Set (ℝ × E))
    (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hR : ContDiffOn ℝ ∞ R U)
    (hpos : ∀ z ∈ U, ∀ v : E, v ≠ 0 → 0 < G z v v)
    (hsym : ∀ z ∈ U, ∀ v w : E, G z v w = G z w v)
    (q Y : ℝ → E) (s : ℝ) (hz : (s, q s) ∈ U)
    (hq : DifferentiableAt ℝ q s) (hq2 : DifferentiableAt ℝ (deriv q) s)
    (hY : DifferentiableAt ℝ Y s) (hY2 : DifferentiableAt ℝ (deriv Y) s)
    (hphase : deriv (deriv q) s = (regularizedCoordinatePhase G R (s, (q s, deriv q s))).2)
    (hlinear : deriv (deriv Y) s =
      (fderiv ℝ (regularizedCoordinatePhase G R) (s, (q s, deriv q s))
        (0, (Y s, deriv Y s))).2) (W : E) :
    let C := coordinateConnectionBilinear G
    let P : E → E →L[ℝ] ℝ := fun x =>
      (fderiv ℝ R (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)
    let d : ℝ → E := fun r => deriv Y r + C (r, q r) (deriv q r) (Y r)
    G (s, q s) (deriv d s + C (s, q s) (deriv q s) (d s)) W -
      M08.weightedChartPotential (G (s, q s)) (C (s, q s))
        ((fderiv ℝ C (s, q s)).comp (ContinuousLinearMap.inr ℝ ℝ E))
        (fderiv ℝ C (s, q s) (1, 0)) ((2 * s ^ 2) • P (q s))
        ((2 * s ^ 2) • fderiv ℝ P (q s)) (deriv q s) (Y s) W +
      fderiv ℝ G (s, q s) (1, 0) (d s) W = 0 := by
  let C := coordinateConnectionBilinear G
  let H : E → E →L[ℝ] E →L[ℝ] ℝ := fun x => fderiv ℝ G (s, x) (1, 0)
  let P : E → E →L[ℝ] ℝ := fun x =>
    (fderiv ℝ R (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)
  let d : ℝ → E := fun r => deriv Y r + C (r, q r) (deriv q r) (Y r)
  have hC : DifferentiableAt ℝ C (s, q s) :=
    ((coordinateConnectionBilinear_contDiffOn G U hU hG hpos).contDiffAt
      (hU.mem_nhds hz)).differentiableAt (by simp)
  have hCs : ∀ᶠ z in 𝓝 (s, q s), ∀ v w, C z v w = C z w v := by
    filter_upwards [hU.mem_nhds hz] with z hz'
    intro v w
    exact coordinateConnection_symm G z
      ((hG.contDiffAt (hU.mem_nhds hz')).differentiableAt (by simp))
      (by filter_upwards [hU.mem_nhds hz'] with z' hz''; exact hsym z' hz'') v w
  have hcomm := coordinate_jacobi_commutation C q Y s hC hCs hq hq2 hY hY2
  dsimp only at hcomm
  rw [hphase, hlinear] at hcomm
  have hlin := regularizedCoordinatePhase_covariant_linearized_pairing G R U hU hG hR
    hpos hsym s (q s) hz (deriv q s) (Y s) (deriv Y s) W
  dsimp only at hlin
  rw [← hcomm] at hlin
  have htime := coordinateMetric_time_compatible G U hU hG hpos hsym s (q s) hz
    (Y s) (deriv q s) W
  dsimp only at htime
  rw [htime] at hlin
  have htime_sym := fderiv_bilinear_symm C (s, q s) hC hCs (1, 0) (deriv q s) (Y s)
  dsimp only
  rw [M08.weightedChartPotential_apply, M08.chartCurvatureAlong_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    smul_apply, smul_eq_mul, map_add, map_sub, add_apply, sub_apply] at hlin ⊢
  rw [htime_sym] at hlin
  linear_combination hlin

end PoincareConjecture.M14
