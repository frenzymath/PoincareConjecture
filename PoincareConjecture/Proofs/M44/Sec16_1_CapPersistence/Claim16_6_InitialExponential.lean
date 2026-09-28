import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_NormalizedComparison
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_GeodesicTransport
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.RadialCurve

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta : ℝ}

structure NormalizedCapExponential (Q : SurgeryCapClose g₀ S g tip scale eta) (R : ℝ) where
  radius_pos : 0 < R
  map : E → S.carrier
  frame : E ≃L[ℝ] E
  frame_inner : ∀ v w, Q.normalizedMetric.pullbackCoefficients
    (extChartAt (𝓡 3) tip).symm (extChartAt (𝓡 3) tip tip) (frame v) (frame w) = inner ℝ v w
  smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ map (Metric.ball 0 R)
  map_zero : map 0 = tip
  initial_derivative : HasFDerivAt (fun v => extChartAt (𝓡 3) tip (map v))
    frame.toContinuousLinearMap 0
  geodesic : ∀ v ∈ Metric.ball 0 R,
    Q.normalizedMetric.IsGeodesicOn (fun t : ℝ => map (t • v))
      {t | t • v ∈ Metric.ball 0 R}
  distance_bound : ∀ v ∈ Metric.ball 0 R, ∀ t ∈ Icc (0 : ℝ) 1,
    Q.normalizedMetric.edist tip (map (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t
  map_mem : ∀ v ∈ Metric.ball 0 R, map v ∈ Q.map '' g₀.metric.ball 0 eta⁻¹

theorem exists_normalizedCapExponential
    (Q : SurgeryCapClose g₀ S g tip scale eta) {R : ℝ} (hR : 0 < R)
    (hReta : R ≤ eta⁻¹) (hcompact : IsCompact (closure (Q.normalizedMetric.ball tip R))) :
    Nonempty (NormalizedCapExponential Q R) := by
  obtain ⟨L, e, hL, he, he0, heD, hgeo⟩ :=
    Q.normalizedMetric.exists_orthonormal_radial_exponential_of_precompact_ball tip hR hcompact
  refine ⟨{
    radius_pos := hR
    map := e
    frame := L
    frame_inner := hL
    smooth := he
    map_zero := he0
    initial_derivative := heD
    geodesic := fun v hv => (hgeo v hv).1
    distance_bound := fun v hv t ht => ((hgeo v hv).2 t ht).2
    map_mem := ?_ }⟩
  intro v hv
  apply Q.normalizedComparison.image_contains
  have hd := ((hgeo v hv).2 1 (by simp)).2
  simp only [one_smul, ENNReal.ofReal_one, mul_one] at hd
  have hvR : ‖v‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  change Q.normalizedMetric.edist tip (e v) < ENNReal.ofReal (1 * eta⁻¹)
  simpa only [one_mul] using hd.trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr Q.eta_pos)).mpr (hvR.trans_le hReta))

theorem exists_normalizedCapExponential_of_buffer
    (Q : SurgeryCapClose g₀ S g tip scale eta) (heta : eta < 1)
    {r R : ℝ} (hr : 0 < r) (hrEta : r < eta⁻¹) (hR : 0 < R)
    (hRr : R ≤ Real.sqrt (1 - eta) * r) : Nonempty (NormalizedCapExponential Q R) := by
  have hroot : Real.sqrt (1 - eta) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [Q.eta_pos])
  have hReta : R ≤ eta⁻¹ := hRr.trans
    ((mul_le_mul_of_nonneg_right hroot hr.le).trans (by simpa only [one_mul] using hrEta.le))
  have hcompact : IsCompact (closure (Q.normalizedMetric.ball tip R)) :=
    (Q.isCompact_closure_normalized_ball heta hr hrEta).of_isClosed_subset isClosed_closure
      (closure_mono (fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal hRr)))
  exact exists_normalizedCapExponential Q hR hReta hcompact

theorem exists_initial_exponential_threshold (R : ℝ) (hR : 0 < R) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (g₀ : StandardInitialMetric)
      (S : GeneralizedSliceCarrier.{u}) (g : RiemannianMetric 3 S.carrier)
      (tip : S.carrier) (scale eta : ℝ) (Q : SurgeryCapClose g₀ S g tip scale eta),
      eta ≤ delta → Nonempty (NormalizedCapExponential Q R) := by
  have hden : 0 < 2 * R + 2 := by linarith
  refine ⟨min (1 / 2) (2 * R + 2)⁻¹, lt_min (by norm_num) (inv_pos.mpr hden), ?_⟩
  intro g₀ S g tip scale eta Q heta
  have hhalf : eta ≤ 1 / 2 := heta.trans (min_le_left _ _)
  have hinv := one_div_le_one_div_of_le Q.eta_pos (heta.trans (min_le_right _ _))
  simp only [one_div, inv_inv] at hinv
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - eta) := Real.le_sqrt_of_sq_le (by nlinarith)
  apply exists_normalizedCapExponential_of_buffer Q (by linarith) (r := 2 * R + 1)
    (by linarith) (by linarith) hR
  calc
    R ≤ (1 / 2) * (2 * R + 1) := by linarith
    _ ≤ Real.sqrt (1 - eta) * (2 * R + 1) :=
      mul_le_mul_of_nonneg_right hroot (by linarith)

namespace NormalizedCapExponential

variable {Q : SurgeryCapClose g₀ S g tip scale eta} {R : ℝ}

noncomputable def coordinateMap (D : NormalizedCapExponential Q R) : E → E := Q.inverse ∘ D.map

theorem coordinateMap_smooth (D : NormalizedCapExponential Q R) :
    ContDiffOn ℝ ∞ D.coordinateMap (Metric.ball 0 R) := by
  apply contMDiffOn_iff_contDiffOn.mp
  exact Q.inverse_smooth.comp D.smooth D.map_mem

theorem coordinateMap_zero (D : NormalizedCapExponential Q R) : D.coordinateMap 0 = 0 := by
  have h0 : (0 : E) ∈ g₀.metric.ball 0 eta⁻¹ := by
    rw [M36.standard_ball_eq_euclidean g₀ (inv_pos.mpr Q.eta_pos)]
    exact Metric.mem_ball_self ((M36.radialEuclideanRadius_pos_iff g₀ _).mpr
      (inv_pos.mpr Q.eta_pos))
  change Q.inverse (D.map 0) = 0
  exact (congrArg Q.inverse D.map_zero).trans
    ((congrArg Q.inverse Q.map_tip.symm).trans (Q.left_inverse h0))

noncomputable def phase (D : NormalizedCapExponential Q R) (z : E × ℝ) : E × E :=
  (D.coordinateMap (z.2 • z.1), fderiv ℝ D.coordinateMap (z.2 • z.1) z.1)

theorem phase_eq_curve_velocity (D : NormalizedCapExponential Q R)
    {v : E} {t : ℝ} (ht : t • v ∈ Metric.ball 0 R) :
    D.phase (v, t) =
      (D.coordinateMap (t • v), deriv (fun s => D.coordinateMap (s • v)) t) := by
  have hd := (D.coordinateMap_smooth.contDiffAt (Metric.isOpen_ball.mem_nhds ht)).differentiableAt
    (by simp)
  have hcurve := hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const v)
  refine Prod.ext rfl ?_
  simpa only [phase, Function.comp_def, id_eq, one_smul] using hcurve.deriv.symm

theorem phase_smooth (D : NormalizedCapExponential Q R) :
    ContDiffOn ℝ ∞ D.phase {z : E × ℝ | z.2 • z.1 ∈ Metric.ball 0 R} := by
  intro z hz
  have harg : ContDiffAt ℝ ∞ (fun p : E × ℝ => p.2 • p.1) z := by fun_prop
  have hmap := D.coordinateMap_smooth.contDiffAt (Metric.isOpen_ball.mem_nhds hz)
  have hphase : ContDiffAt ℝ ∞ D.phase z := (hmap.comp z harg).prodMk
    (((hmap.fderiv_right (m := ∞) (by simp)).comp z harg).clm_apply contDiffAt_fst)
  exact hphase.contDiffWithinAt

theorem phase_initial (D : NormalizedCapExponential Q R) (v : E) :
    D.phase (v, 0) = (0, fderiv ℝ D.coordinateMap 0 v) := by
  simp only [phase, zero_smul, D.coordinateMap_zero]

theorem coordinate_phase_hasDerivAt (D : NormalizedCapExponential Q R)
    {v : E} (hv : v ∈ Metric.ball 0 R) {t : ℝ} (ht : t • v ∈ Metric.ball 0 R) :
    HasDerivAt (fun s => (D.coordinateMap (s • v), deriv (fun u => D.coordinateMap (u • v)) s))
      (coordinateGeodesicField Q.normalizedCoefficients
        (D.coordinateMap (t • v), deriv (fun u => D.coordinateMap (u • v)) t)) t :=
  Q.hasDerivAt_normalized_geodesic_phase (D.geodesic v hv) ht (D.map_mem _ ht)

theorem phase_hasDerivAt (D : NormalizedCapExponential Q R)
    {v : E} (hv : v ∈ Metric.ball 0 R) {t : ℝ} (ht : t • v ∈ Metric.ball 0 R) :
    HasDerivAt (fun s => D.phase (v, s))
      (coordinateGeodesicField Q.normalizedCoefficients (D.phase (v, t))) t := by
  have hcont : ContinuousAt (fun s : ℝ => s • v) t := by fun_prop
  have heq : (fun s => D.phase (v, s)) =ᶠ[𝓝 t]
      (fun s => (D.coordinateMap (s • v), deriv (fun u => D.coordinateMap (u • v)) s)) := by
    filter_upwards [hcont.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds ht)] with s hs
    exact D.phase_eq_curve_velocity hs
  rw [D.phase_eq_curve_velocity ht]
  exact (D.coordinate_phase_hasDerivAt hv ht).congr_of_eventuallyEq heq

end NormalizedCapExponential

end PoincareConjecture.M44
