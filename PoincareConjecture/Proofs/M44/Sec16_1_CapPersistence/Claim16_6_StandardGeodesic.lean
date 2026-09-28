import PoincareConjecture.Proofs.M44.Mathlib.RadialDirection
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_ExponentialBalls
import PoincareConjecture.Proofs.M36.StandardBalls
import PoincareConjecture.Proofs.M36.RadialEquality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace

namespace PoincareConjecture.M44

open M36 RiemannianMetric

theorem standard_radial_arclength_nonneg (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) : 0 ≤ radialArclength g₀ ‖x‖ := by
  simpa only [radialArclength_zero] using
    (radialArclength_strictMono g₀).monotone (norm_nonneg x)

theorem standard_segment_radial_arclength (g₀ : StandardInitialMetric)
    {γ : ℝ → StandardCapSpace} {x : StandardCapSpace} (hγ0 : γ 0 = 0)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g₀.metric.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g₀.metric.edist 0 x)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    radialArclength g₀ ‖γ t‖ = t * radialArclength g₀ ‖x‖ := by
  have h := hmin 0 (by simp) t ht
  rw [hγ0, standard_edist_zero, standard_edist_zero, zero_sub, abs_neg,
    abs_of_nonneg ht.1, ← ENNReal.ofReal_mul ht.1] at h
  exact (ENNReal.ofReal_eq_ofReal_iff
    (standard_radial_arclength_nonneg g₀ (γ t))
    (mul_nonneg ht.1 (standard_radial_arclength_nonneg g₀ x))).mp h

theorem standard_geodesic_hasDerivAt (g₀ : StandardInitialMetric)
    {γ : ℝ → StandardCapSpace} {I : Set ℝ}
    (hγ : g₀.metric.IsGeodesicOn γ I) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt γ (deriv γ t) t := by
  exact ((contMDiffAt_iff_contDiffAt.mp (hγ.contMDiffAt ht)).differentiableAt
    (by simp)).hasDerivAt

theorem standard_segment_energy (g₀ : StandardInitialMetric)
    {γ : ℝ → StandardCapSpace} {x : StandardCapSpace} {ε : ℝ}
    (hε : 0 < ε) (hγ : g₀.metric.IsGeodesicOn γ (Ioo (-ε) (1 + ε)))
    (hγ0 : γ 0 = 0)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g₀.metric.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g₀.metric.edist 0 x)
    {t : ℝ} (ht : t ∈ Ioo (-ε) (1 + ε)) :
    g₀.metric.inner (γ t) (deriv γ t) (deriv γ t) =
      (radialArclength g₀ ‖x‖) ^ 2 := by
  have hzero : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  have hv : HasDerivAt (fun s => extChartAt (𝓡 3) (0 : StandardCapSpace) (γ s))
      (deriv γ 0) 0 := by
    simpa only [StandardCapSpace, extChartAt_self_eq, modelWithCornersSelf_coe,
      id_eq] using standard_geodesic_hasDerivAt g₀ hγ hzero
  have hspeed0 := hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hv hmin
  rw [standard_edist_zero] at hspeed0
  have hs0 : g₀.metric.tangentNorm 0 (deriv γ 0) = radialArclength g₀ ‖x‖ :=
    (ENNReal.ofReal_eq_ofReal_iff (Real.sqrt_nonneg _)
      (standard_radial_arclength_nonneg g₀ x)).mp hspeed0
  obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm (by linarith)
  have hCt := hC t ht
  have hC0 := hC 0 hzero
  rw [mfderiv_eq_fderiv] at hCt hC0
  change g₀.metric.tangentNorm (γ t) (deriv γ t) = (C : ℝ) at hCt
  change g₀.metric.tangentNorm (γ 0) (deriv γ 0) = (C : ℝ) at hC0
  rw [hγ0, hs0] at hC0
  have hs := hCt.trans hC0.symm
  have hsq := congrArg (fun r : ℝ => r ^ 2) hs
  simpa only [tangentNorm, Real.sq_sqrt (metric_inner_nonneg _ _ _)] using hsq

theorem standard_segment_radial_velocity (g₀ : StandardInitialMetric)
    {γ : ℝ → StandardCapSpace} {x : StandardCapSpace} {ε : ℝ}
    (hε : 0 < ε) (hγ : g₀.metric.IsGeodesicOn γ (Ioo (-ε) (1 + ε)))
    (hγ0 : γ 0 = 0) (hx : x ≠ 0)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g₀.metric.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g₀.metric.edist 0 x)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt γ
      ((radialArclength g₀ ‖x‖ / radialSpeed g₀ ‖γ t‖ * ‖γ t‖⁻¹) • γ t) t := by
  let R := radialArclength g₀ ‖x‖
  have hR : 0 < R := radialArclength_pos g₀ (norm_pos_iff.mpr hx)
  have htI : t ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith [ht.1, ht.2]
  have hrad := standard_segment_radial_arclength g₀ hγ0 hmin ⟨ht.1.le, ht.2.le⟩
  have hne : γ t ≠ 0 := by
    intro hz
    rw [hz, norm_zero, radialArclength_zero] at hrad
    exact (mul_pos ht.1 hR).ne' hrad.symm
  have hd := standard_geodesic_hasDerivAt g₀ hγ htI
  have harc : HasDerivAt (fun s => radialArclength g₀ ‖γ s‖) R t := by
    have hlin : HasDerivAt (fun s : ℝ => s * R) R t := by
      simpa only [one_mul, id_eq] using (hasDerivAt_id t).mul_const R
    apply hlin.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact standard_segment_radial_arclength g₀ hγ0 hmin ⟨hs.1.le, hs.2.le⟩
  have hradial := (radial_path_hasDerivAt g₀ hd hne).unique harc
  have henergy := standard_segment_energy g₀ hε hγ hγ0 hmin htI
  change g₀.metric.inner (γ t) (deriv γ t) (deriv γ t) = R ^ 2 at henergy
  have hunit : g₀.metric.inner (γ t) (R⁻¹ • deriv γ t) (R⁻¹ • deriv γ t) = 1 := by
    simp only [map_smul, smul_apply, smul_eq_mul, henergy]
    field_simp
  have hunitRadial : radialSpeed g₀ ‖γ t‖ *
      inner ℝ (‖γ t‖⁻¹ • γ t) (R⁻¹ • deriv γ t) = 1 := by
    rw [real_inner_smul_right, ← mul_left_comm, hradial, inv_mul_cancel₀ hR.ne']
  have hv := congrArg (fun w => R • w)
    (unit_velocity_of_radial_derivative_one g₀ hne hunit hunitRadial)
  simp only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul] at hv
  convert hd using 1
  simpa only [R, div_eq_mul_inv, smul_smul, mul_assoc] using hv.symm

theorem standard_segment_formula (g₀ : StandardInitialMetric)
    {γ : ℝ → StandardCapSpace} {x : StandardCapSpace} {ε : ℝ}
    (hε : 0 < ε) (hγ : g₀.metric.IsGeodesicOn γ (Ioo (-ε) (1 + ε)))
    (hγ0 : γ 0 = 0) (hγ1 : γ 1 = x) (hx : x ≠ 0)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g₀.metric.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g₀.metric.edist 0 x) :
    EqOn γ (fun t => radialEuclideanRadius g₀ (t * radialArclength g₀ ‖x‖) •
      (‖x‖⁻¹ • x)) (Icc (0 : ℝ) 1) := by
  let R := radialArclength g₀ ‖x‖
  let d := ‖γ (1 / 2)‖⁻¹ • γ (1 / 2)
  have hR : 0 < R := radialArclength_pos g₀ (norm_pos_iff.mpr hx)
  have hne (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : γ t ≠ 0 := by
    intro hz
    have h := standard_segment_radial_arclength g₀ hγ0 hmin ⟨ht.1.le, ht.2.le⟩
    rw [hz, norm_zero, radialArclength_zero] at h
    exact (mul_pos ht.1 hR).ne' h.symm
  have hdir (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : ‖γ t‖⁻¹ • γ t = d :=
    normalized_direction_eq_of_radial isOpen_Ioo (convex_Ioo (0 : ℝ) 1).isPreconnected
      (fun s hs => standard_segment_radial_velocity g₀ hε hγ hγ0 hx hmin hs)
      hne ht (by constructor <;> norm_num)
  have hformula : EqOn γ (fun t => radialEuclideanRadius g₀ (t * R) • d)
      (Ioo (0 : ℝ) 1) := by
    intro t ht
    have hnorm : ‖γ t‖ = radialEuclideanRadius g₀ (t * R) := by
      rw [← standard_segment_radial_arclength g₀ hγ0 hmin ⟨ht.1.le, ht.2.le⟩,
        radialEuclideanRadius_arclength]
    calc
      γ t = ‖γ t‖ • (‖γ t‖⁻¹ • γ t) := by
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hne t ht)), one_smul]
      _ = ‖γ t‖ • d := congrArg (fun v => ‖γ t‖ • v) (hdir t ht)
      _ = radialEuclideanRadius g₀ (t * R) • d := by rw [hnorm]
  have hclosed : EqOn γ (fun t => radialEuclideanRadius g₀ (t * R) • d)
      (Icc (0 : ℝ) 1) := by
    apply hformula.of_subset_closure
    · exact hγ.contMDiffOn.continuousOn.mono
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    · exact (((radialEuclideanRadius_contDiff g₀).continuous.comp
        (continuous_id.mul continuous_const)).smul continuous_const).continuousOn
    · exact Ioo_subset_Icc_self
    · rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hend : x = ‖x‖ • d := by
    simpa only [hγ1, one_mul, R, radialEuclideanRadius_arclength] using
      hclosed (x := 1) (by simp)
  have hd : d = ‖x‖⁻¹ • x := by
    calc
      d = ‖x‖⁻¹ • (‖x‖ • d) := by
        rw [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
      _ = ‖x‖⁻¹ • x := congrArg (fun v => ‖x‖⁻¹ • v) hend.symm
  simpa only [hd, R] using hclosed

theorem standard_segment_initial_velocity (g₀ : StandardInitialMetric)
    {γ : ℝ → StandardCapSpace} {x : StandardCapSpace} {ε : ℝ}
    (hε : 0 < ε) (hγ : g₀.metric.IsGeodesicOn γ (Ioo (-ε) (1 + ε)))
    (hγ0 : γ 0 = 0) (hγ1 : γ 1 = x) (hx : x ≠ 0)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g₀.metric.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g₀.metric.edist 0 x) :
    HasDerivAt γ
      ((radialArclength g₀ ‖x‖ / radialSpeed g₀ 0) • (‖x‖⁻¹ • x)) 0 := by
  let R := radialArclength g₀ ‖x‖
  have hf := standard_segment_formula g₀ hε hγ hγ0 hγ1 hx hmin
  have hrad : HasDerivAt (fun t => radialEuclideanRadius g₀ (t * R))
      (R / radialSpeed g₀ 0) 0 := by
    have h := (radialEuclideanRadius_hasDerivAt g₀ (0 * R)).comp 0
      ((hasDerivAt_id (0 : ℝ)).mul_const R)
    simpa only [Function.comp_def, id_eq, zero_mul, one_mul,
      radialEuclideanRadius_zero, div_eq_mul_inv, mul_comm] using h
  have hext := hrad.smul_const (‖x‖⁻¹ • x)
  have hwithin : HasDerivWithinAt γ
      ((R / radialSpeed g₀ 0) • (‖x‖⁻¹ • x)) (Icc (0 : ℝ) 1) 0 :=
    hext.hasDerivWithinAt.congr_of_mem hf (by simp)
  have hzero : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  have hd := standard_geodesic_hasDerivAt g₀ hγ hzero
  exact hd.congr_deriv ((uniqueDiffOn_Icc_zero_one 0 (by simp)).eq_deriv
    (Icc (0 : ℝ) 1) hd.hasDerivWithinAt hwithin)

end PoincareConjecture.M44
