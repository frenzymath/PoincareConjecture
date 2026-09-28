import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PolarMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_hasFDerivAt_norm_radial
    (theta : AnnulusCoordinates) (htheta : ‖theta‖ = 1)
    {r : ℝ} (hr : 0 < r) :
    HasFDerivAt (fun x : AnnulusCoordinates => ‖x‖) (innerSL ℝ theta) (r • theta) := by
  have hnorm : ‖r • theta‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, htheta, mul_one]
  have hsqrt := Real.hasDerivAt_sqrt (show ‖r • theta‖ ^ 2 ≠ 0 by rw [hnorm]; positivity)
  have h := hsqrt.comp_hasFDerivAt (r • theta)
    (hasStrictFDerivAt_norm_sq (r • theta)).hasFDerivAt
  convert! h using 1
  · funext x
    exact (Real.sqrt_sq (norm_nonneg x)).symm
  · ext w
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, real_inner_smul_left,
      hnorm, Real.sqrt_sq hr.le]
    field_simp
    ring

theorem m64Intrinsic_radial_field_pairing
    (N : IntrinsicAnnulus) {e : AnnulusCoordinates → AnnulusCoordinates}
    (b : OrthonormalBasis (Fin 2) ℝ AnnulusCoordinates)
    {r : ℝ} (hr : 0 < r)
    (he : ContMDiffAt (𝓡 2) (𝓡 2) ∞ e (r • b 0))
    (hi : Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (r • b 0)))
    (hgauss : ∀ᶠ s in 𝓝 r, ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e (s • b 0) (s • b 0) w = inner ℝ (s • b 0) w)
    {f : ℝ → ℝ} {f' : ℝ} (hf : HasDerivAt f f' r)
    (w : AnnulusCoordinates) :
    let ρ : ℝ → ℝ := fun s => N.metric.pullbackVolumeDensity e (s • b 0)
    let B := N.metric.pullbackCoefficients e
    let Y : AnnulusCoordinates → AnnulusCoordinates := fun x => f ‖x‖ • x
    B (r • b 0) (fderiv ℝ Y (r • b 0) w +
      coordinateChristoffel B (r • b 0) w (Y (r • b 0))) w =
      (f r + r * f') * inner ℝ (b 0) w ^ 2 +
        f r * (ρ r ^ 2 + r * ρ r * deriv ρ r) * inner ℝ (b 1) w ^ 2 := by
  let B : AnnulusCoordinates → AnnulusCoordinates →L[ℝ] AnnulusCoordinates →L[ℝ] ℝ :=
    N.metric.pullbackCoefficients e
  let ρ : ℝ → ℝ := fun s => N.metric.pullbackVolumeDensity e (s • b 0)
  let Y : AnnulusCoordinates → AnnulusCoordinates := fun x => f ‖x‖ • x
  have hnorm : ‖r • b 0‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, b.norm_eq_one, mul_one]
  have hnormD := m64Intrinsic_hasFDerivAt_norm_radial (b 0) (b.norm_eq_one 0) hr
  have hfD : HasFDerivAt (fun x : AnnulusCoordinates => f ‖x‖)
      (f' • innerSL ℝ (b 0)) (r • b 0) := by
    have hf' : HasDerivAt f f' ‖r • b 0‖ := by simpa only [hnorm] using hf
    exact hf'.comp_hasFDerivAt _ hnormD
  have hY := hfD.smul (hasFDerivAt_id (r • b 0))
  have hDY : fderiv ℝ Y (r • b 0) w =
      (f' * inner ℝ (b 0) w) • (r • b 0) + f r • w := by
    change fderiv ℝ ((fun x : AnnulusCoordinates => f ‖x‖) • id) (r • b 0) w = _
    rw [hY.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      innerSL_apply_apply, smul_eq_mul, hnorm, id_eq, add_comm]
  have hB : DifferentiableAt ℝ B (r • b 0) :=
    (N.metric.contDiffAt_pullbackCoefficients he).differentiableAt (by simp)
  have hsymm : ∀ᶠ x in 𝓝 (r • b 0), ∀ u v, B x u v = B x v u :=
    Eventually.of_forall fun _ _ _ => N.metric.symm _ _ _
  have hΓ : coordinateChristoffel B (r • b 0) w (Y (r • b 0)) =
      f r • coordinateChristoffel B (r • b 0) (r • b 0) w := by
    change CoordinateExponential.christoffelBilinear B (r • b 0) w
      (f ‖r • b 0‖ • (r • b 0)) = _
    rw [hnorm, map_smul, CoordinateExponential.christoffelBilinear_symm hB hsymm]
    rfl
  have hmetric := m64Intrinsic_radial_pullback_metric N e b hr hgauss.self_of_nhds w
  have hconn := m64Intrinsic_radial_christoffel_pairing N b hr he hi hgauss w
  change B (r • b 0) (coordinateChristoffel B (r • b 0) (r • b 0) w) w =
    r * ρ r * deriv ρ r * inner ℝ (b 1) w ^ 2 at hconn
  change B (r • b 0) w w = inner ℝ (b 0) w ^ 2 +
    ρ r ^ 2 * inner ℝ (b 1) w ^ 2 at hmetric
  have hrow := m64Intrinsic_radial_pullback_first_row N e b hr hgauss.self_of_nhds w
  change B (r • b 0) (b 0) w = inner ℝ (b 0) w at hrow
  change B (r • b 0) (fderiv ℝ Y (r • b 0) w +
    coordinateChristoffel B (r • b 0) w (Y (r • b 0))) w =
      (f r + r * f') * inner ℝ (b 0) w ^ 2 +
        f r * (ρ r ^ 2 + r * ρ r * deriv ρ r) * inner ℝ (b 1) w ^ 2
  rw [hDY, hΓ]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
    hmetric, hconn, hrow]
  ring

theorem m64Intrinsic_focusing_pairing_ge_of_log_derivative
    (N : IntrinsicAnnulus) {e : AnnulusCoordinates → AnnulusCoordinates}
    (b : OrthonormalBasis (Fin 2) ℝ AnnulusCoordinates)
    {r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ) (hrpi : κ * r < Real.pi)
    (he : ContMDiffAt (𝓡 2) (𝓡 2) ∞ e (r • b 0))
    (hi : Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (r • b 0)))
    (hgauss : ∀ᶠ s in 𝓝 r, ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e (s • b 0) (s • b 0) w = inner ℝ (s • b 0) w)
    (hlog : let y : ℝ → ℝ := fun s => s * N.metric.pullbackVolumeDensity e (s • b 0)
      κ * Real.cos (κ * r) / Real.sin (κ * r) ≤ deriv y r / y r)
    (w : AnnulusCoordinates) :
    let B := N.metric.pullbackCoefficients e
    let Y : AnnulusCoordinates → AnnulusCoordinates :=
      fun x => (Real.sin (κ * ‖x‖) / (κ * ‖x‖)) • x
    Real.cos (κ * r) * B (r • b 0) w w ≤
      B (r • b 0) (fderiv ℝ Y (r • b 0) w +
        coordinateChristoffel B (r • b 0) w (Y (r • b 0))) w := by
  let ρ : ℝ → ℝ := fun s => N.metric.pullbackVolumeDensity e (s • b 0)
  let y : ℝ → ℝ := fun s => s * ρ s
  have hρ : DifferentiableAt ℝ ρ r := by
    exact ((N.metric.contDiffAt_pullbackVolumeDensity he hi).1.comp
      (f := fun s : ℝ => s • b 0) r (by fun_prop)).differentiableAt (by simp)
  have hρpos : 0 < ρ r := (N.metric.contDiffAt_pullbackVolumeDensity he hi).2
  have hyd : deriv y r = ρ r + r * deriv ρ r := by
    convert! ((hasDerivAt_id r).mul hρ.hasDerivAt).deriv using 1
    simp only [id_eq, one_mul]
  have hsin : 0 < Real.sin (κ * r) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos hκ hr) hrpi
  have hlin : HasDerivAt (fun s : ℝ => κ * s) κ r := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id r).const_mul κ
  have hsind : HasDerivAt (fun s : ℝ => Real.sin (κ * s))
      (κ * Real.cos (κ * r)) r := by
    simpa only [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (κ * r)).comp r hlin
  have hf := hsind.div hlin (mul_pos hκ hr).ne'
  have hp := m64Intrinsic_radial_field_pairing N b hr he hi hgauss hf w
  have hradial : Real.sin (κ * r) / (κ * r) + r *
      ((κ * Real.cos (κ * r) * (κ * r) - Real.sin (κ * r) * κ) / (κ * r) ^ 2) =
        Real.cos (κ * r) := by
    field_simp
    ring
  have htransverse : (Real.sin (κ * r) / (κ * r)) *
      (ρ r ^ 2 + r * ρ r * deriv ρ r) =
        (Real.sin (κ * r) / κ) * (deriv y r / y r) * ρ r ^ 2 := by
    rw [hyd]
    dsimp only [y]
    field_simp
  change κ * Real.cos (κ * r) / Real.sin (κ * r) ≤ deriv y r / y r at hlog
  have hcomp : Real.cos (κ * r) ≤ (Real.sin (κ * r) / κ) * (deriv y r / y r) := by
    have h := mul_le_mul_of_nonneg_left hlog (div_pos hsin hκ).le
    have hcancel : Real.sin (κ * r) / κ *
        (κ * Real.cos (κ * r) / Real.sin (κ * r)) = Real.cos (κ * r) := by
      field_simp
    rwa [hcancel] at h
  change N.metric.pullbackCoefficients e (r • b 0)
    (fderiv ℝ (fun x : AnnulusCoordinates => (Real.sin (κ * ‖x‖) / (κ * ‖x‖)) • x)
      (r • b 0) w + coordinateChristoffel (N.metric.pullbackCoefficients e)
        (r • b 0) w ((Real.sin (κ * ‖r • b 0‖) / (κ * ‖r • b 0‖)) • (r • b 0))) w =
    (Real.sin (κ * r) / (κ * r) + r *
      ((κ * Real.cos (κ * r) * (κ * r) - Real.sin (κ * r) * κ) / (κ * r) ^ 2)) *
        inner ℝ (b 0) w ^ 2 +
      Real.sin (κ * r) / (κ * r) * (ρ r ^ 2 + r * ρ r * deriv ρ r) *
        inner ℝ (b 1) w ^ 2 at hp
  rw [hradial, htransverse] at hp
  dsimp only
  rw [hp, m64Intrinsic_radial_pullback_metric N e b hr hgauss.self_of_nhds w, mul_add]
  apply add_le_add le_rfl
  have h := mul_le_mul_of_nonneg_right hcomp
    (mul_nonneg (sq_nonneg (ρ r)) (sq_nonneg (inner ℝ (b 1) w)))
  simpa only [ρ, mul_assoc] using h

theorem m64Intrinsic_focusing_pairing_ge_of_gaussian_upper
    (N : IntrinsicAnnulus) (K : ℝ) (hK : N.GaussianCurvatureBound K)
    {e : AnnulusCoordinates → AnnulusCoordinates} {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (h0 : (0 : AnnulusCoordinates) ∈ U)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U)
    (hgeo : ∀ v ∈ U,
      N.metric.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 v) = inner ℝ u v)
    (hgauss : ∀ v ∈ U, ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e v v w = inner ℝ v w)
    (basis : OrthonormalBasis (Fin 2) ℝ AnnulusCoordinates)
    {b r : ℝ} (hb : 0 < b) (hbpi : Real.sqrt (max K 1) * b < Real.pi)
    (hsub : ∀ s ∈ Icc 0 b, s • basis 0 ∈ U)
    (hmap : ∀ s ∈ Ioo 0 b, e (s • basis 0) ∈ standardAnnulusDomain)
    (hr : r ∈ Ioo 0 b) (w : AnnulusCoordinates) :
    let κ := Real.sqrt (max K 1)
    let B := N.metric.pullbackCoefficients e
    let Y : AnnulusCoordinates → AnnulusCoordinates :=
      fun x => (Real.sin (κ * ‖x‖) / (κ * ‖x‖)) • x
    Real.cos (κ * r) * B (r • basis 0) w w ≤
      B (r • basis 0) (fderiv ℝ Y (r • basis 0) w +
        coordinateChristoffel B (r • basis 0) w (Y (r • basis 0))) w := by
  have hmax : 0 ≤ max K 1 := le_trans zero_le_one (le_max_right K 1)
  have hκ : 0 < Real.sqrt (max K 1) :=
    Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right K 1))
  have hKκ : K ≤ Real.sqrt (max K 1) ^ 2 := by
    rw [Real.sq_sqrt hmax]
    exact le_max_left K 1
  have hi := m64Intrinsic_radial_mfderiv_injective_of_gaussian_upper N K
    (Real.sqrt (max K 1)) hK hκ hKκ hU h0 he hgeo hmetric
    (basis 0) (basis.norm_eq_one 0) hb hbpi hsub hmap
  have hr' : r ∈ Icc 0 b := ⟨hr.1.le, hr.2.le⟩
  have hgs : ∀ᶠ s in 𝓝 r, ∀ v : AnnulusCoordinates,
      N.metric.pullbackCoefficients e (s • basis 0) (s • basis 0) v =
        inner ℝ (s • basis 0) v := by
    have hc : ContinuousAt (fun s : ℝ => s • basis 0) r := by fun_prop
    filter_upwards [hc.preimage_mem_nhds (hU.mem_nhds (hsub r hr'))] with s hs v
    exact hgauss _ hs v
  apply m64Intrinsic_focusing_pairing_ge_of_log_derivative N basis hr.1 hκ
    ((mul_lt_mul_of_pos_left hr.2 hκ).trans hbpi)
    (he.contMDiffAt (hU.mem_nhds (hsub r hr'))) (hi r hr') hgs
  exact m64Intrinsic_polarDensity_log_derivative_ge_sqrt_max_cot N K hK hU h0 he hgeo
    hmetric (basis 0) (basis.norm_eq_one 0) hb hbpi.le hsub hi hmap hr

end PoincareConjecture
