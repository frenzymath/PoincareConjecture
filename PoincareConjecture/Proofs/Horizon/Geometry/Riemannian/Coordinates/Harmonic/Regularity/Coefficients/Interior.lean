import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.Absorption
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.Extension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.Localization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.HolderAssembly
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.EquationBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.DensityBounds












noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.HarmonicCoordinates

open Poincare.Parabolic.Interior



theorem exists_uniform_scalar_interior_halfHolder {n : ℕ} (hn : 2 ≤ n) :
    let V := EuclideanSpace ℝ (Fin n)
    let B₀ : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
    ∃ δ : ℝ, 0 < δ ∧ ∀ R a b K : ℝ,
      0 < R → R ≤ 1 → 0 < a → 0 ≤ b → 0 ≤ K →
      ∀ U M B : ℝ≥0, ∃ H : ℝ≥0, 0 < H ∧
      ∀ (g : RiemannianMetric n V) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v : V,
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 R, D.curvatureTensorNorm x ≤ K) →
        (∀ x ∈ Metric.ball 0 R, ∀ i : Fin n,
          D.laplacian (fun y : V => y i) x = 0) →
        (∀ x ∈ Metric.ball 0 R, ‖g.euclideanCoefficients x - B₀‖ < δ) →
        ∀ u : V → ℝ, ContDiff ℝ ∞ u →
          (∀ x ∈ Metric.ball 0 (R / 32), ‖u x‖ ≤ U) →
          (∀ x ∈ Metric.ball 0 (R / 32), ‖fderiv ℝ u x‖ ≤ M) →
          (∀ x ∈ Metric.ball 0 (R / 32),
            |g.pullbackVolumeDensity id x * D.laplacian u x| ≤ B) →
          ∀ x ∈ Metric.ball 0 (R / 128), ∀ y ∈ Metric.ball 0 (R / 128),
            ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ (H : ℝ) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨ε, hε, habsorb⟩ := exists_uniform_small_divergence_gradient_halfHolder hn
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨δ₁, hδ₁, hext⟩ := exists_uniform_divergence_error_extension hn hεr
  obtain ⟨δ₂, hδ₂, hcoeff⟩ := exists_uniform_divergence_operator_lipschitz hn hεr
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂,
    fun R a b K hR hR1 ha hb hK U M B => ?_⟩
  obtain ⟨L₁, hL₁, hext⟩ := hext R a b K hR hR1 ha hb hK
  obtain ⟨L₂, hL₂, hcoeff⟩ := hcoeff R a b K hR hR1 ha hb hK
  let ρ := R / 64
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let χ := rescaledCutoff (unitSpatialBump (E := EuclideanSpace ℝ (Fin n))) 0 ρ
  have hχ : ContDiff ℝ ∞ χ := contDiff_rescaledCutoff unitSpatialBump.contDiff 0 ρ
  have hχc : HasCompactSupport χ := hasCompactSupport_rescaled_unit_cutoff hρ 0
  obtain ⟨C₁, C₂, hC₁, hC₂, hc₁, hc₂⟩ :=
    exists_unit_cutoff_derivative_bounds (E := EuclideanSpace ℝ (Fin n))
  let c₁ : ℝ≥0 := ⟨C₁ / ρ, by positivity⟩
  let c₂ : ℝ≥0 := ⟨C₂ / ρ ^ 2, by positivity⟩
  let l₁ : ℝ≥0 := ⟨L₁, hL₁.le⟩
  let l₂ : ℝ≥0 := ⟨L₂, hL₂.le⟩
  let A : ℝ≥0 := ε + 1
  let F : ℝ≥0 := B + U * n * (l₂ * c₁ + A * c₂) + 2 * A * c₁ * M
  obtain ⟨H, hH, hestimate⟩ := habsorb (max (2 * ε) l₁) U (M + c₁ * U) F
  refine ⟨H, hH, fun g D hell hcurv hharm hnear u hu hubound hdubound hlubound => ?_⟩
  obtain ⟨E, hE, -, hEeq, hEbound, hEder⟩ := hext g D hell hcurv hharm
    (fun x hx => (hnear x hx).trans_le (min_le_left _ _))
  obtain ⟨hAsmall, hAder, -⟩ := hcoeff g D hell hcurv hharm
    (fun x hx => (hnear x hx).trans_le (min_le_right _ _))
  have hχS : tsupport χ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 32) :=
    (tsupport_rescaled_unit_cutoff_subset hρ 0).trans
      (Metric.closedBall_subset_ball (by dsimp [ρ]; linarith))
  have hχnorm (x) : ‖χ x‖ ≤ 1 := by
    have hx := rescaled_unit_cutoff_mem_Icc (E := EuclideanSpace ℝ (Fin n)) 0 ρ x
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  have hχder (x) : ‖fderiv ℝ χ x‖ ≤ c₁ :=
    norm_fderiv_rescaledCutoff_le unitSpatialBump.contDiff hρ hc₁ 0 x
  have hχder₂ (x) : ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ c₂ :=
    norm_fderiv_fderiv_rescaledCutoff_le unitSpatialBump.contDiff hC₂ hρ hc₂ 0 x
  let v := fun x => χ x * u x
  have hv : ContDiff ℝ ∞ v := hχ.mul hu
  have hvc : HasCompactSupport v := hχc.mul_right
  have hvS : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 32) :=
    tsupport_mul_subset_left.trans hχS
  have hvbound (x) : ‖v x‖ ≤ U := by
    by_cases hx : x ∈ tsupport χ
    · exact (norm_mul _ _).trans_le ((mul_le_mul (hχnorm x) (hubound x (hχS hx))
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    · simp only [v, image_eq_zero_of_notMem_tsupport hx, zero_mul, norm_zero]
      exact U.coe_nonneg
  have hvder (x) : ‖fderiv ℝ v x‖ ≤ (M + c₁ * U : ℝ≥0) := by
    by_cases hx : x ∈ tsupport χ
    · rw [fderiv_fun_mul (hχ.differentiable (by simp) x) (hu.differentiable (by simp) x)]
      calc
        _ ≤ ‖χ x • fderiv ℝ u x‖ + ‖u x • fderiv ℝ χ x‖ := norm_add_le _ _
        _ = ‖χ x‖ * ‖fderiv ℝ u x‖ + ‖u x‖ * ‖fderiv ℝ χ x‖ := by simp only [norm_smul]
        _ ≤ 1 * (M : ℝ) + (U : ℝ) * c₁ := add_le_add
          (mul_le_mul (hχnorm x) (hdubound x (hχS hx)) (norm_nonneg _) zero_le_one)
          (mul_le_mul (hubound x (hχS hx)) (hχder x) (norm_nonneg _) U.coe_nonneg)
        _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring
    · have hxv : x ∉ tsupport v := fun h => hx (tsupport_mul_subset_left h)
      rw [fderiv_of_notMem_tsupport ℝ hxv, norm_zero]
      positivity
  have hAsup (x) (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 32)) :
      ‖g.euclideanDivergenceOperator x‖ ≤ A := by
    have hxR := (Metric.ball_subset_ball (by linarith : R / 32 ≤ R)) hx
    calc
      _ ≤ ‖g.euclideanDivergenceOperator x - ContinuousLinearMap.id ℝ _‖ +
          ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ := norm_le_norm_sub_add _ _
      _ ≤ (ε : ℝ) + 1 := add_le_add (hAsmall x hxR).le ContinuousLinearMap.norm_id_le
      _ = _ := by rfl
  have hforcing (x) (hx : x ∈ tsupport v) :
      |g.pullbackVolumeDensity id x * D.laplacian v x| ≤ F := by
    have hx' := hvS hx
    have hx8 := (Metric.ball_subset_ball (by linarith : R / 32 ≤ R / 8)) hx'
    have h := D.abs_density_mul_laplacian_mul_le hχ hu x
    change |g.pullbackVolumeDensity id x * D.laplacian v x| ≤ _ at h
    apply h.trans
    change _ ≤ (B : ℝ) + (U : ℝ) * n * (L₂ * (c₁ : ℝ) + (A : ℝ) * c₂) +
      2 * (A : ℝ) * c₁ * M
    have hχabs : |χ x| ≤ 1 := by simpa only [Real.norm_eq_abs] using hχnorm x
    have huabs : |u x| ≤ U := by simpa only [Real.norm_eq_abs] using hubound x hx'
    calc
      _ ≤ 1 * (B : ℝ) + (U : ℝ) * n * (L₂ * (c₁ : ℝ) + (A : ℝ) * c₂) +
          2 * (A : ℝ) * c₁ * M := by
        gcongr <;> first | exact hχabs | exact hlubound x hx' | exact huabs |
          exact hAder x hx8 | exact hχder x | exact hAsup x hx' |
          exact hχder₂ x | exact hdubound x hx'
      _ = _ := by ring
  have hholder := hestimate E v hE hv hvc hEbound
    (holderWith_half_of_norm_fderiv_le (hE.differentiable (by simp)) hEbound hEder)
    hvbound hvder
    (D.norm_stationaryEllipticResidual_coordinateErrorFlux_le hv hvS
      (fun x hx => hEeq x (Metric.ball_subset_closedBall hx)) F.coe_nonneg hforcing)
  have heq (x) (hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 128)) :
      fderiv ℝ v x = fderiv ℝ u x := by
    have hxρ : ‖x - 0‖ < ρ / 2 := by
      simpa only [Metric.mem_ball, dist_zero_right, sub_zero,
        show ρ / 2 = R / 128 by dsimp [ρ]; ring] using hx
    have hχone := rescaled_unit_cutoff_eventuallyEq_one hρ 0 hxρ
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hχone] with y hy
    simp only [v, χ, hy, one_mul]
  intro x hx y hy
  have h := hholder.dist_le x y
  rw [dist_eq_norm, heq x hx, heq y hy, dist_eq_norm] at h
  exact h




theorem exists_uniform_harmonic_metric_halfHolder {n : ℕ} (hn : 2 ≤ n) :
    let V := EuclideanSpace ℝ (Fin n)
    let B₀ : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
    ∃ δ : ℝ, 0 < δ ∧ ∀ R a b K : ℝ,
      0 < R → R ≤ 1 → 0 < a → a ≤ 1 → 1 ≤ b → 0 ≤ K →
      ∃ H : ℝ, 0 < H ∧
      ∀ (g : RiemannianMetric n V) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v : V,
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 R, D.curvatureTensorNorm x ≤ K) →
        (∀ x ∈ Metric.ball 0 R, ∀ i : Fin n,
          D.laplacian (fun y : V => y i) x = 0) →
        (∀ x ∈ Metric.ball 0 R, ‖g.euclideanCoefficients x - B₀‖ < δ) →
        (∀ x ∈ Metric.ball 0 (R / 128), ‖fderiv ℝ g.euclideanCoefficients x‖ ≤ H) ∧
        ∀ x ∈ Metric.ball 0 (R / 128), ∀ y ∈ Metric.ball 0 (R / 128),
          ‖fderiv ℝ g.euclideanCoefficients x - fderiv ℝ g.euclideanCoefficients y‖ ≤
            H * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨δ, hδ, hscalar⟩ := exists_uniform_scalar_interior_halfHolder hn
  refine ⟨δ, hδ, fun R a b K hR hR1 ha ha1 hb hK => ?_⟩
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  obtain ⟨L, hL, hder⟩ := exists_uniform_harmonic_metric_derivative_bound hn hR hR1 ha hb0 hK
  let U : ℝ≥0 := ⟨δ + 1, by positivity⟩
  let M : ℝ≥0 := ⟨L, hL.le⟩
  let F : ℝ≥0 := ⟨Real.sqrt (b ^ n) *
    (2 * (n : ℝ) * K * b + (32 * (n : ℝ) ^ 2 * b / a ^ 3) * L ^ 2), by positivity⟩
  obtain ⟨H, hH, hscalar⟩ := hscalar R a b K hR hR1 ha hb0 hK U M F
  refine ⟨max L ((n : ℝ) ^ 2 * H) + 1, by positivity,
    fun g D hell hcurv hharm hnear => ?_⟩
  have h32R : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 32) ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  have h328 : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 32) ⊆ Metric.ball 0 (R / 8) :=
    Metric.ball_subset_ball (by linarith)
  have h1288 : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R / 128) ⊆ Metric.ball 0 (R / 8) :=
    Metric.ball_subset_ball (by linarith)
  have hbound := hder g D hell hcurv hharm
  have hcoeff : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  have hentry (i j : Fin n) := hscalar g D hell hcurv hharm hnear
    (fun z => g.euclideanCoefficients z (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j))
    ((hcoeff.clm_apply contDiff_const).clm_apply contDiff_const)
  have hentry' (i j : Fin n) : ∀ x ∈ Metric.ball 0 (R / 128),
      ∀ y ∈ Metric.ball 0 (R / 128),
        ‖fderiv ℝ (fun z => g.euclideanCoefficients z (EuclideanSpace.basisFun (Fin n) ℝ i)
            (EuclideanSpace.basisFun (Fin n) ℝ j)) x -
          fderiv ℝ (fun z => g.euclideanCoefficients z (EuclideanSpace.basisFun (Fin n) ℝ i)
            (EuclideanSpace.basisFun (Fin n) ℝ j)) y‖ ≤ (H : ℝ) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
    apply hentry i j
    · intro x hx
      rw [Real.norm_eq_abs]
      apply (abs_bilinear_basis_apply_le_norm (g.euclideanCoefficients x) i j).trans
      let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
      calc
        _ ≤ ‖g.euclideanCoefficients x - B₀‖ + ‖B₀‖ := norm_le_norm_sub_add _ _
        _ ≤ δ + 1 := add_le_add (hnear x (h32R hx)).le (norm_innerSL_le ℝ)
        _ = _ := rfl
    · intro x hx
      exact (norm_fderiv_bilinear_field_entry_le
        (hcoeff.differentiable (by simp) x) i j).trans (hbound x (h328 hx))
    · intro x hx
      have hh : ∀ᶠ y in 𝓝 x, ∀ i : Fin n,
          D.laplacian (fun z : EuclideanSpace ℝ (Fin n) => z i) y = 0 := by
        filter_upwards [Metric.isOpen_ball.mem_nhds (h32R hx)] with y hy
        exact hharm y hy
      have hforce := D.abs_laplacian_metric_le_of_harmonic hh ha ha1 hb
        (fun v => (hell x (h32R hx) v).1) (fun v => (hell x (h32R hx) v).2)
        (hcurv x (h32R hx)) (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)
      simp only [OrthonormalBasis.norm_eq_one, mul_one] at hforce
      have hforce' : |D.laplacian
          (fun z => g.euclideanCoefficients z (EuclideanSpace.basisFun (Fin n) ℝ i)
            (EuclideanSpace.basisFun (Fin n) ℝ j)) x| ≤
          2 * (n : ℝ) * K * b + (32 * (n : ℝ) ^ 2 * b / a ^ 3) * L ^ 2 := by
        apply hforce.trans
        gcongr
        exact hbound x (h328 hx)
      rw [abs_mul]
      have hdensity : |g.pullbackVolumeDensity id x| ≤ Real.sqrt (b ^ n) := by
        rw [abs_of_nonneg (show 0 ≤ g.pullbackVolumeDensity id x from Real.sqrt_nonneg _)]
        exact (g.pullbackVolumeDensity_id_bounds x ha (hell x (h32R hx))).2
      exact mul_le_mul hdensity hforce' (abs_nonneg _) (Real.sqrt_nonneg _)
  constructor
  · intro x hx
    exact (hbound x (h1288 hx)).trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  · intro x hx y hy
    exact (g.norm_fderiv_euclideanCoefficients_sub_le_of_entry_halfHolder H.coe_nonneg hentry' hx hy).trans
      (mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one))
        (Real.rpow_nonneg (norm_nonneg _) _))

end PoincareConjecture.HarmonicCoordinates
