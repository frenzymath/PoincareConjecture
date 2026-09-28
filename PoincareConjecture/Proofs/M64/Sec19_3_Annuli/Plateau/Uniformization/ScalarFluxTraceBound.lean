import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarIntegratedTrace
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarFluxBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

theorem scalar_integral_mul_sq_le {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} {f g : alpha → ℝ} (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    (∫ x, f x * g x ∂mu) ^ 2 ≤ (∫ x, (f x) ^ 2 ∂mu) * ∫ x, (g x) ^ 2 ∂mu := by
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) mu := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) mu := by simpa using hg
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hg'
  have hholder : (∫ x, |f x| * |g x| ∂mu) ≤
      Real.sqrt (∫ x, (f x) ^ 2 ∂mu) * Real.sqrt (∫ x, (g x) ^ 2 ∂mu) := by
    simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow] using hh
  have hn : |∫ x, f x * g x ∂mu| ≤
      Real.sqrt (∫ x, (f x) ^ 2 ∂mu) * Real.sqrt (∫ x, (g x) ^ 2 ∂mu) := by
    calc
      _ ≤ ∫ x, |f x * g x| ∂mu := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun x => f x * g x) (μ := mu)
      _ = ∫ x, |f x| * |g x| ∂mu := by simp only [abs_mul]
      _ ≤ _ := hholder
  have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _))).mpr hn
  simpa only [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]
    using hsq

private theorem circle_memLp {f : ℝ → ℝ} (hc : ContinuousOn f (Icc (0 : ℝ) 1)) :
    MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply (memLp_two_iff_integrable_sq
    ((hc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)).mpr
  exact ((hc.pow 2).integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

def scalarCoverRadialTotalEnergy (H : Plane → ℝ) : ℝ :=
  ∫ z in Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1,
    (fderiv ℝ (H ∘ scalarCoverMap) z (1, 0)) ^ 2

def scalarCoverCircleDifferentialEnergy (H : Plane → ℝ) (r : ℝ) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1, ‖fderiv ℝ H (scalarCoverMap (r, t))‖ ^ 2

theorem scalarCover_boundary_flux_sq_bound {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hE : IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Ioo (1 : ℝ) 2,
      scalarCoverWeightedFlux D H r ^ 2 ≤
        C ^ 2 * scalarCoverRadialTotalEnergy H *
          ((r - 1) * scalarCoverCircleDifferentialEnergy H r) ∧
      (scalarFluxPeriod D H r - scalarCoverWeightedFlux D H r) ^ 2 ≤
        C ^ 2 * scalarCoverRadialTotalEnergy H *
          ((2 - r) * scalarCoverCircleDifferentialEnergy H r) := by
  obtain ⟨C, hC, hbound⟩ := exists_scalarCover_angular_flux_bound D
  refine ⟨C, hC, ?_⟩
  intro r hr
  let U : ℝ → ℝ := fun t => H (scalarCoverMap (r, t))
  let B : ℝ → ℝ := fun t => scalarCoverForm D H (r, t) (0, 1)
  have hUc : Continuous U :=
    hHc.comp (scalarCoverMap_smooth.continuous.comp (continuous_const.prodMk continuous_id))
  have hBs := (scalarCoverForm_smooth_closed D hHs hlap).1
  have hBc : ContinuousOn B (Icc (0 : ℝ) 1) :=
    (hBs.continuousOn.clm_apply continuousOn_const).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ _ => hr)
  have hUL := circle_memLp hUc.continuousOn
  have hOL : MemLp (fun t => 1 - U t) 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    circle_memLp (continuous_const.sub hUc).continuousOn
  have hBL := circle_memLp hBc
  have hdfc : ContinuousOn (fderiv ℝ H) scalarAnnulus :=
    (contMDiffOn_iff_contDiffOn.mp hHs).continuousOn_fderiv_of_isOpen
      scalarAnnulus_isOpen (by simp)
  have hdc : ContinuousOn (fun t : ℝ => ‖fderiv ℝ H (scalarCoverMap (r, t))‖)
      (Icc (0 : ℝ) 1) :=
    ((hdfc.comp scalarCoverMap_smooth.continuous.continuousOn
      (fun _ hz => scalarCoverMap_mem hz)).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ _ => hr)).norm
  have hBenergy : (∫ t in Ioo (0 : ℝ) 1, B t ^ 2) ≤
      C ^ 2 * scalarCoverCircleDifferentialEnergy H r := by
    have hDi := (circle_memLp hdc).integrable_sq
    have h := integral_mono_ae hBL.integrable_sq (hDi.const_mul (C ^ 2))
      (ae_of_all _ (fun t => ?_))
    · simpa only [integral_const_mul, scalarCoverCircleDifferentialEnergy] using h
    · have hb := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC.le (norm_nonneg _))).mpr
        (hbound H (r, t) hr)
      simpa only [sq_abs, mul_pow] using hb
  have htrace := scalarCover_integrated_boundary_trace_energy hHc hHs hE hinner houter hr
  have hweighted : scalarCoverWeightedFlux D H r = ∫ t in Ioo (0 : ℝ) 1, U t * B t := by
    rw [scalarCoverWeightedFlux, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
  have hperiod : scalarFluxPeriod D H r = ∫ t in Ioo (0 : ℝ) 1, B t := by
    rw [scalarFluxPeriod_eq_cover_integral, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
  have herror : scalarFluxPeriod D H r - scalarCoverWeightedFlux D H r =
      ∫ t in Ioo (0 : ℝ) 1, (1 - U t) * B t := by
    rw [hperiod, hweighted]
    have hBi : IntegrableOn B (Ioo (0 : ℝ) 1) :=
      (hBc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
    erw [← integral_sub hBi (hUL.integrable_mul hBL)]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t _
    simp only [Pi.mul_apply]
    ring
  have hBn : 0 ≤ ∫ t in Ioo (0 : ℝ) 1, B t ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hRn : 0 ≤ scalarCoverRadialTotalEnergy H := integral_nonneg (fun _ => sq_nonneg _)
  constructor
  · rw [hweighted]
    calc
      _ ≤ (∫ t in Ioo (0 : ℝ) 1, U t ^ 2) * (∫ t in Ioo (0 : ℝ) 1, B t ^ 2) :=
        scalar_integral_mul_sq_le hUL hBL
      _ ≤ ((r - 1) * scalarCoverRadialTotalEnergy H) *
          (C ^ 2 * scalarCoverCircleDifferentialEnergy H r) :=
        mul_le_mul htrace.1 hBenergy hBn (mul_nonneg (sub_pos.mpr hr.1).le hRn)
      _ = _ := by ring
  · rw [herror]
    calc
      _ ≤ (∫ t in Ioo (0 : ℝ) 1, (1 - U t) ^ 2) * (∫ t in Ioo (0 : ℝ) 1, B t ^ 2) :=
        scalar_integral_mul_sq_le hOL hBL
      _ ≤ ((2 - r) * scalarCoverRadialTotalEnergy H) *
          (C ^ 2 * scalarCoverCircleDifferentialEnergy H r) :=
        mul_le_mul htrace.2 hBenergy hBn (mul_nonneg (sub_pos.mpr hr.2).le hRn)
      _ = _ := by ring

end PoincareConjecture.M64Uniformization
