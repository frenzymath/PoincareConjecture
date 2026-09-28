import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarEnergyPeriod
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverFiniteFibers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Module
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ
local notation "Band" => Set.prod (Ioo (1 : ℝ) 2) (Ioo (0 : ℝ) 1)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem scalarNormalizedCoverMap_det {H : Plane → ℝ} {V : Cover → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    (P : ℝ) {z : Cover} (hz : z ∈ scalarCoverStrip) :
    (fderiv ℝ (scalarNormalizedCoverMap H V P) z).det = scalarCoverJacobian D H z / P := by
  have hU := ((scalarCoverPotential_smooth hHs).contDiffAt
    (scalarCoverStrip_isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hVnorm : HasFDerivAt (fun y => V y / P) (P⁻¹ • scalarCoverForm D H z) z := by
    convert! (hdV z hz).const_smul P⁻¹ using 1
    ext y
    simp [div_eq_mul_inv, mul_comm]
  have hF := hU.hasFDerivAt.prodMk hVnorm
  change HasFDerivAt (scalarNormalizedCoverMap H V P) _ z at hF
  rw [hF.fderiv, ContinuousLinearMap.det,
    ← LinearMap.det_toMatrix (Basis.finTwoProd ℝ)]
  simp only [Matrix.det_fin_two, LinearMap.toMatrix_apply, Basis.finTwoProd_zero,
    Basis.finTwoProd_one, Basis.coe_finTwoProd_repr, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_coe, smul_apply, smul_eq_mul]
  simp only [scalarCoverJacobian, div_eq_mul_inv]
  ring

theorem scalarNormalizedCoverMap_abs_det {H : Plane → ℝ} {V : Cover → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : 0 < P) {z : Cover} (hz : z ∈ scalarCoverStrip) :
    |(fderiv ℝ (scalarNormalizedCoverMap H V P) z).det| =
      scalarCoverJacobian D H z / P := by
  rw [scalarNormalizedCoverMap_det D hHs hdV P hz]
  exact abs_of_nonneg (div_nonneg (scalarCoverJacobian_nonneg D hHs hz) hP.le)

theorem scalarNormalizedCoverMap_abs_det_integrable {H : Plane → ℝ} {V : Cover → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : 0 < P) (hJ : IntegrableOn (scalarCoverJacobian D H) Band) :
    IntegrableOn (fun z => |(fderiv ℝ (scalarNormalizedCoverMap H V P) z).det|) Band := by
  apply (hJ.div_const P).congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
  exact (scalarNormalizedCoverMap_abs_det D hHs hdV hP hz.1).symm

theorem scalarNormalizedCoverMap_total_abs_det_one (w : H1Zero D scalarAnnulus)
    {H : Plane → ℝ} {V : Cover → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
        annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ))
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z) :
    (∫ z in Band,
      |(fderiv ℝ (scalarNormalizedCoverMap H V (scalarFluxPeriod D H (3 / 2))) z).det|) = 1 := by
  have hP := scalarPotential_fluxPeriod_pos D w hHc hHs hHae hlap hinner houter
    (by norm_num : (3 / 2 : ℝ) ∈ Ioo 1 2)
  obtain ⟨hJ, -, -⟩ := scalarPotential_unitCover_energy D w hHs hHae
  calc
    _ = ∫ z in Band, scalarCoverJacobian D H z / scalarFluxPeriod D H (3 / 2) := by
      apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      intro z hz
      exact scalarNormalizedCoverMap_abs_det D hHs hdV hP hz.1
    _ = (∫ z in Band, scalarCoverJacobian D H z) / scalarFluxPeriod D H (3 / 2) := by
      simp only [div_eq_mul_inv, integral_mul_const]
    _ = 1 := by
      erw [scalarCoverJacobian_integral_eq_period D hHc hHs hlap
        (scalarPotential_finite_differential_energy D w hHs hHae) hJ hinner houter,
        div_self hP.ne']

theorem scalarNormalizedCoverMap_image_area_le_one (w : H1Zero D scalarAnnulus)
    {H : Plane → ℝ} {V : Cover → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
        annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ))
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z) :
    volume (scalarNormalizedCoverMap H V (scalarFluxPeriod D H (3 / 2)) '' Band) ≤ 1 := by
  let P := scalarFluxPeriod D H (3 / 2)
  let F := scalarNormalizedCoverMap H V P
  have hP : 0 < P := scalarPotential_fluxPeriod_pos D w hHc hHs hHae hlap hinner houter
    (by norm_num : (3 / 2 : ℝ) ∈ Ioo 1 2)
  have hJ := (scalarPotential_unitCover_energy D w hHs hHae).1
  have hint := scalarNormalizedCoverMap_abs_det_integrable D hHs hdV hP hJ
  have hmass : (∫⁻ z in Band, ENNReal.ofReal |(fderiv ℝ F z).det|) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z => abs_nonneg _)]
    rw [scalarNormalizedCoverMap_total_abs_det_one D w hHc hHs hHae hlap hinner houter hdV]
    norm_num
  have hdiff (z : Cover) (hz : z ∈ Band) : DifferentiableAt ℝ F z := by
    have hU := ((scalarCoverPotential_smooth hHs).contDiffAt
      (scalarCoverStrip_isOpen.mem_nhds hz.1)).differentiableAt (by simp)
    have hVnorm : DifferentiableAt ℝ (fun y => V y / P) z := by
      convert! ((hdV z hz.1).const_smul P⁻¹).differentiableAt using 1
      ext y
      simp [div_eq_mul_inv, mul_comm]
    exact hU.prodMk hVnorm
  exact (addHaar_image_le_lintegral_abs_det_fderiv volume
    (measurableSet_Ioo.prod measurableSet_Ioo)
    (fun z hz => (hdiff z hz).hasFDerivAt.hasFDerivWithinAt)).trans_eq hmass

end PoincareConjecture.M64Uniformization
