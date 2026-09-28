import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LipschitzRectangleFTC












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S



theorem m64_lipschitz_green_integrable {f phi : LoopPlane → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f m64AnnulusDomain) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
    IntegrableOn (fun p => phi p * fderiv ℝ f p (EuclideanSpace.single i 1)) S volume ∧
      IntegrableOn (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1) * f p) S volume := by
  constructor
  · obtain ⟨C, hC⟩ := m64AnnulusDomain_isCompact.bddAbove_image hphi.continuous.continuousOn.norm
    apply (m64_lipschitz_partial_integrable hf i).bdd_mul (c := C)
      hphi.continuous.aestronglyMeasurable
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    exact hC (mem_image_of_mem _ (interior_subset hp))
  · have hc := ((hphi.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := EuclideanSpace.single i 1))).continuousOn.mul hf.continuousOn
    exact (hc.integrableOn_compact m64AnnulusDomain_isCompact).mono_set interior_subset



theorem m64Annulus_vertical_green_lipschitz
    {f phi : LoopPlane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hphi : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p * fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1)) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) * f p) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 1) * f (annulusPoint x 1) -
          phi (annulusPoint x 0) * f (annulusPoint x 0) := by
  obtain ⟨hleft, hright⟩ := m64_lipschitz_green_integrable hf.lipschitzOnWith hphi 1
  rw [← integral_add hleft hright,
    m64AnnulusInteriorIntegral_eq_iterated_integrable
      (fun p => phi p * fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1) +
        fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) * f p) (hleft.add hright)]
  have hdiff := m64AnnulusPoint_measurePreserving.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (hf.ae_differentiableAt (μ := volume)))
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hdiff] with x hx
  have hslice := hf.comp (m64AnnulusPoint_vertical_lipschitz x)
  have hac := (hslice.lipschitzOnWith (s := uIcc (0 : ℝ) 1)).absolutelyContinuousOnInterval
  have hpc : ContDiff ℝ 1 (fun s => phi (annulusPoint x s)) := hphi.comp (by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_id)
  have hpac := (hpc.contDiffOn (s := uIcc (0 : ℝ) 1)).absolutelyContinuousOnInterval
  calc
    _ = ∫ s in Icc (0 : ℝ) 1,
        deriv (fun t => phi (annulusPoint x t)) s * f (annulusPoint x s) +
          phi (annulusPoint x s) * deriv (fun t => f (annulusPoint x t)) s := by
      apply integral_congr_ae
      filter_upwards [hx] with s hs
      have hd := (hs.hasFDerivAt.comp_hasDerivAt s
        (m64AnnulusPoint_vertical_hasDerivAt x s)).deriv
      have hp := ((hphi.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
        (m64AnnulusPoint_vertical_hasDerivAt x s)).deriv
      simp only [Function.comp_def] at hd hp
      rw [hd, hp]
      ring
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
      exact hpac.integral_deriv_mul_eq_sub hac



theorem m64Annulus_horizontal_green_lipschitz
    {f phi : LoopPlane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hphi : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p * fderiv ℝ f p (EuclideanSpace.single (0 : Fin 2) 1)) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (0 : Fin 2) 1) * f p) =
      ∫ s in Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) * f (annulusPoint curvePeriod s) -
          phi (annulusPoint 0 s) * f (annulusPoint 0 s) := by
  obtain ⟨hleft, hright⟩ := m64_lipschitz_green_integrable hf.lipschitzOnWith hphi 0
  rw [← integral_add hleft hright,
    m64AnnulusInteriorIntegral_eq_iterated_swap_integrable
      (fun p => phi p * fderiv ℝ f p (EuclideanSpace.single (0 : Fin 2) 1) +
        fderiv ℝ phi p (EuclideanSpace.single (0 : Fin 2) 1) * f p) (hleft.add hright)]
  have hdiff := m64AnnulusPoint_measurePreserving.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (hf.ae_differentiableAt (μ := volume)))
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hdiff
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with s hs
  have hslice := hf.comp (m64AnnulusPoint_horizontal_lipschitz s)
  have hac := (hslice.lipschitzOnWith
    (s := uIcc (0 : ℝ) curvePeriod)).absolutelyContinuousOnInterval
  have hpc : ContDiff ℝ 1 (fun x => phi (annulusPoint x s)) := hphi.comp (by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_id
    · exact contDiff_const)
  have hpac := (hpc.contDiffOn
    (s := uIcc (0 : ℝ) curvePeriod)).absolutelyContinuousOnInterval
  calc
    _ = ∫ x in Icc (0 : ℝ) curvePeriod,
        deriv (fun t => phi (annulusPoint t s)) x * f (annulusPoint x s) +
          phi (annulusPoint x s) * deriv (fun t => f (annulusPoint t s)) x := by
      apply integral_congr_ae
      filter_upwards [hs] with x hx
      have hd := (hx.hasFDerivAt.comp_hasDerivAt x
        (m64AnnulusPoint_horizontal_hasDerivAt s x)).deriv
      have hp := ((hphi.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt x
        (m64AnnulusPoint_horizontal_hasDerivAt s x)).deriv
      simp only [Function.comp_def, Prod.swap] at hd hp
      rw [hd, hp]
      ring
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by unfold curvePeriod; positivity : 0 ≤ curvePeriod)]
      exact hpac.integral_deriv_mul_eq_sub hac



theorem m64Annulus_vertical_green_lipschitzOn
    {f phi : LoopPlane → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f m64AnnulusDomain)
    (hphi : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p * fderiv ℝ f p (EuclideanSpace.single (1 : Fin 2) 1)) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) * f p) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 1) * f (annulusPoint x 1) -
          phi (annulusPoint x 0) * f (annulusPoint x 0) := by
  obtain ⟨F, hF, heq⟩ := hf.extend_real
  have hd : ∀ᵐ p ∂mu, fderiv ℝ f p = fderiv ℝ F p := by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    apply EventuallyEq.fderiv_eq
    filter_upwards [isOpen_interior.mem_nhds hp] with q hq
    exact heq (interior_subset hq)
  have hv : f =ᵐ[mu] F := by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    exact heq (interior_subset hp)
  have hi (i : Fin 2) :
      (∫ p in S, phi p * fderiv ℝ f p (EuclideanSpace.single i 1)) =
        ∫ p in S, phi p * fderiv ℝ F p (EuclideanSpace.single i 1) :=
    integral_congr_ae (hd.mono fun p hp =>
      congrArg (fun L : LoopPlane →L[ℝ] ℝ => phi p * L (EuclideanSpace.single i 1)) hp)
  have hj (i : Fin 2) :
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * f p) =
        ∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * F p :=
    integral_congr_ae (hv.mono fun p hp =>
      congrArg (fun t : ℝ => fderiv ℝ phi p (EuclideanSpace.single i 1) * t) hp)
  rw [hi, hj, m64Annulus_vertical_green_lipschitz hF hphi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have h0 := heq (show annulusPoint x 0 ∈ m64AnnulusDomain from
    ⟨hx.1, hx.2, le_rfl, zero_le_one⟩)
  have h1 := heq (show annulusPoint x 1 ∈ m64AnnulusDomain from
    ⟨hx.1, hx.2, zero_le_one, le_rfl⟩)
  rw [h0, h1]



theorem m64Annulus_horizontal_green_lipschitzOn
    {f phi : LoopPlane → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f m64AnnulusDomain)
    (hphi : ContDiff ℝ 1 phi) :
    (∫ p in S, phi p * fderiv ℝ f p (EuclideanSpace.single (0 : Fin 2) 1)) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (0 : Fin 2) 1) * f p) =
      ∫ s in Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) * f (annulusPoint curvePeriod s) -
          phi (annulusPoint 0 s) * f (annulusPoint 0 s) := by
  obtain ⟨F, hF, heq⟩ := hf.extend_real
  have hd : ∀ᵐ p ∂mu, fderiv ℝ f p = fderiv ℝ F p := by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    apply EventuallyEq.fderiv_eq
    filter_upwards [isOpen_interior.mem_nhds hp] with q hq
    exact heq (interior_subset hq)
  have hv : f =ᵐ[mu] F := by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    exact heq (interior_subset hp)
  have hi (i : Fin 2) :
      (∫ p in S, phi p * fderiv ℝ f p (EuclideanSpace.single i 1)) =
        ∫ p in S, phi p * fderiv ℝ F p (EuclideanSpace.single i 1) :=
    integral_congr_ae (hd.mono fun p hp =>
      congrArg (fun L : LoopPlane →L[ℝ] ℝ => phi p * L (EuclideanSpace.single i 1)) hp)
  have hj (i : Fin 2) :
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * f p) =
        ∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * F p :=
    integral_congr_ae (hv.mono fun p hp =>
      congrArg (fun t : ℝ => fderiv ℝ phi p (EuclideanSpace.single i 1) * t) hp)
  rw [hi, hj, m64Annulus_horizontal_green_lipschitz hF hphi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hP : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have h0 := heq (show annulusPoint 0 s ∈ m64AnnulusDomain from
    ⟨le_rfl, hP, hs.1, hs.2⟩)
  have h1 := heq (show annulusPoint curvePeriod s ∈ m64AnnulusDomain from
    ⟨hP, le_rfl, hs.1, hs.2⟩)
  rw [h0, h1]

end PoincareConjecture
