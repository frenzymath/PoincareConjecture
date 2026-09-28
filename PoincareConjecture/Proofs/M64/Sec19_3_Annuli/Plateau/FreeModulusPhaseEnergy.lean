import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.FullStripPhase
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.FreeTraceSubsequence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CirclePhaseEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleMeasurableIntegration
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamGeometry
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusReduction
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.Def19_12_PositiveDegree













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

open Proofs.M58

local notation "S" => interior m64AnnulusDomain
local notation "Strip" => Set.preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)




theorem full_strip_phase_horizontal_energy
    {L : LoopPlane → ℝ} (hL : ContDiffOn ℝ 1 L Strip) {d : ℝ}
    (hshift : ∀ x s, L (annulusPoint (x + curvePeriod) s) = L (annulusPoint x s) + d)
    (hI : IntegrableOn (fun p => (fderiv ℝ L p e0) ^ 2) S) :
    d ^ 2 ≤ curvePeriod * ∫ p in S, (fderiv ℝ L p e0) ^ 2 := by
  let D := fun p : LoopPlane => (fderiv ℝ L p e0) ^ 2
  have hO : IsOpen Strip := isOpen_Ioo.preimage (EuclideanSpace.proj 1).continuous
  have hDf : ContinuousOn (fderiv ℝ L) Strip :=
    (hL.fderiv_of_isOpen hO (m := 0) (by norm_num)).continuousOn
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hslice (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
      d ^ 2 ≤ curvePeriod * ∫ x in Icc (0 : ℝ) curvePeriod, D (annulusPoint x s) := by
    have hp (x : ℝ) : annulusPoint x s ∈ Strip := hs
    have hline : Continuous (fun x : ℝ => annulusPoint x s) := by
      unfold annulusPoint
      fun_prop
    have hc : Continuous (fun x => fderiv ℝ L (annulusPoint x s) e0) :=
      (hDf.comp_continuous hline hp).clm_apply continuous_const
    have hd (x : ℝ) : HasDerivAt (fun y => L (annulusPoint y s))
        (fderiv ℝ L (annulusPoint x s) e0) x :=
      (((hL _ (hp x)).contDiffAt (hO.mem_nhds (hp x))).differentiableAt
        one_ne_zero).hasFDerivAt.comp_hasDerivAt x
          (m64AnnulusPoint_horizontal_hasDerivAt s x)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (hc.intervalIntegrable 0 curvePeriod)
    have hperiod := hshift 0 s
    simp only [zero_add] at hperiod
    rw [hperiod, add_sub_cancel_left] at hFTC
    have hcs := SpectralHeatNative.integral_sq_le_time_mul_integral_sq hP.le
      (hc.intervalIntegrable 0 curvePeriod) ((hc.pow 2).intervalIntegrable 0 curvePeriod)
    rw [hFTC] at hcs
    simpa only [intervalIntegral.integral_of_le hP.le,
      ← integral_Icc_eq_integral_Ioc, D] using hcs
  have hprod := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hI
  have hae : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), s ∈ Ioo (0 : ℝ) 1 := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)))]
    exact ae_restrict_mem measurableSet_Ioo
  calc
    d ^ 2 = ∫ _s in Icc (0 : ℝ) 1, d ^ 2 := by simp
    _ ≤ ∫ s in Icc (0 : ℝ) 1,
        curvePeriod * ∫ x in Icc (0 : ℝ) curvePeriod, D (annulusPoint x s) := by
      apply integral_mono_ae
        (show IntegrableOn (fun _ : ℝ => d ^ 2) (Icc (0 : ℝ) 1) volume from
          integrableOn_const isCompact_Icc.measure_ne_top)
        (hprod.integral_prod_right.const_mul curvePeriod)
      exact hae.mono hslice
    _ = curvePeriod * ∫ p in S, D p := by
      rw [integral_const_mul,
        m64AnnulusInteriorIntegral_eq_iterated_swap_integrable D hI]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem annulus_weighted_energy_ge_phase_degree
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map Strip)
    (L0 : ℝ → ℝ) (hL0 : Continuous L0)
    (hzero : ∀ x, P.circle.quotient (L0 x) = (c0 x).2)
    {d : ℝ} (hshift : ∀ x, L0 (x + curvePeriod) = L0 x + d)
    {r : ℝ} (hr : 0 < r)
    (hE : IntegrableOn (fun p => (r * m60AreaGram (P.flow.metric t) A.map p 0 0 +
      r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1) / 2) m64AnnulusDomain) :
    r * d ^ 2 / (2 * curvePeriod) ≤ m64ClassicalWeightedGramEnergy (P.flow.metric t) A r := by
  obtain ⟨L, -, hL, hquot, -, hp⟩ :=
    annulus_full_strip_exists_circle_phase P t A hA L0 hL0 hzero hshift
  let D := fun p : LoopPlane => (fderiv ℝ L p e0) ^ 2
  let W := fun p => (r * m60AreaGram (P.flow.metric t) A.map p 0 0 +
    r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1) / 2
  have hO : IsOpen Strip := isOpen_Ioo.preimage (EuclideanSpace.proj 1).continuous
  have hsub : S ⊆ Strip := fun p hp =>
    let h := (m64AnnulusInterior_coordinates p).mp hp
    ⟨h.2.2.1, h.2.2.2⟩
  have hbound (p : LoopPlane) (hpS : p ∈ S) : (r / 2) * D p ≤ W p := by
    have hp' := hsub hpS
    have hgrad := local_circle_phase_column_sq_le_gram P t A.map L p
      (((hA p hp').contMDiffAt (hO.mem_nhds hp')).mdifferentiableAt one_ne_zero)
      (((hL p hp').contDiffAt (hO.mem_nhds hp')).differentiableAt one_ne_zero)
      (show P.circle.quotient ∘ L =ᶠ[𝓝 p] Prod.snd ∘ A.map from by
        filter_upwards [hO.mem_nhds hp'] with q hq
        exact hquot q ⟨hq.1.le, hq.2.le⟩) (0 : Fin 2)
    have hgrad' : D p ≤ m60AreaGram (P.flow.metric t) A.map p 0 0 := by
      simpa only [EuclideanSpace.basisFun_apply] using hgrad
    have hpos := mul_nonneg (inv_nonneg.mpr hr.le)
      (m60AreaGram_diagonal_nonneg (P.flow.metric t) A.map p 1)
    have hmul := mul_le_mul_of_nonneg_left hgrad' hr.le
    dsimp only [W]
    nlinarith
  have hmajor (p : LoopPlane) (hpS : p ∈ S) : D p ≤ (2 / r) * W p := by
    have h := mul_le_mul_of_nonneg_left (hbound p hpS) (by positivity : 0 ≤ 2 / r)
    have heq : (2 / r) * ((r / 2) * D p) = D p := by field_simp
    rwa [heq] at h
  have hDf : ContinuousOn (fderiv ℝ L) Strip :=
    (hL.fderiv_of_isOpen hO (m := 0) (by norm_num)).continuousOn
  have hDc : ContinuousOn D S :=
    ((hDf.clm_apply continuousOn_const).pow 2).mono hsub
  have hWi : IntegrableOn W S := hE.mono_set interior_subset
  have hDi : IntegrableOn D S := by
    apply (hWi.const_mul (2 / r)).mono_nonneg
      (hDc.aestronglyMeasurable isOpen_interior.measurableSet)
      (ae_of_all _ (fun p => sq_nonneg (fderiv ℝ L p e0)))
    exact (ae_restrict_mem isOpen_interior.measurableSet).mono hmajor
  have hphase := full_strip_phase_horizontal_energy hL hp hDi
  change d ^ 2 ≤ curvePeriod * ∫ p in S, D p at hphase
  have hi := setIntegral_mono_on (hDi.const_mul (r / 2)) hWi
    isOpen_interior.measurableSet hbound
  rw [integral_const_mul] at hi
  have hWE : (∫ p in S, W p) = m64ClassicalWeightedGramEnergy (P.flow.metric t) A r := by
    unfold m64ClassicalWeightedGramEnergy
    rw [m64Annulus_restrict_closed_eq_interior]
  rw [hWE] at hi
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  apply (div_le_iff₀ (mul_pos (by norm_num) hP)).mpr
  have hh := mul_le_mul_of_nonneg_left hphase hr.le
  have hh' := mul_le_mul_of_nonneg_right hi
    (by positivity : 0 ≤ 2 * curvePeriod)
  nlinarith




theorem free_ramp_annulus_weighted_energy_ge_winding
    (P : M62.CircleProductData F circumference) (t : ℝ) (gamma : ℝ → P.charts.Point)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma t)
    (sigma : M64PeriodicDegreeOneLift) {c1 : ℝ → P.charts.Point}
    (A : M64Annulus (P.flow.metric t) (gamma ∘ sigma.map) c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map Strip)
    {r : ℝ} (hr : 0 < r)
    (hE : IntegrableOn (fun p => (r * m60AreaGram (P.flow.metric t) A.map p 0 0 +
      r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1) / 2) m64AnnulusDomain) :
    r * circumference ^ 2 / (2 * curvePeriod) ≤
      m64ClassicalWeightedGramEnergy (P.flow.metric t) A r := by
  obtain ⟨lift⟩ := m63PositiveDegreeLift_nonempty P gamma hperiod hgamma hramp
  have hL0 : Continuous (lift.lift ∘ sigma.map) :=
    lift.regular.continuous.comp (degreeOneLift_continuous sigma)
  have hs (x : ℝ) : (lift.lift ∘ sigma.map) (x + curvePeriod) =
      (lift.lift ∘ sigma.map) x + (lift.degree : ℝ) * circumference := by
    simp only [Function.comp_apply, sigma.period_shift, lift.period_shift]
  have hh := annulus_weighted_energy_ge_phase_degree P t A hA
    (lift.lift ∘ sigma.map) hL0 (fun x => lift.quotient_eq (sigma.map x)) hs hr hE
  have hdeg : (1 : ℝ) ≤ lift.degree := by exact_mod_cast lift.degree_positive
  have hcirc : 0 < circumference := P.circle.positive
  have hsq : circumference ^ 2 ≤ ((lift.degree : ℝ) * circumference) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hdeg hcirc.le]
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq hr.le) (by unfold curvePeriod; positivity)).trans hh



theorem free_ramp_annulus_modulus_le_of_energy_bound
    (P : M62.CircleProductData F circumference) (t : ℝ) (gamma : ℝ → P.charts.Point)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma t)
    (sigma : M64PeriodicDegreeOneLift) {c1 : ℝ → P.charts.Point}
    (A : M64Annulus (P.flow.metric t) (gamma ∘ sigma.map) c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map Strip)
    {r E : ℝ} (hr : 0 < r)
    (hE : IntegrableOn (fun p => (r * m60AreaGram (P.flow.metric t) A.map p 0 0 +
      r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1) / 2) m64AnnulusDomain)
    (hbound : m64ClassicalWeightedGramEnergy (P.flow.metric t) A r ≤ E) :
    r ≤ (2 * curvePeriod * E) / circumference ^ 2 := by
  have hh := (free_ramp_annulus_weighted_energy_ge_winding
    P t gamma hgamma hperiod hramp sigma A hA hr hE).trans hbound
  have hP : 0 < 2 * curvePeriod := by unfold curvePeriod; positivity
  have hi := (div_le_iff₀ hP).mp hh
  apply (le_div_iff₀ (sq_pos_of_pos P.circle.positive)).mpr
  nlinarith

end PoincareConjecture.M64
