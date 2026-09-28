import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCylinderAdmission
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarSmoothAnnulusApproximation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusEnergyDensity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Strip" => Set.preimage (fun p : Plane => p 1) (Ioo (0 : ℝ) 1)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem scalarModulusEnergyDensity_eq_area
    (g : RiemannianMetric n M) (f : Plane → M) {r : ℝ} (hr : 0 < r) (p : Plane)
    (hc : r * m60AreaGram g f p 0 0 = r⁻¹ * m60AreaGram g f p 1 1)
    (ho : m60AreaGram g f p 0 1 = 0) :
    m64ModulusEnergyDensity g r f p = m60AreaDensity g f p := by
  let a := m60AreaGram g f p 0 0
  let b := m60AreaGram g f p 1 1
  have hscale : b = r ^ 2 * a := by
    have h := congrArg (fun x : ℝ => r * x) hc
    rw [← mul_assoc r r⁻¹, mul_inv_cancel₀ hr.ne', one_mul] at h
    nlinarith
  have hdet : Matrix.det (m60AreaGram g f p) = (r * a) ^ 2 := by
    rw [Matrix.det_fin_two, m60AreaGram_symm g f p 1 0, ho]
    simp only [zero_mul, sub_zero]
    change a * b = (r * a) ^ 2
    rw [hscale]
    ring
  have ha : 0 ≤ r * a := mul_nonneg hr.le (m60AreaGram_diagonal_nonneg g f p 0)
  have harea : m60AreaDensity g f p = r * a := by
    unfold m60AreaDensity
    rw [hdet, max_eq_right (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
  rw [harea, m64ModulusEnergyDensity, ← hc]
  dsimp only [a]
  ring

variable [T2Space M]

theorem exists_smooth_free_annulus_energy_lt_area
    (g : RiemannianMetric n M) (f : Plane → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (eta : ℝ) (heta : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧ ∃ sigma0 sigma1 : M64PeriodicDegreeOneLift,
      ContDiff ℝ 1 sigma0.map ∧ ContDiff ℝ 1 sigma1.map ∧
      StrictMono sigma0.map ∧ StrictMono sigma1.map ∧
      (∀ x : ℝ, 0 < deriv sigma0.map x) ∧ (∀ x : ℝ, 0 < deriv sigma1.map x) ∧
      ∃ A : M64Annulus g
        ((fun x => f (scalarCoverMap (1, x / curvePeriod))) ∘ sigma0.map)
        ((fun x => f (scalarCoverMap (2, x / curvePeriod))) ∘ sigma1.map),
        ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior ∧
        IntegrableOn (fun p => (r * m60AreaGram g A.map p 0 0 +
          r⁻¹ * m60AreaGram g A.map p 1 1) / 2) m64AnnulusDomain ∧
        m64ClassicalWeightedGramEnergy g A r <
          (∫ x in scalarAnnulus, m60AreaDensity g f x) + eta := by
  obtain ⟨delta, hdelta, hsmall⟩ :=
    m64RegularizedPullbackMetric_exists_annular_area_lt g f hf eta heta
  let q := m64RegularizedPullbackMetric g f hf delta hdelta
  obtain ⟨r, hr, K, F, sigma0, sigma1, hF, hFs, -, -, -, -, hperiod,
    hs0, hs1, hm0, hm1, hd0, hd1, hb0, hb1, hconf, hFA, harea⟩ :=
    exists_lipschitz_free_modulus_conformal_cylinder q
  obtain ⟨A, hAeq⟩ := scalarClosedCylinder_admit g f hf hF hperiod sigma0 sigma1 hb0 hb1
  have hStrip : IsOpen Strip := isOpen_Ioo.preimage (EuclideanSpace.proj 1).continuous
  have hu : ContMDiffOn (𝓡 2) (𝓡 n) ∞ (f ∘ F) Strip :=
    hf.comp_contMDiffOn (contMDiffOn_iff_contDiffOn.mpr hFs)
  let E := m64ModulusEnergyDensity g r (f ∘ F)
  have hEnonneg (p : Plane) : 0 ≤ E p := by
    exact div_nonneg (add_nonneg
      (mul_nonneg hr.le (m60AreaGram_diagonal_nonneg g (f ∘ F) p 0))
      (mul_nonneg (inv_nonneg.mpr hr.le) (m60AreaGram_diagonal_nonneg g (f ∘ F) p 1)))
      (by norm_num)
  have hEbound {p : Plane} (hp : p ∈ scalarCylinderFundamental) :
      E p ≤ m60AreaDensity q F p := by
    have hFd := (hFs.contDiffAt (hStrip.mem_nhds hp.1)).differentiableAt (by simp)
    have h0 := mul_le_mul_of_nonneg_left
      (regularizedPullback_comp_gram_le g f hf hdelta hFd 0) hr.le
    have h1 := mul_le_mul_of_nonneg_left
      (regularizedPullback_comp_gram_le g f hf hdelta hFd 1) (inv_nonneg.mpr hr.le)
    rw [← scalarModulusEnergyDensity_eq_area q F hr p (hconf p hp.1).1 (hconf p hp.1).2]
    exact div_le_div_of_nonneg_right (add_le_add h0 h1) (by norm_num)
  have hEc : ContinuousOn E Strip := by
    intro p hp
    have hup := hu.contMDiffAt (hStrip.mem_nhds hp)
    have h0 := (m64AreaGram_entry_contDiffAt (g := g) hup 0 0).continuousAt
    have h1 := (m64AreaGram_entry_contDiffAt (g := g) hup 1 1).continuousAt
    have hc : ContinuousAt E p :=
      ((continuousAt_const.mul h0).add (continuousAt_const.mul h1)).div_const 2
    exact hc.continuousWithinAt
  have hEI : IntegrableOn E scalarCylinderFundamental := by
    apply hFA.mono' ((hEc.mono (fun _ hp => hp.1)).aestronglyMeasurable
      scalarCylinderFundamental_measurable)
    filter_upwards [ae_restrict_mem scalarCylinderFundamental_measurable] with p hp
    rw [Real.norm_of_nonneg (hEnonneg p)]
    exact hEbound hp
  have hEIclosed : IntegrableOn E m64AnnulusDomain :=
    (integrableOn_congr_set_ae scalarCylinderFundamental_ae_eq_domain).mp hEI
  have henergy := m64ModulusEnergyDensity_ae_eq_of_eqOn g r hAeq
  have hAI : IntegrableOn (m64ModulusEnergyDensity g r A.map) m64AnnulusDomain :=
    hEIclosed.congr henergy.symm
  have hinterior : m64AnnulusInterior ⊆ Strip ∩ m64AnnulusDomain := by
    intro p hp
    simp only [m64AnnulusInterior, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      Set.mem_Ioo] at hp
    exact ⟨hp 1 trivial, (hp 0 trivial).1.le, (hp 0 trivial).2.le,
      (hp 1 trivial).1.le, (hp 1 trivial).2.le⟩
  refine ⟨r, hr, sigma0, sigma1, hs0, hs1, hm0, hm1, hd0, hd1, A,
    (hu.mono (fun _ hp => (hinterior hp).1)).congr (fun _ hp => hAeq (hinterior hp).2),
    hAI, ?_⟩
  calc
    m64ClassicalWeightedGramEnergy g A r = ∫ p in m64AnnulusDomain, E p :=
      integral_congr_ae henergy
    _ = ∫ p in scalarCylinderFundamental, E p :=
      (setIntegral_congr_set scalarCylinderFundamental_ae_eq_domain).symm
    _ ≤ ∫ p in scalarCylinderFundamental, m60AreaDensity q F p := by
      apply integral_mono_ae hEI hFA
      filter_upwards [ae_restrict_mem scalarCylinderFundamental_measurable] with p hp
      exact hEbound hp
    _ = ∫ x in scalarAnnulus, m60AreaDensity q id x := harea
    _ < (∫ x in scalarAnnulus, m60AreaDensity g f x) + eta := hsmall

end PoincareConjecture.M64Uniformization
