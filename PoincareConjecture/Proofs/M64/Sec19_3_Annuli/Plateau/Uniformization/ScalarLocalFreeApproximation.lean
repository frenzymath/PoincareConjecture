import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarLocalMajorantArea
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarLocalCylinderAdmission
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarSmoothFreeApproximation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarPeriodicRectangleEquality













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Strip" => Set.preimage (fun p : Plane => p 1) (Ioo (0 : ℝ) 1)
local notation "K" => Set.preimage scalarAnnulusDefining (Ici (0 : ℝ))

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem scalarLocal_comp_gram_le
    (g : RiemannianMetric n M) (q : RiemannianMetric 2 Plane)
    {f : Plane → M} {F : Plane → Plane} {p : Plane}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (F p))
    (hF : DifferentiableAt ℝ F p)
    (hmajor : ∀ v : Plane,
      g.inner (f (F p)) (mfderiv (𝓡 2) (𝓡 n) f (F p) v)
        (mfderiv (𝓡 2) (𝓡 n) f (F p) v) ≤ q.inner (F p) v v) (i : Fin 2) :
    m60AreaGram g (f ∘ F) p i i ≤ m60AreaGram q F p i i := by
  unfold m60AreaGram
  rw [mfderiv_comp p hf (mdifferentiableAt_iff_differentiableAt.mpr hF)]
  exact hmajor _

variable [T2Space M]






theorem exists_localC1_free_annulus_energy_lt_area_fullStrip
    (g : RiemannianMetric n M) (f : Plane → M)
    {U : Set Plane} (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U) (eta : ℝ) (heta : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧ ∃ sigma0 sigma1 : M64PeriodicDegreeOneLift,
      ContDiff ℝ 1 sigma0.map ∧ ContDiff ℝ 1 sigma1.map ∧
      StrictMono sigma0.map ∧ StrictMono sigma1.map ∧
      (∀ x : ℝ, 0 < deriv sigma0.map x) ∧ (∀ x : ℝ, 0 < deriv sigma1.map x) ∧
      ∃ A : M64Annulus g
        ((fun x => f (scalarCoverMap (1, x / curvePeriod))) ∘ sigma0.map)
        ((fun x => f (scalarCoverMap (2, x / curvePeriod))) ∘ sigma1.map),
        ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map Strip ∧
        IntegrableOn (fun p => (r * m60AreaGram g A.map p 0 0 +
          r⁻¹ * m60AreaGram g A.map p 1 1) / 2) m64AnnulusDomain ∧
        m64ClassicalWeightedGramEnergy g A r <
          (∫ x in scalarAnnulus, m60AreaDensity g f x) + eta := by
  obtain ⟨q, hmajor, hsmall⟩ := scalarLocalC1_exists_metric_majorant_area_lt g f
    scalarClosedAnnulus_isCompact hU hKU hf eta heta
  have hsmall' : (∫ p in scalarAnnulus, m60AreaDensity q id p) <
      (∫ p in scalarAnnulus, m60AreaDensity g f p) + eta := by
    simpa only [setIntegral_congr_set scalarAnnulus_ae_eq_closed] using hsmall
  obtain ⟨r, hr, L, F, sigma0, sigma1, hF, hFs, hFopen, hFclosed, -, -, hperiod,
    hs0, hs1, hm0, hm1, hd0, hd1, hb0, hb1, hconf, hFA, harea⟩ :=
    exists_lipschitz_free_modulus_conformal_cylinder q
  have hclosure : closure scalarAnnulus ⊆ K :=
    closure_minimal (fun x hx => ((scalarAnnulusDefining_pos x).mpr hx).le)
      (isClosed_le continuous_const scalarAnnulusDefining_smooth.continuous)
  have hmaps : MapsTo F m64AnnulusDomain U :=
    fun _ hp => hKU (hclosure (hFclosed ⟨hp.2.2.1, hp.2.2.2⟩))
  obtain ⟨A, hAeq⟩ :=
    scalarLocalC1ClosedCylinder_admit g f hU hf hF hmaps hperiod sigma0 sigma1 hb0 hb1
  have hStrip : IsOpen Strip := isOpen_Ioo.preimage (EuclideanSpace.proj 1).continuous
  have hFstrip : MapsTo F Strip K :=
    fun _ hp => ((scalarAnnulusDefining_pos _).mpr (hFopen hp)).le
  have hu : ContMDiffOn (𝓡 2) (𝓡 n) 1 (f ∘ F) Strip :=
    hf.comp (contMDiffOn_iff_contDiffOn.mpr (hFs.of_le (by simp)))
      (fun _ hp => hKU (hFstrip hp))
  let E := m64ModulusEnergyDensity g r (f ∘ F)
  have hEnonneg (p : Plane) : 0 ≤ E p := by
    exact div_nonneg (add_nonneg
      (mul_nonneg hr.le (m60AreaGram_diagonal_nonneg g (f ∘ F) p 0))
      (mul_nonneg (inv_nonneg.mpr hr.le) (m60AreaGram_diagonal_nonneg g (f ∘ F) p 1)))
      (by norm_num)
  have hEbound {p : Plane} (hp : p ∈ scalarCylinderFundamental) :
      E p ≤ m60AreaDensity q F p := by
    have hFd := (hFs.contDiffAt (hStrip.mem_nhds hp.1)).differentiableAt (by simp)
    have hfd := (hf.contMDiffAt (hU.mem_nhds (hKU (hFstrip hp.1)))).mdifferentiableAt one_ne_zero
    have h0 := mul_le_mul_of_nonneg_left
      (scalarLocal_comp_gram_le g q hfd hFd (hmajor _ (hFstrip hp.1)) 0) hr.le
    have h1 := mul_le_mul_of_nonneg_left
      (scalarLocal_comp_gram_le g q hfd hFd (hmajor _ (hFstrip hp.1)) 1) (inv_nonneg.mpr hr.le)
    rw [← scalarModulusEnergyDensity_eq_area q F hr p (hconf p hp.1).1 (hconf p hp.1).2]
    exact div_le_div_of_nonneg_right (add_le_add h0 h1) (by norm_num)
  have hEc : ContinuousOn E Strip := by
    have hG := scalarC1_AreaGram_continuousOn g hStrip hu
    have hentry (i j : Fin 2) : ContinuousOn (fun p => m60AreaGram g (f ∘ F) p i j) Strip :=
      (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hG)
    exact ((continuousOn_const.mul (hentry 0 0)).add
      (continuousOn_const.mul (hentry 1 1))).div_const 2
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
  have hAclosed : EqOn A.map (f ∘ F) {p | p 1 ∈ Icc (0 : ℝ) 1} :=
    scalar_periodic_eqOn_closedStrip (f := A.map) (g := f ∘ F)
      (fun x s _ => A.periodic x s) (fun x s hs => congrArg f (hperiod x s hs)) hAeq
  have hAstrip : EqOn A.map (f ∘ F) Strip := fun _ hp => hAclosed ⟨hp.1.le, hp.2.le⟩
  refine ⟨r, hr, sigma0, sigma1, hs0, hs1, hm0, hm1, hd0, hd1, A,
    hu.congr hAstrip, hAI, ?_⟩
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
    _ < (∫ x in scalarAnnulus, m60AreaDensity g f x) + eta := hsmall'




theorem exists_localC1_free_annulus_energy_lt_area
    (g : RiemannianMetric n M) (f : Plane → M)
    {U : Set Plane} (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U) (eta : ℝ) (heta : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧ ∃ sigma0 sigma1 : M64PeriodicDegreeOneLift,
      ContDiff ℝ 1 sigma0.map ∧ ContDiff ℝ 1 sigma1.map ∧
      StrictMono sigma0.map ∧ StrictMono sigma1.map ∧
      (∀ x : ℝ, 0 < deriv sigma0.map x) ∧ (∀ x : ℝ, 0 < deriv sigma1.map x) ∧
      ∃ A : M64Annulus g
        ((fun x => f (scalarCoverMap (1, x / curvePeriod))) ∘ sigma0.map)
        ((fun x => f (scalarCoverMap (2, x / curvePeriod))) ∘ sigma1.map),
        ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map m64AnnulusInterior ∧
        IntegrableOn (fun p => (r * m60AreaGram g A.map p 0 0 +
          r⁻¹ * m60AreaGram g A.map p 1 1) / 2) m64AnnulusDomain ∧
        m64ClassicalWeightedGramEnergy g A r <
          (∫ x in scalarAnnulus, m60AreaDensity g f x) + eta := by
  obtain ⟨r, hr, sigma0, sigma1, hs0, hs1, hm0, hm1, hd0, hd1, A, hA, hAI, hAE⟩ :=
    exists_localC1_free_annulus_energy_lt_area_fullStrip g f hU hKU hf eta heta
  refine ⟨r, hr, sigma0, sigma1, hs0, hs1, hm0, hm1, hd0, hd1, A, hA.mono ?_, hAI, hAE⟩
  intro p hp
  simp only [m64AnnulusInterior, Set.mem_preimage, Set.mem_pi, Set.mem_univ] at hp
  exact hp 1 trivial

end PoincareConjecture.M64Uniformization
