import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusPhaseEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarFreeModulusApproximation













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

local notation "Strip" => Set.preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)




theorem free_ramp_minimizing_sequence_with_upper_modulus
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hperiod0 : Function.Periodic gamma0 curvePeriod)
    (hperiod1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 t)
    (A0 : M64Annulus (P.flow.metric t) gamma0 gamma1) :
    ∃ H : ℝ, 0 < H ∧
      ∃ (r : ℕ → ℝ) (sigma0 sigma1 : ℕ → M64PeriodicDegreeOneLift)
        (A : ∀ j, M64Annulus (P.flow.metric t)
          (gamma0 ∘ (sigma0 j).map) (gamma1 ∘ (sigma1 j).map)),
        (∀ j, 0 < r j ∧ r j ≤ H) ∧
        (∀ j, ContDiff ℝ 1 (sigma0 j).map ∧ ContDiff ℝ 1 (sigma1 j).map) ∧
        (∀ j, StrictMono (sigma0 j).map ∧ StrictMono (sigma1 j).map) ∧
        (∀ j x, 0 < deriv (sigma0 j).map x ∧ 0 < deriv (sigma1 j).map x) ∧
        (∀ j, ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 (A j).map Strip) ∧
        (∀ j, IntegrableOn (fun p =>
          (r j * m60AreaGram (P.flow.metric t) (A j).map p 0 0 +
            (r j)⁻¹ * m60AreaGram (P.flow.metric t) (A j).map p 1 1) / 2) m64AnnulusDomain) ∧
        (∀ j, m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j) ≤
          m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 + 1) ∧
        Tendsto (fun j => m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j))
          atTop (𝓝 (m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1)) := by
  classical
  have h0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1 gamma0 := hgamma0.of_le (by norm_num)
  have h1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1 gamma1 := hgamma1.of_le (by norm_num)
  have hcand (j : ℕ) : ∃ r : ℝ, 0 < r ∧
      ∃ sigma0 sigma1 : M64PeriodicDegreeOneLift,
        ContDiff ℝ 1 sigma0.map ∧ ContDiff ℝ 1 sigma1.map ∧
        StrictMono sigma0.map ∧ StrictMono sigma1.map ∧
        (∀ x, 0 < deriv sigma0.map x) ∧ (∀ x, 0 < deriv sigma1.map x) ∧
        ∃ A : M64Annulus (P.flow.metric t) (gamma0 ∘ sigma0.map) (gamma1 ∘ sigma1.map),
          ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map Strip ∧
          IntegrableOn (fun p => (r * m60AreaGram (P.flow.metric t) A.map p 0 0 +
            r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1) / 2) m64AnnulusDomain ∧
          m64ClassicalWeightedGramEnergy (P.flow.metric t) A r <
            m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 + 1 / ((j : ℝ) + 1) := by
    have heps : 0 < 1 / ((j : ℝ) + 1) := by positivity
    obtain ⟨B, hB⟩ := m64LeastAnnulusArea_near_minimizer A0 (half_pos heps)
    obtain ⟨r, hr, sigma0, sigma1, hs0, hs1, hm0, hm1, hd0, hd1, A, hA, hI, hE⟩ :=
      M64Uniformization.exists_free_annulus_energy_lt_area B h0 h1 (half_pos heps)
    exact ⟨r, hr, sigma0, sigma1, hs0, hs1, hm0, hm1, hd0, hd1, A, hA, hI, by linarith⟩
  choose r hr sigma0 sigma1 hs0 hs1 hm0 hm1 hd0 hd1 A hA hI hE using hcand
  have htransport := m64FreeBoundaryAreaTransport_of_collars h0.continuous hperiod0
    (m64PeriodicC1Curve_metric_lipschitz (P.flow.metric t) h0 hperiod0)
    h1.continuous hperiod1
    (m64PeriodicC1Curve_metric_lipschitz (P.flow.metric t) h1 hperiod1)
  have hlower (j : ℕ) : m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 ≤
      m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j) :=
    m64LeastAnnulusArea_le_free_weightedGramEnergy htransport (sigma0 j) (sigma1 j)
      (A j) (hr j) (hI j)
  have hbound (j : ℕ) : m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j) ≤
      m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 + 1 := by
    have hsmall : 1 / ((j : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity : 0 < (j : ℝ) + 1)).mpr
        (by linarith [show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j])
    exact (hE j).le.trans (add_le_add le_rfl hsmall)
  let H := 2 * curvePeriod * (m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 + 1) /
    circumference ^ 2
  have hupper (j : ℕ) : r j ≤ H := free_ramp_annulus_modulus_le_of_energy_bound
    P t gamma0 hgamma0 hperiod0 hramp0 (sigma0 j) (A j) (hA j) (hr j) (hI j) (hbound j)
  have hH : 0 < H := (hr 0).trans_le (hupper 0)
  refine ⟨H, hH, r, sigma0, sigma1, A, fun j => ⟨hr j, hupper j⟩,
    fun j => ⟨hs0 j, hs1 j⟩, fun j => ⟨hm0 j, hm1 j⟩,
    fun j x => ⟨hd0 j x, hd1 j x⟩, hA, hI, hbound, ?_⟩
  have hlim : Tendsto
      (fun j : ℕ => m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 + 1 / ((j : ℝ) + 1))
      atTop (𝓝 (m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1)) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    hlower (fun j => (hE j).le)



theorem free_ramp_minimizing_sequence_with_convergent_modulus
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hperiod0 : Function.Periodic gamma0 curvePeriod)
    (hperiod1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 t)
    (A0 : M64Annulus (P.flow.metric t) gamma0 gamma1) :
    ∃ H r0 : ℝ, 0 < H ∧ r0 ∈ Icc (0 : ℝ) H ∧
      ∃ (r : ℕ → ℝ) (sigma0 sigma1 : ℕ → M64PeriodicDegreeOneLift)
        (A : ∀ j, M64Annulus (P.flow.metric t)
          (gamma0 ∘ (sigma0 j).map) (gamma1 ∘ (sigma1 j).map)),
        (∀ j, 0 < r j ∧ r j ≤ H) ∧ Tendsto r atTop (𝓝 r0) ∧
        (∀ j, ContDiff ℝ 1 (sigma0 j).map ∧ ContDiff ℝ 1 (sigma1 j).map) ∧
        (∀ j, StrictMono (sigma0 j).map ∧ StrictMono (sigma1 j).map) ∧
        (∀ j x, 0 < deriv (sigma0 j).map x ∧ 0 < deriv (sigma1 j).map x) ∧
        (∀ j, ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 (A j).map Strip) ∧
        (∀ j, IntegrableOn (fun p =>
          (r j * m60AreaGram (P.flow.metric t) (A j).map p 0 0 +
            (r j)⁻¹ * m60AreaGram (P.flow.metric t) (A j).map p 1 1) / 2) m64AnnulusDomain) ∧
        (∀ j, m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j) ≤
          m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 + 1) ∧
        Tendsto (fun j => m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j))
          atTop (𝓝 (m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1)) := by
  obtain ⟨H, hH, r, sigma0, sigma1, A, hr, hs, hm, hd, hA, hI, hE, hlim⟩ :=
    free_ramp_minimizing_sequence_with_upper_modulus P t gamma0 gamma1
      hgamma0 hgamma1 hperiod0 hperiod1 hramp0 A0
  obtain ⟨r0, hr0, k, hk, hk0⟩ := isCompact_Icc.tendsto_subseq
    (fun j => show r j ∈ Icc (0 : ℝ) H from ⟨(hr j).1.le, (hr j).2⟩)
  exact ⟨H, r0, hH, hr0, r ∘ k, sigma0 ∘ k, sigma1 ∘ k, fun j => A (k j),
    fun j => hr (k j), hk0, fun j => hs (k j), fun j => hm (k j),
    fun j => hd (k j), fun j => hA (k j), fun j => hI (k j), fun j => hE (k j),
    hlim.comp hk.tendsto_atTop⟩

end PoincareConjecture.M64
