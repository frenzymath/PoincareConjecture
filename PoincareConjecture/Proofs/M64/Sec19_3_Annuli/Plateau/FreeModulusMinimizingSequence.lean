import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusConfinedApproximation













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

local notation "Strip" => Set.preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)




theorem free_ramp_minimizing_sequence_of_disjoint_images
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hperiod0 : Function.Periodic gamma0 curvePeriod)
    (hperiod1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 t)
    (hdisjoint : Disjoint (range gamma0) (range gamma1))
    (A0 : M64Annulus (P.flow.metric t) gamma0 gamma1) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧
      ∃ (r : ℕ → ℝ) (sigma0 sigma1 : ℕ → M64PeriodicDegreeOneLift)
        (A : ∀ j, M64Annulus (P.flow.metric t)
          (gamma0 ∘ (sigma0 j).map) (gamma1 ∘ (sigma1 j).map)),
        (∀ j, r j ∈ Icc lo hi) ∧
        (∀ j, ContDiff ℝ 1 (sigma0 j).map ∧ ContDiff ℝ 1 (sigma1 j).map) ∧
        (∀ j, StrictMono (sigma0 j).map ∧ StrictMono (sigma1 j).map) ∧
        (∀ j x, 0 < deriv (sigma0 j).map x ∧ 0 < deriv (sigma1 j).map x) ∧
        (∀ j, ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 (A j).map Strip) ∧
        (∀ j, m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j) ≤
          m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 + 1) ∧
        Tendsto (fun j => m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j))
          atTop (𝓝 (m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1)) := by
  classical
  obtain ⟨lo, hi, hlo, hlohi, hcand⟩ := free_ramp_approximation_confined_of_disjoint_images
    P t gamma0 gamma1 hgamma0 hgamma1 hperiod0 hperiod1 hramp0 hdisjoint A0
  choose r hr sigma0 sigma1 hs0 hs1 hm0 hm1 hd0 hd1 A hA hI hE using
    fun j : ℕ => hcand (1 / ((j : ℝ) + 1)) (by positivity)
  have h0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1 gamma0 := hgamma0.of_le (by norm_num)
  have h1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1 gamma1 := hgamma1.of_le (by norm_num)
  have htransport := m64FreeBoundaryAreaTransport_of_collars h0.continuous hperiod0
    (m64PeriodicC1Curve_metric_lipschitz (P.flow.metric t) h0 hperiod0)
    h1.continuous hperiod1
    (m64PeriodicC1Curve_metric_lipschitz (P.flow.metric t) h1 hperiod1)
  have hlower (j : ℕ) : m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 ≤
      m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j) :=
    m64LeastAnnulusArea_le_free_weightedGramEnergy htransport (sigma0 j) (sigma1 j)
      (A j) (hlo.trans_le (hr j).1) (hI j)
  have hbound (j : ℕ) : m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j) ≤
      m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 + 1 := by
    have hsmall : 1 / ((j : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity : 0 < (j : ℝ) + 1)).mpr
        (by linarith [show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j])
    exact (hE j).le.trans (add_le_add le_rfl hsmall)
  refine ⟨lo, hi, hlo, hlohi, r, sigma0, sigma1, A, hr, fun j => ⟨hs0 j, hs1 j⟩,
    fun j => ⟨hm0 j, hm1 j⟩, fun j x => ⟨hd0 j x, hd1 j x⟩, hA, hbound, ?_⟩
  have hlim : Tendsto
      (fun j : ℕ => m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 + 1 / ((j : ℝ) + 1))
      atTop (𝓝 (m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1)) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    hlower (fun j => (hE j).le)

end PoincareConjecture.M64
